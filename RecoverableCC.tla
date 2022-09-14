--------------------------- MODULE RecoverableCC ---------------------------
\* Recoverable MongoDB causal protocol

EXTENDS Naturals, FiniteSets, Sequences, TLC, CMvSpec

\* constants and variables
CONSTANTS Client, Server,       \* the set of clients and servers
          Key, Value,           \* the set of keys and values
          Nil,                  \* model value, place holder
          OpTimes,              \* op count at most
          PtStop                \* max physical time

VARIABLES Primary,        \* Primary node
          Secondary,      \* secondary nodes
          Oplog,          \* oplog[s]: oplog at server[s]
          Store,          \* store[s]: data stored at server[s]
          Ct,             \* Ct[s]: cluster time at node s
          Ot,             \* Ot[s]: the last applied operation time at server s
          ServerMsg,      \* ServerMsg[s]: the channel of heartbeat msgs at server s
          Pt,             \* Pt[s]: physical time at server s
          State,          \* State[s]: the latest Ot of all servers that server s knows
          SyncSource,     \* sync source of server node s     
          BlockedClient,  \* BlockedClient: Client operations in progress
          BlockedThread,  \* BlockedThread: blocked user thread and content
          BlockedVar,     \* Used to wake up pending ops
          History,        \* History[c]: History sequence at client c
          Messages,       \* Message channels
          OpCount,        \* OpCount[c]: op count for client c  
          Cp,             \* Cp[s]: majority commit point at server s
          SnapshotTable,  \* SnapshotTable[s] : snapshot mapping table at server s  
          CurrentTerm     \* CurrentTerm[s]: current election term at server s 
                          \* -> updated in update_position, heartbeat and replicate
          
-----------------------------------------------------------------------------          
\* group related vars to optimize code
electionVars == <<Primary, Secondary>>              \* vars that are related to election  
storageVars == <<Oplog, Store>>                     \* vars that are related to storage
messageVar == <<ServerMsg>>                         \* var that is related to message
servernodeVars == <<Ot, SyncSource>>                \* vars that each server node holds for itself
learnableVars == <<Ct, State, Cp, CurrentTerm>>     \* vars that must learn from msgs
timeVar == <<Pt>>                                   \* var that is used for timing 
clientnodeVars == <<History, OpCount>>

serverVars == <<electionVars, storageVars, messageVar, servernodeVars, learnableVars, timeVar>>
tunableVars == <<BlockedClient, BlockedThread, History, Messages, OpCount, SnapshotTable>>  

vars == <<Primary, Secondary, Oplog, Store, Ct, Ot, Messages, 
          ServerMsg, BlockedClient, BlockedThread, OpCount, Pt, Cp, 
          State, SnapshotTable, History, CurrentTerm, SyncSource, BlockedVar>>      
-----------------------------------------------------------------------------
ASSUME Cardinality(Client) >= 1  \* at least one client
ASSUME Cardinality(Server) >= 2  \* at least one primary and one secondary
ASSUME Cardinality(Key) >= 1     \* at least one object
ASSUME Cardinality(Value) >= 2   \* at least two values to update
-----------------------------------------------------------------------------
\* Helpers
HLCLt(x, y) == IF x.p < y.p THEN TRUE
               ELSE IF x.p = y.p THEN IF x.l < y.l THEN TRUE
                                      ELSE FALSE
                    ELSE FALSE
HLCEq(x, y) == IF x.p = y.p
                    THEN IF x.l = y.l THEN TRUE
                         ELSE FALSE
               ELSE FALSE                    
                
HLCMin(x, y) == IF HLCLt(x, y) THEN x ELSE y
HLCMax(x, y) == IF HLCLt(x, y) THEN y ELSE x
HLCType == [ p : Nat, l : Nat ]
HLCMinSet(s) == CHOOSE x \in s: \A y \in s: ~HLCLt(y, x)   
Min(x, y) == IF x < y THEN x ELSE y
Max(x, y) == IF x > y THEN x ELSE y

\* snapshot helpers
RECURSIVE SelectSnapshotIndex_Rec(_, _, _)
SelectSnapshotIndex_Rec(stable, cp, index) ==
    IF index > Len(stable) THEN Nil \* cannot find such snapshot at cp
    ELSE IF HLCLt(stable[index].ot, cp) THEN SelectSnapshotIndex_Rec(stable, cp, index + 1) \* go further
         ELSE IF HLCLt(cp, stable[index].ot) THEN Nil
              ELSE index \* match
              
SelectSnapshot(stable, cp) == LET index == SelectSnapshotIndex_Rec(stable, cp, 1)
                              IN  IF index /= Nil THEN stable[index].store  
                                  ELSE Nil
                                  
SelectSnapshotIndex(stable, cp) == SelectSnapshotIndex_Rec(stable, cp, 1)

\* The election term of each oplog entry
LogTerm(i, index) == IF index = 0 THEN 0 ELSE Oplog[i][index].term   
LastTerm(i) == LogTerm(i, Len(Oplog[i]))   
                              
\* Is node i ahead of node j
NotBehind(i, j) == \/ LastTerm(i) > LastTerm(j)
                   \/ /\ LastTerm(i) = LastTerm(j)
                      /\ Len(Oplog[i]) >= Len(Oplog[j])                           

IsMajority(servers) == Cardinality(servers) * 2 > Cardinality(Server)
                                      
\* Return the maximum value from a set, or undefined if the set is empty.
MaxVal(s) == CHOOSE x \in s : \A y \in s : x >= y                            

\* clock
MaxPt == LET x == CHOOSE s \in Server: \A s1 \in Server \ {s}:
                            Pt[s] >= Pt[s1] IN Pt[x]      
                            
Tick(s) == Ct' = IF Ct[s].p >= Pt[s] THEN [ Ct EXCEPT ![s] = [ p |-> @.p, l |-> @.l+1] ]
                                     ELSE [ Ct EXCEPT ![s] = [ p |-> Pt[s], l |-> 0] ]  
                                     
\* Server s update its Ct according to msgCt and then tick                                     
UpdateAndTick(s, msgCt) ==
    LET newCt == [ Ct EXCEPT ![s] = HLCMax(Ct[s], msgCt) ] \* Update ct first according to msg
    IN  Ct' = IF newCt[s].p >= Pt[s] THEN [ newCt EXCEPT ![s] = [ p |-> @.p, l |-> @.l+1] ]
                                     ELSE [ newCt EXCEPT ![s] = [ p |-> Pt[s], l |-> 0] ]                  

\* heartbeat - Only Primary node sends heartbeat once advance pt
BroadcastHeartbeat(s) == 
    LET msg == [ type|-> "heartbeat", s |-> s, aot |-> Ot[s], 
                 ct |-> Ct[s], cp |-> Cp[s], term |-> CurrentTerm[s] ]
    IN ServerMsg' = [x \in Server |-> IF x = s THEN ServerMsg[x]
                                               ELSE Append(ServerMsg[x], msg)]     
                                                                                                                             
\* Can node i sync from node j?
CanSyncFrom(i, j) ==
    /\ Len(Oplog[i]) < Len(Oplog[j])
    /\ LastTerm(i) = LogTerm(j, Len(Oplog[i]))
    
\* Oplog entries needed to replicate from j to i
ReplicateOplog(i, j) ==     
    LET len_i == Len(Oplog[i])
        len_j == Len(Oplog[j])
    IN IF i \in Secondary /\ len_i < len_j
                        THEN SubSeq(Oplog[j], len_i + 1, len_j)
                        ELSE <<>>

\* Can node i rollback its log based on j's log
CanRollback(i, j) == /\ Len(Oplog[i]) > 0       
                     /\ Len(Oplog[j]) > 0
                     /\ LastTerm(i) < LastTerm(j)
                     /\ \/ Len(Oplog[i]) > Len(Oplog[j])
                        \/ /\ Len(Oplog[i]) <= Len(Oplog[j])
                           /\ LastTerm(i) /= LogTerm(j, Len(Oplog[i]))                       
                           
\* Returns the highest common index between two divergent logs. 
\* If there is no common index between the logs, returns 0.
RollbackCommonPoint(i, j) == 
    LET commonIndices == {k \in DOMAIN Oplog[i] : 
                            /\ k <= Len(Oplog[j])
                            /\ Oplog[i][k] = Oplog[j][k]} IN
        IF commonIndices = {} THEN 0 ELSE MaxVal(commonIndices)    
        
\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}
QuorumAgreeInSameTerm(states) == 
    LET quorums == {Q \in Quorum :
                    \* Make sure all nodes in quorum have actually applied some entries.
                    /\ \/ \A s \in Q : states[s].p > 0
                       \/ /\ \A s \in Q : states[s].p = 0
                          /\ \A s \in Q : states[s].l > 0
                    \* Make sure every applied entry in quorum has the same term.
                    /\ \A s, t \in Q : 
                       s # t => states[s].term = states[s].term} 
    IN quorums            

\* The set of servers whose replicate progress are greater than ot
ReplicatedServers(states, ot) ==
    LET serverSet == {subServers \in SUBSET(Server): \A s \in subServers: LET stateTime == [p|-> states[s].p, l|-> states[s].l]
                                                                          IN  ~HLCLt(stateTime, ot)}
    IN  CHOOSE maxSet \in serverSet: \A otherSet \in serverSet: Cardinality(otherSet) <= Cardinality(maxSet)
 
\* Compute a new common point according to new update position msg
ComputeNewCp(s) == 
    \* primary node: compute new mcp
    IF s \in Primary THEN 
        LET quorumAgree == QuorumAgreeInSameTerm(State[s]) IN
        IF  Cardinality(quorumAgree) > 0 
            THEN LET QuorumSet == CHOOSE i \in quorumAgree: TRUE
                     serverInQuorum == CHOOSE j \in QuorumSet: TRUE
                     termOfQuorum == State[s][serverInQuorum].term \* never commit log entries from previous terms
                     StateSet == {[p |-> State[s][j].p, l |-> State[s][j].l]: j \in QuorumSet}
                     newCommitPoint == HLCMinSet(StateSet)
                 IN  IF termOfQuorum = CurrentTerm[s]
                        THEN [p |-> newCommitPoint.p, l |-> newCommitPoint.l, term |-> termOfQuorum]
                     ELSE Cp[s]
          ELSE Cp[s]
    \* secondary node: update mcp   
    ELSE IF Len(ServerMsg[s]) /= 0 THEN
            LET msgCP == [ p |-> ServerMsg[s][1].cp.p, l |-> ServerMsg[s][1].cp.l ] IN 
            IF /\ ~ HLCLt(msgCP, Cp[s])
               /\ ~ HLCLt(Ot[s], msgCP)
               \* The term of cp must equal to the CurrentTerm of that node to advance it
               /\ ServerMsg[s][1].term = CurrentTerm[s] 
               THEN ServerMsg[s][1].cp
            ELSE Cp[s]
         ELSE Cp[s]
         
GetNewState(s, d, np, nl, nterm) == 
    LET newSubState == [p |-> np, l |-> nl, term |-> nterm] 
        sState == State[s]
    IN  [sState EXCEPT ![d] = newSubState]    
                                                      
-----------------------------------------------------------------------------
\* Init Part  
InitPrimary == Primary = {CHOOSE s \in Server: TRUE}
InitSecondary == Secondary = Server \ Primary
InitOplog == Oplog = [ s \in Server |-> <<>> ]
InitStore == Store = [ n \in Server \cup Client  |-> [ k \in Key |-> 0 ] ]
InitCt == Ct = [ n \in Server \cup Client |-> [ p |-> 0, l |-> 0 ] ]
InitOt == Ot = [ n \in Server \cup Client |-> [ p |-> 0, l |-> 0 ] ]
InitServerMsg == ServerMsg = [ s \in Server |-> <<>> ]
InitPt == Pt = [ s \in Server |-> 1 ]
InitState == State = [ s \in Server |-> [ s0 \in Server |-> 
                                              [ p |-> 0, l |-> 0, term |-> 0 ] ] ]
InitSyncSource == SyncSource = [ s \in Server |-> Nil] 
InitBlockedClient == BlockedClient = {}
InitBlockedThread == BlockedThread = [s \in Client |-> Nil ] 
InitHistory == History = [c \in Client |-> <<>>]  \* History operation seq is empty  
InitMessages == Messages = {}
InitOpCount == OpCount = [ c \in Client |-> OpTimes ]
InitCp == Cp = [ n \in Server \cup Client |-> [ p |-> 0, l |-> 0, term |-> 0 ] ]
InitSnap == SnapshotTable = [ s \in Server |-> <<[ ot |-> [ p |-> 0, l |-> 0 ], 
                                                   store |-> [ k \in Key |-> 0] ] >>]  
InitCurrentTerm == CurrentTerm = [ p \in Primary |-> 1 ] @@ [ s \in Server |-> 0 ] 
InitBlockedVar == BlockedVar = {}
                                                                             

Init == 
    /\ InitPrimary /\ InitSecondary /\ InitOplog /\ InitStore /\ InitCt 
    /\ InitOt /\ InitPt  /\ InitServerMsg /\ InitState 
    /\ InitSyncSource /\ InitBlockedClient /\ InitBlockedThread 
    /\ InitHistory /\ InitMessages /\ InitOpCount
    /\ InitCp /\ InitSnap /\ InitCurrentTerm /\ InitBlockedVar
     
-----------------------------------------------------------------------------
\* Next State Actions  
\* Replication Protocol: possible actions 

\* A primary node steps down to secondary
Stepdown == 
    /\ BlockedVar = {}
    /\ \E s \in Primary:
        /\ Primary' = Primary \ {s}
        /\ Secondary' = Secondary \cup {s}
    /\ UNCHANGED <<storageVars, servernodeVars, Ct, messageVar, timeVar, Cp, State, CurrentTerm, tunableVars, BlockedVar>>

\* There are majority nodes agree to elect node i to become primary                            
ElectPrimary ==
    /\ BlockedVar = {}
    /\ \E i \in Server: \E majorNodes \in SUBSET(Server):
        /\ IsMajority(majorNodes) 
        /\ \A j \in majorNodes: /\ NotBehind(i, j)
                                /\ CurrentTerm[i] >= CurrentTerm[j]
       \* voted nodes for i cannot be primary anymore
        /\ Primary' = LET possiblePrimary == Primary \ majorNodes
                      IN possiblePrimary \cup {i}
       \* add voted nodes into secondaries          
        /\ Secondary' = LET possibleSecondary == Secondary \cup majorNodes
                        IN possibleSecondary \ {i}    
       \* advance the term of voted nodes by magic                                                        
        /\ CurrentTerm' = [index \in Server |-> IF index \in (majorNodes \cup {i})
                                                THEN CurrentTerm[i] + 1
                                                ELSE CurrentTerm[index]]
       \* perform noop                                         
        /\ Oplog' = LET entry == [k |-> Nil, v |-> Nil, 
                                  ot |-> Ot[i], term |-> CurrentTerm'[i]]
                        newLog == Append(Oplog[i], entry)
                    IN [Oplog EXCEPT ![i] = newLog]                                         
        \* A primary node do not have any sync source                                        
        /\ SyncSource' = [SyncSource EXCEPT ![i] = Nil ]
    /\ UNCHANGED <<Store, Ct, Ot, messageVar, timeVar, Cp, State, tunableVars, BlockedVar>> 
                                                                                                                                                                                
\* A server node deal with heartbeat msg                                                                                                                                                                                                  
ServerTakeHeartbeat ==
    /\ BlockedVar = {}
    /\ \E s \in Server:
        /\ Len(ServerMsg[s]) /= 0  \* message channel is not empty
        /\ ServerMsg[s][1].type = "heartbeat"
        /\ CurrentTerm[s] = ServerMsg[s][1].term \* only consider heartbeat msg in same term
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], ServerMsg[s][1].ct) ]
        /\ State' = LET newState == GetNewState(s, ServerMsg[s][1].s, ServerMsg[s][1].aot.p, ServerMsg[s][1].aot.l,ServerMsg[s][1].term)
                    IN  [ State EXCEPT ![s] = newState]
        /\ Cp' = LET newcp == ComputeNewCp(s)
                 IN [ Cp EXCEPT ![s] = newcp ]
        /\ IF HLCLt(Cp[s], Cp'[s]) THEN BlockedVar' = BlockedVar \cup { c \in BlockedClient: BlockedThread[c].s = s}
           ELSE BlockedVar' = BlockedVar                 
       /\ ServerMsg' = [ ServerMsg EXCEPT ![s] = Tail(@) ]       
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, timeVar, CurrentTerm, tunableVars>>

\* A server node deal with update position msg
ServerTakeUpdatePosition == 
    /\ BlockedVar = {}
    /\ \E s \in Server:
        /\ Len(ServerMsg[s]) /= 0  \* message channel is not empty
        /\ ServerMsg[s][1].type = "update_position"
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], ServerMsg[s][1].ct) ] \* update ct accordingly
        /\ State' = LET newState == GetNewState(s, ServerMsg[s][1].s, ServerMsg[s][1].aot.p, ServerMsg[s][1].aot.l,ServerMsg[s][1].term)
                    IN  [ State EXCEPT ![s] = newState]
        /\ Cp' = LET newcp == ComputeNewCp(s)
                 IN [ Cp EXCEPT ![s] = newcp ]  
        /\ IF HLCLt(Cp[s], Cp'[s]) THEN BlockedVar' = BlockedVar \cup { c \in BlockedClient: BlockedThread[c].s = s}
           ELSE BlockedVar' = BlockedVar          
        /\ CurrentTerm' = [CurrentTerm EXCEPT ![s] = Max(CurrentTerm[s], ServerMsg[s][1].term)]             
        /\ ServerMsg' = LET newServerMsg == [ServerMsg EXCEPT ![s] = Tail(@)]
                       IN  ( LET  appendMsg == [ type |-> "update_position", s |-> ServerMsg[s][1].s, aot |-> ServerMsg[s][1].aot, 
                                          ct |-> ServerMsg[s][1].ct, cp |-> ServerMsg[s][1].cp, term |-> ServerMsg[s][1].term ]
                             IN ( LET newMsg == IF s \in Primary \/ SyncSource[s] = Nil
                                                    THEN newServerMsg \* If s is primary, accept the msg, else forward it to its sync source
                                                ELSE [newServerMsg EXCEPT ![SyncSource[s]] = Append(newServerMsg[SyncSource[s]], appendMsg)]
                                  IN newMsg))
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, timeVar, tunableVars>>                   
                  
                  
\* A primary node advance its physical time
AdvancePt == 
    /\ BlockedVar = {}
    /\ \E s \in Primary:            \* for simplicity
           /\ Pt[s] <= PtStop 
           /\ LET tickedPt == Pt[s] + 1
                  maxPt == Max(MaxPt, tickedPt)
              IN Pt' = [ s1 \in Server |-> maxPt ] 
\*           /\ Pt' = [ Pt EXCEPT ![s] = @+1 ] \* advance physical time
           /\ BroadcastHeartbeat(s)          \* broadcast heartbeat periodly
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, learnableVars, tunableVars, BlockedVar>>
                                    
\* Replication                                     
 Replicate == 
    /\ BlockedVar = {}
    /\ \E i, j \in Server: 
        /\ CanSyncFrom(i, j) \* i can sync from j only need not to rollback
        /\ i \in Secondary
        /\ ReplicateOplog(i, j) /= <<>>
        /\ Oplog' = [Oplog EXCEPT ![i] = @ \o ReplicateOplog(i, j)]
        /\ Store' = [Store EXCEPT ![i] =  Store[j]]
        /\ Ct' = [Ct EXCEPT ![i] = HLCMax(Ct[i], Ct[j])] \* update Ct[i] 
        /\ Ot' = [Ot EXCEPT ![i] = HLCMax(Ot[i], Ot[j])] \* update Ot[i]    
        /\ Cp' = [Cp EXCEPT ![i] = HLCMax(Cp[i], Cp[j])] \* update Cp[i]
        /\ IF HLCLt(Cp[i], Cp'[i]) THEN BlockedVar' = BlockedVar \cup { c \in BlockedClient: BlockedThread[c].s = i}
            ELSE BlockedVar' = BlockedVar      
        /\ CurrentTerm' = [CurrentTerm EXCEPT ![i] = Max(CurrentTerm[i], CurrentTerm[j])] \* update CurrentTerm
        /\ State' = 
            LET newStatei == [p |-> Ot'[i].p, l |-> Ot'[i].l, term |-> CurrentTerm'[i]]
                newStatej == [p |-> Ot[j].p, l |-> Ot[j].l,term |-> CurrentTerm[j]]
            IN LET SubHbState == State[i]
                   hb == [ SubHbState EXCEPT ![i] = newStatei ] \* update i's self state (used in mcp computation
                   hb1 == [hb EXCEPT ![j] = newStatej ] \* update j's state i knows 
               IN [ State EXCEPT ![i] = hb1]
        /\ LET msg == [ type |-> "update_position", s |-> i, aot |-> Ot'[i], ct |-> Ct'[i], cp |-> Cp'[i], term |-> CurrentTerm'[i] ]
           IN ServerMsg' = [ ServerMsg EXCEPT ![j] = Append(ServerMsg[j], msg) ]
        /\ SnapshotTable' = 
           LET SnapshotIndex == SelectSnapshotIndex(SnapshotTable[i], Ot'[i]) \* snapshot after store[i] changes
           IN  IF SnapshotIndex /= Nil
                THEN [ SnapshotTable EXCEPT ![i][SnapshotIndex] = [ot |-> Ot'[i], store |-> Store'[i]]]
               ELSE [ SnapshotTable EXCEPT ![i] = Append(@, [ot |-> Ot'[i], store |-> Store'[i] ]) ]      \* create a new snapshot           
        /\ SyncSource' = [SyncSource EXCEPT ![i] = j] 
    /\ UNCHANGED <<electionVars, timeVar, BlockedClient, BlockedThread, History, Messages, OpCount>>    
    
\* Simulate the situation that a node crash and suddently back to the state in Cp[s]
NodeCrashAndBack ==
    /\ BlockedVar = {}
    /\ \E s \in Server:
       /\ Len(Oplog[s]) >= 2 \* there is sth in the log
       /\ HLCLt([p |-> 0, l |-> 0], Cp[s])
       /\ SelectSnapshotIndex(SnapshotTable[s], Cp[s]) /= Nil \* exist related snapshot
       /\ Ot' = [ Ot EXCEPT ![s] = Cp[s] ]
       /\ Ct' = [ Ct EXCEPT ![s] = Cp[s] ]
       /\ Store' = [ Store EXCEPT ![s] = SelectSnapshot(SnapshotTable[s], Cp[s])]
       /\ SnapshotTable' = LET snapTail == CHOOSE n \in 1..Len(SnapshotTable[s]): HLCEq(SnapshotTable[s][n].ot, Cp[s])
                           IN  LET remainSnap == SubSeq(SnapshotTable[s], 1, snapTail)
                               IN  [SnapshotTable EXCEPT ![s] = remainSnap]
       /\ Oplog' = LET logTail == CHOOSE n \in 1..Len(Oplog[s]): HLCEq(Oplog[s][n].ot, Cp[s])
                   IN  LET remainLog == SubSeq(Oplog[s], 1, logTail)
                       IN  [Oplog EXCEPT ![s] = remainLog]
       /\ State' = LET newState == GetNewState(s, s, Ot'[s].p, Ot'[s].l, CurrentTerm[s])      
                   IN  [State EXCEPT ![s] = newState]      \* update primary state
    /\ UNCHANGED <<electionVars, ServerMsg, Pt, Cp, SyncSource, 
                   BlockedClient, BlockedThread, History, Messages, OpCount, CurrentTerm, BlockedVar>>                    
                    
\* Rollback i's oplog and recover it to j's state   
\* Recover to j's state immediately to prevent internal client request  
RollbackAndRecover ==
    /\ BlockedVar = {}
    /\ \E i, j \in Server:
        /\ i \in Secondary
        /\ CanRollback(i, j)
        /\ LET cmp == RollbackCommonPoint(i, j)  IN
           LET commonLog == SubSeq(Oplog[i], 1, cmp)
               appendLog == SubSeq(Oplog[j], cmp+1, Len(Oplog[j]))
           IN Oplog' = [Oplog EXCEPT ![i] = commonLog \o appendLog]
        /\ CurrentTerm' = [CurrentTerm EXCEPT ![i] = Max(CurrentTerm[i], CurrentTerm[j])] \* update CurrentTerm                                
        /\ Store' = [Store EXCEPT ![i] =  Store[j]]
        /\ Ct' = [Ct EXCEPT ![i] = HLCMax(Ct[i], Ct[j])] \* update Ct[i] 
        /\ Ot' = [Ot EXCEPT ![i] = HLCMax(Ot[i], Ot[j])] \* update Ot[i] 
        /\ Cp' = [Cp EXCEPT ![i] = HLCMax(Cp[i], Cp[j])] \* update Cp[i]
        /\ IF HLCLt(Cp[i], Cp'[i]) THEN BlockedVar' = BlockedVar \cup { c \in BlockedClient: BlockedThread[c].s = i}
            ELSE BlockedVar' = BlockedVar      
        /\ State' = 
            LET newStatei == [p |-> Ot'[i].p, l |-> Ot'[i].l, term |-> CurrentTerm'[i]]
                newStatej == [p |-> Ot[j].p, l |-> Ot[j].l,term |-> CurrentTerm[j]]
            IN LET SubHbState == State[i]
                   hb == [ SubHbState EXCEPT ![i] = newStatei ] \* update i's self state (used in mcp computation
                   hb1 == [hb EXCEPT ![j] = newStatej ] \* update j's state i knows 
               IN [ State EXCEPT ![i] = hb1]
        /\ SnapshotTable' = LET snapTail == CHOOSE n \in 1..Len(SnapshotTable[i]): HLCEq(SnapshotTable[i][n].ot, Cp'[i])
                            IN  LET remainSnap == SubSeq(SnapshotTable[i], 1, snapTail)
                               IN  [SnapshotTable EXCEPT ![i] = remainSnap]       
        /\ LET msg == [ type |-> "update_position", s |-> i, aot |-> Ot'[i], ct |-> Ct'[i], cp |-> Cp'[i], term |-> CurrentTerm'[i] ]
           IN ServerMsg' = [ ServerMsg EXCEPT ![j] = Append(ServerMsg[j], msg) ]
        /\ SyncSource' = [SyncSource EXCEPT ![i] = j]  
    /\ UNCHANGED <<electionVars, timeVar, BlockedClient, BlockedThread, History, Messages, OpCount>>    
    
----------------------------------------------------------------------------- 
\* Get and Put request
PutRequest == 
    /\ BlockedVar = {}
    /\ \E k \in Key, v \in Value, c \in Client \ BlockedClient, s \in Primary:
        /\ OpCount[c] /= 0 \* have chance to do an op
        /\ UpdateAndTick(s, Ct[c]) \* update and tick the ct of s according to c
        /\ Ot' = [ Ot EXCEPT ![s] = Ct'[s] ] \* advance the last applied operation time Ot[s]
        /\ Store' = [ Store EXCEPT ![s][k] = v ] 
        /\ SnapshotTable' = 
           LET SnapshotIndex == SelectSnapshotIndex(SnapshotTable[s], Ot'[s]) \* snapshot after store[i] changes
           IN  IF SnapshotIndex /= Nil
                THEN [ SnapshotTable EXCEPT ![s][SnapshotIndex] = [ot |-> Ot'[s], store |-> Store'[s]]]
               ELSE [ SnapshotTable EXCEPT ![s] = Append(@, [ot |-> Ot'[s], store |-> Store'[s] ]) ]      \* create a new snapshot 
        /\ Oplog' = LET entry == [k |-> k, v |-> v, ot |-> Ot'[s],term |-> CurrentTerm[s] ] \* append operation to oplog[s]
                        newLog == Append(Oplog[s], entry)
                    IN [Oplog EXCEPT ![s] = newLog]  
        /\ State' = LET newState == GetNewState(s, s, Ot'[s].p, Ot'[s].l, CurrentTerm[s])      
                    IN  [State EXCEPT ![s] = newState]      \* update primary state               
        /\ BlockedThread' = [BlockedThread EXCEPT ![c] = [type |-> "write", ot |-> Ot'[s], s |-> s, 
                                   k |-> k, v |-> v ] ] \* add the user History to BlockedThread[c]  
        /\ BlockedClient' = BlockedClient \cup {c} \* wait for server reply
        /\ BlockedVar' = BlockedVar \cup {c}
    /\ UNCHANGED <<electionVars, messageVar, Messages, SyncSource, timeVar, CurrentTerm, Cp, History, OpCount>>     
    
GetRequest ==
    /\ BlockedVar = {}
    /\ \E k \in Key, c \in Client \ BlockedClient, s \in Server: 
       /\ OpCount[c] /= 0
       /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], Ct[c]) ] \* update the ct of s according to c
       /\ BlockedThread' = [BlockedThread EXCEPT ![c] = 
                            [type |-> "read", s |-> s, k |-> k, ot |-> Ot[c]]]
       /\ BlockedClient' = BlockedClient \cup {c} 
       /\ BlockedVar' = BlockedVar \cup {c}
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, Messages, ServerMsg, CurrentTerm, History, OpCount, 
                   Pt, Cp, State, SnapshotTable>>   

PendingReply == 
    /\ BlockedVar /= {}
    /\ \E c \in BlockedVar:
        /\ \/ HLCLt(Cp[BlockedThread[c].s], BlockedThread[c].ot)
           \/ SelectSnapshotIndex(SnapshotTable[BlockedThread[c].s], Cp[BlockedThread[c].s]) = Nil
        /\ BlockedVar' = BlockedVar \ {c} \* wait for next wake up
    /\ UNCHANGED <<serverVars, tunableVars>>    
                
PutReply == 
    /\ BlockedVar /= {} \* There is some op wait to be returned
    /\ \E c \in BlockedVar:
        /\ BlockedThread[c] /=  Nil
        /\ BlockedThread[c].type = "write"
        /\ ~ HLCLt(Cp[BlockedThread[c].s], BlockedThread[c].ot) \* w:majority
        /\ Ct' = [ Ct EXCEPT ![c] = HLCMax(@, Ct[BlockedThread[c].s]) ]
        /\ Ot' = [ Ot EXCEPT ![c] = HLCMax(@, BlockedThread[c].ot) ]
        /\ History' = [ History EXCEPT ![c] = Append (@, [ type |-> "write", ts |-> BlockedThread[c].ot, 
                        k |-> BlockedThread[c].k, v |-> BlockedThread[c].v, count |-> OpCount[c]]) ]
        /\ OpCount' = [ OpCount EXCEPT ![c] = @-1 ]
        /\ BlockedClient' = BlockedClient \ {c}
        /\ BlockedThread' =  [ BlockedThread EXCEPT ![c] = Nil ] \* remove blocked state
        /\ BlockedVar' = BlockedVar \ {c}
     /\ UNCHANGED <<electionVars, storageVars, messageVar, Messages, SyncSource, State, Pt, Cp, CurrentTerm, SnapshotTable>>
     
GetReply ==
    /\ BlockedVar /= {}
    /\ \A v \in BlockedVar: BlockedThread[v].type /= "write"
    /\ \E c \in BlockedVar:
       /\ BlockedThread[c] /= Nil
       /\ BlockedThread[c].type = "read"    
       /\ ~ HLCLt(Cp[BlockedThread[c].s], BlockedThread[c].ot) \* wait until cp[s] >= target ot 
       /\ SelectSnapshotIndex(SnapshotTable[BlockedThread[c].s], Cp[BlockedThread[c].s]) /= Nil \* exist related snapshot
       /\ Ct' = [ Ct EXCEPT ![c] = HLCMax(@, Ct[BlockedThread[c].s]) ]
       /\ LET retVal == SelectSnapshot(SnapshotTable[BlockedThread[c].s], Cp[BlockedThread[c].s])[BlockedThread[c].k]
              otTime == [ p|-> Cp[BlockedThread[c].s].p, l |-> Cp[BlockedThread[c].s].l ]
          IN /\ Store' = [ Store EXCEPT ![c][BlockedThread[c].k] =  retVal]
             /\ Ot' = [ Ot EXCEPT ![c] = HLCMax(@, otTime) ]
             /\ History' = [ History EXCEPT ![c] = Append (@, [ type |-> "read", 
                             ts |-> otTime, k |-> BlockedThread[c].k, 
                             v |-> retVal, count |-> OpCount[c]]) ]
       /\ BlockedClient' = BlockedClient \ {c}
       /\ OpCount' = [ OpCount EXCEPT ![c] = @-1 ]             
       /\ BlockedThread' = [ BlockedThread EXCEPT ![c] = Nil ]  
       /\ BlockedVar' = BlockedVar \ {c}   
    /\ UNCHANGED <<electionVars, Oplog, messageVar, Messages, SyncSource, State, Pt, Cp, CurrentTerm, SnapshotTable>>                     
    
-----------------------------------------------------------------------------
\* Next state for all configurations
Next == \/ PutRequest \/ GetRequest
        \/ PutReply \/ GetReply \/ PendingReply
        \/ Replicate 
        \/ AdvancePt
        \/ ServerTakeHeartbeat
        \/ ServerTakeUpdatePosition
        \/ NodeCrashAndBack
        \/ Stepdown
        \/ RollbackAndRecover
        \/ ElectPrimary
        
Spec == Init /\ [][Next]_vars       

-----------------------------------------------------------------------------
\* Causal Specifications
MonotonicRead == \A c \in Client: \A i,j \in DOMAIN History[c]:
                    /\ i<j 
                    /\ History[c][i].op = "get"
                    /\ History[c][j].op = "get"
                    => ~ HLCLt(History[c][j].ts, History[c][i].ts)
   
MonotonicWrite == \A c \in Client: \A i,j \in DOMAIN History[c]:
                    /\ i<j 
                    /\ History[c][i].op = "put"
                    /\ History[c][j].op = "put"
                    => ~ HLCLt(History[c][j].ts, History[c][i].ts)   
                    
ReadYourWrite == \A c \in Client: \A i,j \in DOMAIN History[c]:
                /\ i < j
                /\ History[c][i].op = "put"
                /\ History[c][j].op = "get"
                => ~ HLCLt(History[c][j].ts, History[c][i].ts)
                
WriteFollowRead == \A c \in Client: \A i,j \in DOMAIN History[c]:
                /\ i < j
                /\ History[c][i].op = "get"
                /\ History[c][j].op = "put"
                => ~ HLCLt(History[c][j].ts, History[c][i].ts)
                
TotalOrderForWrites == LET writes == WriteOps(History, Client)
                        IN  \A w \in writes:
                                \A w1 \in writes:
                                   \/ w1 = w
                                   \/ w1.ts /= w.ts

MonotonicOt == \A c \in Client: \A i,j \in DOMAIN History[c]:
                /\ i < j 
                => ~HLCLt(History[c][j].ts, History[c][i].ts)
                
\* CMv Specification
CMvSatisfaction == 
                  \/ \A c \in Client: Len(History[c]) = 0
                  \/ CMvDef(History, Client)

=============================================================================
