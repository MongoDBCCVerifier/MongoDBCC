----------------------------- MODULE DurableCC -----------------------------
\* Durable MongoDB causal protocol

EXTENDS Naturals, FiniteSets, Sequences, TLC, CMvSpec

\* constants and variables
CONSTANTS Client, Server,       \* the set of clients and servers
          Key, Value,           \* the set of keys and values
          Nil,                  \* model value, place holder
          OpTimes,              \* op count at most
          PtStop               \* max physical time
          
VARIABLES Primary,        \* Primary node
          Secondary,      \* secondary nodes
          Oplog,          \* oplog[s]: oplog at server[s]
          Store,          \* store[s]: data stored at server[s]
          Ct,             \* Ct[s]: cluster time at node s
          Ot,             \* Ot[s]: the last applied operation time at server s
          ServerMsg,      \* ServerMsg[s]: the channel of heartbeat msgs at server s
          Pt,             \* Pt[s]: physical time at server s
          State,          \* State[s]: the latest Ot of all servers that server s knows
          SyncSource,     \* SyncSource[s]: sync source of server node s
          BlockedClient,  \* BlockedClient: Client operations in progress
          BlockedThread,  \* BlockedThread: blocked user thread and content
          History,        \* History[c]: History sequence at client c
          Messages,       \* Message channels
          OpCount,        \* OpCount[c]: op count for client c  
          Cp,             \* Cp[s]: majority commit point at server s
          SnapshotTable,  \* SnapshotTable[s] : snapshot mapping table at server s  
          BlockedVar      \* Used to wake up pending ops
          
-----------------------------------------------------------------------------          
\* group related vars to optimize code
electionVars == <<Primary, Secondary>>              \* vars that are related to election  
storageVars == <<Oplog, Store>>                     \* vars that are related to storage
messageVar == <<ServerMsg>>                         \* var that is related to message
servernodeVars == <<Ot, SyncSource>>                    \* vars that each server node holds for itself
learnableVars == <<Ct, State, Cp>>     \* vars that must learn from msgs
timeVar == <<Pt>>                                   \* var that is used for timing

serverVars == <<electionVars, storageVars, messageVar, servernodeVars, learnableVars, timeVar>>
tunableVars == <<BlockedClient, BlockedThread, History, Messages, OpCount, SnapshotTable>>

vars == <<Primary, Secondary, Oplog, Store, Ct, Ot, ServerMsg, 
          Pt, Cp, State, SyncSource, BlockedClient, BlockedThread,
          History, Messages, OpCount, SnapshotTable, BlockedVar>>
-----------------------------------------------------------------------------
ASSUME Cardinality(Client) >= 1  \* at least one clinet
ASSUME Cardinality(Server) >= 2  \* at least one primary and one secondary
ASSUME Cardinality(Key) >= 1     \* at least one object
ASSUME Cardinality(Value) >= 2   \* at least two values to update
-----------------------------------------------------------------------------
\* Helpers
HLCLt(x, y) == IF x.p < y.p THEN TRUE
               ELSE IF x.p = y.p
                       THEN IF x.l < y.l THEN TRUE
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

\* Is node i ahead of node j
NotBehind(i, j) == Len(Oplog[i]) >= Len(Oplog[j])                       

IsMajority(servers) == Cardinality(servers) * 2 > Cardinality(Server)
                                      
\* Return the maximum value from a set, or undefined if the set is empty.
MaxVal(s) == CHOOSE x \in s : \A y \in s : x >= y        

\* clock
MaxPt == LET x == CHOOSE s \in Server: \A s1 \in Server \ {s}:
                            Pt[s] >= Pt[s1] IN Pt[x]      
                            
Tick(s) == Ct' = IF Ct[s].p >= Pt[s] 
                    THEN [ Ct EXCEPT ![s] = [ p |-> @.p, l |-> @.l+1] ]
                 ELSE [ Ct EXCEPT ![s] = [ p |-> Pt[s], l |-> 0] ]  

\* Server s update its Ct according to msgCt and then tick                     
UpdateAndTick(s, msgCt) ==
    LET newCt == [ Ct EXCEPT ![s] = HLCMax(Ct[s], msgCt) ] \* Update ct first according to msg
    IN  Ct' = IF newCt[s].p >= Pt[s] THEN [ newCt EXCEPT ![s] = [ p |-> @.p, l |-> @.l+1] ]
                                     ELSE [ newCt EXCEPT ![s] = [ p |-> Pt[s], l |-> 0] ]                                   

\* heartbeat
\* Only Primary node sends heartbeat once advance pt
BroadcastHeartbeat(s) == 
    LET msg == [ type|-> "heartbeat", s |-> s, aot |-> Ot[s], 
                 ct |-> Ct[s], cp |-> Cp[s] ]
    IN ServerMsg' = [x \in Server |-> IF x = s THEN ServerMsg[x]
                                               ELSE Append(ServerMsg[x], msg)]                                                                                   

\* Can node i sync from node j?
CanSyncFrom(i, j) == Len(Oplog[i]) < Len(Oplog[j])

\* Oplog entries needed to replicate from j to i
ReplicateOplog(i, j) ==     
    LET len_i == Len(Oplog[i])
        len_j == Len(Oplog[j])
    IN IF i \in Secondary /\ len_i < len_j
                        THEN SubSeq(Oplog[j], len_i + 1, len_j)
                        ELSE <<>>
                        
\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}
QuorumAgree(states) == 
    LET quorums == {Q \in Quorum :
                    \* Make sure all nodes in quorum have actually applied some entries.
                    \/ \A s \in Q : states[s].p > 0
                    \/ /\ \A s \in Q : states[s].p = 0
                       /\ \A s \in Q : states[s].l > 0}
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
        LET quorumAgree == QuorumAgree(State[s]) IN
        IF  Cardinality(quorumAgree) > 0 
            THEN LET QuorumSet == CHOOSE i \in quorumAgree: TRUE
                     StateSet == {[p |-> State[s][j].p, l |-> State[s][j].l]: j \in QuorumSet}
                     newCommitPoint == HLCMinSet(StateSet)
                 IN  [p |-> newCommitPoint.p, l |-> newCommitPoint.l]
        ELSE Cp[s]
    \* secondary node: update mcp   
    ELSE IF Len(ServerMsg[s]) /= 0 THEN
            LET msgCP == [ p |-> ServerMsg[s][1].cp.p, l |-> ServerMsg[s][1].cp.l ] IN 
            IF /\ ~ HLCLt(msgCP, Cp[s])
               /\ ~ HLCLt(Ot[s], msgCP)
               THEN ServerMsg[s][1].cp
            ELSE Cp[s]
         ELSE Cp[s]
    
GetNewState(s, d, np, nl) == 
    LET newSubState == [p |-> np, l |-> nl] 
        sState == State[s]
    IN  [sState EXCEPT ![d] = newSubState]  
                  
\* Init Part                       
-----------------------------------------------------------------------------
InitPrimary == Primary = {CHOOSE s \in Server: TRUE}
InitSecondary == Secondary = Server \ Primary
InitOplog == Oplog = [ s \in Server |-> <<>> ]
InitStore == Store = [ n \in Server \cup Client  |-> [ k \in Key |-> 0 ] ]
InitCt == Ct = [ n \in Server \cup Client |-> [ p |-> 0, l |-> 0 ] ]
InitOt == Ot = [ n \in Server \cup Client |-> [ p |-> 0, l |-> 0 ] ]
InitServerMsg == ServerMsg = [ s \in Server |-> <<>> ]
InitPt == Pt = [ s \in Server |-> 1 ]
InitState == State = [ s \in Server |-> [ s0 \in Server |-> [ p |-> 0, l |-> 0] ] ] 
InitSyncSource == SyncSource = [ s \in Server |-> Nil]    
InitBlockedClient == BlockedClient = {}
InitBlockedThread == BlockedThread = [ s \in Client |-> Nil ]
InitHistory == History = [ c \in Client |-> <<>> ]
InitMessages == Messages = {}
InitOpCount == OpCount = [ c \in Client |-> OpTimes ]   
InitCp == Cp = [ n \in Server \cup Client |-> [ p |-> 0, l |-> 0 ] ]
InitSnap == SnapshotTable = [ s \in Server |-> <<[ ot |-> [ p |-> 0, l |-> 0 ], 
                                                   store |-> [ k \in Key |-> 0] ] >>]     
InitBlockedVar == BlockedVar = {}                                                                                                             

Init == 
    /\ InitPrimary /\ InitSecondary /\ InitOplog /\ InitStore /\ InitCt 
    /\ InitOt /\ InitPt /\ InitServerMsg /\ InitState
    /\ InitSyncSource /\ InitBlockedClient /\ InitBlockedThread
    /\ InitHistory /\ InitMessages /\ InitOpCount 
    /\ InitCp /\ InitSnap /\ InitBlockedVar
    
\* Next State Actions  
\* Replication Protocol: possible actions  
-----------------------------------------------------------------------------                                                           
\* A server node deal with heartbeat msg                                                                                                                                                                                                          
ServerTakeHeartbeat ==
    /\ BlockedVar = {}
    /\ \E s \in Server:
        /\ Len(ServerMsg[s]) /= 0  \* message channel is not empty
        /\ ServerMsg[s][1].type = "heartbeat"
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], ServerMsg[s][1].ct) ]          
        /\ State' = LET newState == GetNewState(s, ServerMsg[s][1].s, ServerMsg[s][1].aot.p, ServerMsg[s][1].aot.l)
                    IN  [State EXCEPT ![s] = newState]
        /\ Cp' = LET newcp == ComputeNewCp(s)
                 IN [ Cp EXCEPT ![s] = newcp ]
        /\ IF HLCLt(Cp[s], Cp'[s]) THEN BlockedVar' = BlockedVar \cup { c \in BlockedClient: BlockedThread[c].s = s}
           ELSE BlockedVar' = BlockedVar         
       /\ ServerMsg' = [ ServerMsg EXCEPT ![s] = Tail(@) ]    
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, timeVar, tunableVars>>

\* A server node deal with update position msg
ServerTakeUpdatePosition == 
    /\ BlockedVar = {}
    /\ \E s \in Server:
        /\ Len(ServerMsg[s]) /= 0  \* message channel is not empty
        /\ ServerMsg[s][1].type = "update_position"
        /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], ServerMsg[s][1].ct) ] \* update ct accordingly
        /\ State' = LET newState == GetNewState(s, ServerMsg[s][1].s, ServerMsg[s][1].aot.p, ServerMsg[s][1].aot.l)
                    IN  [State EXCEPT ![s] = newState]
        /\ Cp' = LET newcp == ComputeNewCp(s)
                 IN [ Cp EXCEPT ![s] = newcp ] 
        /\ IF HLCLt(Cp[s], Cp'[s]) THEN BlockedVar' = BlockedVar \cup { c \in BlockedClient: BlockedThread[c].s = s}
           ELSE BlockedVar' = BlockedVar
        /\ ServerMsg' = LET newServerMsg == [ServerMsg EXCEPT ![s] = Tail(@)]
                       IN  ( LET  appendMsg == [ type |-> "update_position", s |-> ServerMsg[s][1].s, aot |-> ServerMsg[s][1].aot, 
                                          ct |-> ServerMsg[s][1].ct, cp |-> ServerMsg[s][1].cp ]
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
               
\* Replicate oplog from node j to node i, and update related structures accordingly
 Replicate == 
    /\ BlockedVar = {}
    /\ \E i, j \in Server: 
        /\ CanSyncFrom(i, j) \* i can sync from j
        /\ i \in Secondary
        /\ ReplicateOplog(i, j) /= <<>>
        /\ Oplog' = [Oplog EXCEPT ![i] = @ \o ReplicateOplog(i, j)]
        /\ Store' = [Store EXCEPT ![i] =  Store[j]]
        /\ Ct' = [Ct EXCEPT ![i] = HLCMax(Ct[i], Ct[j])] \* update Ct[i] 
        /\ Ot' = [Ot EXCEPT ![i] = HLCMax(Ot[i], Ot[j])] \* update Ot[i]    
        /\ Cp' = [Cp EXCEPT ![i] = HLCMax(Cp[i], Cp[j])] \* update Cp[i]
        /\ IF HLCLt(Cp[i], Cp'[i]) THEN BlockedVar' = BlockedVar \cup { c \in BlockedClient: BlockedThread[c].s = i}
           ELSE BlockedVar' = BlockedVar
        /\ State' = 
            LET newStatei == [p |-> Ot'[i].p, l |-> Ot'[i].l ]
                newStatej == [p |-> Ot[j].p, l |-> Ot[j].l ]
            IN LET SubHbState == State[i]
                   hb == [ SubHbState EXCEPT ![i] = newStatei ] \* update i's self state (used in mcp computation
                   hb1 == [hb EXCEPT ![j] = newStatej ] \* update j's state i knows 
               IN [ State EXCEPT ![i] = hb1]
        /\ SnapshotTable' = 
           LET SnapshotIndex == SelectSnapshotIndex(SnapshotTable[i], Ot'[i]) \* snapshot after store[i] changes
           IN  IF SnapshotIndex /= Nil
                THEN [ SnapshotTable EXCEPT ![i][SnapshotIndex] = [ot |-> Ot'[i], store |-> Store'[i]]]
               ELSE [ SnapshotTable EXCEPT ![i] = Append(@, [ot |-> Ot'[i], store |-> Store'[i] ]) ]      \* create a new snapshot        
        /\ LET msg == [ type |-> "update_position", s |-> i, aot |-> Ot'[i], ct |-> Ct'[i], cp |-> Cp'[i] ]
           IN ServerMsg' = [ ServerMsg EXCEPT ![j] = Append(ServerMsg[j], msg) ]
        /\ SyncSource' = [SyncSource EXCEPT ![i] = j] 
    /\ UNCHANGED <<electionVars, timeVar, BlockedClient, BlockedThread, History, Messages, OpCount>>        
       
----------------------------------------------------------------------------- 
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
        /\ Oplog' = LET entry == [k |-> k, v |-> v, ot |-> Ot'[s] ] \* append operation to oplog[s]
                        newLog == Append(Oplog[s], entry)
                    IN [Oplog EXCEPT ![s] = newLog]  
        /\ State' = LET newState == GetNewState(s, s, Ot'[s].p, Ot'[s].l)      
                    IN  [State EXCEPT ![s] = newState]      \* update primary state               
        /\ BlockedThread' = [BlockedThread EXCEPT ![c] = [type |-> "write", ot |-> Ot'[s], s |-> s, 
                                   k |-> k, v |-> v ] ] \* add the user History to BlockedThread[c]  
        /\ BlockedClient' = BlockedClient \cup {c} \* wait for server reply
        /\ BlockedVar' = BlockedVar \cup {c}
    /\ UNCHANGED <<electionVars, messageVar, Messages, SyncSource, timeVar, Cp, History, OpCount>>     
 
GetRequest ==
    /\ BlockedVar = {}
    /\ \E k \in Key, c \in Client \ BlockedClient, s \in Server: 
       /\ OpCount[c] /= 0
       /\ Ct' = [ Ct EXCEPT ![s] = HLCMax(Ct[s], Ct[c]) ] \* update the ct of s according to c
       /\ BlockedThread' = [BlockedThread EXCEPT ![c] = 
                            [type |-> "read", s |-> s, k |-> k, ot |-> Ot[c]]]
       /\ BlockedClient' = BlockedClient \cup {c} 
       /\ BlockedVar' = BlockedVar \cup {c}
    /\ UNCHANGED <<electionVars, storageVars, servernodeVars, Messages, ServerMsg, History, OpCount, 
                   Pt, Cp, State, SnapshotTable>>   

\* Get and put request 
----------------------------------------------------------------------------- 

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
     /\ UNCHANGED <<electionVars, storageVars, messageVar, Messages, SyncSource, State, Pt, Cp, SnapshotTable>>

GetReply ==
    /\ BlockedVar /= {}
    /\ \A v \in BlockedVar: BlockedThread[v].type /= "write"
    /\ \E c \in BlockedVar:
       /\ BlockedThread[c] /= Nil
       /\ BlockedThread[c].type = "read"    
       /\ ~ HLCLt(Cp[BlockedThread[c].s], BlockedThread[c].ot) \* wait until cp[s] >= target ot 
       /\ SelectSnapshotIndex(SnapshotTable[BlockedThread[c].s], Cp[BlockedThread[c].s]) /= Nil \* exist related snapshot
       /\ Ct' = [ Ct EXCEPT ![c] = HLCMax(@, Ct[BlockedThread[c].s]) ]
       /\ Ot' = [ Ot EXCEPT ![c] = HLCMax(@, Cp[BlockedThread[c].s]) ]
       /\ LET retVal == SelectSnapshot(SnapshotTable[BlockedThread[c].s], Cp[BlockedThread[c].s])[BlockedThread[c].k]
          IN /\ Store' = [ Store EXCEPT ![c][BlockedThread[c].k] =  retVal]
             /\ History' = [ History EXCEPT ![c] = Append (@, [ type |-> "read", 
                             ts |-> Cp[BlockedThread[c].s], k |-> BlockedThread[c].k, 
                             v |-> retVal, count |-> OpCount[c]]) ]
       /\ BlockedClient' = BlockedClient \ {c}
       /\ OpCount' = [ OpCount EXCEPT ![c] = @-1 ]             
       /\ BlockedThread' = [ BlockedThread EXCEPT ![c] = Nil ]  
       /\ BlockedVar' = BlockedVar \ {c}   
    /\ UNCHANGED <<electionVars, Oplog, messageVar, Messages, SyncSource, State, Pt, Cp, SnapshotTable>>
    
----------------------------------------------------------------------------- 

\* Simulate the situation that the primary node crash and suddently back to the state in Cp[s]
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
       /\ Oplog' = LET logTail == CHOOSE n \in 1..Len(Oplog[s]): Oplog[s][n].ot = Cp[s]
                   IN  LET remainLog == SubSeq(Oplog[s], 1, logTail)
                       IN  [Oplog EXCEPT ![s] = remainLog]
       /\ State' = LET newState == GetNewState(s, s, Ot'[s].p, Ot'[s].l)      
                   IN  [State EXCEPT ![s] = newState]      \* update primary state
    /\ UNCHANGED <<electionVars, ServerMsg, Pt, Cp, SyncSource, 
                   BlockedClient, BlockedThread, History, Messages, OpCount, BlockedVar>>

-----------------------------------------------------------------------------                 
\* Next state for all configurations
Next == \/ Replicate
        \/ AdvancePt
        \/ ServerTakeHeartbeat
        \/ ServerTakeUpdatePosition
        \/ PutRequest
        \/ GetRequest
        \/ PendingReply
        \/ PutReply
        \/ GetReply
        \/ NodeCrashAndBack
        
Spec == Init /\ [][Next]_vars      

-----------------------------------------------------------------------------
\* Causal Specifications
MonotonicRead == \A c \in Client: \A i,j \in DOMAIN History[c]:
                    /\ i<j 
                    /\ History[c][i].type = "read"
                    /\ History[c][j].type = "read"
                    => ~ HLCLt(History[c][j].ts, History[c][i].ts)
   
MonotonicWrite == \A c \in Client: \A i,j \in DOMAIN History[c]:
                    /\ i<j 
                    /\ History[c][i].type = "write"
                    /\ History[c][j].type = "write"
                    => ~ HLCLt(History[c][j].ts, History[c][i].ts)   
                    
ReadYourWrite == \A c \in Client: \A i,j \in DOMAIN History[c]:
                /\ i < j
                /\ History[c][i].type = "write"
                /\ History[c][j].type = "read"
                => ~ HLCLt(History[c][j].ts, History[c][i].ts)
                
WriteFollowRead == \A c \in Client: \A i,j \in DOMAIN History[c]:
                /\ i < j
                /\ History[c][i].type = "read"
                /\ History[c][j].type = "write"
                => ~ HLCLt(History[c][j].ts, History[c][i].ts)
                
TotoalOrderForWrites == LET writes == WriteOps(History, Client)
                        IN  \A w \in writes:
                                \A w1 \in writes:
                                   \/ w1 = w
                                   \/ w1.ts /= w.ts

MonotonicOt == \A c \in Client: \A i,j \in DOMAIN History[c]:
                /\ i < j 
                => ~HLCLt(History[c][j].ts, History[c][i].ts)
                
\* CMv Specifaction
CMvSatisfaction == 
                  \/ \A c \in Client: Len(History[c]) = 0
                  \/ CMvDef(History, Client)

=============================================================================
