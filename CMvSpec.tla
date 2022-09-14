------------------------------ MODULE CMvSpec ------------------------------
(***************************************************************************
 TLA+ Specification for causal consistency model CMv
 ***************************************************************************)
 
EXTENDS Naturals, Sequences, TLC, Functions,RelationUtils, SequencesExt, FiniteSets

InitVal == 0

HLCeq(x, y) == IF x.p = y.p
                    THEN IF x.l = y.l THEN TRUE
                         ELSE FALSE
               ELSE FALSE   

RECURSIVE Seq2OpSet(_)
Seq2OpSet(s) == \* Transform a sequence s into the set of ops in s
    IF s = <<>> THEN {}
    ELSE LET h == Head(s)
             t == Tail(s)
         IN  {h} \cup Seq2OpSet(t)   
         
Ops(h, clients) ==
    UNION { Seq2OpSet(h[c]): c \in clients }
\* The program order of h \in History is a union of total orders among operations in the same session    

WriteOps(h, clients) == 
    {op \in Ops(h, clients): op.type = "write"}

ReadOps(h, clients) == 
    {op \in Ops(h, clients): op.type = "read"}  
    
SO(h, clients) == UNION {Seq2Rel(h[c]): c \in clients }      
-------------------------------------------------

\* The set of operations that preceed o \in Operation in session order in history h
SOPast(h, clients, o) == InverseImage(SO(h, clients), o) \cup {o} \* Original definition in paper, including itself

PreSeq(seq, o) == \* All of the operations before o in sequence seq
    LET so == Seq2Rel(seq)
    IN SelectSeq(seq, LAMBDA op: <<op, o>> \in so)
-------------------------------------------------
KvsSemantics(seq, o) == \* Is o \in Operation legal when it is appended to seq
    IF o.type = "write" THEN TRUE ELSE
    LET wseq == SelectSeq(seq, LAMBDA op: op.type = "write" /\ op.k = o.k)
    IN  IF wseq = <<>> THEN o.v = InitVal
        ELSE o.v = wseq[Len(wseq)].v
                
KvsSemanticsOperations(seq, ops) ==
    \A o \in ops:
        LET preSeq == PreSeq(seq, o)
        IN  KvsSemantics(preSeq, o)    
           
\* Return value consistency for V(e) = so^-1           
ReturnValueConisnstency(h, clients, seq, ops) ==
    \A o \in ops: LET sopast == SOPast(h, clients, o)
                  IN  KvsSemanticsOperations(seq, sopast)
        
-------------------------------------------------
\* Definition of relations used in CMv definition  

RF(h, clients) == 
    {<<w, r>> \in WriteOps(h, clients) \X ReadOps(h, clients): w.k = r.k /\ w.v = r.v /\ HLCeq(w.ts,r.ts)}

VIS(h, clients) == 
    TC( SO(h, clients) \cup RF(h, clients) )

HB(h, clients) == 
    TC( SO(h, clients) \cup VIS(h, clients) )    \*actually, HB = VIS    
        
CMvDef(h, clients) ==
     LET ops == Ops(h, clients)
         hb == HB(h, clients)
         vis == VIS(h, clients)
     IN \/ Cardinality(ops) <= 1
        \/ /\ Respect(vis, hb)
           /\ \E arb \in AllLinearExtensions(vis, ops):
              /\ ReturnValueConisnstency(h, clients, arb, ops)


=============================================================================

