--------------------------- MODULE SameSetTypeOK ---------------------------
EXTENDS SameSetImplementation, TLAPS

\* Type Statements
Valid_pc == pc \in [PROCESSES -> PCSet]
Valid_F == F \in UFAbsSet
Valid_u == u \in [PROCESSES -> NodeSet]
Valid_v == v \in [PROCESSES -> NodeSet]
Valid_w == w \in [PROCESSES -> NodeSet]
Valid_c == c \in [PROCESSES -> NodeSet]
Valid_d == d \in [PROCESSES -> NodeSet]
Valid_M == M \in SUBSET Configs
Valid_ret == ret \in [PROCESSES -> {ACK, TRUE, FALSE} \cup NodeSet]

TypeOK == 
    /\ Valid_pc
    /\ Valid_F
    /\ Valid_u
    /\ Valid_v
    /\ Valid_w
    /\ Valid_c
    /\ Valid_d
    /\ Valid_M
    /\ Valid_ret
    
LEMMA InitTypeOK == Init => TypeOK
  <1> USE DEF Init, TypeOK
  <1> SUFFICES ASSUME Init
               PROVE TypeOK
    OBVIOUS
  <1> TypeOK
    <2>1. Valid_pc
      BY DEF Valid_pc, PCSet
    <2>2. Valid_F
      BY DEF Valid_F, InitF, UFAbsSet
    <2>3. Valid_u
      BY DEF Valid_u
    <2>4. Valid_v
      BY DEF Valid_v
    <2>5. Valid_w
      BY DEF Valid_w
    <2>6. Valid_c
      BY DEF Valid_c
    <2>7. Valid_d
      BY DEF Valid_d
    <2>8. Valid_M
      BY DEF Valid_M, Configs, InitState, InitRet, InitOp, InitArg, StateSet, ReturnSet, OpSet, ArgSet, UFAbsSet
    <2>9. Valid_ret
      BY DEF Valid_ret
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9
  <1> QED
    OBVIOUS
    
LEMMA NextTypeOK == TypeOK /\ [Next]_varlist => TypeOK'
  <1> USE DEF TypeOK, varlist, Step, NodeSet, PCSet, Valid_pc, Valid_F, Valid_u, 
              Valid_v, Valid_w, Valid_c, Valid_d, Valid_M, Valid_ret, UFAbsSet
  <1> SUFFICES ASSUME TypeOK /\ [Next]_varlist
               PROVE  TypeOK'
    OBVIOUS
  <1>1. ASSUME NEW p \in PROCESSES, Decide(p)
        PROVE TypeOK'
    BY <1>1 DEF Decide
  <1>2. ASSUME NEW p \in PROCESSES, F1(p)
        PROVE TypeOK'
    BY <1>2 DEF F1
  <1>3. ASSUME NEW p \in PROCESSES, FR(p)
        PROVE TypeOK'
    BY <1>3 DEF FR
  <1>4. ASSUME NEW p \in PROCESSES, U1(p)
        PROVE TypeOK'
    <2> USE <1>4 DEF U1, UFUniteShared
    <2>1. Valid_pc'
      OBVIOUS
    <2>2. Valid_u'
      OBVIOUS
    <2>3. Valid_v'
      OBVIOUS
    <2>4. Valid_w'
      OBVIOUS
    <2>5. Valid_c'
      OBVIOUS
    <2>6. Valid_d'
      OBVIOUS
    <2>7. Valid_M'
      OBVIOUS
    <2>8. Valid_ret'
      OBVIOUS
    <2>9. Valid_F'
      <3>1. F' \in [NodeSet -> NodeSet]
        OBVIOUS
      <3>2. \A i \in NodeSet: F'[F'[i]] = F'[i]
        <4> CASE F' = [i \in NodeSet |-> IF F[i] = F[c[p]] THEN F[d[p]] ELSE F[i]]
          OBVIOUS
        <4> CASE F' = [i \in NodeSet |-> IF F[i] = F[d[p]] THEN F[c[p]] ELSE F[i]]
          OBVIOUS
        <4> QED
          OBVIOUS
      <3> QED
        BY <3>1, <3>2
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9
  <1>5. ASSUME NEW p \in PROCESSES, UR(p)
        PROVE TypeOK'
    BY <1>5 DEF UR
  <1>6. ASSUME NEW p \in PROCESSES, S1(p)
        PROVE TypeOK'
    BY <1>6 DEF S1
  <1>7. ASSUME NEW p \in PROCESSES, S2(p)
        PROVE TypeOK'
    BY <1>7 DEF S2
  <1>8. ASSUME NEW p \in PROCESSES, S3(p)
        PROVE TypeOK'
    BY <1>8 DEF S3
  <1>9. ASSUME NEW p \in PROCESSES, SR(p)
        PROVE TypeOK'
    BY <1>9 DEF SR
  <1>10. CASE UNCHANGED varlist
    BY <1>10
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10 DEF Step, Next
    
THEOREM SameSetTypeOK == SameSetSpec => []TypeOK
  BY PTL, InitTypeOK, NextTypeOK DEF SameSetSpec

=============================================================================
\* Modification History
\* Last modified Sun Feb 15 17:51:22 EST 2026 by karunram
\* Last modified Mon Jan 12 17:21:38 EST 2026 by elucca
\* Created Mon Jan 12 16:32:12 EST 2026 by elucca
