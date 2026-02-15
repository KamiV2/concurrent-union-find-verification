---------------------------- MODULE SameSetInv ----------------------------
EXTENDS SameSetTypeOK

Con_U1(t,p) == pc[p] = "U1" => /\ t.op[p] = "U"
                             /\ t.arg[p] = <<c[p], d[p]>>
                             /\ t.ret[p] = BOT

Con_UR(t,p) == pc[p] = "UR" => /\ t.op[p] = "U"
                             /\ t.arg[p] = <<c[p], d[p]>>
                             /\ t.ret[p] = ret[p]
                                                          
Con_F1(t,p) == pc[p] = "F1" => /\ t.op[p] = "F"
                             /\ t.arg[p] = c[p]
                             /\ t.ret[p] = BOT

Con_FR(t,p) == pc[p] = "FR" => /\ t.op[p] = "F"
                             /\ t.arg[p] = c[p]
                             /\ t.ret[p] = ret[p]
   
Con_S1(t,p) == pc[p] = "S1" => /\ t.op[p] = "S"
                             /\ t.arg[p] = <<c[p], d[p]>>
                             /\ t.ret[p] = BOT

Con_S2(t,p) == pc[p] = "S2" => /\ t.op[p] = "S"
                             /\ t.arg[p] = <<c[p], d[p]>>
                             /\ t.ret[p] = BOT

Con_S3(t,p) == pc[p] = "S3" => /\ t.op[p] = "S"
                             /\ t.arg[p] = <<c[p], d[p]>>
                             /\ \/ t.ret[p] = BOT
                                \/ /\ F[u[p]] = u[p]
                                   /\ t.ret[p] = FALSE

Con_SR(t,p) == pc[p] = "SR" => /\ t.op[p] = "S"
                             /\ t.arg[p] = <<c[p], d[p]>>
                             /\ t.ret[p] = ret[p]
                                                          
Con_0(t,p) == pc[p] = "0" => /\ t.op[p] = BOT
                           /\ t.arg[p] = BOT
                           /\ t.ret[p] = BOT


Con_U1Prime(t,p) == pc'[p] = "U1" => /\ t.op[p] = "U"
                                   /\ t.arg[p] = <<c'[p], d'[p]>>
                                   /\ t.ret[p] = BOT

Con_URPrime(t,p) == pc'[p] = "UR" => /\ t.op[p] = "U"
                                   /\ t.arg[p] = <<c'[p], d'[p]>>
                                   /\ t.ret[p] = ret'[p]
                                                          
Con_F1Prime(t,p) == pc'[p] = "F1" => /\ t.op[p] = "F"
                                   /\ t.arg[p] = c'[p]
                                   /\ t.ret[p] = BOT

Con_FRPrime(t,p) == pc'[p] = "FR" => /\ t.op[p] = "F"
                                   /\ t.arg[p] = c'[p]
                                   /\ t.ret[p] = ret'[p]
   
Con_S1Prime(t,p) == pc'[p] = "S1" => /\ t.op[p] = "S"
                                   /\ t.arg[p] = <<c'[p], d'[p]>>
                                   /\ t.ret[p] = BOT

Con_S2Prime(t,p) == pc'[p] = "S2" => /\ t.op[p] = "S"
                                   /\ t.arg[p] = <<c'[p], d'[p]>>
                                   /\ t.ret[p] = BOT

Con_S3Prime(t,p) == pc'[p] = "S3" => /\ t.op[p] = "S"
                                   /\ t.arg[p] = <<c'[p], d'[p]>>
                                   /\ \/ t.ret[p] = BOT
                                      \/ /\ F'[u'[p]] = u'[p]
                                         /\ t.ret[p] = FALSE

Con_SRPrime(t,p) == pc'[p] = "SR" => /\ t.op[p] = "S"
                                   /\ t.arg[p] = <<c'[p], d'[p]>>
                                   /\ t.ret[p] = ret'[p]
                                                          
Con_0Prime(t,p) == pc'[p] = "0" => /\ t.op[p] = BOT
                                 /\ t.arg[p] = BOT
                                 /\ t.ret[p] = BOT


Q == {t \in Configs: 
      /\ t.sigma = F
      /\ \A p \in PROCESSES: /\ Con_U1(t,p)
                             /\ Con_UR(t,p)
                             /\ Con_F1(t,p)
                             /\ Con_FR(t,p)
                             /\ Con_S1(t,p)
                             /\ Con_S2(t,p)
                             /\ Con_S3(t,p)
                             /\ Con_SR(t,p)
                             /\ Con_0(t,p)}
                             
SamePart == \A p \in PROCESSES : pc[p] \in {"S2", "S3", "SR"} => F[u[p]] = F[c[p]] /\ F[v[p]] = F[d[p]]

QNE == Q # {}

QinM == Q \in SUBSET M

Linearizable == M # {}

Lines == {"F1", "FR", "U1", "UR", "S1", "S2", "S3", "SR", "0"}

ProcOpPrime == [p \in PROCESSES |-> IF pc'[p] \in {"F1", "FR"} THEN "F"
                                    ELSE IF pc'[p] \in {"U1", "UR"} THEN "U"
                                    ELSE IF pc'[p] \in {"S1", "S2", "S3", "SR"} THEN "S"
                                    ELSE BOT]

ProcArgPrime == [p \in PROCESSES |-> IF pc'[p] \in {"F1", "FR"} THEN c'[p]
                                     ELSE IF pc'[p] \in {"U1", "UR", "S1", "S2", "S3", "SR"} THEN <<c'[p], d'[p]>>
                                     ELSE BOT]

ProcRetPrime == [p \in PROCESSES |-> IF pc'[p] \in {"FR", "UR", "SR"} THEN ret'[p]
                                     ELSE BOT]

LEMMA LinReqs == QNE /\ QinM => Linearizable
  BY DEF QNE, QinM, Linearizable

LEMMA SameSetInitSamePart == Init => SamePart
  BY DEF Init, SamePart

LEMMA SameSetNextSamePart == SamePart /\ TypeOK /\ [Next]_varlist => SamePart'
  <1> SUFFICES ASSUME SamePart /\ TypeOK /\ [Next]_varlist
               PROVE  SamePart'
    OBVIOUS
  <1> USE DEF TypeOK, Valid_pc, Valid_F, Valid_u, Valid_v, Valid_w, SamePart,
              Valid_c, Valid_d, Valid_M, Valid_ret, Configs, StateSet, ReturnSet, 
              OpSet, ArgSet, UFAbsSet, Q, Con_F1, Con_FR, Con_U1, Con_UR, Con_S1, Con_S2, Con_S3, Con_SR, Con_0
  <1>0. TypeOK'
    BY NextTypeOK
  <1>1. ASSUME NEW p \in PROCESSES, Decide(p)
        PROVE SamePart'
    BY <1>1 DEF Decide
  <1>2. ASSUME NEW p \in PROCESSES, F1(p)
        PROVE SamePart'
    BY <1>2 DEF F1 
  <1>3. ASSUME NEW p \in PROCESSES, FR(p)
        PROVE SamePart'
    BY <1>3 DEF FR
  <1>4. ASSUME NEW p \in PROCESSES, U1(p)
        PROVE SamePart'
    <2> USE <1>4 DEF U1
    <2> SUFFICES ASSUME NEW q \in PROCESSES', pc'[q] \in {"S2", "S3", "SR"}
                 PROVE (/\ F[u[q]] = F[c[q]] 
                        /\ F[v[q]] = F[d[q]])'
      OBVIOUS
    <2>1. pc[q] \in {"S2", "S3", "SR"}
      OBVIOUS
    <2>2. /\ F[u[q]] = F[c[q]] 
          /\ F[v[q]] = F[d[q]]
      BY <2>1
    <2> CASE F' = [i \in NodeSet |-> IF F[i] = F[c[q]] THEN F[d[q]] ELSE F[i]]
      OBVIOUS
    <2> CASE F' = [i \in NodeSet |-> IF F[i] = F[d[q]] THEN F[c[q]] ELSE F[i]]
      OBVIOUS
    <2> QED
      BY DEF Con_U1, UFUniteShared
  <1>5. ASSUME NEW p \in PROCESSES, UR(p)
        PROVE SamePart'
    BY <1>5 DEF UR
  <1>6. ASSUME NEW p \in PROCESSES, S1(p)
        PROVE SamePart'
    BY <1>6 DEF S1
  <1>7. ASSUME NEW p \in PROCESSES, S2(p)
        PROVE SamePart'
    BY <1>7, ZenonT(30) DEF S2
  <1>8. ASSUME NEW p \in PROCESSES, S3(p)
        PROVE SamePart'
    BY <1>8 DEF S3
  <1>9. ASSUME NEW p \in PROCESSES, SR(p)
        PROVE SamePart'
    BY <1>9 DEF SR
  <1>10. ASSUME UNCHANGED varlist
         PROVE SamePart'
    BY <1>10 DEF varlist, Con_F1, Con_FR, Con_U1, Con_UR, Con_S1, Con_S2, Con_S3, Con_SR, Con_0
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10 DEF Next, Step

LEMMA SameSetSamePart == SameSetSpec => []SamePart
  BY SameSetInitSamePart, SameSetNextSamePart, PTL, SameSetTypeOK DEF SameSetSpec

LEMMA SameSetInitQNE == Init => QNE
    <1> USE DEF Init, Q, InitF, InitOp, InitArg, InitRet, Configs, InitState,
              UFAbsSet, Con_F1, Con_FR, Con_U1, Con_UR, Con_S1, Con_S2, Con_S3, Con_SR, Con_0
  <1> SUFFICES ASSUME Init
                 PROVE QNE
    OBVIOUS
  <1> DEFINE InitT == [sigma |-> InitState,  ret |-> InitRet, op |-> InitOp, arg |-> InitArg]
  <1>1. InitT \in Q
    <2>1. InitT \in Configs
      <3>1. InitT.sigma \in StateSet
        BY DEF StateSet
      <3>2. InitT.op \in OpSet
        BY DEF OpSet
      <3>3. InitT.arg \in ArgSet
        BY DEF ArgSet
      <3>4. InitT.ret \in ReturnSet
        BY DEF ReturnSet
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4
    <2>2. InitT.sigma = F
      OBVIOUS
    <2>3. ASSUME NEW q \in PROCESSES
          PROVE InitT.op[q] = BOT
      OBVIOUS
    <2>4. ASSUME NEW q \in PROCESSES
          PROVE InitT.arg[q] = BOT
      OBVIOUS
    <2>5. ASSUME NEW q \in PROCESSES
          PROVE InitT.ret[q] = BOT
      OBVIOUS
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1> QED
    BY <1>1 DEF QNE

LEMMA SameSetNextQNE == QNE /\ TypeOK /\ [Next]_varlist => QNE'
  <1> SUFFICES ASSUME QNE /\ TypeOK /\ [Next]_varlist
               PROVE  QNE'
    OBVIOUS
  <1> USE DEF QNE, TypeOK, Valid_pc, Valid_F, Valid_u, Valid_v, Valid_w,
              Valid_c, Valid_d, Valid_M, Valid_ret, Configs, StateSet, ReturnSet, 
              OpSet, ArgSet, UFAbsSet, Q, Con_F1, Con_FR, Con_U1, Con_UR, Con_S1, Con_S2, Con_S3, Con_SR, Con_0,
              Con_U1Prime, Con_URPrime, Con_F1Prime, Con_FRPrime, Con_S1Prime, Con_S2Prime, Con_S3Prime, 
              Con_SRPrime, Con_0Prime, ProcOpPrime, ProcArgPrime, ProcRetPrime
  <1>0. TypeOK'
    BY NextTypeOK
  <1> DEFINE t == [sigma |-> F', op |-> ProcOpPrime, arg |-> ProcArgPrime, ret |-> ProcRetPrime]
  <1>1. t \in Q'
    <2>1. t \in Configs
      <3>1. t.sigma \in StateSet
        BY <1>0
      <3>2. t.op \in OpSet
        OBVIOUS
      <3>3. t.arg \in ArgSet
        BY <1>0
      <3>4. t.ret \in ReturnSet
        BY <1>0
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4
    <2>2. t.sigma = F'
      OBVIOUS
    <2> SUFFICES ASSUME NEW q \in PROCESSES'
                 PROVE /\ Con_U1Prime(t,q)
                       /\ Con_URPrime(t,q)
                       /\ Con_F1Prime(t,q)
                       /\ Con_FRPrime(t,q)
                       /\ Con_S1Prime(t,q)
                       /\ Con_S2Prime(t,q)
                       /\ Con_S3Prime(t,q)
                       /\ Con_SRPrime(t,q)
                       /\ Con_0Prime(t,q)
      BY <2>1, <2>2  
    <2>3. Con_U1Prime(t,q)
      BY DEF Con_U1Prime
    <2>4. Con_URPrime(t,q)
      BY DEF Con_URPrime
    <2>5. Con_F1Prime(t,q)
      BY DEF Con_F1Prime
    <2>6. Con_FRPrime(t,q)
      BY DEF Con_FRPrime
    <2>7. Con_S1Prime(t,q)
      BY DEF Con_S1Prime
    <2>8. Con_S2Prime(t,q)
      BY DEF Con_S2Prime
    <2>9. Con_S3Prime(t,q)
      BY DEF Con_S3Prime
    <2>10. Con_SRPrime(t,q)
      BY DEF Con_SRPrime
    <2>11. Con_0Prime(t,q)
      BY DEF Con_0Prime
    <2> QED
      BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11
  <1> QED
    BY <1>1
    
    
LEMMA SameSetQNE == SameSetSpec => []QNE
  BY SameSetInitQNE, SameSetNextQNE, PTL, SameSetTypeOK DEF SameSetSpec

LEMMA SameSetInitQinM == Init => QinM
  <1> SUFFICES ASSUME Init
               PROVE QinM
    OBVIOUS
  <1> USE DEF Init, Q, InitF, InitOp, InitArg, InitRet, Configs, InitState,
              UFAbsSet, Con_F1, Con_FR, Con_U1, Con_UR, Con_S1, Con_S2, Con_S3, Con_SR, Con_0
  <1> DEFINE InitT == [sigma |-> InitState,  ret |-> InitRet, op |-> InitOp, arg |-> InitArg]
  <1>1. Q = {InitT}
    <2>1. InitT \in Q
      <3>1. InitT \in Configs
        <4>1. InitT.sigma \in StateSet
          BY DEF StateSet
        <4>2. InitT.op \in OpSet
          BY DEF OpSet
        <4>3. InitT.arg \in ArgSet
          BY DEF ArgSet
        <4>4. InitT.ret \in ReturnSet
          BY DEF ReturnSet
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4
      <3>2. InitT.sigma = F
        OBVIOUS
      <3>3. ASSUME NEW q \in PROCESSES
            PROVE InitT.op[q] = BOT
        OBVIOUS
      <3>4. ASSUME NEW q \in PROCESSES
            PROVE InitT.arg[q] = BOT
        OBVIOUS
      <3>5. ASSUME NEW q \in PROCESSES
            PROVE InitT.ret[q] = BOT
        OBVIOUS
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5
    <2>2. \A t \in Configs: t # InitT => ~(t \in Q)
      <3> SUFFICES ASSUME NEW t \in Configs, t # InitT
                   PROVE ~(t \in Q)
        OBVIOUS
      <3> CASE t.sigma # InitT.sigma
        OBVIOUS
      <3> CASE t.op # InitT.op
        <4>1. t.op \in [PROCESSES -> {"F", "U", "S", BOT}]
          BY DEF OpSet
        <4>2. \E q \in PROCESSES: t.op[q] # BOT
          BY <4>1 
        <4> QED
          BY <4>2
      <3> CASE t.arg # InitT.arg
        <4>1. t.arg \in [PROCESSES -> {BOT} \cup NodeSet \cup NodeSet \X NodeSet]
          BY DEF ArgSet
        <4>2. \E q \in PROCESSES: t.arg[q] # BOT
          BY <4>1 
        <4> QED
          BY <4>2
      <3> CASE t.ret # InitT.ret
        <4>1. t.ret \in [PROCESSES -> {ACK, BOT, TRUE, FALSE} \cup NodeSet]
          BY DEF ReturnSet
        <4>2. \E q \in PROCESSES: t.ret[q] # BOT
          BY <4>1 
        <4> QED
          BY <4>2
      <3> QED
        OBVIOUS
    <2> QED
      BY <2>1, <2>2
  <1>2. {InitT} \in SUBSET M
    OBVIOUS
  <1> QED
    BY <1>1, <1>2 DEF QinM

LEMMA SameSetNextQinM == QinM /\ TypeOK /\ SamePart /\ [Next]_varlist => QinM'
  <1> SUFFICES ASSUME QinM /\ TypeOK /\ SamePart /\ [Next]_varlist
               PROVE  QinM'
    OBVIOUS
  <1> USE DEF QinM, TypeOK, Valid_pc, Valid_F, Valid_u, Valid_v, Valid_w,
              Valid_c, Valid_d, Valid_M, Valid_ret, Configs, StateSet, ReturnSet, 
              OpSet, ArgSet, UFAbsSet, Q, Con_F1, Con_FR, Con_U1, Con_UR, Con_S1, Con_S2, Con_S3, Con_SR, Con_0,
              Con_U1Prime, Con_URPrime, Con_F1Prime, Con_FRPrime, Con_S1Prime, Con_S2Prime, Con_S3Prime, 
              Con_SRPrime, Con_0Prime
  <1>0. TypeOK'
    BY NextTypeOK
  <1> SUFFICES ASSUME NEW t \in Q'
               PROVE t \in M'
    OBVIOUS
  <1>1. ASSUME NEW p \in PROCESSES, Decide(p)
        PROVE t \in M'
    <2> USE <1>1 DEF Decide
    <2> DEFINE told == [t EXCEPT !.op = [t.op EXCEPT ![p] = BOT],
                                 !.arg = [t.arg EXCEPT ![p] = BOT]]
    <2>1. told \in Q
      <3>1. told \in Configs
        OBVIOUS
      <3>2. told.sigma = F
        OBVIOUS
      <3> SUFFICES ASSUME NEW q \in PROCESSES
                   PROVE /\ Con_U1(told, q)
                         /\ Con_UR(told, q)
                         /\ Con_F1(told, q)
                         /\ Con_FR(told, q)
                         /\ Con_S1(told, q)
                         /\ Con_S2(told, q)
                         /\ Con_S3(told, q)
                         /\ Con_SR(told, q)
                         /\ Con_0(told, q)
        BY <3>1, <3>2
      <3>3. Con_U1(told, q)
        OBVIOUS
      <3>4. Con_UR(told, q)
        OBVIOUS
      <3>5. Con_F1(told, q)
        OBVIOUS
      <3>6. Con_FR(told, q)
        OBVIOUS
      <3>7. Con_S1(told, q)
        OBVIOUS
      <3>8. Con_S2(told, q)
        OBVIOUS
      <3>9. Con_S3(told, q)
        OBVIOUS
      <3>10. Con_SR(told, q)
        OBVIOUS
      <3>11. Con_0(told, q)
        OBVIOUS
      <3> QED
        BY <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11
    <2>2. told \in M
      BY <2>1
    <2>3. t \in M'
      <3>1. told.ret[p] = BOT /\ told.arg[p] = BOT /\ told.op[p] = BOT
        OBVIOUS
      <3>2. t.sigma = told.sigma
        OBVIOUS
      <3>3. t.ret = told.ret
        OBVIOUS
      <3> CASE pc' = [pc EXCEPT ![p] = "F1"]
        <4> SUFFICES \E told1 \in M: /\ told1.ret[p] = BOT
                                     /\ told1.op[p] = BOT
                                     /\ told1.arg[p] = BOT
                                     /\ t.sigma = told1.sigma
                                     /\ t.op = [told1.op EXCEPT ![p] = "F"]
                                     /\ t.arg = [told1.arg EXCEPT ![p] = c'[p]]
                                     /\ t.ret = told1.ret
          BY ZenonT(30)
        <4>1. t.op = [told.op EXCEPT ![p] = "F"]
          OBVIOUS
        <4>2. t.arg = [told.arg EXCEPT ![p] = c'[p]]
          OBVIOUS
        <4> QED
          BY <3>1, <3>2, <3>3, <4>1, <4>2, <2>2
      <3> CASE pc' = [pc EXCEPT ![p] = "U1"]
        <4> SUFFICES \E told1 \in M: /\ told1.ret[p] = BOT
                                     /\ told1.op[p] = BOT
                                     /\ told1.arg[p] = BOT
                                     /\ t.sigma = told1.sigma
                                     /\ t.op = [told1.op EXCEPT ![p] = "U"]
                                     /\ t.arg = [told1.arg EXCEPT ![p] = <<c'[p], d'[p]>>]
                                     /\ t.ret = told1.ret
          OBVIOUS
        <4>1. t.op = [told.op EXCEPT ![p] = "U"]
          OBVIOUS
        <4>2. t.arg = [told.arg EXCEPT ![p] = <<c'[p], d'[p]>>]
          OBVIOUS
        <4> QED
          BY <3>1, <3>2, <3>3, <4>1, <4>2, <2>2
      <3> CASE pc' = [pc EXCEPT ![p] = "S1"]
        <4> SUFFICES \E told1 \in M: /\ told1.ret[p] = BOT
                                     /\ told1.op[p] = BOT
                                     /\ told1.arg[p] = BOT
                                     /\ t.sigma = told1.sigma
                                     /\ t.op = [told1.op EXCEPT ![p] = "S"]
                                     /\ t.arg = [told1.arg EXCEPT ![p] = <<c'[p], d'[p]>>]
                                     /\ t.ret = told1.ret
          OBVIOUS
        <4>1. t.op = [told.op EXCEPT ![p] = "S"]
          OBVIOUS
        <4>2. t.arg = [told.arg EXCEPT ![p] = <<c'[p], d'[p]>>]
          OBVIOUS
        <4> QED
          BY <3>1, <3>2, <3>3, <4>1, <4>2, <2>2
      <3> QED
        OBVIOUS
    <2> QED
      BY <2>3
  <1>2. ASSUME NEW p \in PROCESSES, F1(p)
        PROVE t \in M'
    <2> USE <1>2 DEF F1
    <2> DEFINE told == [t EXCEPT !.ret = [t.ret EXCEPT ![p] = BOT]]
    <2>1. told \in Q
      <3>1. told \in Configs
        OBVIOUS
      <3>2. told.sigma = F
        OBVIOUS
      <3> SUFFICES ASSUME NEW q \in PROCESSES
                   PROVE /\ Con_U1(told, q)
                         /\ Con_UR(told, q)
                         /\ Con_F1(told, q)
                         /\ Con_FR(told, q)
                         /\ Con_S1(told, q)
                         /\ Con_S2(told, q)
                         /\ Con_S3(told, q)
                         /\ Con_SR(told, q)
                         /\ Con_0(told, q)
        BY <3>1, <3>2
      <3>3. Con_U1(told, q)
        OBVIOUS
      <3>4. Con_UR(told, q)
        OBVIOUS
      <3>5. Con_F1(told, q)
        OBVIOUS
      <3>6. Con_FR(told, q)
        OBVIOUS
      <3>7. Con_S1(told, q)
        OBVIOUS
      <3>8. Con_S2(told, q)
        OBVIOUS
      <3>9. Con_S3(told, q)
        OBVIOUS
      <3>10. Con_SR(told, q)
        OBVIOUS
      <3>11. Con_0(told, q)
        OBVIOUS
      <3> QED
        BY <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11
    <2>2. told \in M
      BY <2>1
    <2>3. t \in M'
      <3>1. told.ret[p] = BOT
        OBVIOUS
      <3>2. t.sigma = told.sigma
        OBVIOUS
      <3>3. t.ret = [told.ret EXCEPT ![p] = told.sigma[told.arg[p]]]
        <4>1. ret'[p] = F[c[p]]
          OBVIOUS
        <4>2. told.sigma[c[p]] = F[c[p]]
          BY <3>2
        <4>3. told.sigma[told.arg[p]] = F[c[p]]
          BY <4>2
        <4>4. t.ret[p] = ret'[p]
          OBVIOUS
        <4> QED
          BY <4>1, <4>3, <4>4, ZenonT(30)
      <3>4. t.op = told.op
        OBVIOUS
      <3>5. t.arg = told.arg
        OBVIOUS
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <2>2
    <2> QED
      BY <2>3
  <1>3. ASSUME NEW p \in PROCESSES, FR(p)
        PROVE t \in M'
    <2> USE <1>3 DEF FR
    <2> DEFINE told == [t EXCEPT !.ret = [t.ret EXCEPT ![p] = ret[p]],
                                 !.op = [t.op EXCEPT ![p] = "F"],
                                 !.arg = [t.arg EXCEPT ![p] = c[p]]]
    <2>1. told \in Q
      <3>1. told \in Configs
        OBVIOUS
      <3>2. told.sigma = F
        OBVIOUS
      <3> SUFFICES ASSUME NEW q \in PROCESSES
                   PROVE /\ Con_U1(told, q)
                         /\ Con_UR(told, q)
                         /\ Con_F1(told, q)
                         /\ Con_FR(told, q)
                         /\ Con_S1(told, q)
                         /\ Con_S2(told, q)
                         /\ Con_S3(told, q)
                         /\ Con_SR(told, q)
                         /\ Con_0(told, q)
        BY <3>1, <3>2
      <3>3. Con_U1(told, q)
        OBVIOUS
      <3>4. Con_UR(told, q)
        OBVIOUS
      <3>5. Con_F1(told, q)
        OBVIOUS
      <3>6. Con_FR(told, q)
        OBVIOUS
      <3>7. Con_S1(told, q)
        OBVIOUS
      <3>8. Con_S2(told, q)
        OBVIOUS
      <3>9. Con_S3(told, q)
        OBVIOUS
      <3>10. Con_SR(told, q)
        OBVIOUS
      <3>11. Con_0(told, q)
        OBVIOUS
      <3> QED
        BY <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11
    <2>2. told \in M
      BY <2>1
    <2>3. t \in M'
      <3>1. told.ret[p] = ret[p]
        OBVIOUS
      <3>2. t.sigma = told.sigma
        OBVIOUS
      <3>3. t.ret = [told.ret EXCEPT ![p] = BOT]
        OBVIOUS
      <3>4. t.op = [told.op EXCEPT ![p] = BOT]
        OBVIOUS
      <3>5. t.arg = [told.arg EXCEPT ![p] = BOT]
        OBVIOUS
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <2>2
    <2> QED
      BY <2>3
  <1>4. ASSUME NEW p \in PROCESSES, U1(p)
        PROVE t \in M'
    <2> USE <1>4 DEF U1
    <2> DEFINE told == [t EXCEPT !.ret = [t.ret EXCEPT ![p] = BOT],
                                 !.sigma = F]
    <2>1. told \in Q
      <3>1. told \in Configs
        OBVIOUS
      <3>2. told.sigma = F
        OBVIOUS
      <3> SUFFICES ASSUME NEW q \in PROCESSES
                   PROVE /\ Con_U1(told, q)
                         /\ Con_UR(told, q)
                         /\ Con_F1(told, q)
                         /\ Con_FR(told, q)
                         /\ Con_S1(told, q)
                         /\ Con_S2(told, q)
                         /\ Con_S3(told, q)
                         /\ Con_SR(told, q)
                         /\ Con_0(told, q)
        BY <3>1, <3>2
      <3>3. Con_U1(told, q)
        OBVIOUS
      <3>4. Con_UR(told, q)
        OBVIOUS
      <3>5. Con_F1(told, q)
        OBVIOUS
      <3>6. Con_FR(told, q)
        OBVIOUS
      <3>7. Con_S1(told, q)
        OBVIOUS
      <3>8. Con_S2(told, q)
        OBVIOUS
      <3>9. Con_S3(told, q)
        BY DEF UFUniteShared
      <3>10. Con_SR(told, q)
        OBVIOUS
      <3>11. Con_0(told, q)
        OBVIOUS
      <3> QED
        BY <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11
    <2>2. told \in M
      BY <2>1
    <2>3. t \in M'
      <3>1. told.ret[p] = BOT
        OBVIOUS
      <3>2. t.ret = [told.ret EXCEPT ![p] = ACK]
        OBVIOUS
      <3>3. t.op = told.op
        OBVIOUS
      <3>4. t.arg = told.arg
        OBVIOUS
      <3>5. IF F' = [i \in NodeSet |-> IF F[i] = F[c[p]] THEN F[d[p]] ELSE F[i]] 
             THEN UFSUnite(told.sigma, told.arg[p][1], told.arg[p][2], t.sigma)
             ELSE UFSUnite(told.sigma, told.arg[p][2], told.arg[p][1], t.sigma)
        <4>1. /\ told.arg[p][1] = c[p]
              /\ told.arg[p][2] = d[p]
          OBVIOUS
        <4> CASE F' = [i \in NodeSet |-> IF F[i] = F[c[p]] THEN F[d[p]] ELSE F[i]]
          <5> SUFFICES /\ told.sigma \in StateSet /\ t.sigma \in StateSet
                       /\ told.arg[p][1] \in NodeSet /\ told.arg[p][2] \in NodeSet
                       /\ t.sigma = [i \in NodeSet |-> IF told.sigma[i] = told.sigma[told.arg[p][1]] THEN told.sigma[told.arg[p][2]] ELSE told.sigma[i]]
            BY DEF UFSUnite
          <5>1. told.sigma \in StateSet
            OBVIOUS
          <5>2. t.sigma \in StateSet
            <6>1. t.sigma = [i \in NodeSet |-> IF told.sigma[i] = told.sigma[c[p]] THEN told.sigma[d[p]] ELSE told.sigma[i]]
              OBVIOUS
            <6> SUFFICES ASSUME NEW node \in NodeSet'
                         PROVE /\ t.sigma \in [NodeSet -> NodeSet]
                               /\ t.sigma[t.sigma[node]] = t.sigma[node]
              OBVIOUS
            <6>2. t.sigma \in [NodeSet -> NodeSet]
              <7>1. told.sigma \in [NodeSet -> NodeSet]
                OBVIOUS
              <7> QED
                BY <7>1
            <6>3. t.sigma[t.sigma[node]] = t.sigma[node]
              <7> CASE told.sigma[node] = told.sigma[c[p]]
                <8>1. t.sigma[node] = told.sigma[d[p]]
                  OBVIOUS
                <8>2. t.sigma[t.sigma[node]] = told.sigma[d[p]]
                  BY <8>1
                <8> QED
                  BY <8>1, <8>2
              <7> CASE ~(told.sigma[node] = told.sigma[c[p]])
                <8>1. t.sigma[node] = told.sigma[node]
                  OBVIOUS
                <8>2. t.sigma[t.sigma[node]] = told.sigma[node]
                  BY <8>1
                <8> QED
                  BY <8>1, <8>2
              <7> QED
                OBVIOUS
            <6> QED
              BY <6>2, <6>3
          <5>3. told.arg[p][1] \in NodeSet /\ told.arg[p][2] \in NodeSet
            BY <4>1
          <5>4. t.sigma = [i \in NodeSet |-> IF told.sigma[i] = told.sigma[told.arg[p][1]] THEN told.sigma[told.arg[p][2]] ELSE told.sigma[i]]
            BY <4>1 
          <5> QED
            BY <5>1, <5>2, <5>3, <5>4
        <4> CASE ~(F' = [i \in NodeSet |-> IF F[i] = F[c[p]] THEN F[d[p]] ELSE F[i]])
          <5> SUFFICES /\ told.sigma \in StateSet /\ t.sigma \in StateSet
                       /\ told.arg[p][1] \in NodeSet /\ told.arg[p][2] \in NodeSet
                       /\ t.sigma = [i \in NodeSet |-> IF told.sigma[i] = told.sigma[told.arg[p][2]] THEN told.sigma[told.arg[p][1]] ELSE told.sigma[i]]
            BY DEF UFSUnite
          <5>1. told.sigma \in StateSet
            OBVIOUS
          <5>2. t.sigma \in StateSet
            <6>1. t.sigma = [i \in NodeSet |-> IF told.sigma[i] = told.sigma[d[p]] THEN told.sigma[c[p]] ELSE told.sigma[i]]
              BY DEF UFUniteShared
            <6> SUFFICES ASSUME NEW node \in NodeSet'
                         PROVE /\ t.sigma \in [NodeSet -> NodeSet]
                               /\ t.sigma[t.sigma[node]] = t.sigma[node]
              OBVIOUS
            <6>2. t.sigma \in [NodeSet -> NodeSet]
              <7>1. told.sigma \in [NodeSet -> NodeSet]
                OBVIOUS
              <7> QED
                BY <7>1
            <6>3. t.sigma[t.sigma[node]] = t.sigma[node]
              <7> CASE told.sigma[node] = told.sigma[d[p]]
                <8>1. t.sigma[node] = told.sigma[c[p]]
                  BY <6>1
                <8>2. t.sigma[t.sigma[node]] = told.sigma[c[p]]
                  BY <8>1
                <8> QED
                  BY <8>1, <8>2
              <7> CASE ~(told.sigma[node] = told.sigma[d[p]])
                <8>1. t.sigma[node] = told.sigma[node]
                  BY <6>1
                <8>2. t.sigma[t.sigma[node]] = told.sigma[node]
                  BY <8>1
                <8> QED
                  BY <8>1, <8>2
              <7> QED
                OBVIOUS
            <6> QED
              BY <6>2, <6>3
          <5>3. told.arg[p][1] \in NodeSet /\ told.arg[p][2] \in NodeSet
            BY <4>1
          <5>4. t.sigma = [i \in NodeSet |-> IF told.sigma[i] = told.sigma[told.arg[p][2]] THEN told.sigma[told.arg[p][1]] ELSE told.sigma[i]]
            BY <4>1 DEF UFUniteShared
          <5> QED
            BY <5>1, <5>2, <5>3, <5>4
        <4> QED
          OBVIOUS
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <2>2
    <2> QED
      BY <2>3
  <1>5. ASSUME NEW p \in PROCESSES, UR(p)
        PROVE t \in M'
    <2> USE <1>5 DEF UR
    <2> DEFINE told == [t EXCEPT !.ret = [t.ret EXCEPT ![p] = ret[p]],
                                 !.op = [t.op EXCEPT ![p] = "U"],
                                 !.arg = [t.arg EXCEPT ![p] = <<c[p], d[p]>>]]
    <2>1. told \in Q
      <3>1. told \in Configs
        OBVIOUS
      <3>2. told.sigma = F
        OBVIOUS
      <3> SUFFICES ASSUME NEW q \in PROCESSES
                   PROVE /\ Con_U1(told, q)
                         /\ Con_UR(told, q)
                         /\ Con_F1(told, q)
                         /\ Con_FR(told, q)
                         /\ Con_S1(told, q)
                         /\ Con_S2(told, q)
                         /\ Con_S3(told, q)
                         /\ Con_SR(told, q)
                         /\ Con_0(told, q)
        BY <3>1, <3>2
      <3>3. Con_U1(told, q)
        OBVIOUS
      <3>4. Con_UR(told, q)
        OBVIOUS
      <3>5. Con_F1(told, q)
        OBVIOUS
      <3>6. Con_FR(told, q)
        OBVIOUS
      <3>7. Con_S1(told, q)
        OBVIOUS
      <3>8. Con_S2(told, q)
        OBVIOUS
      <3>9. Con_S3(told, q)
        OBVIOUS
      <3>10. Con_SR(told, q)
        OBVIOUS
      <3>11. Con_0(told, q)
        OBVIOUS
      <3> QED
        BY <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11
    <2>2. told \in M
      BY <2>1
    <2>3. t \in M'
      <3>1. told.ret[p] = ret[p]
        OBVIOUS
      <3>2. t.sigma = told.sigma
        OBVIOUS
      <3>3. t.ret = [told.ret EXCEPT ![p] = BOT]
        OBVIOUS
      <3>4. t.op = [told.op EXCEPT ![p] = BOT]
        OBVIOUS
      <3>5. t.arg = [told.arg EXCEPT ![p] = BOT]
        OBVIOUS
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <2>2
    <2> QED
      BY <2>3
  <1>6. ASSUME NEW p \in PROCESSES, S1(p)
        PROVE t \in M'
    <2> USE <1>6 DEF S1
    <2>1. t \in Q
      OBVIOUS
    <2>2. t \in M
      BY <2>1
    <2>3. t \in M'
      BY <2>2
    <2> QED
      BY <2>3
  <1>7. ASSUME NEW p \in PROCESSES, S2(p)
        PROVE t \in M'
    <2> USE <1>7 DEF S2
    <2> DEFINE told == [t EXCEPT !.ret = [t.ret EXCEPT ![p] = BOT],
                                 !.sigma = F]
    <2>1. told \in Q
      <3>1. told \in Configs
        OBVIOUS
      <3>2. told.sigma = F
        OBVIOUS
      <3> SUFFICES ASSUME NEW q \in PROCESSES
                   PROVE /\ Con_U1(told, q)
                         /\ Con_UR(told, q)
                         /\ Con_F1(told, q)
                         /\ Con_FR(told, q)
                         /\ Con_S1(told, q)
                         /\ Con_S2(told, q)
                         /\ Con_S3(told, q)
                         /\ Con_SR(told, q)
                         /\ Con_0(told, q)
        BY <3>1, <3>2
      <3>3. Con_U1(told, q)
        OBVIOUS
      <3>4. Con_UR(told, q)
        OBVIOUS
      <3>5. Con_F1(told, q)
        OBVIOUS
      <3>6. Con_FR(told, q)
        BY ZenonT(30)
      <3>7. Con_S1(told, q)
        OBVIOUS
      <3>8. Con_S2(told, q)
        OBVIOUS
      <3>9. Con_S3(told, q)
        OBVIOUS
      <3>10. Con_SR(told, q)
        OBVIOUS
      <3>11. Con_0(told, q)
        OBVIOUS
      <3> QED
        BY <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11
    <2>2. told \in M
      BY <2>1
    <2>3. t \in M'
      <3>1. told.ret[p] = BOT
        OBVIOUS
      <3>2. t.sigma = told.sigma
        OBVIOUS
      <3>3. t.op = told.op
        OBVIOUS
      <3>4. t.arg = told.arg
        OBVIOUS
      <3> CASE u'[p] = v'[p]
        <4> SUFFICES \E told1 \in M: /\ told1.ret[p] = BOT
                                     /\ t.sigma = told1.sigma
                                     /\ t.ret = [told1.ret EXCEPT ![p] = IF told1.sigma[told1.arg[p][1]] = told1.sigma[told1.arg[p][2]]
                                                                        THEN TRUE
                                                                        ELSE FALSE]
                                     /\ t.op  = told1.op
                                     /\ t.arg = told1.arg
          OBVIOUS 
        <4>1. t.ret = [told.ret EXCEPT ![p] = IF told.sigma[told.arg[p][1]] = told.sigma[told.arg[p][2]]
                                               THEN TRUE
                                               ELSE FALSE]
          <5>1. t.ret[p] = TRUE
            OBVIOUS
          <5>2. t.ret = [told.ret EXCEPT ![p] = TRUE]
           BY <5>1
          <5>3. told.sigma[told.arg[p][1]] = told.sigma[told.arg[p][2]]
            <6>1. told.sigma[told.arg[p][1]] = F[c[p]]
              OBVIOUS
            <6>2. told.sigma[told.arg[p][2]] = F[d[p]]
              OBVIOUS
            <6> QED
              BY <6>1, <6>2 DEF SamePart
          <5> QED
            BY <5>2, <5>3
        <4> QED
          BY <2>2, <3>1, <3>2, <3>3, <3>4, <4>1
      <3> CASE ~(u'[p] = v'[p])
        <4> SUFFICES \E told1 \in M: /\ told1.ret[p] = BOT
                                     /\ t.sigma = told1.sigma
                                     /\ \/ /\ F[u[p]] = u[p]
                                           /\ told1.sigma[told1.arg[p][1]] # told1.sigma[told1.arg[p][2]]
                                           /\ t.ret = [told1.ret EXCEPT ![p] = IF told1.sigma[told1.arg[p][1]] = told1.sigma[told1.arg[p][2]]
                                                                              THEN TRUE
                                                                              ELSE FALSE]
                                        \/ t.ret =  told1.ret
                                     /\ t.op = told1.op
                                     /\ t.arg = told1.arg
          OBVIOUS
        <4> CASE F[u[p]] = u[p]  
          <5> CASE t.ret[p] = BOT
            <6>1. t.ret = told.ret
              OBVIOUS
            <6> QED
              BY <2>2, <3>1, <3>2, <3>3, <3>4, <6>1
          <5> CASE t.ret[p] = FALSE
            <6>1. t.ret = [told.ret EXCEPT ![p] = IF told.sigma[told.arg[p][1]] = told.sigma[told.arg[p][2]]
                                                   THEN TRUE
                                                   ELSE FALSE]
              <7>1. t.ret = [told.ret EXCEPT ![p] = FALSE]
                OBVIOUS
              <7>2. told.sigma[told.arg[p][1]] # told.sigma[told.arg[p][2]]
                <8>1. told.sigma[told.arg[p][1]] = F[c[p]]
                  OBVIOUS
                <8>2. told.sigma[told.arg[p][2]] = F[d[p]]
                  OBVIOUS
                <8> QED
                  BY <8>1, <8>2 DEF SamePart
              <7> QED
                BY <7>1, <7>2
            <6> QED
              BY <2>2, <3>1, <3>2, <3>3, <3>4, <6>1
          <5> QED
            OBVIOUS
        <4> CASE ~(F[u[p]] = u[p])
          <5>1. t.ret = told.ret
            OBVIOUS
          <5> QED
            BY <2>2, <3>1, <3>2, <3>3, <3>4, <5>1
        <4> QED
          OBVIOUS
      <3> QED
        OBVIOUS
    <2> QED
      BY <2>3
  <1>8. ASSUME NEW p \in PROCESSES, S3(p)
        PROVE t \in M'
    <2> USE <1>8 DEF S3
    <2>1. t \in Q
      <3>1. t \in Configs
        OBVIOUS
      <3>2. t.sigma = F
        OBVIOUS
      <3> SUFFICES ASSUME NEW q \in PROCESSES
                   PROVE /\ Con_U1(t, q)
                         /\ Con_UR(t, q)
                         /\ Con_F1(t, q)
                         /\ Con_FR(t, q)
                         /\ Con_S1(t, q)
                         /\ Con_S2(t, q)
                         /\ Con_S3(t, q)
                         /\ Con_SR(t, q)
                         /\ Con_0(t, q)
        BY <3>1, <3>2
      <3>3. Con_U1(t, q)
        OBVIOUS
      <3>4. Con_UR(t, q)
        OBVIOUS
      <3>5. Con_F1(t, q)
        OBVIOUS
      <3>6. Con_FR(t, q)
        OBVIOUS
      <3>7. Con_S1(t, q)
        OBVIOUS
      <3>8. Con_S2(t, q)
        OBVIOUS
      <3>9. Con_S3(t, q)
        OBVIOUS
      <3>10. Con_SR(t, q)
        OBVIOUS
      <3>11. Con_0(t, q)
        OBVIOUS
      <3> QED
        BY <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11
    <2>2. t \in M
      BY <2>1
    <2>3. t \in M'
      BY <2>2
    <2> QED
      BY <2>3
  <1>9. ASSUME NEW p \in PROCESSES, SR(p)
        PROVE t \in M'
    <2> USE <1>9 DEF SR
    <2> DEFINE told == [t EXCEPT !.ret = [t.ret EXCEPT ![p] = ret[p]],
                                 !.op = [t.op EXCEPT ![p] = "S"],
                                 !.arg = [t.arg EXCEPT ![p] = <<c[p], d[p]>>]]
    <2>1. told \in Q
      <3>1. told \in Configs
        OBVIOUS
      <3>2. told.sigma = F
        OBVIOUS
      <3> SUFFICES ASSUME NEW q \in PROCESSES
                   PROVE /\ Con_U1(told, q)
                         /\ Con_UR(told, q)
                         /\ Con_F1(told, q)
                         /\ Con_FR(told, q)
                         /\ Con_S1(told, q)
                         /\ Con_S2(told, q)
                         /\ Con_S3(told, q)
                         /\ Con_SR(told, q)
                         /\ Con_0(told, q)
        BY <3>1, <3>2
      <3>3. Con_U1(told, q)
        OBVIOUS
      <3>4. Con_UR(told, q)
        OBVIOUS
      <3>5. Con_F1(told, q)
        OBVIOUS
      <3>6. Con_FR(told, q)
        OBVIOUS
      <3>7. Con_S1(told, q)
        OBVIOUS
      <3>8. Con_S2(told, q)
        OBVIOUS
      <3>9. Con_S3(told, q)
        OBVIOUS
      <3>10. Con_SR(told, q)
        OBVIOUS
      <3>11. Con_0(told, q)
        OBVIOUS
      <3> QED
        BY <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11
    <2>2. told \in M
      BY <2>1
    <2>3. t \in M'
      <3>1. told.ret[p] = ret[p]
        OBVIOUS
      <3>2. t.sigma = told.sigma
        OBVIOUS
      <3>3. t.ret = [told.ret EXCEPT ![p] = BOT]
        OBVIOUS
      <3>4. t.op = [told.op EXCEPT ![p] = BOT]
        OBVIOUS
      <3>5. t.arg = [told.arg EXCEPT ![p] = BOT]
        OBVIOUS
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <2>2
    <2> QED
      BY <2>3
  <1>10. ASSUME UNCHANGED varlist
         PROVE t \in M'
    BY <1>10 DEF varlist
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10 DEF Next, Step

LEMMA SameSetQinM == SameSetSpec => []QinM
  BY SameSetInitQinM, SameSetNextQinM, PTL, SameSetTypeOK, SameSetSamePart DEF SameSetSpec

THEOREM SameSetLinearizable == SameSetSpec => []Linearizable
  <1> SUFFICES ASSUME QNE, QinM
               PROVE Linearizable
    BY SameSetQNE, SameSetQinM, PTL
  <1> QED
    BY DEF QNE, QinM, Linearizable

=============================================================================
\* Modification History
\* Last modified Sun Feb 15 17:51:28 EST 2026 by karunram
\* Last modified Mon Jan 19 10:50:33 EST 2026 by elucca
\* Created Mon Jan 12 16:31:54 EST 2026 by elucca
