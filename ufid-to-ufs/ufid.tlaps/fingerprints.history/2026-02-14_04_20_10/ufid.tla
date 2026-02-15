-------------------------------- MODULE ufid --------------------------------

EXTENDS UFSImplementation, UFSTypeOK, UFSIDProperties, TLAPS, FiniteSetTheorems

I_U1(t,p) == pc[p] = "U1" => /\ t.op[p] = "U"
                             /\ t.arg[p] = <<c[p], d[p]>>
                             /\ t.ret[p] = BOT

I_UR(t,p) == pc[p] = "UR" => /\ t.op[p] = "U"
                             /\ t.arg[p] = <<c[p], d[p]>>
                             /\ t.ret[p] = ret[p]
                                                         
I_F1(t,p) == pc[p] = "F1" => /\ t.op[p] = "F"
                             /\ t.arg[p] = c[p]
                             /\ t.ret[p] = BOT

I_FR(t,p) == pc[p] = "FR" => /\ t.op[p] = "F"
                             /\ t.arg[p] = c[p]
                             /\ t.ret[p] = ret[p]
  
  
I_Sk(t, p) == pc[p] \in {"S1", "S2", "S3", "S4", "S5", "S6"} => /\ t.op[p] = "S"
                                                                /\ t.arg[p] = <<c[p], d[p]>>
                                                                /\ t.ret[p] = BOT

I_SR(t,p) == pc[p] = "SR" => /\ t.op[p] = "S"
                             /\ t.arg[p] = <<c[p], d[p]>>
                             /\ t.ret[p] = ret[p]
                                                         
I_0(t,p) == pc[p] = "0" => /\ t.op[p] = BOT
                           /\ t.arg[p] = BOT
                           /\ t.ret[p] = BOT


I_U1Prime(t,p) == pc'[p] = "U1" => /\ t.op[p] = "U"
                                   /\ t.arg[p] = <<c'[p], d'[p]>>
                                   /\ t.ret[p] = BOT

I_URPrime(t,p) == pc'[p] = "UR" => /\ t.op[p] = "U"
                                   /\ t.arg[p] = <<c'[p], d'[p]>>
                                   /\ t.ret[p] = ret'[p]
                                                          
I_F1Prime(t,p) == pc'[p] = "F1" => /\ t.op[p] = "F"
                                   /\ t.arg[p] = c'[p]
                                   /\ t.ret[p] = BOT

I_FRPrime(t,p) == pc'[p] = "FR" => /\ t.op[p] = "F"
                                   /\ t.arg[p] = c'[p]
                                   /\ t.ret[p] = ret'[p]
                                   
I_SkPrime(t, p) == pc'[p] \in {"S1", "S2", "S3", "S4", "S5", "S6"} => /\ t.op[p] = "S"
                                                                      /\ t.arg[p] = <<c'[p], d'[p]>>
                                                                      /\ t.ret[p] = BOT

I_SRPrime(t,p) == pc'[p] = "SR" => /\ t.op[p] = "S"
                                   /\ t.arg[p] = <<c'[p], d'[p]>>
                                   /\ t.ret[p] = ret'[p]
                                                         
I_0Prime(t,p) == pc'[p] = "0" => /\ t.op[p] = BOT
                                 /\ t.arg[p] = BOT
                                 /\ t.ret[p] = BOT

Q == {t \in Configs: 
     /\ t.sigma = UF.rep
     /\ \A p \in PROCESSES: /\ I_U1(t,p)
                            /\ I_UR(t,p)
                            /\ I_F1(t,p)
                            /\ I_FR(t,p)
                            /\ I_Sk(t,p)
                            /\ I_SR(t,p)
                            /\ I_0(t,p)}
                            
I_1 == \A p \in PROCESSES : pc[p] \in {"S2", "S3", "S4", "S5", "S6", "SR"} => UF.rep[u[p]] = UF.rep[c[p]] /\ UF.rep[v[p]] = UF.rep[d[p]]
I_2 == \A p \in PROCESSES : pc[p] = "S1" => (i_u[p] = 0 /\ i_v[p] = 0)

I_IDs == \A p \in PROCESSES: pc[p] \in {"S1", "S2", "S3", "S4", "S5", "S6", "SR"} =>
                                 /\ UF.id[UF.rep[u[p]]] >= i_u[p]
                                 /\ UF.id[UF.rep[v[p]]] >= i_v[p]

QNE == Q # {}

QinM == Q \in SUBSET M

MAllEqual == \A x, y \in M: x = y

Linearizable == M # {}

StrongLinearizable == Cardinality(M) = 1

Inv == QNE /\ QinM /\ I_1 /\ I_IDs /\ IDUniqueness /\ MAllEqual

Lines == {"F1", "FR", "U1", "UR", "S1", "S2", "S3", "S4", "S5", "S6", "SR", "0"}

ProcOpPrime == [p \in PROCESSES |-> IF pc'[p] \in {"F1", "FR"} THEN "F"
                                   ELSE IF pc'[p] \in {"U1", "UR"} THEN "U"
                                   ELSE IF pc'[p] \in {"S1", "S2", "S3", "S4", "S5", "S6", "SR"} THEN "S"
                                   ELSE BOT]

ProcArgPrime == [p \in PROCESSES |-> IF pc'[p] \in {"F1", "FR"} THEN c'[p]
                                    ELSE IF pc'[p] \in {"U1", "UR", "S1", "S2", "S3", "S4", "S5", "S6", "SR"} THEN <<c'[p], d'[p]>>
                                    ELSE BOT]

ProcRetPrime == [p \in PROCESSES |-> IF pc'[p] \in {"FR", "UR", "SR"} THEN ret'[p]
                                    ELSE BOT]
LEMMA LinReqs == QNE /\ QinM => Linearizable
  BY DEF QNE, QinM, Linearizable

LEMMA StrongLinReqs == Linearizable /\ MAllEqual => StrongLinearizable
  BY FS_Singleton DEF Linearizable, MAllEqual

LEMMA InitI_1 == Init => I_1
 BY DEF Init, I_1


LEMMA NextI_1 == I_1 /\ TypeOK /\ [Next]_varlist => I_1'
 <1> SUFFICES ASSUME I_1 /\ TypeOK /\ [Next]_varlist
              PROVE  I_1'
   OBVIOUS
 <1> USE DEF TypeOK, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK, I_1,
             cTypeOK, dTypeOK, MTypeOK, retTypeOK, Configs, Idems, ReturnSet, 
             OpSet, ArgSet, Q, I_F1, I_FR, I_U1, I_UR, I_Sk
 <1>0. TypeOK'
   <2>1. CASE Next
     BY <2>1, TypeOKNext
   <2>2. CASE UNCHANGED varlist
     BY <2>2, TypeOKUnchanged
   <2>3. QED
     BY <2>1, <2>2
 <1>1. ASSUME NEW p \in PROCESSES, Decide(p)
       PROVE I_1'
   <2> pc'[p] \in {"S1", "F1", "U1"}
     BY <1>1 DEF Decide
   <2> QED
     BY <1>1 DEF Decide
 <1>2. ASSUME NEW p \in PROCESSES, F1(p)
       PROVE I_1'
   BY <1>2 DEF F1 
 <1>3. ASSUME NEW p \in PROCESSES, FR(p)
       PROVE I_1'
   BY <1>3 DEF FR
 <1>4. ASSUME NEW p \in PROCESSES, U1(p)
       PROVE I_1'
   <2> USE <1>4 DEF U1
   <2> SUFFICES ASSUME NEW q \in PROCESSES', pc'[q] \in {"S2", "S3", "S4", "S5", "S6", "SR"}
                PROVE (/\ UF.rep[u[q]] = UF.rep[c[q]] 
                       /\ UF.rep[v[q]] = UF.rep[d[q]])'
     OBVIOUS
   <2>1. pc[q] \in {"S2", "S3", "S4", "S5", "S6", "SR"}
     OBVIOUS
   <2>2. /\ UF.rep[u[q]] = UF.rep[c[q]] 
         /\ UF.rep[v[q]] = UF.rep[d[q]]
     BY <2>1
   <2> CASE UF.rep' = [i \in NodeSet |-> IF UF.rep[i] = UF.rep[c[q]] THEN UF.rep[d[q]] ELSE UF.rep[i]]
     OBVIOUS
   <2> CASE UF.rep' = [i \in NodeSet |-> IF UF.rep[i] = UF.rep[d[q]] THEN UF.rep[c[q]] ELSE UF.rep[i]]
     OBVIOUS
   <2> QED
     BY DEF I_U1, UFUnite, URep, SmallerRep, LargerRep
 <1>5. ASSUME NEW p \in PROCESSES, UR(p)
       PROVE I_1'
   BY <1>5 DEF UR
 <1>6. ASSUME NEW p \in PROCESSES, S1(p)
       PROVE I_1'
    BY <1>6 DEF S1, Idems, TypeOK, UFTypeOK, UFId_StateSet, uTypeOK, I_1
 <1>7. ASSUME NEW p \in PROCESSES, S2(p)
       PROVE I_1'
   BY <1>7 DEF S2
 <1>8. ASSUME NEW p \in PROCESSES, S3(p)
       PROVE I_1'
   BY <1>8 DEF S3, Idems, TypeOK, UFTypeOK, UFId_StateSet, vTypeOK, I_1   
 <1>9. ASSUME NEW p \in PROCESSES, S4(p)
       PROVE I_1'
   BY <1>9 DEF S4
 <1>10. ASSUME NEW p \in PROCESSES, S5(p)
       PROVE I_1'
   BY <1>10 DEF S5, Idems, TypeOK, UFTypeOK, UFId_StateSet, uTypeOK, I_1   
 <1>11. ASSUME NEW p \in PROCESSES, S6(p)
       PROVE I_1'
   BY <1>11 DEF S6
 <1>12. ASSUME NEW p \in PROCESSES, SR(p)
       PROVE I_1'
   BY <1>12 DEF SR
 <1>13. ASSUME UNCHANGED varlist
        PROVE I_1'
   BY <1>13 DEF varlist, I_F1, I_FR, I_U1, I_UR, I_Sk
 <1> QED
   BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13 DEF Next, Step

LEMMA SpecMaintainsI1 == UFSSpec => []I_1
 BY InitI_1, NextI_1, PTL, SpecTypeOK DEF UFSSpec

LEMMA InitI_2 == Init => I_2
 BY DEF Init, I_2

LEMMA NextI_2 == I_2 /\ TypeOK /\ [Next]_varlist => I_2'
 <1> SUFFICES ASSUME I_2 /\ TypeOK /\ [Next]_varlist
              PROVE  I_2'
   OBVIOUS
 <1> USE DEF TypeOK, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK,
             cTypeOK, dTypeOK, MTypeOK, retTypeOK, Configs, Idems, ReturnSet, 
             OpSet, ArgSet, Q, I_2
 <1>0. TypeOK'
   <2>1. CASE Next
     BY <2>1, TypeOKNext
   <2>2. CASE UNCHANGED varlist
     BY <2>2, TypeOKUnchanged
   <2>3. QED
     BY <2>1, <2>2
 <1>1. ASSUME NEW p \in PROCESSES, Decide(p)
       PROVE I_2'
   <2> pc'[p] \in {"S1", "F1", "U1"}
     BY <1>1 DEF Decide
   <2> QED
     BY <1>1 DEF Decide
 <1>2. ASSUME NEW p \in PROCESSES, F1(p)
       PROVE I_2'
   BY <1>2 DEF F1
 <1>3. ASSUME NEW p \in PROCESSES, FR(p)
       PROVE I_2'
   BY <1>3 DEF FR
 <1>4. ASSUME NEW p \in PROCESSES, U1(p)
       PROVE I_2'
   BY <1>4 DEF U1
 <1>5. ASSUME NEW p \in PROCESSES, UR(p)
       PROVE I_2'
   BY <1>5 DEF UR
 <1>6. ASSUME NEW p \in PROCESSES, S1(p)
       PROVE I_2'
    BY <1>6 DEF S1
 <1>7. ASSUME NEW p \in PROCESSES, S2(p)
       PROVE I_2'
   BY <1>7 DEF S2
 <1>8. ASSUME NEW p \in PROCESSES, S3(p)
       PROVE I_2'
   BY <1>8 DEF S3   
 <1>9. ASSUME NEW p \in PROCESSES, S4(p)
       PROVE I_2'
   BY <1>9 DEF S4
 <1>10. ASSUME NEW p \in PROCESSES, S5(p)
       PROVE I_2'
   BY <1>10 DEF S5   
 <1>11. ASSUME NEW p \in PROCESSES, S6(p)
       PROVE I_2'
   BY <1>11 DEF S6
 <1>12. ASSUME NEW p \in PROCESSES, SR(p)
       PROVE I_2'
   BY <1>12 DEF SR
 <1>13. ASSUME UNCHANGED varlist
        PROVE I_2'
   BY <1>13 DEF varlist, I_F1, I_FR, I_U1, I_UR, I_Sk
 <1> QED
   BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13 DEF Next, Step

LEMMA SpecMaintainsI2 == UFSSpec => []I_2
 BY InitI_2, NextI_2, PTL, SpecTypeOK DEF UFSSpec

LEMMA InitQNE == Init => QNE
  <1> USE DEF Init, Q, InitUF, InitOp, InitArg, InitRet, Configs, InitState,
              UFId_StateSet, I_F1, I_FR, I_U1, I_UR, I_Sk, I_SR, I_0
  <1> SUFFICES ASSUME Init
                 PROVE QNE
    OBVIOUS
  <1> DEFINE InitT == [sigma |-> InitState,  ret |-> InitRet, op |-> InitOp, arg |-> InitArg]
  <1>1. InitT \in Q
    <2>1. InitT \in Configs
      <3>1. InitT.sigma \in Idems
        BY DEF Idems
      <3>2. InitT.op \in OpSet
        BY DEF OpSet
      <3>3. InitT.arg \in ArgSet
        BY DEF ArgSet
      <3>4. InitT.ret \in ReturnSet
        BY DEF ReturnSet
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4
    <2>2. InitT.sigma = UF.rep
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

LEMMA NextQNE == QNE /\ TypeOK /\ [Next]_varlist => QNE'
  <1> SUFFICES ASSUME QNE /\ TypeOK /\ [Next]_varlist
               PROVE  QNE'
    OBVIOUS
  <1> USE DEF QNE, TypeOK, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK,
              cTypeOK, dTypeOK, MTypeOK, retTypeOK, Configs, Idems, ReturnSet, 
              OpSet, ArgSet, UFId_StateSet, Q, I_F1, I_FR, I_U1, I_UR, I_Sk, I_SR, I_0,
              I_U1Prime, I_URPrime, I_F1Prime, I_FRPrime, I_SkPrime, I_SRPrime, I_0Prime, ProcOpPrime, ProcArgPrime, ProcRetPrime
  <1>0. TypeOK'
    BY TypeOKNext, TypeOKUnchanged
  <1> DEFINE t == [sigma |-> UF.rep', op |-> ProcOpPrime, arg |-> ProcArgPrime, ret |-> ProcRetPrime]
  <1>1. t \in Q'
    <2>1. t \in Configs
      <3>1. t.sigma \in Idems
        BY <1>0
      <3>2. t.op \in OpSet
        OBVIOUS
      <3>3. t.arg \in ArgSet
        BY <1>0
      <3>4. t.ret \in ReturnSet
        BY <1>0
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4
    <2>2. t.sigma = UF.rep'
      OBVIOUS
    <2> SUFFICES ASSUME NEW q \in PROCESSES'
                 PROVE /\ I_U1Prime(t,q)
                       /\ I_URPrime(t,q)
                       /\ I_F1Prime(t,q)
                       /\ I_FRPrime(t,q)
                       /\ I_SkPrime(t,q)
                       /\ I_SRPrime(t,q)
                       /\ I_0Prime(t,q)
      BY <2>1, <2>2  
    <2>3. I_U1Prime(t,q)
      BY DEF I_U1Prime
    <2>4. I_URPrime(t,q)
      BY DEF I_URPrime
    <2>5. I_F1Prime(t,q)
      BY DEF I_F1Prime
    <2>6. I_FRPrime(t,q)
      BY DEF I_FRPrime
    <2>7. I_SkPrime(t,q)
      BY DEF I_SkPrime
    <2>13. I_SRPrime(t,q)
      BY DEF I_SRPrime
    <2>14. I_0Prime(t,q)
      BY DEF I_0Prime
    <2> QED
      BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>13, <2>14
  <1> QED
    BY <1>1
   
LEMMA SpecMaintainsQNE == UFSSpec => []QNE
  BY InitQNE, NextQNE, PTL, SpecTypeOK DEF UFSSpec

LEMMA InitI_IDs == Init => I_IDs
  <1> SUFFICES ASSUME Init,
                      NEW p \in PROCESSES
               PROVE  pc[p] \in {"S1", "S2", "S3", "S4", "S5", "S6", "SR"} =>
                          /\ UF.id[UF.rep[u[p]]] >= i_u[p]
                          /\ UF.id[UF.rep[v[p]]] >= i_v[p]
    BY DEF I_IDs
  <1> QED
    BY DEF Init
    
LEMMA NextI_IDs == I_IDs /\ TypeOK /\ [Next]_varlist /\ I_2 => I_IDs'
  <1> SUFFICES ASSUME I_IDs,
                      TypeOK,
                      I_2,
                      [Next]_varlist
               PROVE  I_IDs'
    BY DEF Next
  <1>1. ASSUME NEW p \in PROCESSES, F1(p)
            PROVE I_IDs'
    BY <1>1 DEF I_IDs, F1
  <1>2. ASSUME NEW p \in PROCESSES, FR(p)
            PROVE I_IDs'
    BY <1>2 DEF I_IDs, FR
  <1>3. ASSUME NEW p \in PROCESSES, U1(p)
            PROVE I_IDs'
    <2> i_u' = i_u /\ i_v' = i_v /\ u' = u /\ v' = v
        BY <1>3 DEF U1
    <2>a. \A x \in NodeSet: (UF.id[UF.rep[x]])' >= UF.id[UF.rep[x]]
        <3> c[p] \in NodeSet /\ d[p] \in NodeSet
            BY DEF TypeOK, cTypeOK, dTypeOK
        <3> UF'.id = UF.id
            BY <1>3 DEF U1, UFUnite
        <3> SUFFICES ASSUME NEW x \in NodeSet
                     PROVE (UF.id[UF.rep[x]])' >= UF.id[UF.rep[x]]
            OBVIOUS
        <3> USE DEF TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs
        <3>1. CASE UF.id[UF.rep[c[p]]] >= UF.id[UF.rep[d[p]]]
            <4> SmallerRep(UF.rep, c[p], d[p]) = UF.rep[d[p]]
                BY <3>1 DEF SmallerRep
            <4> LargerRep(UF.rep, c[p], d[p]) = UF.rep[c[p]]
                BY <3>1 DEF LargerRep
            <4> UF'.rep = [i \in NodeSet |-> IF UF.rep[i] = UF.rep[d[p]] THEN UF.rep[c[p]] ELSE UF.rep[i]]
                BY <1>3 DEF U1, UFUnite, URep
            <4>1. CASE UF.rep[x] = UF.rep[d[p]]
                <5> UF'.rep[x] = UF.rep[c[p]]
                    BY <4>1
                <5> UF.id[UF.rep[c[p]]] >= UF.id[UF.rep[d[p]]]
                    BY <3>1
                <5> QED
                    OBVIOUS
            <4>2. CASE UF.rep[x] # UF.rep[d[p]]
                BY <4>2
            <4> QED
                BY <4>1, <4>2
        <3>2. CASE UF.id[UF.rep[c[p]]] < UF.id[UF.rep[d[p]]]
            <4> SmallerRep(UF.rep, c[p], d[p]) = UF.rep[c[p]]
                BY <3>2 DEF SmallerRep
            <4> LargerRep(UF.rep, c[p], d[p]) = UF.rep[d[p]]
                BY <3>2 DEF LargerRep
            <4> UF'.rep = [i \in NodeSet |-> IF UF.rep[i] = UF.rep[c[p]] THEN UF.rep[d[p]] ELSE UF.rep[i]]
                BY <1>3 DEF U1, UFUnite, URep
            <4>1. CASE UF.rep[x] = UF.rep[c[p]]
                <5> UF'.rep[x] = UF.rep[d[p]]
                    BY <4>1
                <5> UF.id[UF.rep[d[p]]] > UF.id[UF.rep[c[p]]]
                    BY <3>2
                <5> QED
                    OBVIOUS
            <4>2. CASE UF.rep[x] # UF.rep[c[p]]
                <5> QED
                    BY <4>2
            <4> QED
                BY <4>1, <4>2
        <3> QED
            BY <3>1, <3>2
    <2> QED
      <3> SUFFICES ASSUME NEW q \in PROCESSES',
                          (pc[q] \in {"S1", "S2", "S3", "S4", "S5", "S6", "SR"})
                   PROVE  (/\ UF.id[UF.rep[u[q]]] >= i_u[q]
                           /\ UF.id[UF.rep[v[q]]] >= i_v[q])'
        BY <1>3 DEF I_IDs, TypeOK, PCTypeOK, U1
      <3> /\ UF.id[UF.rep[u[q]]] >= (i_u[q])'
          /\ UF.id[UF.rep[v[q]]] >= (i_v[q])'
        BY DEF I_IDs, TypeOK, UFTypeOK, UFId_StateSet, Idems, uTypeOK, vTypeOK, PCTypeOK
      <3>x. /\ (UF.id[UF.rep[u[q]]])' >= UF.id[UF.rep[u[q]]] 
            /\ (UF.id[UF.rep[v[q]]])' >= UF.id[UF.rep[v[q]]]
        BY <1>3, <2>a DEF U1, TypeOK, uTypeOK, vTypeOK
      <3> TypeOK'
        BY TypeOKNext, <1>3 DEF Next, Step
      <3> (UF.id[UF.rep[u[q]]])' \in Nat /\ (UF.id[UF.rep[v[q]]])' \in Nat
        BY DEF TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, uTypeOK, vTypeOK
      <3> UF.id[UF.rep[u[q]]] \in Nat /\ UF.id[UF.rep[v[q]]] \in Nat
        BY DEF TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, uTypeOK, vTypeOK
      <3> i_u[q]' \in Nat /\ i_v[q] \in Nat
        BY DEF TypeOK, i_uTypeOK, i_vTypeOK
      <3> QED
        BY <3>x DEF TypeOK  
  <1>4. ASSUME NEW p \in PROCESSES, UR(p)
            PROVE I_IDs'
    BY <1>4 DEF I_IDs, UR
  <1>5. ASSUME NEW p \in PROCESSES, S1(p)
            PROVE I_IDs'
    <2> SUFFICES ASSUME NEW q \in PROCESSES,
                        (pc'[q] \in {"S1", "S2", "S3", "S4", "S5", "S6", "SR"})
                 PROVE (/\ UF.id[UF.rep[u[q]]] >= i_u[q]
                        /\ UF.id[UF.rep[v[q]]] >= i_v[q])'
      BY <1>5 DEF I_IDs, S1
    <2> TypeOK'
      BY <1>5, TypeOKNext DEF Next, Step 
    <2> i_u[p] = 0 /\ i_v[p] = 0
      BY <1>5 DEF S1, I_2
    <2> \A x \in NodeSet: (UF.id[UF.rep[x]]') >= 0
      BY DEF TypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, Idems
    <2> UNCHANGED <<i_u, i_v, UF>>
      BY <1>5 DEF S1
    <2> QED
      BY <1>5 DEF I_IDs, S1, TypeOK, I_IDs, uTypeOK, vTypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs        
  <1>6. ASSUME NEW p \in PROCESSES, S2(p)
            PROVE I_IDs'
    <2> SUFFICES ASSUME NEW q \in PROCESSES,
                        (pc'[q] \in {"S1", "S2", "S3", "S4", "S5", "S6", "SR"})
                 PROVE (/\ UF.id[UF.rep[u[q]]] >= i_u[q]
                        /\ UF.id[UF.rep[v[q]]] >= i_v[q])'
      BY <1>6 DEF I_IDs, S2
    <2> TypeOK'
      BY <1>6, TypeOKNext DEF Next, Step 
    <2>1. CASE q = p
      <3> USE <2>1
      <3> pc'[p] = "S3"
        BY <1>6 DEF S2, TypeOK, PCTypeOK
      <3> u' = u /\ v' = v /\ i_v' = i_v
        BY <1>6 DEF S2
      <3> UF.id[UF.rep[u[p]]] >= i_u[p] /\ UF.id[UF.rep[v[p]]] >= i_v[p]
        BY <1>6 DEF I_IDs, S2
      <3>1. CASE UF.rep[u[p]] = u[p]
        <4> PICK newId \in IDUpdate(u[p]): UF' = [rep |-> UF.rep, id |-> newId]
          BY <1>6 DEF S2
        <4> \A x \in NodeSet: x # u[p] => newId[x] = UF.id[x]
          BY <1>6 DEF S2, IDUpdate, TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs
        <4> newId[u[p]] >= UF.id[u[p]]
          BY <3>1 DEF IDUpdate, TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, CandID
        <4> i_u'[p] = UF.id[u[p]]
          BY <1>6, <3>1 DEF S2, TypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, uTypeOK, i_uTypeOK
        <4> (UF.id[u[p]])' >= i_u'[p]
          BY <1>6 DEF S2 
        <4>1. (UF.id[UF.rep[u[q]]] >= i_u[q])'
          BY <1>6, <3>1 DEF S2, TypeOK, UFTypeOK, UFId_StateSet, Idems, uTypeOK, vTypeOK, i_uTypeOK
        <4>2. (UF.id[UF.rep[v[q]]] >= i_v[q])'
          BY <1>6, <3>1 DEF S2, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, uTypeOK, vTypeOK, i_vTypeOK
        <4>3. QED
          BY <4>1, <4>2    
      <3>2. CASE UF.rep[u[p]] # u[p]
        <4> PICK newId \in IDUpdate(u[p]): UF' = [rep |-> UF.rep, id |-> newId]
            BY <1>6 DEF S2
        <4> newId[u[p]] = 0
            BY <3>2 DEF IDUpdate, TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, CandID
        <4> UF.id'[u[p]] = 0
            BY <1>6 DEF S2, IDUpdate, CandID
        <4> \A x \in NodeSet: x # u[p] => newId[x] = UF.id[x]
            BY <1>6 DEF S2, IDUpdate, TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs
        <4> i_u'[p] = 0
            BY <1>6, <3>2 DEF S2, TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, Idems, i_uTypeOK
        <4> newId[(UF.rep[u[q]])'] = UF.id[UF.rep[u[q]]]
            BY <3>2 DEF TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, Idems, uTypeOK
        <4>1. (UF.id[UF.rep[u[q]]] >= i_u[q])'
          BY <1>6, <3>2 DEF S2, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, uTypeOK, vTypeOK, i_uTypeOK
        <4>2. (UF.id[UF.rep[v[q]]] >= i_v[q])'
          BY <1>6, <3>2 DEF S2, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, uTypeOK, vTypeOK, i_vTypeOK, I_IDs
        <4>3. QED
          BY <4>1, <4>2 
      <3> QED
        BY <3>1, <3>2
    <2>2. CASE q # p
      <3> PICK newId \in IDUpdate(u[p]): UF' = [rep |-> UF.rep, id |-> newId]
        BY <1>6 DEF S2
      <3> UNCHANGED <<u, v, i_u[q], i_v[q], UF.rep>>
        BY <2>2, <1>6 DEF S2, TypeOK, UFTypeOK, UFId_StateSet
      <3> newId[(UF.rep[u[q]])'] >= UF.id[UF.rep[u[q]]]
        BY <2>2 DEF TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, Idems, IDUpdate, CandID
      <3> newId[(UF.rep[v[q]])'] >= UF.id[UF.rep[v[q]]]
        BY <2>2 DEF TypeOK, vTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, Idems, IDUpdate, CandID
      <3> QED
        BY <1>6, <2>2 DEF S2, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK, I_IDs
    <2> QED
      BY <2>1, <2>2
  <1>7. ASSUME NEW p \in PROCESSES, S3(p)
            PROVE I_IDs'
    <2> SUFFICES ASSUME NEW q \in PROCESSES,
                        (pc'[q] \in {"S1", "S2", "S3", "S4", "S5", "S6", "SR"})
                 PROVE (/\ UF.id[UF.rep[u[q]]] >= i_u[q]
                        /\ UF.id[UF.rep[v[q]]] >= i_v[q])'
      BY <1>7 DEF I_IDs, S3
    <2>1. CASE q # p
      <3> UNCHANGED <<i_u[q], i_v[q], u[q], v[q], UF>>
        BY <2>1, <1>7 DEF S3, TypeOK, i_uTypeOK, i_vTypeOK, uTypeOK, vTypeOK
      <3> UF.id[UF.rep[u[q]]] >= i_u[q] /\ UF.id[UF.rep[v[q]]] >= i_v[q]
        BY <2>1, <1>7 DEF S3, I_IDs, TypeOK, PCTypeOK
      <3> QED
        BY <1>7 DEF S3, I_IDs, TypeOK, i_uTypeOK, i_vTypeOK, uTypeOK, vTypeOK
    <2>2. CASE q = p
      <3> \A x \in NodeSet: UF.id[x]' = UF.id[x]
        BY <1>7 DEF S3
      <3> UNCHANGED <<i_u[q], i_v[q], u[q]>>
        BY <2>2, <1>7 DEF S3, TypeOK, i_uTypeOK, i_vTypeOK, uTypeOK, vTypeOK
      <3> v'[p] = UF.rep[v[p]]
        BY <1>7 DEF S3, TypeOK, vTypeOK, UFTypeOK, UFId_StateSet, Idems
      <3> UF.rep[UF.rep[v[p]]] = UF.rep[v[p]]
        BY <1>7 DEF TypeOK, UFTypeOK, UFId_StateSet, Idems, vTypeOK
      <3> (UF.id[UF.rep[v[p]]])' = UF.id[UF.rep[v[p]]]
        BY <1>7 DEF S3
      <3> QED
        BY <1>7, <2>2 DEF I_IDs, S3
    <2> QED
      BY <2>1, <2>2
  <1>8. ASSUME NEW p \in PROCESSES, S4(p)
            PROVE I_IDs'
    <2> SUFFICES ASSUME NEW q \in PROCESSES,
                            (pc'[q] \in {"S1", "S2", "S3", "S4", "S5", "S6", "SR"})
                    PROVE (/\ UF.id[UF.rep[u[q]]] >= i_u[q]
                            /\ UF.id[UF.rep[v[q]]] >= i_v[q])'
        BY <1>8 DEF I_IDs, S4
    <2> TypeOK'
      BY <1>8, TypeOKNext DEF Next, Step 
    <2> USE DEF S4
    <2>1. CASE p = q
      <3> USE <2>1
      <3> pc'[p] \in {"S5", "SR"}
        BY <1>8 DEF TypeOK, PCTypeOK
      <3> u' = u /\ v' = v /\ i_u' = i_u
        BY <1>8
      <3> UF.id[UF.rep[u[p]]] >= i_u[p] /\ UF.id[UF.rep[v[p]]] >= i_v[p]
        BY <1>8 DEF I_IDs
      <3>1. CASE UF.rep[v[p]] = v[p]
        <4> PICK newId \in IDUpdate(v[p]): UF' = [rep |-> UF.rep, id |-> newId]
          BY <1>8
        <4> \A x \in NodeSet: x # v[p] => newId[x] = UF.id[x]
          BY <1>8 DEF IDUpdate, TypeOK, vTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs
        <4> newId[v[p]] >= UF.id[v[p]]
          BY <3>1 DEF IDUpdate, TypeOK, vTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, CandID
        <4> i_v'[p] = UF.id[v[p]]
          BY <1>8, <3>1 DEF TypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, vTypeOK, i_vTypeOK
        <4> (UF.id[v[p]])' >= i_v'[p]
          BY <1>8 
        <4> UF.rep'[v[q]] = v[q]
          BY <1>8, <3>1 DEF TypeOK, S4, vTypeOK
        <4>1. (UF.id[UF.rep[v[q]]] >= i_v[q])'
          BY <1>8, <3>1 DEF S4, TypeOK, UFTypeOK, UFId_StateSet, Idems, i_uTypeOK, uTypeOK, vTypeOK, i_vTypeOK
        <4>2. (UF.id[UF.rep[u[q]]] >= i_u[q])'
          BY <1>8, <3>1 DEF S4, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK, I_IDs
        <4>3. QED
          BY <4>1, <4>2    
      <3>2. CASE UF.rep[v[p]] # v[p]
        <4> PICK newId \in IDUpdate(v[p]): UF' = [rep |-> UF.rep, id |-> newId]
            BY <1>8 DEF S6
        <4> newId[v[p]] = 0
            BY <3>2 DEF IDUpdate, TypeOK, vTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, CandID
        <4> UF.id'[v[p]] = 0
            BY <1>8 DEF S6, IDUpdate, CandID
        <4> \A x \in NodeSet: x # v[p] => newId[x] = UF.id[x]
            BY <1>8 DEF S6, IDUpdate, TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs
        <4> i_v'[p] = 0
            BY <1>8, <3>2 DEF S6, TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, Idems, i_vTypeOK
        <4> newId[(UF.rep[u[q]])'] = UF.id[UF.rep[u[q]]]
            BY <3>2 DEF TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, Idems, uTypeOK
        <4> newId[(UF.rep[v[q]])'] = UF.id[UF.rep[v[q]]]
            BY <3>2 DEF TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, Idems, vTypeOK, uTypeOK
        <4>1. (UF.id[UF.rep[u[q]]] >= i_u[q])'
          BY <1>8, <3>2 DEF S6, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, uTypeOK, vTypeOK, i_uTypeOK
        <4>2. (UF.id[UF.rep[v[q]]] >= i_v[q])'
          BY <1>8, <3>2 DEF S6, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, uTypeOK, vTypeOK, i_vTypeOK, I_IDs
        <4>3. QED
          BY <4>1, <4>2 
      <3> QED
        BY <3>1, <3>2
    <2>2. CASE q # p
      <3> PICK newId \in IDUpdate(v[p]): UF' = [rep |-> UF.rep, id |-> newId]
        BY <1>8
      <3> UNCHANGED <<u, v, i_u[q], i_v[q], UF.rep>>
        BY <2>2, <1>8 DEF TypeOK, UFTypeOK, UFId_StateSet
      <3> newId[(UF.rep[v[q]])'] >= UF.id[UF.rep[v[q]]]
        BY <2>2 DEF TypeOK, vTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, Idems, IDUpdate, CandID
      <3> newId[(UF.rep[u[q]])'] >= UF.id[UF.rep[u[q]]]
        BY <2>2 DEF TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, Idems, IDUpdate, CandID
      <3> UF.id[UF.rep[u[q]]] >= i_u[q]'
        BY <2>2, <1>8 DEF I_IDs, TypeOK, PCTypeOK
      <3> UF.id[UF.rep[v[q]]] >= i_v[q]'
        BY <2>2, <1>8 DEF I_IDs, TypeOK, PCTypeOK
      <3> newId[(UF.rep[v[q]])'] \in Nat /\ i_v[q]' \in Nat /\ UF.id[UF.rep[v[q]]] \in Nat
        BY DEF TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK
      <3> newId[(UF.rep[u[q]])'] \in Nat /\ i_u[q]' \in Nat /\ UF.id[UF.rep[u[q]]] \in Nat
        BY DEF TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK
      <3> QED
        BY <1>8, <2>2 DEF TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK, I_IDs        
    <2> QED
      BY <2>1, <2>2
  <1>9. ASSUME NEW p \in PROCESSES, S5(p)
            PROVE I_IDs'
    <2> SUFFICES ASSUME NEW q \in PROCESSES,
                        (pc'[q] \in {"S1", "S2", "S3", "S4", "S5", "S6", "SR"})
                 PROVE (/\ UF.id[UF.rep[u[q]]] >= i_u[q]
                        /\ UF.id[UF.rep[v[q]]] >= i_v[q])'
      BY <1>9 DEF I_IDs, S5
    <2>1. CASE q # p
      <3> UNCHANGED <<i_u[q], i_v[q], u[q], v[q], UF>>
        BY <2>1, <1>9 DEF S5, TypeOK, i_uTypeOK, i_vTypeOK, uTypeOK, vTypeOK
      <3> UF.id[UF.rep[u[q]]] >= i_u[q] /\ UF.id[UF.rep[v[q]]] >= i_v[q]
        BY <2>1, <1>9 DEF S5, I_IDs, TypeOK, PCTypeOK
      <3> QED
        BY <1>9 DEF S5, I_IDs, TypeOK, i_uTypeOK, i_vTypeOK, uTypeOK, vTypeOK
    <2>2. CASE q = p
      <3> \A x \in NodeSet: UF.id[x]' = UF.id[x]
        BY <1>9 DEF S5
      <3> UNCHANGED <<i_u[q], i_v[q], v[q]>>
        BY <2>2, <1>9 DEF S5, TypeOK, i_uTypeOK, i_vTypeOK, uTypeOK, vTypeOK
      <3> u'[p] = UF.rep[u[p]]
        BY <1>9 DEF S5, TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, Idems
      <3> UF.rep[UF.rep[u[p]]] = UF.rep[u[p]]
        BY <1>9 DEF TypeOK, UFTypeOK, UFId_StateSet, Idems, uTypeOK
      <3> (UF.id[UF.rep[u[p]]])' = UF.id[UF.rep[u[p]]]
        BY <1>9 DEF S5
      <3> QED
        BY <1>9, <2>2 DEF I_IDs, S5
    <2> QED
      BY <2>1, <2>2
  <1>10. ASSUME NEW p \in PROCESSES, S6(p)
            PROVE I_IDs'
    <2> SUFFICES ASSUME NEW q \in PROCESSES,
                            (pc'[q] \in {"S1", "S2", "S3", "S4", "S5", "S6", "SR"})
                    PROVE (/\ UF.id[UF.rep[u[q]]] >= i_u[q]
                            /\ UF.id[UF.rep[v[q]]] >= i_v[q])'
        BY <1>10 DEF I_IDs, S6
    <2> TypeOK'
      BY <1>10, TypeOKNext DEF Next, Step 
    <2>1. CASE q = p
      <3> USE <2>1
      <3> pc'[p] \in {"S3", "SR"}
        BY <1>10 DEF S6, TypeOK, PCTypeOK
      <3> u' = u /\ v' = v /\ i_v' = i_v
        BY <1>10 DEF S6
      <3> UF.id[UF.rep[u[p]]] >= i_u[p] /\ UF.id[UF.rep[v[p]]] >= i_v[p]
        BY <1>10 DEF I_IDs, S6
      <3>1. CASE UF.rep[u[p]] = u[p]
        <4> PICK newId \in IDUpdate(u[p]): UF' = [rep |-> UF.rep, id |-> newId]
          BY <1>10 DEF S6
        <4> \A x \in NodeSet: x # u[p] => newId[x] = UF.id[x]
          BY <1>10 DEF S6, IDUpdate, TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs
        <4> newId[u[p]] >= UF.id[u[p]]
          BY <3>1 DEF IDUpdate, TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, CandID
        <4> i_u'[p] = UF.id[u[p]]
          BY <1>10, <3>1 DEF S6, TypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, uTypeOK, i_uTypeOK
        <4> (UF.id[u[p]])' >= i_u'[p]
          BY <1>10 DEF S6 
        <4>1. (UF.id[UF.rep[u[q]]] >= i_u[q])'
          BY <1>10, <3>1 DEF S6, TypeOK, UFTypeOK, UFId_StateSet, Idems, uTypeOK, vTypeOK, i_uTypeOK
        <4>2. (UF.id[UF.rep[v[q]]] >= i_v[q])'
          BY <1>10, <3>1 DEF S6, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, uTypeOK, vTypeOK, i_vTypeOK
        <4>3. QED
          BY <4>1, <4>2    
      <3>2. CASE UF.rep[u[p]] # u[p]
        <4> PICK newId \in IDUpdate(u[p]): UF' = [rep |-> UF.rep, id |-> newId]
            BY <1>10 DEF S6
        <4> newId[u[p]] = 0
            BY <3>2 DEF IDUpdate, TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, CandID
        <4> UF.id'[u[p]] = 0
            BY <1>10 DEF S6, IDUpdate, CandID
        <4> \A x \in NodeSet: x # u[p] => newId[x] = UF.id[x]
            BY <1>10 DEF S6, IDUpdate, TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs
        <4> i_u'[p] = 0
            BY <1>10, <3>2 DEF S6, TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, Idems, i_uTypeOK
        <4> newId[(UF.rep[u[q]])'] = UF.id[UF.rep[u[q]]]
            BY <3>2 DEF TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, Idems, uTypeOK
        <4> newId[(UF.rep[v[q]])'] = UF.id[UF.rep[v[q]]]
            BY <3>2 DEF TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, Idems, vTypeOK, uTypeOK
        <4>1. (UF.id[UF.rep[u[q]]] >= i_u[q])'
          BY <1>10, <3>2 DEF S6, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, uTypeOK, vTypeOK, i_uTypeOK
        <4>2. (UF.id[UF.rep[v[q]]] >= i_v[q])'
          BY <1>10, <3>2 DEF S6, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, uTypeOK, vTypeOK, i_vTypeOK, I_IDs
        <4>3. QED
          BY <4>1, <4>2 
      <3> QED
        BY <3>1, <3>2
    <2>2. CASE q # p
      <3> PICK newId \in IDUpdate(u[p]): UF' = [rep |-> UF.rep, id |-> newId]
        BY <1>10 DEF S6
      <3> UNCHANGED <<u, v, i_u[q], i_v[q], UF.rep>>
        BY <2>2, <1>10 DEF S6, TypeOK, UFTypeOK, UFId_StateSet
      <3> newId[(UF.rep[u[q]])'] >= UF.id[UF.rep[u[q]]]
        BY <2>2 DEF TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, Idems, IDUpdate, CandID
      <3> newId[(UF.rep[v[q]])'] >= UF.id[UF.rep[v[q]]]
        BY <2>2 DEF TypeOK, vTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, Idems, IDUpdate, CandID
      <3> UF.id[UF.rep[v[q]]] >= i_v[q]'
        BY <2>2, <1>10 DEF I_IDs, S6, TypeOK, PCTypeOK
      <3> UF.id[UF.rep[u[q]]] >= i_u[q]'
        BY <2>2, <1>10 DEF I_IDs, S6, TypeOK, PCTypeOK
      <3> newId[(UF.rep[v[q]])'] \in Nat /\ i_v[q]' \in Nat /\ UF.id[UF.rep[v[q]]] \in Nat
        BY DEF TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK
      <3> newId[(UF.rep[u[q]])'] \in Nat /\ i_u[q]' \in Nat /\ UF.id[UF.rep[u[q]]] \in Nat
        BY DEF TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK
      <3> QED
        BY <1>10, <2>2 DEF S6, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK, I_IDs        
    <2> QED
      BY <2>1, <2>2
  <1>11. ASSUME NEW p \in PROCESSES, SR(p)
            PROVE I_IDs'
    BY <1>11 DEF I_IDs, SR, TypeOK
  <1>12. ASSUME NEW p \in PROCESSES, Decide(p)
            PROVE I_IDs'
    <2> SUFFICES ASSUME NEW q \in PROCESSES,
                        (pc'[q] \in {"S1", "S2", "S3", "S4", "S5", "S6", "SR"})
                 PROVE (/\ UF.id[UF.rep[u[q]]] >= i_u[q]
                        /\ UF.id[UF.rep[v[q]]] >= i_v[q])'
      BY <1>12 DEF I_IDs, Decide
    <2> pc[p] = "0"
      BY <1>12 DEF Decide
    <2> TypeOK'
      BY <1>12, TypeOKNext DEF Next, Step
    <2> \A x \in NodeSet: (UF.id[UF.rep[x]]') >= 0
      BY DEF TypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, Idems
    <2>1. CASE q = p
        <3> (i_u'[q] = 0 /\ i_v'[q] = 0)
            BY <1>12, <2>1 DEF Decide, TypeOK, i_uTypeOK, i_vTypeOK, PCTypeOK
        <3> QED
            BY <1>12 DEF Decide, TypeOK, uTypeOK, vTypeOK
    <2>2. CASE q # p
        <3> \A x \in NodeSet: UF.id[x]' = UF.id[x]
            BY <1>12 DEF Decide
        <3> UNCHANGED <<i_u[q], i_v[q], u[q], v[q]>>
            BY <2>2, <1>12 DEF Decide, TypeOK, i_uTypeOK, i_vTypeOK, uTypeOK, vTypeOK
        <3> UF.id[UF.rep[u[q]]] >= i_u[q] /\ UF.id[UF.rep[v[q]]] >= i_v[q]
            BY <2>2, <1>12 DEF I_IDs, TypeOK, PCTypeOK, Decide
        <3> QED
            BY <1>12 DEF Decide, I_IDs, TypeOK, i_uTypeOK, i_vTypeOK, uTypeOK, vTypeOK
    <2> QED
      BY <2>1, <2>2
  <1>13. CASE UNCHANGED varlist
    BY <1>13 DEF varlist, I_IDs
  <1> QED
    BY <1>1, <1>10, <1>11, <1>12, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>13 DEF Step, Next


LEMMA SpecMaintainsI_IDs == UFSSpec => []I_IDs
  BY InitI_IDs, NextI_IDs, PTL, SpecTypeOK, SpecMaintainsI2 DEF UFSSpec


LEMMA InitQinM == Init => QinM
  <1> SUFFICES ASSUME Init
               PROVE QinM
    OBVIOUS
  <1> USE DEF Init, Q, InitUF, InitOp, InitArg, InitRet, Configs, InitState,
              UFId_StateSet, I_F1, I_FR, I_U1, I_UR, I_Sk, I_SR, I_0
  <1> DEFINE InitT == [sigma |-> InitState,  ret |-> InitRet, op |-> InitOp, arg |-> InitArg]
  <1>1. Q = {InitT}
    <2>1. InitT \in Q
      <3>1. InitT \in Configs
        <4>1. InitT.sigma \in Idems
          BY DEF Idems
        <4>2. InitT.op \in OpSet
          BY DEF OpSet
        <4>3. InitT.arg \in ArgSet
          BY DEF ArgSet
        <4>4. InitT.ret \in ReturnSet
          BY DEF ReturnSet
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4
      <3>2. InitT.sigma = UF.rep
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

LEMMA NextQinM == QinM /\ TypeOK /\ I_1 /\ I_IDs /\ IDUniqueness /\ [Next]_varlist => QinM'
 <1> SUFFICES ASSUME QinM /\ TypeOK /\ I_1 /\ I_IDs /\ IDUniqueness /\ [Next]_varlist
              PROVE  QinM'
   OBVIOUS
 <1> USE DEF QinM, TypeOK, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK,
             i_vTypeOK, cTypeOK, dTypeOK, MTypeOK, retTypeOK, Configs, Idems, ReturnSet, 
             OpSet, ArgSet, UFId_StateSet, Q, I_F1, I_FR, I_U1, I_UR, I_Sk, I_SR, I_0,
             I_U1Prime, I_URPrime, I_F1Prime, I_FRPrime, I_SkPrime, I_SRPrime, I_0Prime, NodeToIdFuncs
 <1>0. TypeOK'
    BY TypeOKNext, TypeOKUnchanged DEF varlist
 <1> SUFFICES ASSUME NEW t \in Q'
              PROVE t \in M'
   BY DEF Q, QinM 
 <1>1. ASSUME NEW p \in PROCESSES, Decide(p)
       PROVE t \in M'
   <2> USE <1>1 DEF Decide
   <2> \A q \in PROCESSES: q # p => UNCHANGED <<pc[q], c[q], d[q], ret[q]>>
     OBVIOUS
   <2> DEFINE told == [t EXCEPT !.op = [t.op EXCEPT ![p] = BOT],
                                !.arg = [t.arg EXCEPT ![p] = BOT]]
   <2>1. told \in Q
     <3> told \in Configs /\ UF.rep = told.sigma
        BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet, Decide
     <3> t.ret[p] = BOT
         OBVIOUS
     <3> SUFFICES ASSUME NEW q \in PROCESSES
                  PROVE /\ I_U1(told, q)
                        /\ I_UR(told, q)
                        /\ I_F1(told, q)
                        /\ I_FR(told, q)
                        /\ I_Sk(told, q)
                        /\ I_SR(told, q)
                        /\ I_0(told, q)
        BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet
     <3>1. CASE p = q
         BY <3>1, <1>0                 
     <3>2. CASE p # q
        BY <3>2, <1>0
     <3> QED
        BY <3>1, <3>2
   <2> told.ret[p] = BOT /\ told.arg[p] = BOT /\ told.op[p] = BOT
     BY DEF I_0
   <2>2. told \in M
     BY <2>1
   <2>3. t \in M'
     <3> HIDE DEF QinM, TypeOK, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK,
                     i_vTypeOK, cTypeOK, dTypeOK, MTypeOK, retTypeOK, Configs, Idems, ReturnSet, 
                     OpSet, ArgSet, UFId_StateSet, Q, I_F1, I_FR, I_U1, I_UR, I_Sk, I_SR, I_0,
                     I_U1Prime, I_URPrime, I_F1Prime, I_FRPrime, I_SkPrime, I_SRPrime, I_0Prime, NodeToIdFuncs
     <3> USE <1>0
     <3>1. CASE /\ pc' = [pc EXCEPT ![p] = "F1"]
                /\ M' = {t1 \in Configs: \E told1 \in M: /\ told1.ret[p] = BOT
                                                         /\ told1.op[p] = BOT
                                                         /\ told1.arg[p] = BOT
                                                         /\ t1.sigma = told1.sigma
                                                         /\ t1.op = [told1.op EXCEPT ![p] = "F"]
                                                         /\ t1.arg = [told1.arg EXCEPT ![p] = c'[p]]
                                                         /\ t1.ret = told1.ret}
       <4> HIDE DEF Decide
       <4>a. t.arg[p] = c'[p]
          BY <3>1 DEF told, TypeOK, PCTypeOK, I_F1, cTypeOK, Q
       <4>b. t.arg \in ArgSet /\ told.arg \in ArgSet
          BY <2>1 DEF Q, Configs
       <4> t.arg = [told.arg EXCEPT ![p] = c'[p]]
          BY <3>1,  <4>a, <4>b DEF told, TypeOK, Configs, ArgSet, Q, MTypeOK, PCTypeOK, I_F1, cTypeOK
       <4> t.op = [told.op EXCEPT ![p] = "F"]
          BY <3>1 DEF told, TypeOK, Configs, ArgSet, ReturnSet, OpSet, Idems, Q, MTypeOK, PCTypeOK, I_F1
       <4> t.ret = told.ret
          BY DEF told
       <4> t.sigma = told.sigma
          BY DEF told
       <4> t \in Configs
          BY DEF Q
       <4> HIDE DEF told
       <4> QED
          BY <3>1, <2>2
     <3>2. CASE /\ pc' = [pc EXCEPT ![p] = "U1"]
                /\ M' = {t1 \in Configs: \E told1 \in M: /\ told1.ret[p] = BOT
                                                         /\ told1.op[p] = BOT
                                                         /\ told1.arg[p] = BOT
                                                         /\ t1.sigma = told1.sigma
                                                         /\ t1.op = [told1.op EXCEPT ![p] = "U"]
                                                         /\ t1.arg = [told1.arg EXCEPT ![p] = <<c'[p], d'[p]>>]
                                                         /\ t1.ret = told1.ret}
       <4> HIDE DEF Decide
       <4>a. t.arg[p] = <<c'[p], d'[p]>>
          BY <3>2 DEF told, TypeOK, PCTypeOK, I_U1, cTypeOK, dTypeOK, Q
       <4>b. t.arg \in ArgSet /\ told.arg \in ArgSet
          BY <2>1 DEF Q, Configs
       <4> t.arg = [told.arg EXCEPT ![p] = <<c'[p], d'[p]>>]
          BY <3>2,  <4>a, <4>b DEF told, TypeOK, Configs, ArgSet, Q, MTypeOK, PCTypeOK, I_U1, cTypeOK, dTypeOK
       <4> t.op = [told.op EXCEPT ![p] = "U"]
          BY <3>2 DEF told, TypeOK, Configs, ArgSet, ReturnSet, OpSet, Idems, Q, MTypeOK, PCTypeOK, I_U1
       <4> t.ret = told.ret
          BY DEF told
       <4> t.sigma = told.sigma
          BY DEF told
       <4> t \in Configs
          BY DEF Q
       <4> HIDE DEF told
       <4> QED
          BY <3>2, <2>2
     <3>3. CASE /\ pc' = [pc EXCEPT ![p] = "S1"]
                /\ M' = {t1 \in Configs: \E told1 \in M: /\ told1.ret[p] = BOT
                                                         /\ told1.op[p] = BOT
                                                         /\ told1.arg[p] = BOT
                                                         /\ t1.sigma = told1.sigma
                                                         /\ t1.op = [told1.op EXCEPT ![p] = "S"]
                                                         /\ t1.arg = [told1.arg EXCEPT ![p] = <<c'[p], d'[p]>>]
                                                         /\ t1.ret = told1.ret}
       <4> HIDE DEF Decide
       <4>a. t.arg[p] = <<c'[p], d'[p]>>
          BY <3>3 DEF told, TypeOK, PCTypeOK, I_Sk, cTypeOK, dTypeOK, Q
       <4>b. t.arg \in ArgSet /\ told.arg \in ArgSet
          BY <2>1 DEF Q, Configs
       <4> t.arg = [told.arg EXCEPT ![p] = <<c'[p], d'[p]>>]
          BY <3>3,  <4>a, <4>b DEF told, TypeOK, Configs, ArgSet, Q, MTypeOK, PCTypeOK, I_Sk, cTypeOK, dTypeOK
       <4> t.op = [told.op EXCEPT ![p] = "S"]
          BY <3>3 DEF told, TypeOK, Configs, ArgSet, ReturnSet, OpSet, Idems, Q, MTypeOK, PCTypeOK, I_Sk
       <4> t.ret = told.ret
          BY DEF told
       <4> t.sigma = told.sigma
          BY DEF told
       <4> t \in Configs
          BY DEF Q
       <4> HIDE DEF told
       <4> QED
          BY <3>3, <2>2
     <3> QED
       BY <3>1, <3>2, <3>3
   <2> QED
     BY <2>3
 <1>2. ASSUME NEW p \in PROCESSES, F1(p)
       PROVE t \in M'
   <2> USE <1>2 DEF F1
   <2> DEFINE told == [t EXCEPT !.ret = [t.ret EXCEPT ![p] = BOT]]
   <2>1. told \in Q
     <3> told \in Configs /\ UF.rep = told.sigma
        BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet, Decide
     <3> SUFFICES ASSUME NEW q \in PROCESSES
                  PROVE /\ I_U1(told, q)
                        /\ I_UR(told, q)
                        /\ I_F1(told, q)
                        /\ I_FR(told, q)
                        /\ I_Sk(told, q)
                        /\ I_SR(told, q)
                        /\ I_0(told, q)
        BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet
     <3>1. CASE p = q
         BY <3>1, <1>0                 
     <3>2. CASE p # q
        BY <3>2, <1>0
     <3> QED
        BY <3>1, <3>2
   <2>2. told \in M
     BY <2>1
   <2>3. t \in M'
     <3>0. t \in Configs
        OBVIOUS
     <3> SUFFICES \E sold \in M:  /\ sold.ret[p] = BOT
                                  /\ t.ret = [sold.ret EXCEPT ![p] = sold.sigma[sold.arg[p]]]
                                  /\ t.sigma = sold.sigma
                                  /\ t.op = sold.op
                                  /\ t.arg = sold.arg
        BY <3>0
     <3>1. told.ret[p] = BOT
        OBVIOUS
     <3>2. t.sigma = told.sigma
        OBVIOUS
     <3>x. c[p] = told.arg[p]
        OBVIOUS
     <3>y. t.ret = [told.ret EXCEPT ![p] = told.sigma[c[p]]]
        OBVIOUS
     <3>3. t.ret = [told.ret EXCEPT ![p] = told.sigma[told.arg[p]]]
        BY <3>x, <3>y
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
     <3> told \in Configs /\ UF.rep = told.sigma
        BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet, Decide
     <3> SUFFICES ASSUME NEW q \in PROCESSES
                  PROVE /\ I_U1(told, q)
                        /\ I_UR(told, q)
                        /\ I_F1(told, q)
                        /\ I_FR(told, q)
                        /\ I_Sk(told, q)
                        /\ I_SR(told, q)
                        /\ I_0(told, q)
        BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet
     <3>1. CASE p = q
         BY <3>1, <1>0                 
     <3>2. CASE p # q
        BY <3>2, <1>0
     <3> QED
        BY <3>1, <3>2
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
   <2> \A q \in PROCESSES: q # p => UNCHANGED <<pc[q], c[q], d[q], ret[q]>>
     OBVIOUS
   <2> DEFINE told == [t EXCEPT !.ret = [t.ret EXCEPT ![p] = BOT],
                                !.sigma = UF.rep]
   <2>1. told \in Q
     <3> told \in Configs /\ UF.rep = told.sigma
        BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet, Decide
     <3> SUFFICES ASSUME NEW q \in PROCESSES
                  PROVE /\ I_U1(told, q)
                        /\ I_UR(told, q)
                        /\ I_F1(told, q)
                        /\ I_FR(told, q)
                        /\ I_Sk(told, q)
                        /\ I_SR(told, q)
                        /\ I_0(told, q)
        BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet
     <3>1. CASE p = q
         BY <3>1, <1>0                 
     <3>2. CASE p # q
        BY <3>2, <1>0
     <3> QED
        BY <3>1, <3>2
   <2>2. told \in M
     BY <2>1
   <2>3. t \in M'
     <3>0. t \in Configs
        OBVIOUS
     <3> SUFFICES \E sold \in M:  /\ sold.ret[p] = BOT
                                  /\ t.ret = [sold.ret EXCEPT ![p] = ACK]
                                  /\ t.sigma = MetaConfigUnite(sold.sigma, sold.arg[p][1], sold.arg[p][2])
                                  /\ t.op = sold.op
                                  /\ t.arg = sold.arg
        BY <3>0
     <3>1. told.ret[p] = BOT
        OBVIOUS
     <3>2. t.sigma = MetaConfigUnite(told.sigma, told.arg[p][1], told.arg[p][2])
        BY DEF UFUnite, MetaConfigUnite
     <3>3. t.ret = [told.ret EXCEPT ![p] = ACK]
       OBVIOUS
     <3>4. t.op = told.op
       OBVIOUS
     <3>5. t.arg = told.arg
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
     <3> told \in Configs /\ UF.rep = told.sigma
        BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet, Decide
     <3> SUFFICES ASSUME NEW q \in PROCESSES
                  PROVE /\ I_U1(told, q)
                        /\ I_UR(told, q)
                        /\ I_F1(told, q)
                        /\ I_FR(told, q)
                        /\ I_Sk(told, q)
                        /\ I_SR(told, q)
                        /\ I_0(told, q)
        BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet
     <3>1. CASE p = q
         BY <3>1, <1>0                 
     <3>2. CASE p # q
       <4>1. I_U1(told, q)
         BY <3>2, <1>0
       <4>2. I_UR(told, q)
         BY <3>2, <1>0
       <4>3. I_F1(told, q)
         BY <3>2, <1>0
       <4>4. I_FR(told, q)
         BY <3>2, <1>0
       <4>5. I_Sk(told, q)
         BY <3>2, <1>0
       <4>6. I_SR(told, q)
         BY <3>2, <1>0
       <4>7. I_0(told, q)
         BY <3>2, <1>0
       <4>8. QED
         BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7
        
     <3> QED
        BY <3>1, <3>2
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
   <2> QED
     BY <2>1
 <1>7. ASSUME NEW p \in PROCESSES, S2(p)
       PROVE t \in M'
   <2> USE <1>7 DEF S2
   <2>1. t \in Q
     <3> t \in Configs /\ UF.rep = t.sigma
        BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet, Decide
     <3> t.ret[p] = BOT
         OBVIOUS
     <3> SUFFICES ASSUME NEW q \in PROCESSES
                  PROVE /\ I_U1(t, q)
                        /\ I_UR(t, q)
                        /\ I_F1(t, q)
                        /\ I_FR(t, q)
                        /\ I_Sk(t, q)
                        /\ I_SR(t, q)
                        /\ I_0(t, q)
        BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet
     <3> QED
        OBVIOUS
   <2> QED
     BY <2>1
 <1>8. ASSUME NEW p \in PROCESSES, S3(p)
       PROVE t \in M'
   <2> USE <1>8 DEF S3
   <2>1. CASE u[p] = v'[p]
      <3> USE <2>1
      <3> DEFINE told == [t EXCEPT !.ret = [t.ret EXCEPT ![p] = BOT]]
      <3>0. told.sigma[told.arg[p][1]] = told.sigma[told.arg[p][2]]
         BY DEF I_1
      <3>1. told \in Q
         <4> told \in Configs /\ UF.rep = told.sigma
            BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet, Decide
         <4> SUFFICES ASSUME NEW q \in PROCESSES
                      PROVE /\ I_U1(told, q)
                            /\ I_UR(told, q)
                            /\ I_F1(told, q)
                            /\ I_FR(told, q)
                            /\ I_Sk(told, q)
                            /\ I_SR(told, q)
                            /\ I_0(told, q)
            BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet
         <4>1. CASE p = q
             BY <4>1, <1>0                 
         <4>2. CASE p # q
            BY <4>2, <1>0
         <4> QED
            BY <4>1, <4>2
       <3>2. told \in M
         BY <3>1
       <3>3. t \in M'
         <4>0. t \in Configs
            OBVIOUS
         <4> SUFFICES \E sold \in M:  /\ sold.ret[p] = BOT
                                      /\ t.ret = [sold.ret EXCEPT ![p] = IF sold.sigma[sold.arg[p][1]] = sold.sigma[sold.arg[p][2]] THEN TRUE ELSE FALSE]
                                      /\ t.sigma = sold.sigma
                                      /\ t.op = sold.op
                                      /\ t.arg = sold.arg
            BY <4>0
         <4>1. told.ret[p] = BOT
            OBVIOUS
         <4>2. t.sigma = told.sigma
            OBVIOUS
         <4>x. t.ret[p] = TRUE
            OBVIOUS
         <4>3. t.ret = [told.ret EXCEPT ![p] = TRUE]
           BY <4>x
         <4>4. t.op = told.op
           OBVIOUS
         <4>5. t.arg = told.arg
           OBVIOUS
         <4> QED
           BY <4>1, <4>2, <4>3, <4>4, <4>5, <3>2, <3>0
       <3> QED
         BY <3>3
   <2>2. CASE u[p] # v'[p]
       <3> USE <2>2
       <3>1. t \in Q
           <4> t \in Configs /\ UF.rep = t.sigma
              BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet, Decide
           <4> t.ret[p] = BOT
               OBVIOUS
           <4> SUFFICES ASSUME NEW q \in PROCESSES
                      PROVE /\ I_U1(t, q)
                            /\ I_UR(t, q)
                            /\ I_F1(t, q)
                            /\ I_FR(t, q)
                            /\ I_Sk(t, q)
                            /\ I_SR(t, q)
                            /\ I_0(t, q)
              BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet
           <4> QED
              OBVIOUS
       <3> QED
         BY <3>1
   <2> QED
     BY <2>1, <2>2
 <1>9. ASSUME NEW p \in PROCESSES, S4(p)
       PROVE t \in M'
   <2> USE <1>9 DEF S4
   <2>1. CASE i_u[p] > i_v'[p] /\ i_v'[p] > 0
      <3> DEFINE told == [t EXCEPT !.ret = [t.ret EXCEPT ![p] = BOT]]
      <3>p. pc[p] = "S4" /\ pc'[p] = "SR"
         BY <2>1
      <3>q. t.op[p] = "S" /\ t.arg[p] = <<c[p], d[p]>>  
         BY <3>p
      <3>0. told.sigma[told.arg[p][1]] # told.sigma[told.arg[p][2]]
         <4> USE <3>p
         <4> told.arg[p][1] = c[p] /\ told.arg[p][2] = d[p]
            OBVIOUS
         <4> told.sigma[u[p]] = told.sigma[told.arg[p][1]] /\ told.sigma[v[p]] = told.sigma[told.arg[p][2]] 
            BY DEF I_1
         <4> i_v'[p] = UF.id[v[p]]
            BY <2>1
         <4> UF.id[UF.rep[u[p]]] >= i_u[p]
            BY <2>1 DEF I_IDs
         <4> UF.id[v[p]] > 0 /\ UF.rep[v[p]] = v[p]
            BY <2>1 DEF IDUpdate, CandID
         <4> UF.id[UF.rep[u[p]]] > UF.id[UF.rep[v[p]]]
            BY <2>1
         <4> QED
            BY IDUniqueness
      <3>1. told \in Q
         <4> USE <2>1
         <4> UNCHANGED UF.rep
            OBVIOUS
         <4> HIDE DEF QinM, TypeOK, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK,
                     i_vTypeOK, cTypeOK, dTypeOK, MTypeOK, retTypeOK, Configs, Idems, ReturnSet, 
                     OpSet, ArgSet, UFId_StateSet, Q, I_F1, I_FR, I_U1, I_UR, I_Sk, I_SR, I_0,
                     I_U1Prime, I_URPrime, I_F1Prime, I_FRPrime, I_SkPrime, I_SRPrime, I_0Prime, NodeToIdFuncs

         <4> told \in Configs /\ UF.rep = told.sigma
            BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet, Decide
         <4> SUFFICES ASSUME NEW q \in PROCESSES
                      PROVE /\ I_U1(told, q)
                            /\ I_UR(told, q)
                            /\ I_F1(told, q)
                            /\ I_FR(told, q)
                            /\ I_Sk(told, q)
                            /\ I_SR(told, q)
                            /\ I_0(told, q)
            BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet
         <4>1. CASE p = q
           <5> USE DEF QinM, TypeOK, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK,
                       i_vTypeOK, cTypeOK, dTypeOK, MTypeOK, retTypeOK, Configs, Idems, ReturnSet, 
                       OpSet, ArgSet, UFId_StateSet, Q, I_F1, I_FR, I_U1, I_UR, I_Sk, I_SR, I_0,
                       I_U1Prime, I_URPrime, I_F1Prime, I_FRPrime, I_SkPrime, I_SRPrime, I_0Prime, NodeToIdFuncs
           <5> told.ret[p] = BOT /\ told.op[p] = "S" /\ told.arg[p] = <<c[p], d[p]>>
             BY <3>p, <3>q
           <5> QED
               BY <4>1, <1>0 DEF I_F1, I_FR, I_U1, I_UR, I_Sk, I_SR, I_0
         <4>2. CASE p # q
           <5> UNCHANGED <<pc[q], ret[q]>>
               BY <4>2 DEF TypeOK, PCTypeOK, retTypeOK
           <5> USE DEF QinM, TypeOK, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK,
                       i_vTypeOK, cTypeOK, dTypeOK, MTypeOK, retTypeOK, Configs, Idems, ReturnSet, 
                       OpSet, ArgSet, UFId_StateSet, Q, I_F1, I_FR, I_U1, I_UR, I_Sk, I_SR, I_0,
                       I_U1Prime, I_URPrime, I_F1Prime, I_FRPrime, I_SkPrime, I_SRPrime, I_0Prime, NodeToIdFuncs
           <5> QED
               BY <4>2, <1>0 DEF I_F1, I_FR, I_U1, I_UR, I_Sk, I_SR, I_0
                 
         <4> QED
            BY <4>1, <4>2
       <3>2. told \in M
         BY <3>1
       <3>i. t.ret[p] = ret'[p]
         BY <3>p, <2>1
       <3>j. ret'[p] = FALSE
         BY <2>1
       <3>3. t \in M'
         <4>0. t \in Configs
            OBVIOUS
         <4>1. told.ret[p] = BOT
            OBVIOUS
         <4>2. t.sigma = told.sigma
            OBVIOUS
         <4>x. t.ret[p] = FALSE
            BY <3>i, <3>j
         <4>3. t.ret = [told.ret EXCEPT ![p] = FALSE]
           BY <4>x
         <4>4. t.op = told.op
           OBVIOUS
         <4>5. t.arg = told.arg
           OBVIOUS
         <4> QED
           BY <4>1, <4>2, <4>3, <4>4, <4>5, <3>2, <3>0
       <3> QED
         BY <3>3
   <2>2. CASE ~(i_u[p] > i_v'[p] /\ i_v'[p] > 0)
       <3> USE <2>2
       <3>1. t \in Q
           <4> t \in Configs /\ UF.rep = t.sigma
              BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet, Decide
           <4> t.ret[p] = BOT
               OBVIOUS
           <4> SUFFICES ASSUME NEW q \in PROCESSES
                      PROVE /\ I_U1(t, q)
                            /\ I_UR(t, q)
                            /\ I_F1(t, q)
                            /\ I_FR(t, q)
                            /\ I_Sk(t, q)
                            /\ I_SR(t, q)
                            /\ I_0(t, q)
              BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet
           <4> QED
              OBVIOUS
       <3> QED
         BY <3>1
   <2> QED
     BY <2>1, <2>2
 <1>10. ASSUME NEW p \in PROCESSES, S5(p)
       PROVE t \in M'
   <2> USE <1>10 DEF S5
   <2>1. CASE v[p] = u'[p]
      <3> USE <2>1
      <3> DEFINE told == [t EXCEPT !.ret = [t.ret EXCEPT ![p] = BOT]]
      <3>0. told.sigma[told.arg[p][1]] = told.sigma[told.arg[p][2]]
         BY DEF I_1
      <3>1. told \in Q
         <4> told \in Configs /\ UF.rep = told.sigma
            BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet, Decide
         <4> SUFFICES ASSUME NEW q \in PROCESSES
                      PROVE /\ I_U1(told, q)
                            /\ I_UR(told, q)
                            /\ I_F1(told, q)
                            /\ I_FR(told, q)
                            /\ I_Sk(told, q)
                            /\ I_SR(told, q)
                            /\ I_0(told, q)
            BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet
         <4>1. CASE p = q
             BY <4>1, <1>0                 
         <4>2. CASE p # q
            BY <4>2, <1>0
         <4> QED
            BY <4>1, <4>2
       <3>2. told \in M
         BY <3>1
       <3>3. t \in M'
         <4>0. t \in Configs
            OBVIOUS
         <4> SUFFICES \E sold \in M:  /\ sold.ret[p] = BOT
                                      /\ t.ret = [sold.ret EXCEPT ![p] = IF sold.sigma[sold.arg[p][1]] = sold.sigma[sold.arg[p][2]] THEN TRUE ELSE FALSE]
                                      /\ t.sigma = sold.sigma
                                      /\ t.op = sold.op
                                      /\ t.arg = sold.arg
            BY <4>0
         <4>1. told.ret[p] = BOT
            OBVIOUS
         <4>2. t.sigma = told.sigma
            OBVIOUS
         <4>x. t.ret[p] = TRUE
            OBVIOUS
         <4>3. t.ret = [told.ret EXCEPT ![p] = TRUE]
           BY <4>x
         <4>4. t.op = told.op
           OBVIOUS
         <4>5. t.arg = told.arg
           OBVIOUS
         <4> QED
           BY <4>1, <4>2, <4>3, <4>4, <4>5, <3>2, <3>0
       <3> QED
         BY <3>3
   <2>2. CASE v[p] # u'[p]
       <3> USE <2>2
       <3>1. t \in Q
           <4> t \in Configs /\ UF.rep = t.sigma
              BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet, Decide
           <4> t.ret[p] = BOT
               OBVIOUS
           <4> SUFFICES ASSUME NEW q \in PROCESSES
                      PROVE /\ I_U1(t, q)
                            /\ I_UR(t, q)
                            /\ I_F1(t, q)
                            /\ I_FR(t, q)
                            /\ I_Sk(t, q)
                            /\ I_SR(t, q)
                            /\ I_0(t, q)
              BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet
           <4> QED
              OBVIOUS
       <3> QED
         BY <3>1
   <2> QED
     BY <2>1, <2>2
 <1>11. ASSUME NEW p \in PROCESSES, S6(p)
       PROVE t \in M'
   <2> USE <1>11 DEF S6
   <2>1. CASE i_v[p] > i_u'[p] /\ i_u'[p] > 0
      <3> DEFINE told == [t EXCEPT !.ret = [t.ret EXCEPT ![p] = BOT]]
      <3>p. pc[p] = "S6" /\ pc'[p] = "SR"
         BY <2>1
      <3>q. t.op[p] = "S" /\ t.arg[p] = <<c[p], d[p]>>  
         BY <3>p
      <3>0. told.sigma[told.arg[p][1]] # told.sigma[told.arg[p][2]]
         <4> USE <3>p
         <4> told.arg[p][1] = c[p] /\ told.arg[p][2] = d[p]
            OBVIOUS
         <4> told.sigma[u[p]] = told.sigma[told.arg[p][1]] /\ told.sigma[v[p]] = told.sigma[told.arg[p][2]] 
            BY DEF I_1
         <4> i_u'[p] = UF.id[u[p]]
            BY <2>1
         <4> UF.id[UF.rep[v[p]]] >= i_v[p]
            BY <2>1 DEF I_IDs
         <4> UF.id[u[p]] > 0 /\ UF.rep[u[p]] = u[p]
            BY <2>1 DEF IDUpdate, CandID
         <4> UF.id[UF.rep[v[p]]] > UF.id[UF.rep[u[p]]]
            BY <2>1
         <4> QED
            BY IDUniqueness
      <3>1. told \in Q
         <4> USE <2>1
         <4> UNCHANGED UF.rep
            OBVIOUS
         <4> HIDE DEF QinM, TypeOK, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK,
                     i_vTypeOK, cTypeOK, dTypeOK, MTypeOK, retTypeOK, Configs, Idems, ReturnSet, 
                     OpSet, ArgSet, UFId_StateSet, Q, I_F1, I_FR, I_U1, I_UR, I_Sk, I_SR, I_0,
                     I_U1Prime, I_URPrime, I_F1Prime, I_FRPrime, I_SkPrime, I_SRPrime, I_0Prime, NodeToIdFuncs

         <4> told \in Configs /\ UF.rep = told.sigma
            BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet, Decide
         <4> SUFFICES ASSUME NEW q \in PROCESSES
                      PROVE /\ I_U1(told, q)
                            /\ I_UR(told, q)
                            /\ I_F1(told, q)
                            /\ I_FR(told, q)
                            /\ I_Sk(told, q)
                            /\ I_SR(told, q)
                            /\ I_0(told, q)
            BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet
         <4>1. CASE p = q
           <5> USE DEF QinM, TypeOK, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK,
                       i_vTypeOK, cTypeOK, dTypeOK, MTypeOK, retTypeOK, Configs, Idems, ReturnSet, 
                       OpSet, ArgSet, UFId_StateSet, Q, I_F1, I_FR, I_U1, I_UR, I_Sk, I_SR, I_0,
                       I_U1Prime, I_URPrime, I_F1Prime, I_FRPrime, I_SkPrime, I_SRPrime, I_0Prime, NodeToIdFuncs
           <5> told.ret[p] = BOT /\ told.op[p] = "S" /\ told.arg[p] = <<c[p], d[p]>>
             BY <3>p, <3>q
           <5> QED
               BY <4>1, <1>0 DEF I_F1, I_FR, I_U1, I_UR, I_Sk, I_SR, I_0
         <4>2. CASE p # q
           <5> UNCHANGED <<pc[q], ret[q]>>
               BY <4>2 DEF TypeOK, PCTypeOK, retTypeOK
           <5> USE DEF QinM, TypeOK, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK,
                       i_vTypeOK, cTypeOK, dTypeOK, MTypeOK, retTypeOK, Configs, Idems, ReturnSet, 
                       OpSet, ArgSet, UFId_StateSet, Q, I_F1, I_FR, I_U1, I_UR, I_Sk, I_SR, I_0,
                       I_U1Prime, I_URPrime, I_F1Prime, I_FRPrime, I_SkPrime, I_SRPrime, I_0Prime, NodeToIdFuncs
           <5> QED
               BY <4>2, <1>0 DEF I_F1, I_FR, I_U1, I_UR, I_Sk, I_SR, I_0
                 
         <4> QED
            BY <4>1, <4>2
       <3>2. told \in M
         BY <3>1
       <3>i. t.ret[p] = ret'[p]
         BY <3>p, <2>1
       <3>j. ret'[p] = FALSE
         BY <2>1
       <3>3. t \in M'
         <4>0. t \in Configs
            OBVIOUS
         <4>1. told.ret[p] = BOT
            OBVIOUS
         <4>2. t.sigma = told.sigma
            OBVIOUS
         <4>x. t.ret[p] = FALSE
            BY <3>i, <3>j
         <4>y. t.ret = [told.ret EXCEPT ![p] = FALSE]
           BY <4>x
         <4>3. t.ret = [told.ret EXCEPT ![p] = IF told.sigma[told.arg[p][1]] = told.sigma[told.arg[p][2]] THEN TRUE ELSE FALSE]
            BY <4>y, <3>0
         <4>4. t.op = told.op
           OBVIOUS
         <4>5. t.arg = told.arg
           OBVIOUS
         <4> HIDE DEF TypeOK, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK,
                     i_vTypeOK, cTypeOK, dTypeOK, MTypeOK, retTypeOK, Configs, Idems, ReturnSet, 
                     OpSet, ArgSet, UFId_StateSet, Q, I_F1, I_FR, I_U1, I_UR, I_Sk, I_SR, I_0,
                     I_U1Prime, I_URPrime, I_F1Prime, I_FRPrime, I_SkPrime, I_SRPrime, I_0Prime, NodeToIdFuncs, told
         <4> USE DEF TypeOK, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK,
                     i_vTypeOK, cTypeOK, dTypeOK, MTypeOK, retTypeOK, ReturnSet, 
                     OpSet, ArgSet
         <4> M' = {s \in Configs: \E sold \in M: /\ sold.ret[p] = BOT
                                                 /\ s.ret = [sold.ret EXCEPT ![p] = IF sold.sigma[sold.arg[p][1]] = sold.sigma[sold.arg[p][2]] THEN TRUE ELSE FALSE]
                                                 /\ s.arg = sold.arg
                                                 /\ s.op = sold.op
                                                 /\ s.sigma = sold.sigma}
            BY <2>1 DEF S6
         <4> HIDE DEF S6
         <4> QED
           BY <4>1, <4>2, <4>3, <4>4, <4>5, <3>2, <4>0
       <3> QED
         BY <3>3
   <2>2. CASE ~(i_v[p] > i_u'[p] /\ i_u'[p] > 0)
       <3> USE <2>2
       <3>1. t \in Q
           <4> t \in Configs /\ UF.rep = t.sigma
              BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet, Decide
           <4> t.ret[p] = BOT
               OBVIOUS
           <4> SUFFICES ASSUME NEW q \in PROCESSES
                      PROVE /\ I_U1(t, q)
                            /\ I_UR(t, q)
                            /\ I_F1(t, q)
                            /\ I_FR(t, q)
                            /\ I_Sk(t, q)
                            /\ I_SR(t, q)
                            /\ I_0(t, q)
              BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet
           <4> QED
              OBVIOUS
       <3> QED
         BY <3>1
   <2> QED
     BY <2>1, <2>2
 <1>12. ASSUME NEW p \in PROCESSES, SR(p)
       PROVE t \in M'
   <2> USE <1>12 DEF SR
   <2> DEFINE told == [t EXCEPT !.ret = [t.ret EXCEPT ![p] = ret[p]],
                                !.op = [t.op EXCEPT ![p] = "S"],
                                !.arg = [t.arg EXCEPT ![p] = <<c[p], d[p]>>]]
   <2>1. told \in Q
     <3> told \in Configs /\ UF.rep = told.sigma
        BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet, Decide
     <3> SUFFICES ASSUME NEW q \in PROCESSES
                  PROVE /\ I_U1(told, q)
                        /\ I_UR(told, q)
                        /\ I_F1(told, q)
                        /\ I_FR(told, q)
                        /\ I_Sk(told, q)
                        /\ I_SR(told, q)
                        /\ I_0(told, q)
        BY DEF Q, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs, Configs, ArgSet, OpSet, ReturnSet
     <3>1. CASE p = q
         BY <3>1, <1>0                 
     <3>2. CASE p # q
       <4>1. I_U1(told, q)
         BY <3>2, <1>0
       <4>2. I_UR(told, q)
         BY <3>2, <1>0
       <4>3. I_F1(told, q)
         BY <3>2, <1>0
       <4>4. I_FR(told, q)
         BY <3>2, <1>0
       <4>5. I_Sk(told, q)
         BY <3>2, <1>0
       <4>6. I_SR(told, q)
         BY <3>2, <1>0
       <4>7. I_0(told, q)
         BY <3>2, <1>0
       <4>8. QED
         BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7
        
     <3> QED
        BY <3>1, <3>2
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
 <1>13. ASSUME UNCHANGED varlist
        PROVE t \in M'
   BY <1>13 DEF varlist
 <1> QED
   BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13 DEF Next, Step

LEMMA SpecMaintainsQinM == UFSSpec => []QinM
  BY InitQinM, NextQinM, PTL, SpecTypeOK, SpecMaintainsI1, SpecMaintainsI_IDs, SpecIDProperties DEF UFSSpec

THEOREM SpecLinearizable == UFSSpec => []Linearizable
  <1> SUFFICES ASSUME QNE, QinM
               PROVE Linearizable
    BY SpecMaintainsQNE, SpecMaintainsQinM, PTL
  <1> QED
    BY DEF QNE, QinM, Linearizable
    

LEMMA InitMAllEqual == Init => MAllEqual
    BY DEF Init, MAllEqual

LEMMA NextMAllEqual == MAllEqual /\ TypeOK /\ Linearizable /\ [Next]_varlist => MAllEqual'
  <1> SUFFICES ASSUME MAllEqual, TypeOK, Linearizable,
                      [Next]_varlist
               PROVE  MAllEqual'
    OBVIOUS
  <1>0. TypeOK'
    BY TypeOKNext, TypeOKUnchanged
  <1>1. ASSUME NEW p \in PROCESSES,
               F1(p)
        PROVE  MAllEqual'
    <2> PICK told \in M: \A sold \in M: sold = told
        BY DEF MAllEqual, Linearizable
    <2>1. \A t \in M': /\ t.sigma = told.sigma
                       /\ t.ret = [told.ret EXCEPT ![p] = told.sigma[told.arg[p]]]
                       /\ t.op = told.op
                       /\ t.arg = told.arg
        BY <1>1 DEF F1
    <2>2. M' \subseteq Configs
        BY <1>0 DEF TypeOK, Configs, MTypeOK
    <2> SUFFICES ASSUME NEW x \in M', NEW y \in M'
               PROVE  (x = y)
        BY DEF MAllEqual
    <2>3. x.arg = y.arg /\ x.op = y.op /\ x.ret = y.ret /\ x.sigma = y.sigma
        BY <2>1
    <2> QED
        BY <1>0, <2>3 DEF TypeOK, Configs, MTypeOK
  <1>2. ASSUME NEW p \in PROCESSES,
               FR(p)
        PROVE  MAllEqual'
    <2> PICK told \in M: \A sold \in M: sold = told
        BY DEF MAllEqual, Linearizable
    <2>1. \A t \in M': /\ t.sigma = told.sigma
                       /\ t.ret = [told.ret EXCEPT ![p] = BOT]
                       /\ t.op = [told.op EXCEPT ![p] = BOT]
                       /\ t.arg = [told.arg EXCEPT ![p] = BOT]
        BY <1>2 DEF FR
    <2>2. M' \subseteq Configs
        BY <1>0 DEF TypeOK, Configs, MTypeOK
    <2> SUFFICES ASSUME NEW x \in M', NEW y \in M'
               PROVE  (x = y)
        BY DEF MAllEqual
    <2>3. x.arg = y.arg /\ x.op = y.op /\ x.ret = y.ret /\ x.sigma = y.sigma
        BY <2>1
    <2> QED
        BY <1>0, <2>3 DEF TypeOK, Configs, MTypeOK
  <1>3. ASSUME NEW p \in PROCESSES,
               U1(p)
        PROVE  MAllEqual'
    <2> PICK told \in M: \A sold \in M: sold = told
        BY DEF MAllEqual, Linearizable
    <2>1. \A t \in M': /\ t.sigma = MetaConfigUnite(told.sigma, told.arg[p][1], told.arg[p][2])
                       /\ t.ret = [told.ret EXCEPT ![p] = ACK]
                       /\ t.op = told.op
                       /\ t.arg = told.arg
        BY <1>3 DEF U1
    <2>2. M' \subseteq Configs
        BY <1>0 DEF TypeOK, Configs, MTypeOK
    <2> SUFFICES ASSUME NEW x \in M', NEW y \in M'
               PROVE  (x = y)
        BY DEF MAllEqual
    <2>3. x.arg = y.arg /\ x.op = y.op /\ x.ret = y.ret /\ x.sigma = y.sigma
        BY <2>1
    <2> QED
        BY <1>0, <2>3 DEF TypeOK, Configs, MTypeOK
  <1>4. ASSUME NEW p \in PROCESSES,
               UR(p)
        PROVE  MAllEqual'
    <2> PICK told \in M: \A sold \in M: sold = told
        BY DEF MAllEqual, Linearizable
    <2>1. \A t \in M': /\ t.sigma = told.sigma
                       /\ t.ret = [told.ret EXCEPT ![p] = BOT]
                       /\ t.op = [told.op EXCEPT ![p] = BOT]
                       /\ t.arg = [told.arg EXCEPT ![p] = BOT]
        BY <1>4 DEF UR
    <2>2. M' \subseteq Configs
        BY <1>0 DEF TypeOK, Configs, MTypeOK
    <2> SUFFICES ASSUME NEW x \in M', NEW y \in M'
               PROVE  (x = y)
        BY DEF MAllEqual
    <2>3. x.arg = y.arg /\ x.op = y.op /\ x.ret = y.ret /\ x.sigma = y.sigma
        BY <2>1
    <2> QED
        BY <1>0, <2>3 DEF TypeOK, Configs, MTypeOK
  <1>5. ASSUME NEW p \in PROCESSES,
               S1(p)
        PROVE  MAllEqual'
    BY <1>5 DEF MAllEqual, S1
  <1>6. ASSUME NEW p \in PROCESSES,
               S2(p)
        PROVE  MAllEqual'
    BY <1>6 DEF MAllEqual, S2
  <1>7. ASSUME NEW p \in PROCESSES,
               S3(p)
        PROVE  MAllEqual'
    <2>1. CASE u[p] = v'[p]
        <3> PICK told \in M: \A sold \in M: sold = told
            BY DEF MAllEqual, Linearizable
        <3>1. \A t \in M': /\ t.sigma = told.sigma
                           /\ t.ret = [told.ret EXCEPT ![p] = IF told.sigma[told.arg[p][1]] = told.sigma[told.arg[p][2]] THEN TRUE ELSE FALSE]
                           /\ t.op = told.op
                           /\ t.arg = told.arg
            BY IsaT(10), <1>7, <2>1 DEF S3
        <3>2. M' \subseteq Configs
            BY <1>0 DEF TypeOK, Configs, MTypeOK
        <3> SUFFICES ASSUME NEW x \in M', NEW y \in M'
                   PROVE  (x = y)
            BY DEF MAllEqual
        <3>3. x.arg = y.arg /\ x.op = y.op /\ x.ret = y.ret /\ x.sigma = y.sigma
            BY <3>1
        <3> QED
            BY <1>0, <3>3 DEF TypeOK, Configs, MTypeOK

    <2>2. CASE u[p] # v'[p]
        BY <1>7, <2>2 DEF MAllEqual, S3
    <2> QED
        BY <2>1, <2>2
  <1>8. ASSUME NEW p \in PROCESSES,
               S4(p)
        PROVE  MAllEqual'
    <2>1. CASE i_u[p] > i_v'[p] /\ i_v'[p] > 0
        <3> PICK told \in M: \A sold \in M: sold = told
            BY DEF MAllEqual, Linearizable
        <3> M' = {t \in Configs: \E s \in M: 
                                /\ s.ret[p] = BOT
                                /\ t.sigma = s.sigma
                                /\ t.ret = [s.ret EXCEPT ![p] = IF s.sigma[s.arg[p][1]] = s.sigma[s.arg[p][2]] THEN TRUE ELSE FALSE]
                                /\ t.op  = s.op
                                /\ t.arg = s.arg
                                /\ s = told}
            BY <1>8, <2>1 DEF S4            
        <3>1. \A t \in M': /\ t.sigma = told.sigma
                           /\ t.ret = [told.ret EXCEPT ![p] = IF told.sigma[told.arg[p][1]] = told.sigma[told.arg[p][2]] THEN TRUE ELSE FALSE]
                           /\ t.op = told.op
                           /\ t.arg = told.arg
            OBVIOUS       
        <3>2. M' \subseteq Configs
            BY <1>0 DEF TypeOK, Configs, MTypeOK
        <3> SUFFICES ASSUME NEW x \in M', NEW y \in M'
                   PROVE  (x = y)
            BY DEF MAllEqual
        <3>3. x.arg = y.arg /\ x.op = y.op /\ x.ret = y.ret /\ x.sigma = y.sigma
            BY <3>1
        <3> QED
            BY <1>0, <3>3 DEF TypeOK, Configs, MTypeOK

    <2>2. CASE ~(i_u[p] > i_v'[p] /\ i_v'[p] > 0)
        BY <1>8, <2>2 DEF MAllEqual, S4
    <2> QED
        BY <2>1, <2>2
  <1>9. ASSUME NEW p \in PROCESSES,
               S5(p)
        PROVE  MAllEqual'
    <2>1. CASE v[p] = u'[p]
        <3> PICK told \in M: \A sold \in M: sold = told
            BY DEF MAllEqual, Linearizable
        <3>1. \A t \in M': /\ t.sigma = told.sigma
                           /\ t.ret = [told.ret EXCEPT ![p] = IF told.sigma[told.arg[p][1]] = told.sigma[told.arg[p][2]] THEN TRUE ELSE FALSE]
                           /\ t.op = told.op
                           /\ t.arg = told.arg
            BY IsaT(10), <1>9, <2>1 DEF S5
        <3>2. M' \subseteq Configs
            BY <1>0 DEF TypeOK, Configs, MTypeOK
        <3> SUFFICES ASSUME NEW x \in M', NEW y \in M'
                   PROVE  (x = y)
            BY DEF MAllEqual
        <3>3. x.arg = y.arg /\ x.op = y.op /\ x.ret = y.ret /\ x.sigma = y.sigma
            BY <3>1
        <3> QED
            BY <1>0, <3>3 DEF TypeOK, Configs, MTypeOK

    <2>2. CASE v[p] # u'[p]
        BY <1>9, <2>2 DEF MAllEqual, S5
    <2> QED
        BY <2>1, <2>2
  <1>10. ASSUME NEW p \in PROCESSES,
                S6(p)
         PROVE  MAllEqual'
    <2>1. CASE i_v[p] > i_u'[p] /\ i_u'[p] > 0
        <3> PICK told \in M: \A sold \in M: sold = told
            BY DEF MAllEqual, Linearizable
        <3> M' = {t \in Configs: \E s \in M: 
                                /\ s.ret[p] = BOT
                                /\ t.sigma = s.sigma
                                /\ t.ret = [s.ret EXCEPT ![p] = IF s.sigma[s.arg[p][1]] = s.sigma[s.arg[p][2]] THEN TRUE ELSE FALSE]
                                /\ t.op  = s.op
                                /\ t.arg = s.arg
                                /\ s = told}
            BY <1>10, <2>1 DEF S6        
        <3>1. \A t \in M': /\ t.sigma = told.sigma
                           /\ t.ret = [told.ret EXCEPT ![p] = IF told.sigma[told.arg[p][1]] = told.sigma[told.arg[p][2]] THEN TRUE ELSE FALSE]
                           /\ t.op = told.op
                           /\ t.arg = told.arg
            OBVIOUS       
        <3>2. M' \subseteq Configs
            BY <1>0 DEF TypeOK, Configs, MTypeOK
        <3> SUFFICES ASSUME NEW x \in M', NEW y \in M'
                   PROVE  (x = y)
            BY DEF MAllEqual
        <3>3. x.arg = y.arg /\ x.op = y.op /\ x.ret = y.ret /\ x.sigma = y.sigma
            BY <3>1
        <3> QED
            BY <1>0, <3>3 DEF TypeOK, Configs, MTypeOK
    <2>2. CASE ~(i_v[p] > i_u'[p] /\ i_u'[p] > 0)
        BY <1>10, <2>2 DEF MAllEqual, S6
    <2> QED
        BY <2>1, <2>2
  <1>11. ASSUME NEW p \in PROCESSES,
                SR(p)
         PROVE  MAllEqual'
    <2> PICK told \in M: \A sold \in M: sold = told
        BY DEF MAllEqual, Linearizable
    <2>1. \A t \in M': /\ t.sigma = told.sigma
                       /\ t.ret = [told.ret EXCEPT ![p] = BOT]
                       /\ t.op = [told.op EXCEPT ![p] = BOT]
                       /\ t.arg = [told.arg EXCEPT ![p] = BOT]
        BY <1>11 DEF SR
    <2>2. M' \subseteq Configs
        BY <1>0 DEF TypeOK, Configs, MTypeOK
    <2> SUFFICES ASSUME NEW x \in M', NEW y \in M'
               PROVE  (x = y)
        BY DEF MAllEqual
    <2>3. x.arg = y.arg /\ x.op = y.op /\ x.ret = y.ret /\ x.sigma = y.sigma
        BY <2>1
    <2> QED
        BY <1>0, <2>1 DEF TypeOK, Configs, MTypeOK
  <1>12. ASSUME NEW p \in PROCESSES,
                Decide(p)
         PROVE  MAllEqual'
     <2>0. \/ /\ pc' = [pc EXCEPT ![p] = "F1"]
              /\ M' = {t \in Configs: \E told \in M:    /\ told.ret[p] = BOT
                                                        /\ told.op[p] = BOT
                                                        /\ told.arg[p] = BOT
                                                        /\ t.sigma = told.sigma
                                                        /\ t.op = [told.op EXCEPT ![p] = "F"]
                                                        /\ t.arg = [told.arg EXCEPT ![p] = c'[p]]
                                                        /\ t.ret = told.ret}
           \/ /\ pc' = [pc EXCEPT ![p] = "U1"]
              /\ M' = {t \in Configs: \E told \in M:    /\ told.ret[p] = BOT
                                                        /\ told.op[p] = BOT
                                                        /\ told.arg[p] = BOT
                                                        /\ t.sigma = told.sigma
                                                        /\ t.op = [told.op EXCEPT ![p] = "U"]
                                                        /\ t.arg = [told.arg EXCEPT ![p] = <<c'[p], d'[p]>>]
                                                        /\ t.ret = told.ret}
           \/ /\ pc' = [pc EXCEPT ![p] = "S1"]
              /\ M' = {t \in Configs: \E told \in M:    /\ told.ret[p] = BOT
                                                        /\ told.op[p] = BOT
                                                        /\ told.arg[p] = BOT
                                                        /\ t.sigma = told.sigma
                                                        /\ t.op = [told.op EXCEPT ![p] = "S"]
                                                        /\ t.arg = [told.arg EXCEPT ![p] = <<c'[p], d'[p]>>]
                                                        /\ t.ret = told.ret}
        BY <1>12 DEF Decide       
     <2>1. CASE /\ pc' = [pc EXCEPT ![p] = "F1"]
                /\ M' = {t \in Configs: \E told \in M:  /\ told.ret[p] = BOT
                                                        /\ told.op[p] = BOT
                                                        /\ told.arg[p] = BOT
                                                        /\ t.sigma = told.sigma
                                                        /\ t.op = [told.op EXCEPT ![p] = "F"]
                                                        /\ t.arg = [told.arg EXCEPT ![p] = c'[p]]
                                                        /\ t.ret = told.ret}
        <3> PICK told \in M: \A sold \in M: sold = told
            BY DEF MAllEqual, Linearizable
        <3>1. M' \subseteq Configs
            BY <1>0 DEF TypeOK, Configs, MTypeOK
        <3> SUFFICES ASSUME NEW x \in M', NEW y \in M'
                   PROVE  (x = y)
            BY DEF MAllEqual
        <3> x \in Configs /\ y \in Configs
            BY <3>1
        <3>a. \E s \in M: /\ s.ret[p] = BOT
                        /\ s.op[p] = BOT
                        /\ s.arg[p] = BOT
                        /\ x.sigma = s.sigma
                        /\ x.op = [s.op EXCEPT ![p] = "F"]
                        /\ x.arg = [s.arg EXCEPT ![p] = c'[p]]
                        /\ x.ret = s.ret
                        /\ s = told
            BY <2>1
        <3>b. \E s \in M: /\ s.ret[p] = BOT
                        /\ s.op[p] = BOT
                        /\ s.arg[p] = BOT
                        /\ y.sigma = s.sigma
                        /\ y.op = [s.op EXCEPT ![p] = "F"]
                        /\ y.arg = [s.arg EXCEPT ![p] = c'[p]]
                        /\ y.ret = s.ret
                        /\ s = told
            BY <2>1
        <3>3. x.arg = y.arg /\ x.op = y.op /\ x.ret = y.ret /\ x.sigma = y.sigma
            BY <3>a, <3>b
        <3> QED
            BY <1>0, <3>3 DEF TypeOK, Configs, MTypeOK
     <2>2. CASE /\ pc' = [pc EXCEPT ![p] = "U1"]
                /\ M' = {t \in Configs: \E told \in M:  /\ told.ret[p] = BOT
                                                        /\ told.op[p] = BOT
                                                        /\ told.arg[p] = BOT
                                                        /\ t.sigma = told.sigma
                                                        /\ t.op = [told.op EXCEPT ![p] = "U"]
                                                        /\ t.arg = [told.arg EXCEPT ![p] = <<c'[p], d'[p]>>]
                                                        /\ t.ret = told.ret}
        <3> PICK told \in M: \A sold \in M: sold = told
            BY DEF MAllEqual, Linearizable
        <3>1. M' \subseteq Configs
            BY <1>0 DEF TypeOK, Configs, MTypeOK
        <3> SUFFICES ASSUME NEW x \in M', NEW y \in M'
                   PROVE  (x = y)
            BY DEF MAllEqual
        <3> x \in Configs /\ y \in Configs
            BY <3>1
        <3>a. \E s \in M: /\ s.ret[p] = BOT
                        /\ s.op[p] = BOT
                        /\ s.arg[p] = BOT
                        /\ x.sigma = s.sigma
                        /\ x.op = [s.op EXCEPT ![p] = "U"]
                        /\ x.arg = [s.arg EXCEPT ![p] = <<c'[p], d'[p]>>]
                        /\ x.ret = s.ret
                        /\ s = told
            BY <2>2
        <3>b. \E s \in M: /\ s.ret[p] = BOT
                        /\ s.op[p] = BOT
                        /\ s.arg[p] = BOT
                        /\ y.sigma = s.sigma
                        /\ y.op = [s.op EXCEPT ![p] = "U"]
                        /\ y.arg = [s.arg EXCEPT ![p] = <<c'[p], d'[p]>>]
                        /\ y.ret = s.ret
                        /\ s = told
            BY <2>2
        <3>3. x.arg = y.arg /\ x.op = y.op /\ x.ret = y.ret /\ x.sigma = y.sigma
            BY <3>a, <3>b
        <3> QED
            BY <1>0, <3>3 DEF TypeOK, Configs, MTypeOK
     <2>3. CASE /\ pc' = [pc EXCEPT ![p] = "S1"]
                /\ M' = {t \in Configs: \E told \in M:  /\ told.ret[p] = BOT
                                                        /\ told.op[p] = BOT
                                                        /\ told.arg[p] = BOT
                                                        /\ t.sigma = told.sigma
                                                        /\ t.op = [told.op EXCEPT ![p] = "S"]
                                                        /\ t.arg = [told.arg EXCEPT ![p] = <<c'[p], d'[p]>>]
                                                        /\ t.ret = told.ret}
        <3> PICK told \in M: \A sold \in M: sold = told
            BY DEF MAllEqual, Linearizable
        <3>1. M' \subseteq Configs
            BY <1>0 DEF TypeOK, Configs, MTypeOK
        <3> SUFFICES ASSUME NEW x \in M', NEW y \in M'
                   PROVE  (x = y)
            BY DEF MAllEqual
        <3> x \in Configs /\ y \in Configs
            BY <3>1
        <3>a. \E s \in M: /\ s.ret[p] = BOT
                        /\ s.op[p] = BOT
                        /\ s.arg[p] = BOT
                        /\ x.sigma = s.sigma
                        /\ x.op = [s.op EXCEPT ![p] = "S"]
                        /\ x.arg = [s.arg EXCEPT ![p] = <<c'[p], d'[p]>>]
                        /\ x.ret = s.ret
                        /\ s = told
            BY <2>3
        <3>b. \E s \in M: /\ s.ret[p] = BOT
                        /\ s.op[p] = BOT
                        /\ s.arg[p] = BOT
                        /\ y.sigma = s.sigma
                        /\ y.op = [s.op EXCEPT ![p] = "S"]
                        /\ y.arg = [s.arg EXCEPT ![p] = <<c'[p], d'[p]>>]
                        /\ y.ret = s.ret
                        /\ s = told
            BY <2>3
        <3>3. x.arg = y.arg /\ x.op = y.op /\ x.ret = y.ret /\ x.sigma = y.sigma
            BY <3>a, <3>b
        <3> QED
            BY <1>0, <3>3 DEF TypeOK, Configs, MTypeOK
    <2> QED
        BY <2>1, <2>2, <2>3, <2>0
  <1>13. CASE UNCHANGED varlist
    BY <1>13 DEF varlist, MAllEqual
  <1>14. QED
    BY <1>1, <1>10, <1>11, <1>12, <1>13, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF Next, Step

LEMMA SpecMaintainsMAllEqual == UFSSpec =>[](MAllEqual) 
  BY InitMAllEqual, NextMAllEqual, PTL, SpecTypeOK, SpecLinearizable DEF UFSSpec






=============================================================================
\* Modification History
\* Last modified Sat Feb 14 05:19:58 EST 2026 by karunram
\* Created Tue Feb 10 16:44:37 EST 2026 by karunram
