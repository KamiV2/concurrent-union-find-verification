-------------------------- MODULE UFSIDProperties --------------------------

EXTENDS UFSImplementation, UFSTypeOK, TLAPS

IDUniqueness == \A x, y \in NodeSet: (UF.id[x] = UF.id[y] /\ UF.id[x] > 0) => x = y
RootsHaveIDs == \A x \in NodeSet: UF.rep[x] = x => UF.id[x] # 0 

LEMMA InitIDInvs == Init => IDUniqueness /\ RootsHaveIDs
  <1> SUFFICES ASSUME Init
               PROVE  IDUniqueness /\ RootsHaveIDs
    OBVIOUS
  <1> \A x \in NodeSet: UF.rep[x] = x
    BY TypeOKInit DEF Init, InitUF, TypeOK, UFTypeOK, Idems, NodeToIdFuncs
  <1> \A x, y \in NodeSet: UF.id[x] = UF.id[y] => x = y
    BY TypeOKInit, InitUFIdFuncExists DEF Init, InitUF, TypeOK, UFTypeOK, Idems, NodeToIdFuncs
  <1> \A x \in NodeSet: UF.id[x] > 0
    <2> SUFFICES ASSUME NEW x \in NodeSet
                 PROVE  UF.id[x] > 0
      OBVIOUS
    <2> UF.id \in [NodeSet -> Nat \ {0}]
      BY TypeOKInit, InitUFIdFuncExists DEF Init, InitUF, TypeOK
    <2> UF.id[x] # 0 /\ UF.id[x] \in Nat
      OBVIOUS
    <2> QED
      OBVIOUS
  <1> QED
    BY DEF IDUniqueness, InitUF, RootsHaveIDs, NodeSet

LEMMA NextIDInvs == IDUniqueness /\ RootsHaveIDs /\ TypeOK /\ [Next]_varlist => IDUniqueness' /\ RootsHaveIDs'
  <1> SUFFICES ASSUME IDUniqueness,
                      RootsHaveIDs,
                      TypeOK,
                      [Next]_varlist
               PROVE  IDUniqueness' /\ RootsHaveIDs'
    BY DEF Next
  <1>1. ASSUME NEW p \in PROCESSES, F1(p)
        PROVE  IDUniqueness' /\ RootsHaveIDs'
    BY <1>1 DEF IDUniqueness, F1, RootsHaveIDs
  <1>2. ASSUME NEW p \in PROCESSES, FR(p)
        PROVE  IDUniqueness' /\ RootsHaveIDs'
    BY <1>2 DEF IDUniqueness, FR, RootsHaveIDs
  <1>3. ASSUME NEW p \in PROCESSES, U1(p)
        PROVE  IDUniqueness' /\ RootsHaveIDs'
    <2> c[p] \in NodeSet /\ d[p] \in NodeSet
        BY DEF TypeOK, cTypeOK, dTypeOK
    <2> UF'.id = UF.id
        BY <1>3 DEF U1, UFUnite
    <2>1. CASE UF.id[UF.rep[c[p]]] >= UF.id[UF.rep[d[p]]]
        <3> SmallerRep(UF.rep, c[p], d[p]) = UF.rep[d[p]]
            BY <2>1 DEF SmallerRep, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs
        <3> LargerRep(UF.rep, c[p], d[p]) = UF.rep[c[p]]
            BY <2>1 DEF LargerRep, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs
        <3> UF'.rep = [i \in NodeSet |-> IF UF.rep[i] = UF.rep[d[p]] THEN UF.rep[c[p]] ELSE UF.rep[i]]
            BY <1>3 DEF U1, UFUnite, URep
        <3> \A x \in NodeSet: UF'.rep[x] = x => UF.rep[x] = x
            BY DEF TypeOK, UFTypeOK, UFId_StateSet, Idems
        <3> QED
            BY DEF IDUniqueness, RootsHaveIDs
    <2>2. CASE UF.id[UF.rep[c[p]]] < UF.id[UF.rep[d[p]]]
        <3> SmallerRep(UF.rep, c[p], d[p]) = UF.rep[c[p]]
            BY <2>2 DEF SmallerRep, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs
        <3> LargerRep(UF.rep, c[p], d[p]) = UF.rep[d[p]]
            BY <2>2 DEF LargerRep, TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs
        <3> UF'.rep = [i \in NodeSet |-> IF UF.rep[i] = UF.rep[c[p]] THEN UF.rep[d[p]] ELSE UF.rep[i]]
            BY <1>3 DEF U1, UFUnite, URep
        <3> \A x \in NodeSet: UF'.rep[x] = x => UF.rep[x] = x
            BY DEF TypeOK, UFTypeOK, UFId_StateSet, Idems
        <3> QED
            BY DEF IDUniqueness, RootsHaveIDs
    <2> QED
        BY <2>1, <2>2 DEF TypeOK, UFTypeOK, UFId_StateSet, Idems, NodeToIdFuncs

  <1>4. ASSUME NEW p \in PROCESSES, UR(p)
        PROVE  IDUniqueness' /\ RootsHaveIDs'
    BY <1>4 DEF IDUniqueness, UR, RootsHaveIDs
  <1>5. ASSUME NEW p \in PROCESSES, S1(p)
        PROVE  IDUniqueness' /\ RootsHaveIDs'
    BY <1>5 DEF IDUniqueness, S1, RootsHaveIDs
  <1>6. ASSUME NEW p \in PROCESSES, S2(p)
        PROVE  IDUniqueness' /\ RootsHaveIDs'
    <2> u[p] \in NodeSet
        BY DEF TypeOK, uTypeOK 
    <2> PICK newId \in IDUpdate(u[p]): UF' = [rep |-> UF.rep, id |-> newId]
        BY <1>6 DEF S2
    <2> \A x \in NodeSet: x # u[p] => UF.id[x] = newId[x]
        BY DEF IDUpdate, TypeOK, UFTypeOK, NodeToIdFuncs, UFId_StateSet
    <2>1. CASE UF.rep[u[p]] = u[p]
        <3> newId[u[p]] > 0
            BY <2>1 DEF IDUpdate, TypeOK, UFTypeOK, NodeToIdFuncs, UFId_StateSet, CandID, RootsHaveIDs
        <3> \A x \in NodeSet: newId[x] = newId[u[p]] => x = u[p]
            BY <2>1 DEF IDUpdate, TypeOK, UFTypeOK, NodeToIdFuncs, UFId_StateSet, CandID, IDUniqueness
        <3> QED
            BY <2>1 DEF IDUniqueness, RootsHaveIDs, TypeOK, UFTypeOK, UFId_StateSet, Idems
    <2>2. CASE UF.rep[u[p]] # u[p]
        <3> newId[u[p]] = 0
            BY <2>2 DEF IDUpdate, TypeOK, UFTypeOK, NodeToIdFuncs, UFId_StateSet, CandID, RootsHaveIDs
        <3> QED
            BY <2>2 DEF IDUniqueness, RootsHaveIDs
    <2> QED
        BY <2>1, <2>2        
\*    BY <1>6 DEF IDUniqueness, S2, RootsHaveIDs
  <1>7. ASSUME NEW p \in PROCESSES, S3(p)
        PROVE  IDUniqueness' /\ RootsHaveIDs'
    BY <1>7 DEF IDUniqueness, S3, RootsHaveIDs
  <1>8. ASSUME NEW p \in PROCESSES, S4(p)    
        PROVE  IDUniqueness' /\ RootsHaveIDs'  
    <2> v[p] \in NodeSet
        BY DEF TypeOK, vTypeOK 
    <2> PICK newId \in IDUpdate(v[p]): UF' = [rep |-> UF.rep, id |-> newId]
        BY <1>8 DEF S4
    <2> \A x \in NodeSet: x # v[p] => UF.id[x] = newId[x]
        BY DEF IDUpdate, TypeOK, UFTypeOK, NodeToIdFuncs, UFId_StateSet
    <2>1. CASE UF.rep[v[p]] = v[p]
        <3> newId[v[p]] > 0
            BY <2>1 DEF IDUpdate, TypeOK, UFTypeOK, NodeToIdFuncs, UFId_StateSet, CandID, RootsHaveIDs
        <3> \A x \in NodeSet: newId[x] = newId[v[p]] => x = v[p]
            BY <2>1 DEF IDUpdate, TypeOK, UFTypeOK, NodeToIdFuncs, UFId_StateSet, CandID, IDUniqueness
        <3> QED
            BY <2>1 DEF IDUniqueness, RootsHaveIDs, TypeOK, UFTypeOK, UFId_StateSet, Idems
    <2>2. CASE UF.rep[v[p]] # v[p]
        <3> newId[v[p]] = 0
            BY <2>2 DEF IDUpdate, TypeOK, UFTypeOK, NodeToIdFuncs, UFId_StateSet, CandID, RootsHaveIDs
        <3> QED
            BY <2>2 DEF IDUniqueness, RootsHaveIDs
    <2> QED
        BY <2>1, <2>2        
  <1>9. ASSUME NEW p \in PROCESSES, S5(p)
        PROVE  IDUniqueness' /\ RootsHaveIDs'
    BY <1>9 DEF IDUniqueness, S5, RootsHaveIDs
  <1>10. ASSUME NEW p \in PROCESSES, S6(p)
         PROVE  IDUniqueness' /\ RootsHaveIDs'
    <2> u[p] \in NodeSet
        BY DEF TypeOK, uTypeOK 
    <2> PICK newId \in IDUpdate(u[p]): UF' = [rep |-> UF.rep, id |-> newId]
        BY <1>10 DEF S6
    <2> \A x \in NodeSet: x # u[p] => UF.id[x] = newId[x]
        BY DEF IDUpdate, TypeOK, UFTypeOK, NodeToIdFuncs, UFId_StateSet
    <2>1. CASE UF.rep[u[p]] = u[p]
        <3> newId[u[p]] > 0
            BY <2>1 DEF IDUpdate, TypeOK, UFTypeOK, NodeToIdFuncs, UFId_StateSet, CandID, RootsHaveIDs
        <3> \A x \in NodeSet: newId[x] = newId[u[p]] => x = u[p]
            BY <2>1 DEF IDUpdate, TypeOK, UFTypeOK, NodeToIdFuncs, UFId_StateSet, CandID, IDUniqueness
        <3> QED
            BY <2>1 DEF IDUniqueness, RootsHaveIDs, TypeOK, UFTypeOK, UFId_StateSet, Idems
    <2>2. CASE UF.rep[u[p]] # u[p]
        <3> newId[u[p]] = 0
            BY <2>2 DEF IDUpdate, TypeOK, UFTypeOK, NodeToIdFuncs, UFId_StateSet, CandID, RootsHaveIDs
        <3> QED
            BY <2>2 DEF IDUniqueness, RootsHaveIDs
    <2> QED
        BY <2>1, <2>2        
  <1>11. ASSUME NEW p \in PROCESSES, SR(p)
         PROVE  IDUniqueness' /\ RootsHaveIDs'
    BY <1>11 DEF IDUniqueness, SR, RootsHaveIDs
  <1>12. ASSUME NEW p \in PROCESSES, Decide(p)
         PROVE  IDUniqueness' /\ RootsHaveIDs'
    BY <1>12 DEF IDUniqueness, Decide, RootsHaveIDs
  <1>13. CASE UNCHANGED varlist
    BY <1>13 DEF varlist, IDUniqueness, RootsHaveIDs
  <1>14. QED
    BY <1>1, <1>10, <1>11, <1>12, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>13 DEF Next, Step

THEOREM SpecIDProperties == UFSSpec => [](IDUniqueness /\ RootsHaveIDs)
    BY InitIDInvs, NextIDInvs, PTL, SpecTypeOK DEF UFSSpec

=============================================================================
\* Modification History
\* Last modified Fri Feb 13 23:26:21 EST 2026 by karunram
\* Created Wed Feb 11 23:27:23 EST 2026 by karunram
