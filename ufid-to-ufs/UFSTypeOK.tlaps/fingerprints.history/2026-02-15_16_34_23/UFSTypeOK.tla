------------------------------ MODULE UFSTypeOK -----------------------------

EXTENDS UFSImplementation, TLAPS

PCTypeOK == pc \in [PROCESSES -> {"0", "F1", "FR", "U1", "UR", "S1", "S2", "S3", "S4", "S5", "S6", "SR"}]

UFTypeOK == UF \in UFId_StateSet

uTypeOK == u \in [PROCESSES -> NodeSet]

vTypeOK == v \in [PROCESSES -> NodeSet]

i_uTypeOK == i_u \in [PROCESSES -> Nat \cup {0}]

i_vTypeOK == i_v \in [PROCESSES -> Nat \cup {0}]

cTypeOK == c \in [PROCESSES -> NodeSet]

dTypeOK == d \in [PROCESSES -> NodeSet]

retTypeOK == ret \in [PROCESSES -> {ACK, TRUE, FALSE, BOT} \cup NodeSet]

MTypeOK == M \subseteq Configs

TypeOK ==
        /\ PCTypeOK
        /\ UFTypeOK
        /\ uTypeOK
        /\ vTypeOK
        /\ i_uTypeOK
        /\ i_vTypeOK
        /\ cTypeOK
        /\ dTypeOK
        /\ retTypeOK
        /\ MTypeOK

LEMMA InitUFIdFuncExists == \E f \in [NodeSet -> Nat \ {0}] : \A i, j \in NodeSet: f[i] = f[j] => i = j
    <1> DEFINE id_func == [i \in NodeSet |-> i]
    <1> id_func \in [NodeSet -> Nat \ {0}]
        BY DEF NodeSet
    <1> \A i, j \in NodeSet: id_func[i] = id_func[j] => i = j
        BY DEF NodeSet
    <1> QED
        OBVIOUS

THEOREM TypeOKInit == Init => TypeOK
    <1> SUFFICES ASSUME Init PROVE TypeOK
        OBVIOUS
    <1> USE DEF Init, TypeOK
    <1>0. InitUF.id \in NodeToIdFuncs
        BY InitUFIdFuncExists DEF InitUF, UFId_StateSet, NodeSet, Idems, NodeToIdFuncs
    <1>1. UF \in UFId_StateSet
        BY <1>0 DEF InitUF, UFId_StateSet, NodeSet, Idems, NodeToIdFuncs
    <1>2. M \subseteq Configs
        BY DEF InitState, InitRet, InitOp, InitArg, Configs, OpSet, ArgSet, ReturnSet, NodeSet, Idems
    <1> QED
        BY <1>1, <1>2 DEF PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK, cTypeOK, dTypeOK, retTypeOK, MTypeOK
    
THEOREM TypeOKNext == TypeOK /\ Next => TypeOK'
  <1> SUFFICES ASSUME TypeOK,
                      NEW p \in PROCESSES,
                      Step(p)
               PROVE  TypeOK'
    BY DEF Next
  <1>1. CASE F1(p)
    <2> M' \subseteq Configs
        BY <1>1 DEF F1, Configs, TypeOK, ReturnSet
    <2> ret' \in [PROCESSES -> {ACK, BOT, TRUE, FALSE} \cup NodeSet]
        BY <1>1 DEF UFTypeOK, UFId_StateSet, cTypeOK, Idems, TypeOK, F1, retTypeOK
    <2> QED
        BY <1>1 DEF F1, TypeOK, Configs, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK, cTypeOK, dTypeOK, retTypeOK, MTypeOK
  <1>2. CASE FR(p)
    <2> M' \subseteq Configs
        BY <1>2 DEF FR, Configs, TypeOK, ReturnSet
    <2> QED
        BY <1>2 DEF FR, TypeOK, Configs, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK, cTypeOK, dTypeOK, retTypeOK, MTypeOK
  <1>3. CASE U1(p)
    <2> M' \subseteq Configs
        BY <1>3 DEF U1, Configs, TypeOK, ReturnSet
    <2> UF' \in UFId_StateSet
        BY <1>3 DEF U1, TypeOK, UFUnite, UFTypeOK, UFId_StateSet, Idems, URep, SmallerRep, LargerRep
    <2> QED
        BY <1>3 DEF U1, TypeOK, Configs, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK, cTypeOK, dTypeOK, retTypeOK, MTypeOK
  <1>4. CASE UR(p)
    <2> M' \subseteq Configs
        BY <1>4 DEF UR, Configs, TypeOK, ReturnSet
    <2> QED
        BY <1>4 DEF UR, TypeOK, Configs, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK, cTypeOK, dTypeOK, retTypeOK, MTypeOK
  <1>5. CASE S1(p)
    <2> u' \in [PROCESSES -> NodeSet]
        BY <1>5 DEF S1, TypeOK, UFTypeOK, UFId_StateSet, Idems, cTypeOK, uTypeOK
    <2> QED
        BY <1>5 DEF S1, TypeOK, Configs, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK, cTypeOK, dTypeOK, retTypeOK, MTypeOK
  <1>6. CASE S2(p)
    <2> i_u' \in [PROCESSES -> Nat \cup {0}]
        BY <1>6 DEF S2, TypeOK, UFTypeOK, UFId_StateSet, uTypeOK, i_uTypeOK, NodeToIdFuncs
    <2> CandID(u[p]) \subseteq Nat \cup {0}
        BY <1>6 DEF CandID, TypeOK, vTypeOK, UFTypeOK, UFId_StateSet, CandID, NodeToIdFuncs
    <2>a. UF'.id \in NodeToIdFuncs
        BY <1>6 DEF S2, TypeOK, vTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, IDUpdate
    <2> UF' \in UFId_StateSet
        BY <2>a, <1>6 DEF S2, TypeOK, UFTypeOK, UFId_StateSet, Idems
    <2> QED
        BY <1>6 DEF S2, TypeOK, Configs, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK, cTypeOK, dTypeOK, retTypeOK, MTypeOK
  <1>7. CASE S3(p)
    <2> v' \in [PROCESSES -> NodeSet]
        BY <1>7 DEF S3, TypeOK, UFTypeOK, UFId_StateSet, Idems, vTypeOK
    <2> QED
        BY <1>7 DEF S3, TypeOK, Configs, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK, cTypeOK, dTypeOK, retTypeOK, MTypeOK
  <1>8. CASE S4(p)
    <2> i_v' \in [PROCESSES -> Nat \cup {0}]
        BY <1>8 DEF S4, TypeOK, UFTypeOK, UFId_StateSet, vTypeOK, i_vTypeOK, NodeToIdFuncs
    <2> M' \subseteq Configs
        BY <1>8 DEF S4, Configs, TypeOK, ReturnSet, OpSet, ArgSet, MTypeOK
    <2> CandID(v[p]) \subseteq Nat \cup {0}
        BY <1>8 DEF CandID, TypeOK, vTypeOK, UFTypeOK, UFId_StateSet, CandID, NodeToIdFuncs
    <2>a. UF'.id \in NodeToIdFuncs
        BY <1>8 DEF S4, TypeOK, vTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, IDUpdate
    <2> UF' \in UFId_StateSet
        BY <2>a, <1>8 DEF S4, TypeOK, UFTypeOK, UFId_StateSet, Idems
    <2> retTypeOK'
        BY <1>8 DEF S4, TypeOK, retTypeOK
    <2> QED
        BY <1>8 DEF S4, TypeOK, Configs, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK, cTypeOK, dTypeOK, retTypeOK, MTypeOK
        
  <1>9. CASE S5(p)
    <2> u' \in [PROCESSES -> NodeSet]
        BY <1>9 DEF S5, TypeOK, UFTypeOK, UFId_StateSet, Idems, uTypeOK
    <2> QED
        BY <1>9 DEF S5, TypeOK, Configs, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK, cTypeOK, dTypeOK, retTypeOK, MTypeOK
  <1>10. CASE S6(p)
    <2> i_u' \in [PROCESSES -> Nat \cup {0}]
        BY <1>10 DEF S6, TypeOK, UFTypeOK, UFId_StateSet, uTypeOK, i_uTypeOK, NodeToIdFuncs
    <2> M' \subseteq Configs
        BY <1>10 DEF S6, Configs, TypeOK, ReturnSet, OpSet, ArgSet, MTypeOK
    <2> CandID(u[p]) \subseteq Nat \cup {0}
        BY <1>10 DEF CandID, TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, CandID, NodeToIdFuncs
    <2>a. UF'.id \in NodeToIdFuncs
        BY <1>10 DEF S6, TypeOK, uTypeOK, UFTypeOK, UFId_StateSet, NodeToIdFuncs, IDUpdate
    <2> UF' \in UFId_StateSet
        BY <2>a, <1>10 DEF S6, TypeOK, UFTypeOK, UFId_StateSet, Idems
    <2> retTypeOK'
        BY <1>10 DEF S6, TypeOK, retTypeOK
    <2> QED
        BY <1>10 DEF S6, TypeOK, Configs, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK, cTypeOK, dTypeOK, retTypeOK, MTypeOK
  <1>11. CASE SR(p)
    <2> M' \subseteq Configs
        BY <1>11 DEF SR, Configs, TypeOK, ReturnSet
    <2> QED
        BY <1>11 DEF SR, TypeOK, Configs, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK, cTypeOK, dTypeOK, retTypeOK, MTypeOK
  <1>12. CASE Decide(p)
    <2> M' \subseteq Configs
        BY <1>12 DEF Decide, Configs, TypeOK, ReturnSet, MTypeOK, OpSet, ArgSet, ReturnSet
    <2> QED
        BY <1>12 DEF Decide, TypeOK, Configs, PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK, cTypeOK, dTypeOK, retTypeOK, MTypeOK
  <1>14. QED
    BY <1>1, <1>10, <1>11, <1>12, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12 DEF Step

THEOREM TypeOKUnchanged == TypeOK /\ UNCHANGED varlist => TypeOK'
  <1> SUFFICES ASSUME TypeOK, UNCHANGED varlist
               PROVE  TypeOK'
                OBVIOUS
    <1> USE DEF TypeOK, varlist
    <1> QED
        BY DEF PCTypeOK, UFTypeOK, uTypeOK, vTypeOK, i_uTypeOK, i_vTypeOK, cTypeOK, dTypeOK, retTypeOK, MTypeOK

THEOREM SpecTypeOK == UFSSpec => []TypeOK
    BY TypeOKInit, TypeOKNext, TypeOKUnchanged, PTL DEF UFSSpec

=============================================================================
\* Modification History
\* Last modified Fri Feb 13 23:21:50 EST 2026 by karunram
\* Created Wed Feb 11 00:54:54 EST 2026 by karunram
