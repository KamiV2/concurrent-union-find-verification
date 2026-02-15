------------------------- MODULE UFSImplementation -------------------------

\* Shared Memory Object: UF-ID object, whose state is represented as an 
\* idempotent function UF.rep and an element-to-id mapping UF.id.
\* ALGORITHM:

\*     0:  CHOOSE i, j \in [1..n]: Find_p(i) \/ Unite_p(i, j) \/ SameSet(i, j)
    
\*         Find_p(c):
\*     F1:    ret = F(c)
\*     FR:    Return ret

\*         Unite_p(c, d):
\*     U1:    ret = Unite(c, d)
\*     UR:    return ret

\*         SameSet_p(c, d):
\*     S1:     u = c; v = d; u = Find(u) 
\*     S2:     i_u = GetId(u)
\*     S3:     v = Find(v); if u = v then ret = True; goto SR
\*     S4:     i_V = GetID(v); if i_U > i_V and i_V > 0 then ret = False; goto SR
\*     S5:     u = Find(u); if u = v then ret = True; goto SR
\*     S6:     i_U = GetID(u); if i_U < i_V and i_U > 0 then ret = False; goto SR else goto S3
\*     SR:     return ret

EXTENDS FiniteSets, Integers
CONSTANT BOT, ACK, PROCESSES, N
VARIABLES pc, UF, u, v, i_u, i_v, c, d, M, ret
NodeSet == 1..N
varlist == <<pc, UF, u, v, i_u, i_v, c, d, M, ret>>
ASSUME NisNat ==    (N \in Nat) /\ (N > 0)
ASSUME AckBotNullDef == BOT \notin NodeSet /\ ACK \notin NodeSet /\ BOT # ACK
ASSUME ExistProc == PROCESSES # {}

Idems == {A \in [NodeSet -> NodeSet]: \A i \in NodeSet: A[A[i]] = A[i]}
NodeToIdFuncs == [NodeSet -> Nat]

UFId_StateSet == [rep: Idems, id: NodeToIdFuncs]

SmallerRep(rep, x, y) == IF UF.id[rep[x]] < UF.id[rep[y]] THEN rep[x] ELSE rep[y]
LargerRep(rep, x, y) == IF UF.id[rep[x]] < UF.id[rep[y]] THEN rep[y] ELSE rep[x]

URep(rep, x, y) == [i \in NodeSet |-> IF rep[i] = SmallerRep(rep, x, y) 
                                           THEN LargerRep(rep, x, y)
                                           ELSE rep[i]]

CandID(x) == IF UF.rep[x] = x 
                THEN {k \in Nat: k >= UF.id[x] /\ \A y \in NodeSet: (k = UF.id[y] => x = y)} 
                ELSE {0}

IDUpdate(x) == {[UF.id EXCEPT ![x] = y]: y \in CandID(x)}

OpSet ==  [PROCESSES -> {"F", "U", "S", BOT}]
ArgSet == [PROCESSES -> {BOT} \cup NodeSet \cup NodeSet \X NodeSet]
ReturnSet == [PROCESSES -> {ACK, BOT, TRUE, FALSE} \cup NodeSet]

Configs == [sigma: Idems, op: OpSet, arg: ArgSet, ret: ReturnSet]


InitState == [i \in NodeSet |-> i]
InitUF ==     [rep |-> [i \in NodeSet |-> i], 
               id |-> CHOOSE f \in [NodeSet -> Nat \ {0}]: \A i, j \in NodeSet: (f[i] = f[j] => i = j)]
InitRet ==   [p \in PROCESSES |-> BOT]
InitOp ==    [p \in PROCESSES |-> BOT]
InitArg ==   [p \in PROCESSES |-> BOT]

UFUnite(x, y) ==    /\ UF \in UFId_StateSet /\ x \in NodeSet /\ y \in NodeSet
                    /\ UF' = [rep |-> URep(UF.rep, x, y), id |-> UF.id]

\* The subset of the Unites that agree with the current state of the UF object
MetaConfigUnite(sigma, x, y) == URep(sigma, x, y)


\* Initial state of algorithm
Init ==         /\ pc = [p \in PROCESSES |-> "0"]
                /\ UF  = InitUF
                /\ u \in [PROCESSES -> NodeSet]
                /\ v \in [PROCESSES -> NodeSet]
                /\ i_u \in [PROCESSES -> Nat \cup {0}]
                /\ i_v \in [PROCESSES -> Nat \cup {0}]
                /\ c \in [PROCESSES -> NodeSet]
                /\ d \in [PROCESSES -> NodeSet]
                /\ ret \in [PROCESSES -> {ACK, TRUE, FALSE, BOT} \cup NodeSet]
                /\ M = {[sigma |-> InitState,  ret |-> InitRet, op |-> InitOp, arg |-> InitArg]}



F1(p) == /\ pc[p] = "F1"
         /\ pc' = [pc EXCEPT ![p] = "FR"]
         /\ ret' = [ret EXCEPT ![p] = UF.rep[c[p]]]
         /\ M' = {t \in Configs: \E told \in M: /\ told.ret[p] = BOT 
                                                /\ t.sigma = told.sigma
                                                /\ t.ret = [told.ret EXCEPT ![p] = told.sigma[told.arg[p]]]
                                                /\ t.op = told.op
                                                /\ t.arg = told.arg}
         /\ UNCHANGED <<UF, u, v, i_u, i_v, c, d>>
         
FR(p) == /\ pc[p] = "FR"
         /\ pc' = [pc EXCEPT ![p] = "0"]
         /\ M' = {t \in Configs: \E told \in M: /\ told.ret[p] = ret[p] 
                                                /\ t.sigma = told.sigma
                                                /\ t.ret = [told.ret EXCEPT ![p] = BOT]
                                                /\ t.op = [told.op EXCEPT ![p] = BOT]
                                                /\ t.arg = [told.arg EXCEPT ![p] = BOT]}
         /\ UNCHANGED <<UF, u, v, i_u, i_v, c, d, ret>>
         
U1(p) == /\ pc[p] = "U1"
         /\ pc' = [pc EXCEPT ![p] = "UR"]
         /\ UFUnite(c[p], d[p])
         /\ ret' = [ret EXCEPT ![p] = ACK]
         /\ M' = {t \in Configs: \E told \in M:  /\ told.ret[p] = BOT
                                                 /\ t.ret = [told.ret EXCEPT ![p] = ACK]
                                                 /\ t.sigma = MetaConfigUnite(told.sigma, told.arg[p][1], told.arg[p][2])
                                                 /\ t.op = told.op
                                                 /\ t.arg = told.arg}
         /\ UNCHANGED <<u, v, i_u, i_v, c, d>>

UR(p) == /\ pc[p] = "UR"
         /\ pc' = [pc EXCEPT ![p] = "0"]
         /\ M' = {t \in Configs: \E told \in M: 
                                        /\ told.ret[p] = ret[p]
                                        /\ t.sigma = told.sigma
                                        /\ t.ret = [told.ret EXCEPT ![p] = BOT]
                                        /\ t.op = [told.op EXCEPT ![p] = BOT]
                                        /\ t.arg = [told.arg EXCEPT ![p] = BOT]}
         /\ UNCHANGED <<UF, u, v, i_u, i_v, c, d, ret>>

S1(p) == /\ pc[p] = "S1"
         /\ pc' = [pc EXCEPT ![p] = "S2"]
         /\ u' = [u EXCEPT ![p] = UF.rep[c[p]]]
         /\ v' = [v EXCEPT ![p] = d[p]]
         /\ UNCHANGED <<UF, i_u, i_v, c, d, ret, M>>

S2(p) == /\ pc[p] = "S2"
         /\ pc' = [pc EXCEPT ![p] = "S3"]
         /\ i_u' = [i_u EXCEPT ![p] = IF UF.rep[u[p]] = u[p] THEN UF.id[u[p]] ELSE 0]
         /\ \E newId \in IDUpdate(u[p]): UF' = [rep |-> UF.rep, id |-> newId]
         /\ UNCHANGED <<i_v, u, v, c, d, ret, M>>

S3(p) == /\ pc[p] = "S3"
         /\ v' = [v EXCEPT ![p] = UF.rep[v[p]]]
         /\ IF u[p] = v'[p]
             THEN /\ ret' = [ret EXCEPT ![p] = TRUE] 
                  /\ pc' = [pc EXCEPT ![p] = "SR"]
                  /\ M' = {t \in Configs: \E told \in M: 
                                                /\ told.ret[p] = BOT
                                                /\ t.sigma = told.sigma
                                                /\ t.ret = [told.ret EXCEPT ![p] = IF told.sigma[told.arg[p][1]] = told.sigma[told.arg[p][2]] THEN TRUE ELSE FALSE]
                                                /\ t.op  = told.op
                                                /\ t.arg = told.arg}
             ELSE /\ ret' = ret 
                  /\ pc' = [pc EXCEPT ![p] = "S4"]
                  /\ M' = M
        /\ UNCHANGED <<UF, u, i_u, i_v, c, d>>

S4(p) == /\ pc[p] = "S4"
         /\ i_v' = [i_v EXCEPT ![p] = IF UF.rep[v[p]] = v[p] THEN UF.id[v[p]] ELSE 0]
         /\ \E newId \in IDUpdate(v[p]): UF' = [rep |-> UF.rep, id |-> newId]
         /\ IF i_u[p] > i_v'[p] /\ i_v'[p] > 0
            THEN /\ ret' = [ret EXCEPT ![p] = FALSE]
                /\ pc' = [pc EXCEPT ![p] = "SR"]
                /\ M' = {t \in Configs: \E told \in M: 
                                                /\ told.ret[p] = BOT
                                                /\ t.sigma = told.sigma
                                                /\ t.ret = [told.ret EXCEPT ![p] = IF told.sigma[told.arg[p][1]] = told.sigma[told.arg[p][2]] THEN TRUE ELSE FALSE]
                                                /\ t.op  = told.op
                                                /\ t.arg = told.arg}
            ELSE /\ ret' = ret
                /\ pc' = [pc EXCEPT ![p] = "S5"]
                /\ M' = M
     /\ UNCHANGED <<u, v, i_u, c, d, M>>

S5(p) == /\ pc[p] = "S5"
         /\ u' = [u EXCEPT ![p] = UF.rep[u[p]]]
         /\ pc' = [pc EXCEPT ![p] = "S6"]
         /\ IF u[p] = v'[p]
             THEN /\ ret' = [ret EXCEPT ![p] = TRUE] 
                  /\ pc' = [pc EXCEPT ![p] = "SR"]
                  /\ M' = {t \in Configs: \E told \in M: 
                                                /\ told.ret[p] = BOT
                                                /\ t.sigma = told.sigma
                                                /\ t.ret = [told.ret EXCEPT ![p] = IF told.sigma[told.arg[p][1]] = told.sigma[told.arg[p][2]] THEN TRUE ELSE FALSE]
                                                /\ t.op  = told.op
                                                /\ t.arg = told.arg}
             ELSE /\ ret' = ret 
                  /\ pc' = [pc EXCEPT ![p] = "S6"]
                  /\ M' = M
         /\ UNCHANGED <<UF, v, i_u, i_v, c, d, ret>>

S6(p) == /\ pc[p] = "S6"
         /\ i_u' = [i_u EXCEPT ![p] = IF UF.rep[u[p]] = u[p] THEN UF.id[u[p]] ELSE 0]
         /\ \E newId \in IDUpdate(u[p]): UF' = [rep |-> UF.rep, id |-> newId]
         /\ UNCHANGED <<u, v, i_v, c, d, M>>
    
         /\ IF i_u'[p] < i_v[p] /\ i_u'[p] > 0
            THEN /\ ret' = [ret EXCEPT ![p] = FALSE]
                 /\ pc' = [pc EXCEPT ![p] = "SR"]
                 /\ M' = {t \in Configs: \E told \in M: 
                                                /\ told.ret[p] = BOT
                                                /\ t.sigma = told.sigma
                                                /\ t.ret = [told.ret EXCEPT ![p] = IF told.sigma[told.arg[p][1]] = told.sigma[told.arg[p][2]] THEN TRUE ELSE FALSE]
                                                /\ t.op  = told.op
                                                /\ t.arg = told.arg}
            ELSE /\ ret' = ret
                 /\ pc' = [pc EXCEPT ![p] = "S3"]
                 /\ M' = M

SR(p) == /\ pc[p] = "SR"
         /\ pc' = [pc EXCEPT ![p] = "0"]
         /\ M' = {t \in Configs: \E told \in M: /\ told.ret[p] = ret[p]
                                                /\ t.sigma = told.sigma
                                                /\ t.ret = [told.ret EXCEPT ![p] = BOT]
                                                /\ t.op = [told.op EXCEPT ![p] = BOT]
                                                /\ t.arg = [told.arg EXCEPT ![p] = BOT]}
         /\ UNCHANGED <<UF, u, v, i_u, i_v, c, d, ret>>

Decide(p) ==    /\ pc[p] = "0"
                    /\  \/  /\ pc' = [pc EXCEPT ![p] = "F1"]
                            /\ \E i \in NodeSet:    
                                        /\ c' = [c EXCEPT ![p] = i]
                                        /\ M' = {t \in Configs: \E told \in M:  /\ told.ret[p] = BOT
                                                                                          /\ told.op[p] = BOT
                                                                                          /\ told.arg[p] = BOT
                                                                                          /\ t.sigma = told.sigma
                                                                                          /\ t.op = [told.op EXCEPT ![p] = "F"]
                                                                                          /\ t.arg = [told.arg EXCEPT ![p] = c'[p]]
                                                                                          /\ t.ret = told.ret}
                              /\ UNCHANGED <<UF, u, v, i_u, i_v, d, ret>>
                         \/  /\ pc' = [pc EXCEPT ![p] = "U1"]
                             /\ \E i \in NodeSet: \E j \in NodeSet: 
                                        /\ c' = [c EXCEPT ![p] = i]
                                        /\ d' = [d EXCEPT ![p] = j]
                                        /\ M' = {t \in Configs: \E told \in M:  /\ told.ret[p] = BOT
                                                                                          /\ told.op[p] = BOT
                                                                                          /\ told.arg[p] = BOT
                                                                                          /\ t.sigma = told.sigma
                                                                                          /\ t.op = [told.op EXCEPT ![p] = "U"]
                                                                                          /\ t.arg = [told.arg EXCEPT ![p] = <<c'[p], d'[p]>>]
                                                                                          /\ t.ret = told.ret}
                              /\ UNCHANGED <<UF, u, v, i_u, i_v, ret>>
                         \/  /\ pc' = [pc EXCEPT ![p] = "S1"]
                             /\ i_u' = [i_u EXCEPT ![p] = 0]
                             /\ i_v' = [i_v EXCEPT ![p] = 0]
                             /\ \E i \in NodeSet: \E j \in NodeSet: 
                                        /\ c' = [c EXCEPT ![p] = i]
                                        /\ d' = [d EXCEPT ![p] = j]
                                        /\ M' = {t \in Configs: \E told \in M:  /\ told.ret[p] = BOT
                                                                                          /\ told.op[p] = BOT
                                                                                          /\ told.arg[p] = BOT
                                                                                          /\ t.sigma = told.sigma
                                                                                          /\ t.op = [told.op EXCEPT ![p] = "S"]
                                                                                          /\ t.arg = [told.arg EXCEPT ![p] = <<c'[p], d'[p]>>]
                                                                                          /\ t.ret = told.ret}
                              /\ UNCHANGED <<UF, u, v, ret>>

Step(p) ==  \/  F1(p)
            \/  FR(p)
            \/  U1(p)
            \/  UR(p)
            \/  S1(p)
            \/  S2(p)
            \/  S3(p)
            \/  S4(p)
            \/  S5(p)
            \/  S6(p)
            \/  SR(p)
            \/  Decide(p)
            

Next ==     \E p \in PROCESSES: Step(p)

UFSSpec == Init /\ [][Next]_varlist


=============================================================================
\* Modification History
\* Last modified Sat Feb 14 00:32:58 EST 2026 by karunram
\* Created Wed Feb 11 01:01:07 EST 2026 by karunram
