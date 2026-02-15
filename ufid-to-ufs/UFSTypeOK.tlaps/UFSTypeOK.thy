(* automatically generated -- do not edit manually *)
theory UFSTypeOK imports Constant Zenon begin
ML_command {* writeln ("*** TLAPS PARSED\n"); *}
consts
  "isReal" :: c
  "isa_slas_a" :: "[c,c] => c"
  "isa_bksl_diva" :: "[c,c] => c"
  "isa_perc_a" :: "[c,c] => c"
  "isa_peri_peri_a" :: "[c,c] => c"
  "isInfinity" :: c
  "isa_lbrk_rbrk_a" :: "[c] => c"
  "isa_less_more_a" :: "[c] => c"

lemma ob'73:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes UF UF'
fixes u u'
fixes v v'
fixes a_iunde_ua a_iunde_ua'
fixes a_iunde_va a_iunde_va'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition NodeSet suppressed *)
(* usable definition varlist suppressed *)
(* usable definition Idems suppressed *)
(* usable definition NodeToIdFuncs suppressed *)
(* usable definition UFId_StateSet suppressed *)
(* usable definition SmallerRep suppressed *)
(* usable definition LargerRep suppressed *)
(* usable definition URep suppressed *)
(* usable definition CandID suppressed *)
(* usable definition IDUpdate suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitUF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition UFUnite suppressed *)
(* usable definition MetaConfigUnite suppressed *)
(* usable definition Init suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition S5 suppressed *)
(* usable definition S6 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition UFSSpec suppressed *)
(* usable definition PCTypeOK suppressed *)
(* usable definition UFTypeOK suppressed *)
(* usable definition uTypeOK suppressed *)
(* usable definition vTypeOK suppressed *)
(* usable definition i_uTypeOK suppressed *)
(* usable definition i_vTypeOK suppressed *)
(* usable definition cTypeOK suppressed *)
(* usable definition dTypeOK suppressed *)
(* usable definition retTypeOK suppressed *)
assumes v'64: "((PCTypeOK) & (UFTypeOK) & (uTypeOK) & (vTypeOK) & (a_iunde_uTypeOKa) & (a_iunde_vTypeOKa) & (cTypeOK) & (dTypeOK) & (retTypeOK) & (((M) \<subseteq> ([''sigma'' : (Idems), ''op'' : ([(PROCESSES) \<rightarrow> ({(''F''), (''U''), (''S''), (BOT)})]), ''arg'' : ([(PROCESSES) \<rightarrow> ((((({(BOT)}) \<union> (NodeSet))) \<union> (((NodeSet) \<times> (NodeSet)))))]), ''ret'' : ([(PROCESSES) \<rightarrow> ((({(ACK), (BOT), (TRUE), (FALSE)}) \<union> (NodeSet)))])]))))"
fixes p
assumes p_in : "(p \<in> (PROCESSES))"
assumes v'66: "((Step ((p))))"
assumes v'79: "((((a_iunde_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))])))"
assumes v'82: "((\<exists> newId \<in> ((IDUpdate ((fapply ((v), (p)))))) : ((((a_UFhash_primea :: c)) = (((''rep'' :> (fapply ((UF), (''rep'')))) @@ (''id'' :> (newId))))))) & (cond(((((greater ((fapply ((a_iunde_ua), (p))), (fapply (((a_iunde_vhash_primea :: c)), (p)))))) \<and> ((greater ((fapply (((a_iunde_vhash_primea :: c)), (p))), ((0))))))), (((((a_rethash_primea :: c)) = ([(ret) EXCEPT ![(p)] = (FALSE)]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''SR'')]))) & ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : (Idems), ''op'' : ([(PROCESSES) \<rightarrow> ({(''F''), (''U''), (''S''), (BOT)})]), ''arg'' : ([(PROCESSES) \<rightarrow> ((((({(BOT)}) \<union> (NodeSet))) \<union> (((NodeSet) \<times> (NodeSet)))))]), ''ret'' : ([(PROCESSES) \<rightarrow> ((({(ACK), (BOT), (TRUE), (FALSE)}) \<union> (NodeSet)))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''ret''))) = ([(fapply ((told), (''ret''))) EXCEPT ![(p)] = (cond((((fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[0])))))) = (fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[Succ[0]])))))))), (TRUE), (FALSE)))]))) & (((fapply ((t), (''op''))) = (fapply ((told), (''op''))))) & (((fapply ((t), (''arg''))) = (fapply ((told), (''arg'')))))))))))), (((((a_rethash_primea :: c)) = (ret))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''S5'')]))) & ((((a_Mhash_primea :: c)) = (M)))))))"
assumes v'83: "(((fapply ((pc), (p))) = (''S4'')))"
assumes v'84: "((((a_iunde_vhash_primea :: c)) = ([(a_iunde_va) EXCEPT ![(p)] = (cond((((fapply ((fapply ((UF), (''rep''))), (fapply ((v), (p))))) = (fapply ((v), (p))))), (fapply ((fapply ((UF), (''id''))), (fapply ((v), (p))))), ((0))))])))"
assumes v'85: "((((a_uhash_primea :: c)) = (u)))"
assumes v'86: "((((a_vhash_primea :: c)) = (v)))"
assumes v'87: "((((a_iunde_uhash_primea :: c)) = (a_iunde_ua)))"
assumes v'88: "((((a_chash_primea :: c)) = (a_ca)))"
assumes v'89: "((((a_dhash_primea :: c)) = (d)))"
assumes v'90: "((((a_Mhash_primea :: c)) = (M)))"
shows "((((a_Mhash_primea :: c)) \<subseteq> ([''sigma'' : (Idems), ''op'' : ([(PROCESSES) \<rightarrow> ({(''F''), (''U''), (''S''), (BOT)})]), ''arg'' : ([(PROCESSES) \<rightarrow> ((((({(BOT)}) \<union> (NodeSet))) \<union> (((NodeSet) \<times> (NodeSet)))))]), ''ret'' : ([(PROCESSES) \<rightarrow> ((({(ACK), (BOT), (TRUE), (FALSE)}) \<union> (NodeSet)))])])))"(is "PROP ?ob'73")
proof -
ML_command {* writeln "*** TLAPS ENTER 73"; *}
show "PROP ?ob'73"

(* BEGIN ZENON INPUT
;; file=UFSTypeOK.tlaps/tlapm_c0367e.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >UFSTypeOK.tlaps/tlapm_c0367e.znn.out
;; obligation #73
$hyp "v'64" (/\ PCTypeOK UFTypeOK uTypeOK vTypeOK a_iunde_uTypeOKa
a_iunde_vTypeOKa cTypeOK dTypeOK retTypeOK (TLA.subseteq M
(TLA.recordset "sigma" Idems "op" (TLA.FuncSet PROCESSES (TLA.set "F" "U" "S" BOT)) "arg" (TLA.FuncSet PROCESSES (TLA.cup (TLA.cup (TLA.set BOT)
NodeSet)
(TLA.prod NodeSet NodeSet))) "ret" (TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK BOT T. F.)
NodeSet)))))
$hyp "p_in" (TLA.in p PROCESSES)
$hyp "v'66" (Step p)
$hyp "v'79" (TLA.in a_iunde_vhash_primea
(TLA.FuncSet PROCESSES (TLA.cup arith.N
(TLA.set 0))))
$hyp "v'82" (/\ (TLA.bEx (IDUpdate (TLA.fapply v p)) ((newId) (= a_UFhash_primea
(TLA.record "rep" (TLA.fapply UF "rep") "id" newId))))
(TLA.cond (/\ (arith.lt (TLA.fapply a_iunde_vhash_primea p)
(TLA.fapply a_iunde_ua p)) (arith.lt 0
(TLA.fapply a_iunde_vhash_primea p))) (/\ (= a_rethash_primea
(TLA.except ret p F.)) (= a_pchash_primea (TLA.except pc p "SR"))
(= a_Mhash_primea
(TLA.subsetOf (TLA.recordset "sigma" Idems "op" (TLA.FuncSet PROCESSES (TLA.set "F" "U" "S" BOT)) "arg" (TLA.FuncSet PROCESSES (TLA.cup (TLA.cup (TLA.set BOT)
NodeSet)
(TLA.prod NodeSet NodeSet))) "ret" (TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK BOT T. F.)
NodeSet))) ((t) (TLA.bEx M ((told) (/\ (= (TLA.fapply (TLA.fapply told "ret") p)
BOT) (= (TLA.fapply t "sigma") (TLA.fapply told "sigma"))
(= (TLA.fapply t "ret")
(TLA.except (TLA.fapply told "ret") p (TLA.cond (= (TLA.fapply (TLA.fapply told "sigma") (TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ 0)))
(TLA.fapply (TLA.fapply told "sigma") (TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))) T. F.)))
(= (TLA.fapply t "op") (TLA.fapply told "op")) (= (TLA.fapply t "arg")
(TLA.fapply told "arg"))))))))) (/\ (= a_rethash_primea ret)
(= a_pchash_primea (TLA.except pc p "S5")) (= a_Mhash_primea
M))))
$hyp "v'83" (= (TLA.fapply pc p) "S4")
$hyp "v'84" (= a_iunde_vhash_primea
(TLA.except a_iunde_va p (TLA.cond (= (TLA.fapply (TLA.fapply UF "rep") (TLA.fapply v p))
(TLA.fapply v p)) (TLA.fapply (TLA.fapply UF "id") (TLA.fapply v p)) 0)))
$hyp "v'85" (= a_uhash_primea u)
$hyp "v'86" (= a_vhash_primea v)
$hyp "v'87" (= a_iunde_uhash_primea a_iunde_ua)
$hyp "v'88" (= a_chash_primea a_ca)
$hyp "v'89" (= a_dhash_primea d)
$hyp "v'90" (= a_Mhash_primea M)
$goal (TLA.subseteq a_Mhash_primea
(TLA.recordset "sigma" Idems "op" (TLA.FuncSet PROCESSES (TLA.set "F" "U" "S" BOT)) "arg" (TLA.FuncSet PROCESSES (TLA.cup (TLA.cup (TLA.set BOT)
NodeSet)
(TLA.prod NodeSet NodeSet))) "ret" (TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK BOT T. F.)
NodeSet))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(PCTypeOK&(UFTypeOK&(uTypeOK&(vTypeOK&(a_iunde_uTypeOKa&(a_iunde_vTypeOKa&(cTypeOK&(dTypeOK&(retTypeOK&(M \\subseteq [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))))))))" (is "_&?z_hp")
 using v'64 by blast
 have z_Hm:"(a_Mhash_primea=M)"
 using v'90 by blast
 assume z_Hn:"(~(a_Mhash_primea \\subseteq [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))" (is "~?z_hch")
 have z_Hp: "?z_hp" (is "_&?z_hr")
 by (rule zenon_and_1 [OF z_Ha])
 have z_Hr: "?z_hr" (is "_&?z_ht")
 by (rule zenon_and_1 [OF z_Hp])
 have z_Ht: "?z_ht" (is "_&?z_hv")
 by (rule zenon_and_1 [OF z_Hr])
 have z_Hv: "?z_hv" (is "_&?z_hx")
 by (rule zenon_and_1 [OF z_Ht])
 have z_Hx: "?z_hx" (is "_&?z_hz")
 by (rule zenon_and_1 [OF z_Hv])
 have z_Hz: "?z_hz" (is "_&?z_hbb")
 by (rule zenon_and_1 [OF z_Hx])
 have z_Hbb: "?z_hbb" (is "_&?z_hbd")
 by (rule zenon_and_1 [OF z_Hz])
 have z_Hbd: "?z_hbd" (is "_&?z_hbf")
 by (rule zenon_and_1 [OF z_Hbb])
 have z_Hbf: "?z_hbf"
 by (rule zenon_and_1 [OF z_Hbd])
 have z_Hci_z_Hbf: "bAll(M, (\<lambda>x. (x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))) == ?z_hbf" (is "?z_hci == _")
 by (unfold subset_def)
 have z_Hci: "?z_hci"
 by (unfold z_Hci_z_Hbf, fact z_Hbf)
 have z_Hcm_z_Hn: "(~bAll(a_Mhash_primea, (\<lambda>x. (x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) == (~?z_hch)" (is "?z_hcm == ?z_hn")
 by (unfold subset_def)
 have z_Hcm: "?z_hcm" (is "~?z_hcn")
 by (unfold z_Hcm_z_Hn, fact z_Hn)
 have z_Hco: "(~?z_hci)"
 by (rule subst [where P="(\<lambda>zenon_Via. (~bAll(zenon_Via, (\<lambda>x. (x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))))", OF z_Hm z_Hcm])
 show FALSE
 by (rule notE [OF z_Hco z_Hci])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 73"; *} qed
lemma ob'84:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes UF UF'
fixes u u'
fixes v v'
fixes a_iunde_ua a_iunde_ua'
fixes a_iunde_va a_iunde_va'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition NodeSet suppressed *)
(* usable definition varlist suppressed *)
(* usable definition Idems suppressed *)
(* usable definition NodeToIdFuncs suppressed *)
(* usable definition UFId_StateSet suppressed *)
(* usable definition SmallerRep suppressed *)
(* usable definition LargerRep suppressed *)
(* usable definition URep suppressed *)
(* usable definition CandID suppressed *)
(* usable definition IDUpdate suppressed *)
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitUF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition UFUnite suppressed *)
(* usable definition MetaConfigUnite suppressed *)
(* usable definition Init suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition S4 suppressed *)
(* usable definition S6 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition UFSSpec suppressed *)
assumes v'58: "((((pc) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''S4''), (''S5''), (''S6''), (''SR'')})]))) & (((UF) \<in> (a_UFIdunde_StateSeta))) & (((u) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((a_iunde_ua) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))]))) & (((a_iunde_va) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE), (BOT)}) \<union> (NodeSet)))]))) & (((M) \<subseteq> ([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]))))"
fixes p
assumes p_in : "(p \<in> (PROCESSES))"
assumes v'60: "((Step ((p))))"
assumes v'74: "((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)])))"
assumes v'75: "(cond((((fapply ((v), (p))) = (fapply (((a_uhash_primea :: c)), (p))))), (((((a_rethash_primea :: c)) = ([(ret) EXCEPT ![(p)] = (TRUE)]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''SR'')]))) & ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''ret''))) = ([(fapply ((told), (''ret''))) EXCEPT ![(p)] = (cond((((fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[0])))))) = (fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[Succ[0]])))))))), (TRUE), (FALSE)))]))) & (((fapply ((t), (''op''))) = (fapply ((told), (''op''))))) & (((fapply ((t), (''arg''))) = (fapply ((told), (''arg'')))))))))))), (((((a_rethash_primea :: c)) = (ret))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''S6'')]))) & ((((a_Mhash_primea :: c)) = (M))))))"
assumes v'76: "(((fapply ((pc), (p))) = (''S5'')))"
assumes v'77: "((((a_uhash_primea :: c)) = ([(u) EXCEPT ![(p)] = (fapply ((fapply ((UF), (''rep''))), (fapply ((u), (p)))))])))"
assumes v'78: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''S6'')])))"
assumes v'79: "((((a_UFhash_primea :: c)) = (UF)))"
assumes v'80: "((((a_vhash_primea :: c)) = (v)))"
assumes v'81: "((((a_iunde_uhash_primea :: c)) = (a_iunde_ua)))"
assumes v'82: "((((a_iunde_vhash_primea :: c)) = (a_iunde_va)))"
assumes v'83: "((((a_chash_primea :: c)) = (a_ca)))"
assumes v'84: "((((a_dhash_primea :: c)) = (d)))"
assumes v'85: "((((a_rethash_primea :: c)) = (ret)))"
shows "(((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''S4''), (''S5''), (''S6''), (''SR'')})]))) & ((((a_UFhash_primea :: c)) \<in> (a_UFIdunde_StateSeta))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & ((((a_iunde_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))]))) & ((((a_iunde_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE), (BOT)}) \<union> (NodeSet)))]))) & ((((a_Mhash_primea :: c)) \<subseteq> ([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]))))"(is "PROP ?ob'84")
proof -
ML_command {* writeln "*** TLAPS ENTER 84"; *}
show "PROP ?ob'84"

(* BEGIN ZENON INPUT
;; file=UFSTypeOK.tlaps/tlapm_60ca0b.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >UFSTypeOK.tlaps/tlapm_60ca0b.znn.out
;; obligation #84
$hyp "v'58" (/\ (TLA.in pc
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "S4" "S5" "S6" "SR")))
(TLA.in UF a_UFIdunde_StateSeta) (TLA.in u (TLA.FuncSet PROCESSES NodeSet))
(TLA.in v (TLA.FuncSet PROCESSES NodeSet)) (TLA.in a_iunde_ua
(TLA.FuncSet PROCESSES (TLA.cup arith.N (TLA.set 0)))) (TLA.in a_iunde_va
(TLA.FuncSet PROCESSES (TLA.cup arith.N (TLA.set 0)))) (TLA.in a_ca
(TLA.FuncSet PROCESSES NodeSet)) (TLA.in d (TLA.FuncSet PROCESSES NodeSet))
(TLA.in ret (TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F. BOT)
NodeSet))) (TLA.subseteq M
(TLA.recordset "sigma" Idems "op" OpSet "arg" ArgSet "ret" ReturnSet)))
$hyp "p_in" (TLA.in p PROCESSES)
$hyp "v'60" (Step p)
$hyp "v'74" (TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES NodeSet))
$hyp "v'75" (TLA.cond (= (TLA.fapply v p)
(TLA.fapply a_uhash_primea p)) (/\ (= a_rethash_primea (TLA.except ret p T.))
(= a_pchash_primea (TLA.except pc p "SR")) (= a_Mhash_primea
(TLA.subsetOf (TLA.recordset "sigma" Idems "op" OpSet "arg" ArgSet "ret" ReturnSet) ((t) (TLA.bEx M ((told) (/\ (= (TLA.fapply (TLA.fapply told "ret") p)
BOT) (= (TLA.fapply t "sigma") (TLA.fapply told "sigma"))
(= (TLA.fapply t "ret")
(TLA.except (TLA.fapply told "ret") p (TLA.cond (= (TLA.fapply (TLA.fapply told "sigma") (TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ 0)))
(TLA.fapply (TLA.fapply told "sigma") (TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))) T. F.)))
(= (TLA.fapply t "op") (TLA.fapply told "op")) (= (TLA.fapply t "arg")
(TLA.fapply told "arg"))))))))) (/\ (= a_rethash_primea ret)
(= a_pchash_primea (TLA.except pc p "S6")) (= a_Mhash_primea
M)))
$hyp "v'76" (= (TLA.fapply pc p) "S5")
$hyp "v'77" (= a_uhash_primea
(TLA.except u p (TLA.fapply (TLA.fapply UF "rep") (TLA.fapply u p))))
$hyp "v'78" (= a_pchash_primea
(TLA.except pc p "S6"))
$hyp "v'79" (= a_UFhash_primea UF)
$hyp "v'80" (= a_vhash_primea v)
$hyp "v'81" (= a_iunde_uhash_primea
a_iunde_ua)
$hyp "v'82" (= a_iunde_vhash_primea a_iunde_va)
$hyp "v'83" (= a_chash_primea a_ca)
$hyp "v'84" (= a_dhash_primea d)
$hyp "v'85" (= a_rethash_primea ret)
$goal (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "S4" "S5" "S6" "SR")))
(TLA.in a_UFhash_primea a_UFIdunde_StateSeta) (TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES NodeSet)) (TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES NodeSet)) (TLA.in a_iunde_uhash_primea
(TLA.FuncSet PROCESSES (TLA.cup arith.N (TLA.set 0))))
(TLA.in a_iunde_vhash_primea (TLA.FuncSet PROCESSES (TLA.cup arith.N
(TLA.set 0)))) (TLA.in a_chash_primea (TLA.FuncSet PROCESSES NodeSet))
(TLA.in a_dhash_primea (TLA.FuncSet PROCESSES NodeSet))
(TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F. BOT) NodeSet)))
(TLA.subseteq a_Mhash_primea
(TLA.recordset "sigma" Idems "op" OpSet "arg" ArgSet "ret" ReturnSet)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((pc \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))&((UF \\in a_UFIdunde_StateSeta)&((u \\in FuncSet(PROCESSES, NodeSet))&((v \\in FuncSet(PROCESSES, NodeSet))&((a_iunde_ua \\in FuncSet(PROCESSES, (Nat \\cup {0})))&((a_iunde_va \\in FuncSet(PROCESSES, (Nat \\cup {0})))&((a_ca \\in FuncSet(PROCESSES, NodeSet))&((d \\in FuncSet(PROCESSES, NodeSet))&((ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))&(M \\subseteq [''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]))))))))))" (is "?z_hq&?z_hbh")
 using v'58 by blast
 have z_Ho:"(a_rethash_primea=ret)"
 using v'85 by blast
 have z_Hn:"(a_dhash_primea=d)"
 using v'84 by blast
 have z_Hm:"(a_chash_primea=a_ca)"
 using v'83 by blast
 have z_Hl:"(a_iunde_vhash_primea=a_iunde_va)"
 using v'82 by blast
 have z_Hk:"(a_iunde_uhash_primea=a_iunde_ua)"
 using v'81 by blast
 have z_Hj:"(a_vhash_primea=v)"
 using v'80 by blast
 have z_Hi:"(a_UFhash_primea=UF)"
 using v'79 by blast
 have z_Hh:"(a_pchash_primea=except(pc, p, ''S6''))" (is "_=?z_hdn")
 using v'78 by blast
 have z_He:"cond(((v[p])=(a_uhash_primea[p])), ((a_rethash_primea=except(ret, p, TRUE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg'']))))))))))))), ((a_rethash_primea=ret)&((a_pchash_primea=?z_hdn)&(a_Mhash_primea=M))))" (is "?z_he")
 using v'75 by blast
 have z_Hd:"(a_uhash_primea \\in FuncSet(PROCESSES, NodeSet))" (is "?z_hd")
 using v'74 by blast
 assume z_Hp:"(~((a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))&((a_UFhash_primea \\in a_UFIdunde_StateSeta)&(?z_hd&((a_vhash_primea \\in FuncSet(PROCESSES, NodeSet))&((a_iunde_uhash_primea \\in FuncSet(PROCESSES, (Nat \\cup {0})))&((a_iunde_vhash_primea \\in FuncSet(PROCESSES, (Nat \\cup {0})))&((a_chash_primea \\in FuncSet(PROCESSES, NodeSet))&((a_dhash_primea \\in FuncSet(PROCESSES, NodeSet))&((a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))&(a_Mhash_primea \\subseteq [''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)])))))))))))" (is "~(?z_hfn&?z_hfo)")
 have z_Hq: "?z_hq"
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hbh: "?z_hbh" (is "?z_hbi&?z_hbl")
 by (rule zenon_and_1 [OF z_Ha])
 have z_Hbi: "?z_hbi"
 by (rule zenon_and_0 [OF z_Hbh])
 have z_Hbl: "?z_hbl" (is "?z_hbm&?z_hbq")
 by (rule zenon_and_1 [OF z_Hbh])
 have z_Hbq: "?z_hbq" (is "?z_hbr&?z_hbt")
 by (rule zenon_and_1 [OF z_Hbl])
 have z_Hbr: "?z_hbr"
 by (rule zenon_and_0 [OF z_Hbq])
 have z_Hbt: "?z_hbt" (is "?z_hbu&?z_hcb")
 by (rule zenon_and_1 [OF z_Hbq])
 have z_Hbu: "?z_hbu"
 by (rule zenon_and_0 [OF z_Hbt])
 have z_Hcb: "?z_hcb" (is "?z_hcc&?z_hce")
 by (rule zenon_and_1 [OF z_Hbt])
 have z_Hcc: "?z_hcc"
 by (rule zenon_and_0 [OF z_Hcb])
 have z_Hce: "?z_hce" (is "?z_hcf&?z_hch")
 by (rule zenon_and_1 [OF z_Hcb])
 have z_Hcf: "?z_hcf"
 by (rule zenon_and_0 [OF z_Hce])
 have z_Hch: "?z_hch" (is "?z_hci&?z_hck")
 by (rule zenon_and_1 [OF z_Hce])
 have z_Hci: "?z_hci"
 by (rule zenon_and_0 [OF z_Hch])
 have z_Hck: "?z_hck" (is "?z_hcl&?z_hcu")
 by (rule zenon_and_1 [OF z_Hch])
 have z_Hcl: "?z_hcl"
 by (rule zenon_and_0 [OF z_Hck])
 have z_Hcu: "?z_hcu"
 by (rule zenon_and_1 [OF z_Hck])
 have z_Hge_z_Hcu: "bAll(M, (\<lambda>x. (x \\in [''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]))) == ?z_hcu" (is "?z_hge == _")
 by (unfold subset_def)
 have z_Hge: "?z_hge"
 by (unfold z_Hge_z_Hcu, fact z_Hcu)
 have z_Hgi_z_Hge: "(\\A x:((x \\in M)=>(x \\in [''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]))) == ?z_hge" (is "?z_hgi == _")
 by (unfold bAll_def)
 have z_Hgi: "?z_hgi" (is "\\A x : ?z_hgl(x)")
 by (unfold z_Hgi_z_Hge, fact z_Hge)
 show FALSE
 proof (rule zenon_notand [OF z_Hp])
  assume z_Hgm:"(~?z_hfn)"
  have z_Hgn: "(~(?z_hdn \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''})))" (is "~?z_hgo")
  by (rule subst [where P="(\<lambda>zenon_Vuac. (~(zenon_Vuac \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))", OF z_Hh z_Hgm])
  show FALSE
  proof (rule zenon_except_notin_funcset [of "pc" "p" "''S6''" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hgn])
   assume z_Hgt:"(~?z_hq)"
   show FALSE
   by (rule notE [OF z_Hgt z_Hq])
  next
   assume z_Hgu:"(~(''S6'' \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hgv")
   have z_Hgw: "(~(''S6'' \\in {''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hgx")
   by (rule zenon_notin_addElt_1 [of "''S6''" "''0''" "{''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hgu])
   have z_Hgz: "(~(''S6'' \\in {''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hha")
   by (rule zenon_notin_addElt_1 [of "''S6''" "''F1''" "{''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hgw])
   have z_Hhc: "(~(''S6'' \\in {''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hhd")
   by (rule zenon_notin_addElt_1 [of "''S6''" "''FR''" "{''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hgz])
   have z_Hhf: "(~(''S6'' \\in {''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hhg")
   by (rule zenon_notin_addElt_1 [of "''S6''" "''U1''" "{''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hhc])
   have z_Hhi: "(~(''S6'' \\in {''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hhj")
   by (rule zenon_notin_addElt_1 [of "''S6''" "''UR''" "{''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hhf])
   have z_Hhl: "(~(''S6'' \\in {''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hhm")
   by (rule zenon_notin_addElt_1 [of "''S6''" "''S1''" "{''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hhi])
   have z_Hho: "(~(''S6'' \\in {''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hhp")
   by (rule zenon_notin_addElt_1 [of "''S6''" "''S2''" "{''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hhl])
   have z_Hhr: "(~(''S6'' \\in {''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hhs")
   by (rule zenon_notin_addElt_1 [of "''S6''" "''S3''" "{''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hho])
   have z_Hhu: "(~(''S6'' \\in {''S5'', ''S6'', ''SR''}))" (is "~?z_hhv")
   by (rule zenon_notin_addElt_1 [of "''S6''" "''S4''" "{''S5'', ''S6'', ''SR''}", OF z_Hhr])
   have z_Hhx: "(~(''S6'' \\in {''S6'', ''SR''}))" (is "~?z_hhy")
   by (rule zenon_notin_addElt_1 [of "''S6''" "''S5''" "{''S6'', ''SR''}", OF z_Hhu])
   have z_Hia: "(''S6''~=''S6'')" (is "?z_hbf~=_")
   by (rule zenon_notin_addElt_0 [of "?z_hbf" "?z_hbf" "{''SR''}", OF z_Hhx])
   show FALSE
   by (rule zenon_noteq [OF z_Hia])
  qed
 next
  assume z_Hic:"(~?z_hfo)" (is "~(?z_hfp&?z_hfq)")
  show FALSE
  proof (rule zenon_notand [OF z_Hic])
   assume z_Hid:"(~?z_hfp)"
   have z_Hie: "(~?z_hbi)"
   by (rule subst [where P="(\<lambda>zenon_Vaac. (~(zenon_Vaac \\in a_UFIdunde_StateSeta)))", OF z_Hi z_Hid])
   show FALSE
   by (rule notE [OF z_Hie z_Hbi])
  next
   assume z_Hij:"(~?z_hfq)" (is "~(_&?z_hfr)")
   show FALSE
   proof (rule zenon_notand [OF z_Hij])
    assume z_Hik:"(~?z_hd)"
    show FALSE
    by (rule notE [OF z_Hik z_Hd])
   next
    assume z_Hil:"(~?z_hfr)" (is "~(?z_hfs&?z_hft)")
    show FALSE
    proof (rule zenon_notand [OF z_Hil])
     assume z_Him:"(~?z_hfs)"
     have z_Hin: "(~?z_hbr)"
     by (rule subst [where P="(\<lambda>zenon_Vcac. (~(zenon_Vcac \\in FuncSet(PROCESSES, NodeSet))))", OF z_Hj z_Him])
     show FALSE
     by (rule notE [OF z_Hin z_Hbr])
    next
     assume z_His:"(~?z_hft)" (is "~(?z_hfu&?z_hfv)")
     show FALSE
     proof (rule zenon_notand [OF z_His])
      assume z_Hit:"(~?z_hfu)"
      have z_Hiu: "(~?z_hbu)"
      by (rule subst [where P="(\<lambda>zenon_Vlac. (~(zenon_Vlac \\in FuncSet(PROCESSES, (Nat \\cup {0})))))", OF z_Hk z_Hit])
      show FALSE
      by (rule notE [OF z_Hiu z_Hbu])
     next
      assume z_Hiz:"(~?z_hfv)" (is "~(?z_hfw&?z_hfx)")
      show FALSE
      proof (rule zenon_notand [OF z_Hiz])
       assume z_Hja:"(~?z_hfw)"
       have z_Hjb: "(~?z_hcc)"
       by (rule subst [where P="(\<lambda>zenon_Vlac. (~(zenon_Vlac \\in FuncSet(PROCESSES, (Nat \\cup {0})))))", OF z_Hl z_Hja])
       show FALSE
       by (rule notE [OF z_Hjb z_Hcc])
      next
       assume z_Hjc:"(~?z_hfx)" (is "~(?z_hfy&?z_hfz)")
       show FALSE
       proof (rule zenon_notand [OF z_Hjc])
        assume z_Hjd:"(~?z_hfy)"
        have z_Hje: "(~?z_hcf)"
        by (rule subst [where P="(\<lambda>zenon_Vcac. (~(zenon_Vcac \\in FuncSet(PROCESSES, NodeSet))))", OF z_Hm z_Hjd])
        show FALSE
        by (rule notE [OF z_Hje z_Hcf])
       next
        assume z_Hjf:"(~?z_hfz)" (is "~(?z_hga&?z_hgb)")
        show FALSE
        proof (rule zenon_notand [OF z_Hjf])
         assume z_Hjg:"(~?z_hga)"
         have z_Hjh: "(~?z_hci)"
         by (rule subst [where P="(\<lambda>zenon_Vcac. (~(zenon_Vcac \\in FuncSet(PROCESSES, NodeSet))))", OF z_Hn z_Hjg])
         show FALSE
         by (rule notE [OF z_Hjh z_Hci])
        next
         assume z_Hji:"(~?z_hgb)" (is "~(?z_hgc&?z_hgd)")
         show FALSE
         proof (rule zenon_notand [OF z_Hji])
          assume z_Hjj:"(~?z_hgc)"
          have z_Hjk: "(~?z_hcl)"
          by (rule subst [where P="(\<lambda>zenon_Vrac. (~(zenon_Vrac \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))))", OF z_Ho z_Hjj])
          show FALSE
          by (rule notE [OF z_Hjk z_Hcl])
         next
          assume z_Hjp:"(~?z_hgd)"
          have z_Hjq_z_Hjp: "(~bAll(a_Mhash_primea, (\<lambda>x. (x \\in [''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)])))) == (~?z_hgd)" (is "?z_hjq == ?z_hjp")
          by (unfold subset_def)
          have z_Hjq: "?z_hjq" (is "~?z_hjr")
          by (unfold z_Hjq_z_Hjp, fact z_Hjp)
          have z_Hjs_z_Hjq: "(~(\\A x:((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)])))) == ?z_hjq" (is "?z_hjs == _")
          by (unfold bAll_def)
          have z_Hjs: "?z_hjs" (is "~(\\A x : ?z_hjw(x))")
          by (unfold z_Hjs_z_Hjq, fact z_Hjq)
          have z_Hjx: "(\\E x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]))))" (is "\\E x : ?z_hjz(x)")
          by (rule zenon_notallex_0 [of "?z_hjw", OF z_Hjs])
          have z_Hka: "?z_hjz((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)])))))" (is "~(?z_hkc=>?z_hkd)")
          by (rule zenon_ex_choose_0 [of "?z_hjz", OF z_Hjx])
          have z_Hkc: "?z_hkc"
          by (rule zenon_notimply_0 [OF z_Hka])
          have z_Hke: "(~?z_hkd)"
          by (rule zenon_notimply_1 [OF z_Hka])
          show FALSE
          proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "((v[p])=(a_uhash_primea[p]))" "((a_rethash_primea=except(ret, p, TRUE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" "((a_rethash_primea=ret)&((a_pchash_primea=?z_hdn)&(a_Mhash_primea=M)))", OF z_He])
           assume z_Hdp:"((v[p])=(a_uhash_primea[p]))" (is "?z_hdq=?z_hdr")
           assume z_Hdt:"((a_rethash_primea=except(ret, p, TRUE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" (is "?z_hdu&?z_hdw")
           have z_Hdw: "?z_hdw" (is "?z_hdx&?z_hdz")
           by (rule zenon_and_1 [OF z_Hdt])
           have z_Hdz: "?z_hdz" (is "_=?z_heb")
           by (rule zenon_and_1 [OF z_Hdw])
           have z_Hkh: "(\\A zenon_Vle:((zenon_Vle \\in a_Mhash_primea)<=>(zenon_Vle \\in ?z_heb)))" (is "\\A x : ?z_hkm(x)")
           by (rule zenon_setequal_0 [of "a_Mhash_primea" "?z_heb", OF z_Hdz])
           have z_Hkn: "?z_hkm((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)])))))" (is "_<=>?z_hko")
           by (rule zenon_all_0 [of "?z_hkm" "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]))))", OF z_Hkh])
           show FALSE
           proof (rule zenon_equiv [OF z_Hkn])
            assume z_Hkp:"(~?z_hkc)"
            assume z_Hkq:"(~?z_hko)"
            show FALSE
            by (rule notE [OF z_Hkp z_Hkc])
           next
            assume z_Hkc:"?z_hkc"
            assume z_Hko:"?z_hko"
            have z_Hkd: "?z_hkd"
            by (rule zenon_in_subsetof_0 [of "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]))))" "[''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))", OF z_Hko])
            show FALSE
            by (rule notE [OF z_Hke z_Hkd])
           qed
          next
           assume z_Hkr:"((v[p])~=(a_uhash_primea[p]))" (is "?z_hdq~=?z_hdr")
           assume z_Hfj:"((a_rethash_primea=ret)&((a_pchash_primea=?z_hdn)&(a_Mhash_primea=M)))" (is "?z_ho&?z_hfk")
           have z_Hfk: "?z_hfk" (is "?z_hh&?z_hfl")
           by (rule zenon_and_1 [OF z_Hfj])
           have z_Hfl: "?z_hfl"
           by (rule zenon_and_1 [OF z_Hfk])
           have z_Hks: "?z_hgl((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)])))))" (is "?z_hkt=>_")
           by (rule zenon_all_0 [of "?z_hgl" "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]))))", OF z_Hgi])
           show FALSE
           proof (rule zenon_imply [OF z_Hks])
            assume z_Hku:"(~?z_hkt)"
            have z_Hkp: "(~?z_hkc)"
            by (rule ssubst [where P="(\<lambda>zenon_Vya. (~((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)])))) \\in zenon_Vya)))", OF z_Hfl z_Hku])
            show FALSE
            by (rule notE [OF z_Hkp z_Hkc])
           next
            assume z_Hkd:"?z_hkd"
            show FALSE
            by (rule notE [OF z_Hke z_Hkd])
           qed
          qed
         qed
        qed
       qed
      qed
     qed
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 84"; *} qed
lemma ob'88:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes UF UF'
fixes u u'
fixes v v'
fixes a_iunde_ua a_iunde_ua'
fixes a_iunde_va a_iunde_va'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition NodeSet suppressed *)
(* usable definition varlist suppressed *)
(* usable definition Idems suppressed *)
(* usable definition NodeToIdFuncs suppressed *)
(* usable definition UFId_StateSet suppressed *)
(* usable definition SmallerRep suppressed *)
(* usable definition LargerRep suppressed *)
(* usable definition URep suppressed *)
(* usable definition CandID suppressed *)
(* usable definition IDUpdate suppressed *)
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitUF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition UFUnite suppressed *)
(* usable definition MetaConfigUnite suppressed *)
(* usable definition Init suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition S4 suppressed *)
(* usable definition S5 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition UFSSpec suppressed *)
assumes v'58: "((((pc) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''S4''), (''S5''), (''S6''), (''SR'')})]))) & (((UF) \<in> (a_UFIdunde_StateSeta))) & (((u) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((a_iunde_ua) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))]))) & (((a_iunde_va) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE), (BOT)}) \<union> (NodeSet)))]))) & (((M) \<subseteq> ([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]))))"
fixes p
assumes p_in : "(p \<in> (PROCESSES))"
assumes v'60: "((Step ((p))))"
assumes v'75: "((((a_iunde_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))])))"
assumes v'76: "((((a_Mhash_primea :: c)) \<subseteq> ([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)])))"
assumes v'77: "((((CandID ((fapply ((u), (p)))))) \<subseteq> (((Nat) \<union> ({((0))})))))"
assumes v'79: "((((a_UFhash_primea :: c)) \<in> (a_UFIdunde_StateSeta)))"
assumes v'80: "((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE), (BOT)}) \<union> (NodeSet)))])))"
assumes v'81: "((\<exists> newId \<in> ((IDUpdate ((fapply ((u), (p)))))) : ((((a_UFhash_primea :: c)) = (((''rep'' :> (fapply ((UF), (''rep'')))) @@ (''id'' :> (newId))))))) & (cond(((((less ((fapply (((a_iunde_uhash_primea :: c)), (p))), (fapply ((a_iunde_va), (p)))))) \<and> ((greater ((fapply (((a_iunde_uhash_primea :: c)), (p))), ((0))))))), (((((a_rethash_primea :: c)) = ([(ret) EXCEPT ![(p)] = (FALSE)]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''SR'')]))) & ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''ret''))) = ([(fapply ((told), (''ret''))) EXCEPT ![(p)] = (cond((((fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[0])))))) = (fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[Succ[0]])))))))), (TRUE), (FALSE)))]))) & (((fapply ((t), (''op''))) = (fapply ((told), (''op''))))) & (((fapply ((t), (''arg''))) = (fapply ((told), (''arg'')))))))))))), (((((a_rethash_primea :: c)) = (ret))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''S3'')]))) & ((((a_Mhash_primea :: c)) = (M)))))))"
assumes v'82: "(((fapply ((pc), (p))) = (''S6'')))"
assumes v'83: "((((a_iunde_uhash_primea :: c)) = ([(a_iunde_ua) EXCEPT ![(p)] = (cond((((fapply ((fapply ((UF), (''rep''))), (fapply ((u), (p))))) = (fapply ((u), (p))))), (fapply ((fapply ((UF), (''id''))), (fapply ((u), (p))))), ((0))))])))"
assumes v'84: "((((a_uhash_primea :: c)) = (u)))"
assumes v'85: "((((a_vhash_primea :: c)) = (v)))"
assumes v'86: "((((a_iunde_vhash_primea :: c)) = (a_iunde_va)))"
assumes v'87: "((((a_chash_primea :: c)) = (a_ca)))"
assumes v'88: "((((a_dhash_primea :: c)) = (d)))"
shows "(((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''S4''), (''S5''), (''S6''), (''SR'')})]))) & ((((a_UFhash_primea :: c)) \<in> (a_UFIdunde_StateSeta))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & ((((a_iunde_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))]))) & ((((a_iunde_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE), (BOT)}) \<union> (NodeSet)))]))) & ((((a_Mhash_primea :: c)) \<subseteq> ([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]))))"(is "PROP ?ob'88")
proof -
ML_command {* writeln "*** TLAPS ENTER 88"; *}
show "PROP ?ob'88"

(* BEGIN ZENON INPUT
;; file=UFSTypeOK.tlaps/tlapm_1818b7.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >UFSTypeOK.tlaps/tlapm_1818b7.znn.out
;; obligation #88
$hyp "v'58" (/\ (TLA.in pc
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "S4" "S5" "S6" "SR")))
(TLA.in UF a_UFIdunde_StateSeta) (TLA.in u (TLA.FuncSet PROCESSES NodeSet))
(TLA.in v (TLA.FuncSet PROCESSES NodeSet)) (TLA.in a_iunde_ua
(TLA.FuncSet PROCESSES (TLA.cup arith.N (TLA.set 0)))) (TLA.in a_iunde_va
(TLA.FuncSet PROCESSES (TLA.cup arith.N (TLA.set 0)))) (TLA.in a_ca
(TLA.FuncSet PROCESSES NodeSet)) (TLA.in d (TLA.FuncSet PROCESSES NodeSet))
(TLA.in ret (TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F. BOT)
NodeSet))) (TLA.subseteq M
(TLA.recordset "sigma" Idems "op" OpSet "arg" ArgSet "ret" ReturnSet)))
$hyp "p_in" (TLA.in p PROCESSES)
$hyp "v'60" (Step p)
$hyp "v'75" (TLA.in a_iunde_uhash_primea
(TLA.FuncSet PROCESSES (TLA.cup arith.N
(TLA.set 0))))
$hyp "v'76" (TLA.subseteq a_Mhash_primea
(TLA.recordset "sigma" Idems "op" OpSet "arg" ArgSet "ret" ReturnSet))
$hyp "v'77" (TLA.subseteq (CandID (TLA.fapply u p)) (TLA.cup arith.N
(TLA.set 0)))
$hyp "v'79" (TLA.in a_UFhash_primea
a_UFIdunde_StateSeta)
$hyp "v'80" (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F. BOT)
NodeSet)))
$hyp "v'81" (/\ (TLA.bEx (IDUpdate (TLA.fapply u p)) ((newId) (= a_UFhash_primea
(TLA.record "rep" (TLA.fapply UF "rep") "id" newId))))
(TLA.cond (/\ (arith.lt (TLA.fapply a_iunde_uhash_primea p)
(TLA.fapply a_iunde_va p)) (arith.lt 0
(TLA.fapply a_iunde_uhash_primea p))) (/\ (= a_rethash_primea
(TLA.except ret p F.)) (= a_pchash_primea (TLA.except pc p "SR"))
(= a_Mhash_primea
(TLA.subsetOf (TLA.recordset "sigma" Idems "op" OpSet "arg" ArgSet "ret" ReturnSet) ((t) (TLA.bEx M ((told) (/\ (= (TLA.fapply (TLA.fapply told "ret") p)
BOT) (= (TLA.fapply t "sigma") (TLA.fapply told "sigma"))
(= (TLA.fapply t "ret")
(TLA.except (TLA.fapply told "ret") p (TLA.cond (= (TLA.fapply (TLA.fapply told "sigma") (TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ 0)))
(TLA.fapply (TLA.fapply told "sigma") (TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))) T. F.)))
(= (TLA.fapply t "op") (TLA.fapply told "op")) (= (TLA.fapply t "arg")
(TLA.fapply told "arg"))))))))) (/\ (= a_rethash_primea ret)
(= a_pchash_primea (TLA.except pc p "S3")) (= a_Mhash_primea
M))))
$hyp "v'82" (= (TLA.fapply pc p) "S6")
$hyp "v'83" (= a_iunde_uhash_primea
(TLA.except a_iunde_ua p (TLA.cond (= (TLA.fapply (TLA.fapply UF "rep") (TLA.fapply u p))
(TLA.fapply u p)) (TLA.fapply (TLA.fapply UF "id") (TLA.fapply u p)) 0)))
$hyp "v'84" (= a_uhash_primea u)
$hyp "v'85" (= a_vhash_primea v)
$hyp "v'86" (= a_iunde_vhash_primea a_iunde_va)
$hyp "v'87" (= a_chash_primea a_ca)
$hyp "v'88" (= a_dhash_primea d)
$goal (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "S4" "S5" "S6" "SR")))
(TLA.in a_UFhash_primea a_UFIdunde_StateSeta) (TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES NodeSet)) (TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES NodeSet)) (TLA.in a_iunde_uhash_primea
(TLA.FuncSet PROCESSES (TLA.cup arith.N (TLA.set 0))))
(TLA.in a_iunde_vhash_primea (TLA.FuncSet PROCESSES (TLA.cup arith.N
(TLA.set 0)))) (TLA.in a_chash_primea (TLA.FuncSet PROCESSES NodeSet))
(TLA.in a_dhash_primea (TLA.FuncSet PROCESSES NodeSet))
(TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F. BOT) NodeSet)))
(TLA.subseteq a_Mhash_primea
(TLA.recordset "sigma" Idems "op" OpSet "arg" ArgSet "ret" ReturnSet)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((pc \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))&((UF \\in a_UFIdunde_StateSeta)&((u \\in FuncSet(PROCESSES, NodeSet))&((v \\in FuncSet(PROCESSES, NodeSet))&((a_iunde_ua \\in FuncSet(PROCESSES, (Nat \\cup {0})))&((a_iunde_va \\in FuncSet(PROCESSES, (Nat \\cup {0})))&((a_ca \\in FuncSet(PROCESSES, NodeSet))&((d \\in FuncSet(PROCESSES, NodeSet))&((ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))&(M \\subseteq [''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]))))))))))" (is "?z_hr&?z_hbi")
 using v'58 by blast
 have z_Hk:"(a_iunde_uhash_primea=except(a_iunde_ua, p, cond((((UF[''rep''])[(u[p])])=(u[p])), ((UF[''id''])[(u[p])]), 0)))" (is "_=?z_hdh")
 using v'83 by blast
 have z_Hl:"(a_uhash_primea=u)"
 using v'84 by blast
 have z_Hm:"(a_vhash_primea=v)"
 using v'85 by blast
 have z_Hn:"(a_iunde_vhash_primea=a_iunde_va)"
 using v'86 by blast
 have z_Ho:"(a_chash_primea=a_ca)"
 using v'87 by blast
 have z_Hp:"(a_dhash_primea=d)"
 using v'88 by blast
 have z_Hi:"(bEx(IDUpdate((u[p])), (\<lambda>newId. (a_UFhash_primea=(''rep'' :> ((UF[''rep''])) @@ ''id'' :> (newId)))))&cond((((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p]))), ((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg'']))))))))))))), ((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=M)))))" (is "?z_hdx&?z_hee")
 using v'81 by blast
 have z_Hd:"(a_iunde_uhash_primea \\in FuncSet(PROCESSES, (Nat \\cup {0})))" (is "?z_hd")
 using v'75 by blast
 have z_Hg:"(a_UFhash_primea \\in a_UFIdunde_StateSeta)" (is "?z_hg")
 using v'79 by blast
 have z_Hh:"(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))" (is "?z_hh")
 using v'80 by blast
 have z_He:"(a_Mhash_primea \\subseteq [''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)])" (is "?z_he")
 using v'76 by blast
 have zenon_L1_: "(\\A zenon_Vwa:((zenon_Vwa \\in PROCESSES)=>((pc[zenon_Vwa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))) ==> ((CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''})))) \\in PROCESSES) ==> (~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''})) ==> ((CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''})))) \\in DOMAIN(pc)) ==> (p~=(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))) ==> (a_pchash_primea=except(pc, p, ''SR'')) ==> FALSE" (is "?z_hgi ==> ?z_hgo ==> ?z_hgw ==> ?z_hgz ==> ?z_hhb ==> ?z_hep ==> FALSE")
 proof -
  assume z_Hgi:"?z_hgi" (is "\\A x : ?z_hhc(x)")
  assume z_Hgo:"?z_hgo"
  assume z_Hgw:"?z_hgw" (is "~?z_hgx")
  assume z_Hgz:"?z_hgz"
  assume z_Hhb:"?z_hhb" (is "_~=?z_hgp")
  assume z_Hep:"?z_hep" (is "_=?z_her")
  have z_Hhd: "?z_hhc(?z_hgp)" (is "_=>?z_hhe")
  by (rule zenon_all_0 [of "?z_hhc" "?z_hgp", OF z_Hgi])
  show FALSE
  proof (rule zenon_imply [OF z_Hhd])
   assume z_Hhf:"(~?z_hgo)"
   show FALSE
   by (rule notE [OF z_Hhf z_Hgo])
  next
   assume z_Hhe:"?z_hhe"
   show FALSE
   proof (rule notE [OF z_Hgw])
    have z_Hhg: "((pc[?z_hgp])=(a_pchash_primea[?z_hgp]))" (is "?z_hhh=?z_hgy")
    proof (rule zenon_nnpp [of "(?z_hhh=?z_hgy)"])
     assume z_Hhi:"(?z_hhh~=?z_hgy)"
     have z_Hhj: "(((isAFcn(a_pchash_primea)<=>isAFcn(?z_her))&(DOMAIN(a_pchash_primea)=DOMAIN(?z_her)))&(\\A zenon_Vptf:((a_pchash_primea[zenon_Vptf])=(?z_her[zenon_Vptf]))))" (is "?z_hhk&?z_hhr")
     by (rule zenon_funequal_0 [of "a_pchash_primea" "?z_her", OF z_Hep])
     have z_Hhr: "?z_hhr" (is "\\A x : ?z_hhw(x)")
     by (rule zenon_and_1 [OF z_Hhj])
     have z_Hhx: "?z_hhw(?z_hgp)" (is "_=?z_hhy")
     by (rule zenon_all_0 [of "?z_hhw" "?z_hgp", OF z_Hhr])
     show FALSE
     proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vafd. (?z_hgy=zenon_Vafd))" "pc" "p" "''SR''" "?z_hgp", OF z_Hhx])
      assume z_Hgz:"?z_hgz"
      assume z_Hic:"(p=?z_hgp)"
      assume z_Hid:"(?z_hgy=''SR'')" (is "_=?z_hbh")
      show FALSE
      by (rule notE [OF z_Hhb z_Hic])
     next
      assume z_Hgz:"?z_hgz"
      assume z_Hhb:"?z_hhb"
      assume z_Hie:"(?z_hgy=?z_hhh)"
      show FALSE
      by (rule zenon_eqsym [OF z_Hie z_Hhi])
     next
      assume z_Hif:"(~?z_hgz)"
      show FALSE
      by (rule notE [OF z_Hif z_Hgz])
     qed
    qed
    have z_Hgx: "?z_hgx"
    by (rule subst [where P="(\<lambda>zenon_Vbyl. (zenon_Vbyl \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))", OF z_Hhg], fact z_Hhe)
    thus "?z_hgx" .
   qed
  qed
 qed
 have zenon_L2_: "(\\A zenon_Vwa:((zenon_Vwa \\in PROCESSES)=>((pc[zenon_Vwa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))) ==> ((CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''})))) \\in PROCESSES) ==> (~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''})) ==> ((CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''})))) \\in DOMAIN(pc)) ==> (p~=(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))) ==> (a_pchash_primea=except(pc, p, ''S3'')) ==> FALSE" (is "?z_hgi ==> ?z_hgo ==> ?z_hgw ==> ?z_hgz ==> ?z_hhb ==> ?z_hgf ==> FALSE")
 proof -
  assume z_Hgi:"?z_hgi" (is "\\A x : ?z_hhc(x)")
  assume z_Hgo:"?z_hgo"
  assume z_Hgw:"?z_hgw" (is "~?z_hgx")
  assume z_Hgz:"?z_hgz"
  assume z_Hhb:"?z_hhb" (is "_~=?z_hgp")
  assume z_Hgf:"?z_hgf" (is "_=?z_hgg")
  have z_Hhd: "?z_hhc(?z_hgp)" (is "_=>?z_hhe")
  by (rule zenon_all_0 [of "?z_hhc" "?z_hgp", OF z_Hgi])
  show FALSE
  proof (rule zenon_imply [OF z_Hhd])
   assume z_Hhf:"(~?z_hgo)"
   show FALSE
   by (rule notE [OF z_Hhf z_Hgo])
  next
   assume z_Hhe:"?z_hhe"
   show FALSE
   proof (rule notE [OF z_Hgw])
    have z_Hhg: "((pc[?z_hgp])=(a_pchash_primea[?z_hgp]))" (is "?z_hhh=?z_hgy")
    proof (rule zenon_nnpp [of "(?z_hhh=?z_hgy)"])
     assume z_Hhi:"(?z_hhh~=?z_hgy)"
     have z_Hij: "(((isAFcn(a_pchash_primea)<=>isAFcn(?z_hgg))&(DOMAIN(a_pchash_primea)=DOMAIN(?z_hgg)))&(\\A zenon_Vif:((a_pchash_primea[zenon_Vif])=(?z_hgg[zenon_Vif]))))" (is "?z_hik&?z_hip")
     by (rule zenon_funequal_0 [of "a_pchash_primea" "?z_hgg", OF z_Hgf])
     have z_Hip: "?z_hip" (is "\\A x : ?z_hiu(x)")
     by (rule zenon_and_1 [OF z_Hij])
     have z_Hiv: "?z_hiu(?z_hgp)" (is "_=?z_hiw")
     by (rule zenon_all_0 [of "?z_hiu" "?z_hgp", OF z_Hip])
     show FALSE
     proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vafd. (?z_hgy=zenon_Vafd))" "pc" "p" "''S3''" "?z_hgp", OF z_Hiv])
      assume z_Hgz:"?z_hgz"
      assume z_Hic:"(p=?z_hgp)"
      assume z_Hix:"(?z_hgy=''S3'')" (is "_=?z_hbd")
      show FALSE
      by (rule notE [OF z_Hhb z_Hic])
     next
      assume z_Hgz:"?z_hgz"
      assume z_Hhb:"?z_hhb"
      assume z_Hie:"(?z_hgy=?z_hhh)"
      show FALSE
      by (rule zenon_eqsym [OF z_Hie z_Hhi])
     next
      assume z_Hif:"(~?z_hgz)"
      show FALSE
      by (rule notE [OF z_Hif z_Hgz])
     qed
    qed
    have z_Hgx: "?z_hgx"
    by (rule subst [where P="(\<lambda>zenon_Vbyl. (zenon_Vbyl \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))", OF z_Hhg], fact z_Hhe)
    thus "?z_hgx" .
   qed
  qed
 qed
 assume z_Hq:"(~((a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))&(?z_hg&((a_uhash_primea \\in FuncSet(PROCESSES, NodeSet))&((a_vhash_primea \\in FuncSet(PROCESSES, NodeSet))&(?z_hd&((a_iunde_vhash_primea \\in FuncSet(PROCESSES, (Nat \\cup {0})))&((a_chash_primea \\in FuncSet(PROCESSES, NodeSet))&((a_dhash_primea \\in FuncSet(PROCESSES, NodeSet))&(?z_hh&?z_he))))))))))" (is "~(?z_hiz&?z_hja)")
 have z_Hr: "?z_hr"
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hbi: "?z_hbi" (is "?z_hbj&?z_hbm")
 by (rule zenon_and_1 [OF z_Ha])
 have z_Hbm: "?z_hbm" (is "?z_hbn&?z_hbr")
 by (rule zenon_and_1 [OF z_Hbi])
 have z_Hbn: "?z_hbn"
 by (rule zenon_and_0 [OF z_Hbm])
 have z_Hbr: "?z_hbr" (is "?z_hbs&?z_hbu")
 by (rule zenon_and_1 [OF z_Hbm])
 have z_Hbs: "?z_hbs"
 by (rule zenon_and_0 [OF z_Hbr])
 have z_Hbu: "?z_hbu" (is "?z_hbv&?z_hcc")
 by (rule zenon_and_1 [OF z_Hbr])
 have z_Hbv: "?z_hbv"
 by (rule zenon_and_0 [OF z_Hbu])
 have z_Hcc: "?z_hcc" (is "?z_hcd&?z_hcf")
 by (rule zenon_and_1 [OF z_Hbu])
 have z_Hcd: "?z_hcd"
 by (rule zenon_and_0 [OF z_Hcc])
 have z_Hcf: "?z_hcf" (is "?z_hcg&?z_hci")
 by (rule zenon_and_1 [OF z_Hcc])
 have z_Hcg: "?z_hcg"
 by (rule zenon_and_0 [OF z_Hcf])
 have z_Hci: "?z_hci" (is "?z_hcj&?z_hcl")
 by (rule zenon_and_1 [OF z_Hcf])
 have z_Hcj: "?z_hcj"
 by (rule zenon_and_0 [OF z_Hci])
 have z_Hee: "?z_hee"
 by (rule zenon_and_1 [OF z_Hi])
 show FALSE
 proof (rule zenon_notand [OF z_Hq])
  assume z_Hjn:"(~?z_hiz)"
  have z_Hjo: "(DOMAIN(pc)=PROCESSES)" (is "?z_hha=_")
  by (rule zenon_in_funcset_1 [of "pc" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hr])
  have z_Hjp: "(DOMAIN(a_iunde_ua)=PROCESSES)" (is "?z_hjq=_")
  by (rule zenon_in_funcset_1 [of "a_iunde_ua" "PROCESSES" "(Nat \\cup {0})", OF z_Hbv])
  show FALSE
  proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p])))" "((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" "((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=M)))", OF z_Hee])
   assume z_Hef:"(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p])))" (is "?z_heg&?z_hej")
   assume z_Hek:"((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" (is "?z_hel&?z_heo")
   have z_Heo: "?z_heo" (is "?z_hep&?z_hes")
   by (rule zenon_and_1 [OF z_Hek])
   have z_Hep: "?z_hep" (is "_=?z_her")
   by (rule zenon_and_0 [OF z_Heo])
   have z_Hjt: "(\\A zenon_Vr:((zenon_Vr \\in PROCESSES)=>((a_iunde_uhash_primea[zenon_Vr]) \\in (Nat \\cup {0}))))" (is "\\A x : ?z_hjz(x)")
   by (rule zenon_in_funcset_2 [of "a_iunde_uhash_primea" "PROCESSES" "(Nat \\cup {0})", OF z_Hd])
   have z_Hjo: "(?z_hha=PROCESSES)"
   by (rule zenon_in_funcset_1 [of "pc" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hr])
   have z_Hgi: "(\\A zenon_Vwa:((zenon_Vwa \\in PROCESSES)=>((pc[zenon_Vwa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''})))" (is "\\A x : ?z_hhc(x)")
   by (rule zenon_in_funcset_2 [of "pc" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hr])
   show FALSE
   proof (rule zenon_notin_funcset [of "a_pchash_primea" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hjn])
    assume z_Hka:"(~isAFcn(a_pchash_primea))" (is "~?z_hhm")
    have z_Hkb: "(~isAFcn(?z_her))" (is "~?z_hhn")
    by (rule subst [where P="(\<lambda>zenon_Vatf. (~isAFcn(zenon_Vatf)))", OF z_Hep z_Hka])
    show FALSE
    by (rule zenon_notisafcn_except [of "pc" "p" "''SR''", OF z_Hkb])
   next
    assume z_Hkg:"(DOMAIN(a_pchash_primea)~=PROCESSES)" (is "?z_hhp~=_")
    have z_Hkh: "(DOMAIN(?z_her)~=PROCESSES)" (is "?z_hhq~=_")
    by (rule subst [where P="(\<lambda>zenon_Vetf. (DOMAIN(zenon_Vetf)~=PROCESSES))", OF z_Hep z_Hkg])
    have z_Hkm: "(?z_hha~=PROCESSES)"
    by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vdtf. (zenon_Vdtf~=PROCESSES))" "pc" "p" "''SR''", OF z_Hkh])
    show FALSE
    by (rule notE [OF z_Hkm z_Hjo])
   next
    assume z_Hkq:"(~(\\A zenon_Vbc:((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))" (is "~(\\A x : ?z_hks(x))")
    have z_Hkt: "(\\E zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))" (is "\\E x : ?z_hku(x)")
    by (rule zenon_notallex_0 [of "?z_hks", OF z_Hkq])
    have z_Hkv: "?z_hku((CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''})))))" (is "~(?z_hgo=>?z_hgx)")
    by (rule zenon_ex_choose_0 [of "?z_hku", OF z_Hkt])
    have z_Hgo: "?z_hgo"
    by (rule zenon_notimply_0 [OF z_Hkv])
    have z_Hgw: "(~?z_hgx)"
    by (rule zenon_notimply_1 [OF z_Hkv])
    have z_Hkw: "(~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hkx")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])" "''0''" "{''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hgw])
    have z_Hkz: "(~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hla")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])" "''F1''" "{''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hkw])
    have z_Hlc: "(~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hld")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])" "''FR''" "{''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hkz])
    have z_Hlf: "(~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hlg")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])" "''U1''" "{''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hlc])
    have z_Hli: "(~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hlj")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])" "''UR''" "{''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hlf])
    have z_Hll: "(~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hlm")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])" "''S1''" "{''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hli])
    have z_Hlo: "(~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hlp")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])" "''S2''" "{''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hll])
    have z_Hlr: "(~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hls")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])" "''S3''" "{''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hlo])
    have z_Hlu: "(~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''S5'', ''S6'', ''SR''}))" (is "~?z_hlv")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])" "''S4''" "{''S5'', ''S6'', ''SR''}", OF z_Hlr])
    have z_Hlx: "(~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''S6'', ''SR''}))" (is "~?z_hly")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])" "''S5''" "{''S6'', ''SR''}", OF z_Hlu])
    have z_Hma: "(~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''SR''}))" (is "~?z_hmb")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])" "''S6''" "{''SR''}", OF z_Hlx])
    have z_Hmd: "((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])~=''SR'')" (is "?z_hgy~=?z_hbh")
    by (rule zenon_notin_addElt_0 [of "?z_hgy" "?z_hbh" "{}", OF z_Hma])
    have z_Hgz: "((CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ?z_hbh})))) \\in ?z_hha)" (is "?z_hgz")
    by (rule ssubst [where P="(\<lambda>zenon_Vrm. ((CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ?z_hbh})))) \\in zenon_Vrm))", OF z_Hjo z_Hgo])
    have z_Hmi: "((CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ?z_hbh})))) \\in ?z_hjq)" (is "?z_hmi")
    by (rule ssubst [where P="(\<lambda>zenon_Vrm. ((CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ?z_hbh})))) \\in zenon_Vrm))", OF z_Hjp z_Hgo])
    have z_Hmj: "?z_hjz((CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ?z_hbh})))))" (is "_=>?z_hmk")
    by (rule zenon_all_0 [of "?z_hjz" "(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ?z_hbh}))))", OF z_Hjt])
    show FALSE
    proof (rule zenon_imply [OF z_Hmj])
     assume z_Hhf:"(~?z_hgo)"
     show FALSE
     by (rule notE [OF z_Hhf z_Hgo])
    next
     assume z_Hmk:"?z_hmk"
     have z_Hml: "((?z_hdh[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ?z_hbh}))))]) \\in (Nat \\cup {0}))" (is "?z_hml")
     by (rule subst [where P="(\<lambda>zenon_Vbxl. ((zenon_Vbxl[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ?z_hbh}))))]) \\in (Nat \\cup {0})))", OF z_Hk z_Hmk])
     show FALSE
     proof (rule zenon_fapplyexcept [of "(\<lambda>x. (x \\in (Nat \\cup {0})))" "a_iunde_ua" "p" "cond((((UF[''rep''])[(u[p])])=(u[p])), ((UF[''id''])[(u[p])]), 0)" "(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ?z_hbh}))))", OF z_Hml])
      assume z_Hmi:"?z_hmi"
      assume z_Hic:"(p=(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ?z_hbh})))))" (is "_=?z_hgp")
      assume z_Hmu:"(cond((((UF[''rep''])[(u[p])])=(u[p])), ((UF[''id''])[(u[p])]), 0) \\in (Nat \\cup {0}))" (is "?z_hmu")
      have z_Hhj: "(((isAFcn(a_pchash_primea)<=>isAFcn(?z_her))&(DOMAIN(a_pchash_primea)=DOMAIN(?z_her)))&(\\A zenon_Vptf:((a_pchash_primea[zenon_Vptf])=(?z_her[zenon_Vptf]))))" (is "?z_hhk&?z_hhr")
      by (rule zenon_funequal_0 [of "a_pchash_primea" "?z_her", OF z_Hep])
      have z_Hhr: "?z_hhr" (is "\\A x : ?z_hhw(x)")
      by (rule zenon_and_1 [OF z_Hhj])
      have z_Hhx: "?z_hhw(?z_hgp)" (is "_=?z_hhy")
      by (rule zenon_all_0 [of "?z_hhw" "?z_hgp", OF z_Hhr])
      show FALSE
      proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vafd. (?z_hgy=zenon_Vafd))" "pc" "p" "?z_hbh" "?z_hgp", OF z_Hhx])
       assume z_Hgz:"?z_hgz"
       assume z_Hic:"(p=?z_hgp)"
       assume z_Hid:"(?z_hgy=?z_hbh)"
       show FALSE
       by (rule notE [OF z_Hmd z_Hid])
      next
       assume z_Hgz:"?z_hgz"
       assume z_Hhb:"(p~=?z_hgp)"
       assume z_Hie:"(?z_hgy=(pc[?z_hgp]))" (is "_=?z_hhh")
       show FALSE
       by (rule notE [OF z_Hhb z_Hic])
      next
       assume z_Hif:"(~?z_hgz)"
       show FALSE
       by (rule notE [OF z_Hif z_Hgz])
      qed
     next
      assume z_Hmi:"?z_hmi"
      assume z_Hhb:"(p~=(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ?z_hbh})))))" (is "_~=?z_hgp")
      assume z_Hmv:"((a_iunde_ua[?z_hgp]) \\in (Nat \\cup {0}))" (is "?z_hmv")
      show FALSE
      by (rule zenon_L1_ [OF z_Hgi z_Hgo z_Hgw z_Hgz z_Hhb z_Hep])
     next
      assume z_Hmx:"(~?z_hmi)"
      show FALSE
      by (rule notE [OF z_Hmx z_Hmi])
     qed
    qed
   qed
  next
   assume z_Hmy:"(~(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p]))))" (is "~(?z_heg&?z_hej)")
   assume z_Hgc:"((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=M)))" (is "?z_hgd&?z_hge")
   have z_Hge: "?z_hge" (is "?z_hgf&?z_hgh")
   by (rule zenon_and_1 [OF z_Hgc])
   have z_Hgf: "?z_hgf" (is "_=?z_hgg")
   by (rule zenon_and_0 [OF z_Hge])
   have z_Hjt: "(\\A zenon_Vr:((zenon_Vr \\in PROCESSES)=>((a_iunde_uhash_primea[zenon_Vr]) \\in (Nat \\cup {0}))))" (is "\\A x : ?z_hjz(x)")
   by (rule zenon_in_funcset_2 [of "a_iunde_uhash_primea" "PROCESSES" "(Nat \\cup {0})", OF z_Hd])
   have z_Hjo: "(?z_hha=PROCESSES)"
   by (rule zenon_in_funcset_1 [of "pc" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hr])
   have z_Hgi: "(\\A zenon_Vwa:((zenon_Vwa \\in PROCESSES)=>((pc[zenon_Vwa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''})))" (is "\\A x : ?z_hhc(x)")
   by (rule zenon_in_funcset_2 [of "pc" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hr])
   show FALSE
   proof (rule zenon_notin_funcset [of "a_pchash_primea" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hjn])
    assume z_Hka:"(~isAFcn(a_pchash_primea))" (is "~?z_hhm")
    have z_Hmz: "(~isAFcn(?z_hgg))" (is "~?z_him")
    by (rule subst [where P="(\<lambda>zenon_Vatf. (~isAFcn(zenon_Vatf)))", OF z_Hgf z_Hka])
    show FALSE
    by (rule zenon_notisafcn_except [of "pc" "p" "''S3''", OF z_Hmz])
   next
    assume z_Hkg:"(DOMAIN(a_pchash_primea)~=PROCESSES)" (is "?z_hhp~=_")
    have z_Hna: "(DOMAIN(?z_hgg)~=PROCESSES)" (is "?z_hio~=_")
    by (rule subst [where P="(\<lambda>zenon_Vetf. (DOMAIN(zenon_Vetf)~=PROCESSES))", OF z_Hgf z_Hkg])
    have z_Hkm: "(?z_hha~=PROCESSES)"
    by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vdtf. (zenon_Vdtf~=PROCESSES))" "pc" "p" "''S3''", OF z_Hna])
    show FALSE
    by (rule notE [OF z_Hkm z_Hjo])
   next
    assume z_Hkq:"(~(\\A zenon_Vbc:((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))" (is "~(\\A x : ?z_hks(x))")
    have z_Hkt: "(\\E zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))" (is "\\E x : ?z_hku(x)")
    by (rule zenon_notallex_0 [of "?z_hks", OF z_Hkq])
    have z_Hkv: "?z_hku((CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''})))))" (is "~(?z_hgo=>?z_hgx)")
    by (rule zenon_ex_choose_0 [of "?z_hku", OF z_Hkt])
    have z_Hgo: "?z_hgo"
    by (rule zenon_notimply_0 [OF z_Hkv])
    have z_Hgw: "(~?z_hgx)"
    by (rule zenon_notimply_1 [OF z_Hkv])
    have z_Hkw: "(~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hkx")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])" "''0''" "{''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hgw])
    have z_Hkz: "(~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hla")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])" "''F1''" "{''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hkw])
    have z_Hlc: "(~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hld")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])" "''FR''" "{''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hkz])
    have z_Hlf: "(~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hlg")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])" "''U1''" "{''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hlc])
    have z_Hli: "(~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hlj")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])" "''UR''" "{''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hlf])
    have z_Hll: "(~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hlm")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])" "''S1''" "{''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hli])
    have z_Hlo: "(~((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in {''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))" (is "~?z_hlp")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])" "''S2''" "{''S3'', ''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hll])
    have z_Hnb: "((a_pchash_primea[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''S4'', ''S5'', ''S6'', ''SR''}))))])~=''S3'')" (is "?z_hgy~=?z_hbd")
    by (rule zenon_notin_addElt_0 [of "?z_hgy" "?z_hbd" "{''S4'', ''S5'', ''S6'', ''SR''}", OF z_Hlo])
    have z_Hgz: "((CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hbd, ''S4'', ''S5'', ''S6'', ''SR''})))) \\in ?z_hha)" (is "?z_hgz")
    by (rule ssubst [where P="(\<lambda>zenon_Vrm. ((CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hbd, ''S4'', ''S5'', ''S6'', ''SR''})))) \\in zenon_Vrm))", OF z_Hjo z_Hgo])
    have z_Hmi: "((CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hbd, ''S4'', ''S5'', ''S6'', ''SR''})))) \\in ?z_hjq)" (is "?z_hmi")
    by (rule ssubst [where P="(\<lambda>zenon_Vrm. ((CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hbd, ''S4'', ''S5'', ''S6'', ''SR''})))) \\in zenon_Vrm))", OF z_Hjp z_Hgo])
    have z_Hmj: "?z_hjz((CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hbd, ''S4'', ''S5'', ''S6'', ''SR''})))))" (is "_=>?z_hmk")
    by (rule zenon_all_0 [of "?z_hjz" "(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hbd, ''S4'', ''S5'', ''S6'', ''SR''}))))", OF z_Hjt])
    show FALSE
    proof (rule zenon_imply [OF z_Hmj])
     assume z_Hhf:"(~?z_hgo)"
     show FALSE
     by (rule notE [OF z_Hhf z_Hgo])
    next
     assume z_Hmk:"?z_hmk"
     have z_Hml: "((?z_hdh[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hbd, ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in (Nat \\cup {0}))" (is "?z_hml")
     by (rule subst [where P="(\<lambda>zenon_Vbxl. ((zenon_Vbxl[(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hbd, ''S4'', ''S5'', ''S6'', ''SR''}))))]) \\in (Nat \\cup {0})))", OF z_Hk z_Hmk])
     show FALSE
     proof (rule zenon_fapplyexcept [of "(\<lambda>x. (x \\in (Nat \\cup {0})))" "a_iunde_ua" "p" "cond((((UF[''rep''])[(u[p])])=(u[p])), ((UF[''id''])[(u[p])]), 0)" "(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hbd, ''S4'', ''S5'', ''S6'', ''SR''}))))", OF z_Hml])
      assume z_Hmi:"?z_hmi"
      assume z_Hic:"(p=(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hbd, ''S4'', ''S5'', ''S6'', ''SR''})))))" (is "_=?z_hgp")
      assume z_Hmu:"(cond((((UF[''rep''])[(u[p])])=(u[p])), ((UF[''id''])[(u[p])]), 0) \\in (Nat \\cup {0}))" (is "?z_hmu")
      have z_Hij: "(((isAFcn(a_pchash_primea)<=>isAFcn(?z_hgg))&(DOMAIN(a_pchash_primea)=DOMAIN(?z_hgg)))&(\\A zenon_Vif:((a_pchash_primea[zenon_Vif])=(?z_hgg[zenon_Vif]))))" (is "?z_hik&?z_hip")
      by (rule zenon_funequal_0 [of "a_pchash_primea" "?z_hgg", OF z_Hgf])
      have z_Hip: "?z_hip" (is "\\A x : ?z_hiu(x)")
      by (rule zenon_and_1 [OF z_Hij])
      have z_Hiv: "?z_hiu(?z_hgp)" (is "_=?z_hiw")
      by (rule zenon_all_0 [of "?z_hiu" "?z_hgp", OF z_Hip])
      show FALSE
      proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vafd. (?z_hgy=zenon_Vafd))" "pc" "p" "?z_hbd" "?z_hgp", OF z_Hiv])
       assume z_Hgz:"?z_hgz"
       assume z_Hic:"(p=?z_hgp)"
       assume z_Hix:"(?z_hgy=?z_hbd)"
       show FALSE
       by (rule notE [OF z_Hnb z_Hix])
      next
       assume z_Hgz:"?z_hgz"
       assume z_Hhb:"(p~=?z_hgp)"
       assume z_Hie:"(?z_hgy=(pc[?z_hgp]))" (is "_=?z_hhh")
       show FALSE
       by (rule notE [OF z_Hhb z_Hic])
      next
       assume z_Hif:"(~?z_hgz)"
       show FALSE
       by (rule notE [OF z_Hif z_Hgz])
      qed
     next
      assume z_Hmi:"?z_hmi"
      assume z_Hhb:"(p~=(CHOOSE zenon_Vbc:(~((zenon_Vbc \\in PROCESSES)=>((a_pchash_primea[zenon_Vbc]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hbd, ''S4'', ''S5'', ''S6'', ''SR''})))))" (is "_~=?z_hgp")
      assume z_Hmv:"((a_iunde_ua[?z_hgp]) \\in (Nat \\cup {0}))" (is "?z_hmv")
      show FALSE
      by (rule zenon_L2_ [OF z_Hgi z_Hgo z_Hgw z_Hgz z_Hhb z_Hgf])
     next
      assume z_Hmx:"(~?z_hmi)"
      show FALSE
      by (rule notE [OF z_Hmx z_Hmi])
     qed
    qed
   qed
  qed
 next
  assume z_Hnc:"(~?z_hja)" (is "~(_&?z_hjb)")
  show FALSE
  proof (rule zenon_notand [OF z_Hnc])
   assume z_Hnd:"(~?z_hg)"
   show FALSE
   by (rule notE [OF z_Hnd z_Hg])
  next
   assume z_Hne:"(~?z_hjb)" (is "~(?z_hjc&?z_hjd)")
   show FALSE
   proof (rule zenon_notand [OF z_Hne])
    assume z_Hnf:"(~?z_hjc)"
    have z_Hng: "(~?z_hbn)"
    by (rule subst [where P="(\<lambda>zenon_Vsxl. (~(zenon_Vsxl \\in FuncSet(PROCESSES, NodeSet))))", OF z_Hl z_Hnf])
    show FALSE
    by (rule notE [OF z_Hng z_Hbn])
   next
    assume z_Hnl:"(~?z_hjd)" (is "~(?z_hje&?z_hjf)")
    show FALSE
    proof (rule zenon_notand [OF z_Hnl])
     assume z_Hnm:"(~?z_hje)"
     have z_Hnn: "(~?z_hbs)"
     by (rule subst [where P="(\<lambda>zenon_Vsxl. (~(zenon_Vsxl \\in FuncSet(PROCESSES, NodeSet))))", OF z_Hm z_Hnm])
     show FALSE
     by (rule notE [OF z_Hnn z_Hbs])
    next
     assume z_Hno:"(~?z_hjf)" (is "~(_&?z_hjg)")
     show FALSE
     proof (rule zenon_notand [OF z_Hno])
      assume z_Hnp:"(~?z_hd)"
      show FALSE
      by (rule notE [OF z_Hnp z_Hd])
     next
      assume z_Hnq:"(~?z_hjg)" (is "~(?z_hjh&?z_hji)")
      show FALSE
      proof (rule zenon_notand [OF z_Hnq])
       assume z_Hnr:"(~?z_hjh)"
       have z_Hns: "(~?z_hcd)"
       by (rule subst [where P="(\<lambda>zenon_Vwxl. (~(zenon_Vwxl \\in FuncSet(PROCESSES, (Nat \\cup {0})))))", OF z_Hn z_Hnr])
       show FALSE
       by (rule notE [OF z_Hns z_Hcd])
      next
       assume z_Hnx:"(~?z_hji)" (is "~(?z_hjj&?z_hjk)")
       show FALSE
       proof (rule zenon_notand [OF z_Hnx])
        assume z_Hny:"(~?z_hjj)"
        have z_Hnz: "(~?z_hcg)"
        by (rule subst [where P="(\<lambda>zenon_Vsxl. (~(zenon_Vsxl \\in FuncSet(PROCESSES, NodeSet))))", OF z_Ho z_Hny])
        show FALSE
        by (rule notE [OF z_Hnz z_Hcg])
       next
        assume z_Hoa:"(~?z_hjk)" (is "~(?z_hjl&?z_hjm)")
        show FALSE
        proof (rule zenon_notand [OF z_Hoa])
         assume z_Hob:"(~?z_hjl)"
         have z_Hoc: "(~?z_hcj)"
         by (rule subst [where P="(\<lambda>zenon_Vsxl. (~(zenon_Vsxl \\in FuncSet(PROCESSES, NodeSet))))", OF z_Hp z_Hob])
         show FALSE
         by (rule notE [OF z_Hoc z_Hcj])
        next
         assume z_Hod:"(~?z_hjm)"
         show FALSE
         proof (rule zenon_notand [OF z_Hod])
          assume z_Hoe:"(~?z_hh)"
          show FALSE
          by (rule notE [OF z_Hoe z_Hh])
         next
          assume z_Hof:"(~?z_he)"
          show FALSE
          by (rule notE [OF z_Hof z_He])
         qed
        qed
       qed
      qed
     qed
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 88"; *} qed
lemma ob'92:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes UF UF'
fixes u u'
fixes v v'
fixes a_iunde_ua a_iunde_ua'
fixes a_iunde_va a_iunde_va'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition NodeSet suppressed *)
(* usable definition varlist suppressed *)
(* usable definition Idems suppressed *)
(* usable definition NodeToIdFuncs suppressed *)
(* usable definition UFId_StateSet suppressed *)
(* usable definition SmallerRep suppressed *)
(* usable definition LargerRep suppressed *)
(* usable definition URep suppressed *)
(* usable definition CandID suppressed *)
(* usable definition IDUpdate suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitUF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition UFUnite suppressed *)
(* usable definition MetaConfigUnite suppressed *)
(* usable definition Init suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition S4 suppressed *)
(* usable definition S5 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition UFSSpec suppressed *)
(* usable definition PCTypeOK suppressed *)
(* usable definition UFTypeOK suppressed *)
(* usable definition uTypeOK suppressed *)
(* usable definition vTypeOK suppressed *)
(* usable definition i_uTypeOK suppressed *)
(* usable definition i_vTypeOK suppressed *)
(* usable definition cTypeOK suppressed *)
(* usable definition dTypeOK suppressed *)
(* usable definition retTypeOK suppressed *)
assumes v'64: "((PCTypeOK) & (UFTypeOK) & (uTypeOK) & (vTypeOK) & (a_iunde_uTypeOKa) & (a_iunde_vTypeOKa) & (cTypeOK) & (dTypeOK) & (retTypeOK) & (((M) \<subseteq> ([''sigma'' : (Idems), ''op'' : ([(PROCESSES) \<rightarrow> ({(''F''), (''U''), (''S''), (BOT)})]), ''arg'' : ([(PROCESSES) \<rightarrow> ((((({(BOT)}) \<union> (NodeSet))) \<union> (((NodeSet) \<times> (NodeSet)))))]), ''ret'' : ([(PROCESSES) \<rightarrow> ((({(ACK), (BOT), (TRUE), (FALSE)}) \<union> (NodeSet)))])]))))"
fixes p
assumes p_in : "(p \<in> (PROCESSES))"
assumes v'66: "((Step ((p))))"
assumes v'81: "((((a_iunde_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))])))"
assumes v'84: "((\<exists> newId \<in> ((IDUpdate ((fapply ((u), (p)))))) : ((((a_UFhash_primea :: c)) = (((''rep'' :> (fapply ((UF), (''rep'')))) @@ (''id'' :> (newId))))))) & (cond(((((less ((fapply (((a_iunde_uhash_primea :: c)), (p))), (fapply ((a_iunde_va), (p)))))) \<and> ((greater ((fapply (((a_iunde_uhash_primea :: c)), (p))), ((0))))))), (((((a_rethash_primea :: c)) = ([(ret) EXCEPT ![(p)] = (FALSE)]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''SR'')]))) & ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : (Idems), ''op'' : ([(PROCESSES) \<rightarrow> ({(''F''), (''U''), (''S''), (BOT)})]), ''arg'' : ([(PROCESSES) \<rightarrow> ((((({(BOT)}) \<union> (NodeSet))) \<union> (((NodeSet) \<times> (NodeSet)))))]), ''ret'' : ([(PROCESSES) \<rightarrow> ((({(ACK), (BOT), (TRUE), (FALSE)}) \<union> (NodeSet)))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''ret''))) = ([(fapply ((told), (''ret''))) EXCEPT ![(p)] = (cond((((fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[0])))))) = (fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[Succ[0]])))))))), (TRUE), (FALSE)))]))) & (((fapply ((t), (''op''))) = (fapply ((told), (''op''))))) & (((fapply ((t), (''arg''))) = (fapply ((told), (''arg'')))))))))))), (((((a_rethash_primea :: c)) = (ret))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''S3'')]))) & ((((a_Mhash_primea :: c)) = (M)))))))"
assumes v'85: "(((fapply ((pc), (p))) = (''S6'')))"
assumes v'86: "((((a_iunde_uhash_primea :: c)) = ([(a_iunde_ua) EXCEPT ![(p)] = (cond((((fapply ((fapply ((UF), (''rep''))), (fapply ((u), (p))))) = (fapply ((u), (p))))), (fapply ((fapply ((UF), (''id''))), (fapply ((u), (p))))), ((0))))])))"
assumes v'87: "((((a_uhash_primea :: c)) = (u)))"
assumes v'88: "((((a_vhash_primea :: c)) = (v)))"
assumes v'89: "((((a_iunde_vhash_primea :: c)) = (a_iunde_va)))"
assumes v'90: "((((a_chash_primea :: c)) = (a_ca)))"
assumes v'91: "((((a_dhash_primea :: c)) = (d)))"
shows "((((a_Mhash_primea :: c)) \<subseteq> ([''sigma'' : (Idems), ''op'' : ([(PROCESSES) \<rightarrow> ({(''F''), (''U''), (''S''), (BOT)})]), ''arg'' : ([(PROCESSES) \<rightarrow> ((((({(BOT)}) \<union> (NodeSet))) \<union> (((NodeSet) \<times> (NodeSet)))))]), ''ret'' : ([(PROCESSES) \<rightarrow> ((({(ACK), (BOT), (TRUE), (FALSE)}) \<union> (NodeSet)))])])))"(is "PROP ?ob'92")
proof -
ML_command {* writeln "*** TLAPS ENTER 92"; *}
show "PROP ?ob'92"

(* BEGIN ZENON INPUT
;; file=UFSTypeOK.tlaps/tlapm_e1263a.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >UFSTypeOK.tlaps/tlapm_e1263a.znn.out
;; obligation #92
$hyp "v'64" (/\ PCTypeOK UFTypeOK uTypeOK vTypeOK a_iunde_uTypeOKa
a_iunde_vTypeOKa cTypeOK dTypeOK retTypeOK (TLA.subseteq M
(TLA.recordset "sigma" Idems "op" (TLA.FuncSet PROCESSES (TLA.set "F" "U" "S" BOT)) "arg" (TLA.FuncSet PROCESSES (TLA.cup (TLA.cup (TLA.set BOT)
NodeSet)
(TLA.prod NodeSet NodeSet))) "ret" (TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK BOT T. F.)
NodeSet)))))
$hyp "p_in" (TLA.in p PROCESSES)
$hyp "v'66" (Step p)
$hyp "v'81" (TLA.in a_iunde_uhash_primea
(TLA.FuncSet PROCESSES (TLA.cup arith.N
(TLA.set 0))))
$hyp "v'84" (/\ (TLA.bEx (IDUpdate (TLA.fapply u p)) ((newId) (= a_UFhash_primea
(TLA.record "rep" (TLA.fapply UF "rep") "id" newId))))
(TLA.cond (/\ (arith.lt (TLA.fapply a_iunde_uhash_primea p)
(TLA.fapply a_iunde_va p)) (arith.lt 0
(TLA.fapply a_iunde_uhash_primea p))) (/\ (= a_rethash_primea
(TLA.except ret p F.)) (= a_pchash_primea (TLA.except pc p "SR"))
(= a_Mhash_primea
(TLA.subsetOf (TLA.recordset "sigma" Idems "op" (TLA.FuncSet PROCESSES (TLA.set "F" "U" "S" BOT)) "arg" (TLA.FuncSet PROCESSES (TLA.cup (TLA.cup (TLA.set BOT)
NodeSet)
(TLA.prod NodeSet NodeSet))) "ret" (TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK BOT T. F.)
NodeSet))) ((t) (TLA.bEx M ((told) (/\ (= (TLA.fapply (TLA.fapply told "ret") p)
BOT) (= (TLA.fapply t "sigma") (TLA.fapply told "sigma"))
(= (TLA.fapply t "ret")
(TLA.except (TLA.fapply told "ret") p (TLA.cond (= (TLA.fapply (TLA.fapply told "sigma") (TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ 0)))
(TLA.fapply (TLA.fapply told "sigma") (TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))) T. F.)))
(= (TLA.fapply t "op") (TLA.fapply told "op")) (= (TLA.fapply t "arg")
(TLA.fapply told "arg"))))))))) (/\ (= a_rethash_primea ret)
(= a_pchash_primea (TLA.except pc p "S3")) (= a_Mhash_primea
M))))
$hyp "v'85" (= (TLA.fapply pc p) "S6")
$hyp "v'86" (= a_iunde_uhash_primea
(TLA.except a_iunde_ua p (TLA.cond (= (TLA.fapply (TLA.fapply UF "rep") (TLA.fapply u p))
(TLA.fapply u p)) (TLA.fapply (TLA.fapply UF "id") (TLA.fapply u p)) 0)))
$hyp "v'87" (= a_uhash_primea u)
$hyp "v'88" (= a_vhash_primea v)
$hyp "v'89" (= a_iunde_vhash_primea a_iunde_va)
$hyp "v'90" (= a_chash_primea a_ca)
$hyp "v'91" (= a_dhash_primea d)
$goal (TLA.subseteq a_Mhash_primea
(TLA.recordset "sigma" Idems "op" (TLA.FuncSet PROCESSES (TLA.set "F" "U" "S" BOT)) "arg" (TLA.FuncSet PROCESSES (TLA.cup (TLA.cup (TLA.set BOT)
NodeSet)
(TLA.prod NodeSet NodeSet))) "ret" (TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK BOT T. F.)
NodeSet))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(PCTypeOK&(UFTypeOK&(uTypeOK&(vTypeOK&(a_iunde_uTypeOKa&(a_iunde_vTypeOKa&(cTypeOK&(dTypeOK&(retTypeOK&(M \\subseteq [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))))))))" (is "_&?z_ho")
 using v'64 by blast
 have z_He:"(bEx(IDUpdate((u[p])), (\<lambda>newId. (a_UFhash_primea=(''rep'' :> ((UF[''rep''])) @@ ''id'' :> (newId)))))&cond((((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p]))), ((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg'']))))))))))))), ((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=M)))))" (is "?z_hcf&?z_hct")
 using v'84 by blast
 have zenon_L1_: "((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg'']))))))))))))) ==> (~((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])) ==> ((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) \\in a_Mhash_primea) ==> FALSE" (is "?z_hdc ==> ?z_hfe ==> ?z_hfm ==> FALSE")
 proof -
  assume z_Hdc:"?z_hdc" (is "?z_hdd&?z_hdh")
  assume z_Hfe:"?z_hfe" (is "~?z_hff")
  assume z_Hfm:"?z_hfm"
  have z_Hdh: "?z_hdh" (is "?z_hdi&?z_hdn")
  by (rule zenon_and_1 [OF z_Hdc])
  have z_Hdn: "?z_hdn" (is "_=?z_hdp")
  by (rule zenon_and_1 [OF z_Hdh])
  have z_Hfn: "(\\A zenon_Vse:((zenon_Vse \\in a_Mhash_primea)<=>(zenon_Vse \\in ?z_hdp)))" (is "\\A x : ?z_hfs(x)")
  by (rule zenon_setequal_0 [of "a_Mhash_primea" "?z_hdp", OF z_Hdn])
  have z_Hft: "?z_hfs((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))))" (is "_<=>?z_hfu")
  by (rule zenon_all_0 [of "?z_hfs" "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))", OF z_Hfn])
  show FALSE
  proof (rule zenon_equiv [OF z_Hft])
   assume z_Hfv:"(~?z_hfm)"
   assume z_Hfw:"(~?z_hfu)"
   show FALSE
   by (rule notE [OF z_Hfv z_Hfm])
  next
   assume z_Hfm:"?z_hfm"
   assume z_Hfu:"?z_hfu"
   have z_Hff: "?z_hff"
   by (rule zenon_in_subsetof_0 [of "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))" "[''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))", OF z_Hfu])
   show FALSE
   by (rule notE [OF z_Hfe z_Hff])
  qed
 qed
 have zenon_L2_: "(a_Mhash_primea=M) ==> (~((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) \\in M)) ==> ((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) \\in a_Mhash_primea) ==> FALSE" (is "?z_hfd ==> ?z_hfx ==> ?z_hgi ==> FALSE")
 proof -
  assume z_Hfd:"?z_hfd"
  assume z_Hfx:"?z_hfx" (is "~?z_hfy")
  assume z_Hgi:"?z_hgi"
  have z_Hgj: "(~?z_hgi)"
  by (rule ssubst [where P="(\<lambda>zenon_Vec. (~((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) \\in zenon_Vec)))", OF z_Hfd z_Hfx])
  show FALSE
  by (rule notE [OF z_Hgj z_Hgi])
 qed
 have zenon_L3_: "((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]) ==> (~(((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))[''ret'']) \\in FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))) ==> FALSE" (is "?z_hgo ==> ?z_hgp ==> FALSE")
 proof -
  assume z_Hgo:"?z_hgo"
  assume z_Hgp:"?z_hgp" (is "~?z_hgq")
  let ?z_hfz = "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))"
  let ?z_hgs = "<<''sigma'', ''op'', ''arg'', ''ret''>>"
  let ?z_hgt = "<<Idems, FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT}), FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet))), FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet))>>"
  have z_Hgu: "(4 \\in DOMAIN(?z_hgs))" by auto
  have z_Hgx: "((?z_hfz[(?z_hgs[4])]) \\in (?z_hgt[4]))" (is "?z_hgx")
  by (rule zenon_in_recordset_field [OF z_Hgo z_Hgu])
  have z_Hgq: "?z_hgq"
  using z_Hgx by auto
  show FALSE
  by (rule notE [OF z_Hgp z_Hgq])
 qed
 assume z_Hm:"(~(a_Mhash_primea \\subseteq [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))" (is "~?z_hhb")
 have z_Ho: "?z_ho" (is "_&?z_hq")
 by (rule zenon_and_1 [OF z_Ha])
 have z_Hq: "?z_hq" (is "_&?z_hs")
 by (rule zenon_and_1 [OF z_Ho])
 have z_Hs: "?z_hs" (is "_&?z_hu")
 by (rule zenon_and_1 [OF z_Hq])
 have z_Hu: "?z_hu" (is "_&?z_hw")
 by (rule zenon_and_1 [OF z_Hs])
 have z_Hw: "?z_hw" (is "_&?z_hy")
 by (rule zenon_and_1 [OF z_Hu])
 have z_Hy: "?z_hy" (is "_&?z_hba")
 by (rule zenon_and_1 [OF z_Hw])
 have z_Hba: "?z_hba" (is "_&?z_hbc")
 by (rule zenon_and_1 [OF z_Hy])
 have z_Hbc: "?z_hbc" (is "_&?z_hbe")
 by (rule zenon_and_1 [OF z_Hba])
 have z_Hbe: "?z_hbe"
 by (rule zenon_and_1 [OF z_Hbc])
 have z_Hhc_z_Hbe: "bAll(M, (\<lambda>x. (x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))) == ?z_hbe" (is "?z_hhc == _")
 by (unfold subset_def)
 have z_Hhc: "?z_hhc"
 by (unfold z_Hhc_z_Hbe, fact z_Hbe)
 have z_Hhe_z_Hhc: "(\\A x:((x \\in M)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))) == ?z_hhc" (is "?z_hhe == _")
 by (unfold bAll_def)
 have z_Hhe: "?z_hhe" (is "\\A x : ?z_hhh(x)")
 by (unfold z_Hhe_z_Hhc, fact z_Hhc)
 have z_Hct: "?z_hct"
 by (rule zenon_and_1 [OF z_He])
 have z_Hhi_z_Hm: "(~bAll(a_Mhash_primea, (\<lambda>x. (x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) == (~?z_hhb)" (is "?z_hhi == ?z_hm")
 by (unfold subset_def)
 have z_Hhi: "?z_hhi" (is "~?z_hhj")
 by (unfold z_Hhi_z_Hm, fact z_Hm)
 have z_Hhk_z_Hhi: "(~(\\A x:((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) == ?z_hhi" (is "?z_hhk == _")
 by (unfold bAll_def)
 have z_Hhk: "?z_hhk" (is "~(\\A x : ?z_hhm(x))")
 by (unfold z_Hhk_z_Hhi, fact z_Hhi)
 have z_Hhn: "(\\E x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))" (is "\\E x : ?z_hho(x)")
 by (rule zenon_notallex_0 [of "?z_hhm", OF z_Hhk])
 have z_Hhp: "?z_hho((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))))" (is "~(?z_hfm=>?z_hff)")
 by (rule zenon_ex_choose_0 [of "?z_hho", OF z_Hhn])
 have z_Hfm: "?z_hfm"
 by (rule zenon_notimply_0 [OF z_Hhp])
 have z_Hfe: "(~?z_hff)"
 by (rule zenon_notimply_1 [OF z_Hhp])
 have z_Hhq_z_Hm: "(~(a_Mhash_primea \\subseteq [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])) == ?z_hm" (is "?z_hhq == _")
 by (unfold prod_def)
 have z_Hhq: "?z_hhq" (is "~?z_hhr")
 by (unfold z_Hhq_z_Hm, fact z_Hm)
 have z_Hhs_z_Hhq: "(~bAll(a_Mhash_primea, (\<lambda>zenon_Vza. (zenon_Vza \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) == ?z_hhq" (is "?z_hhs == _")
 by (unfold subset_def)
 have z_Hhs: "?z_hhs" (is "~?z_hht")
 by (unfold z_Hhs_z_Hhq, fact z_Hhq)
 have z_Hhx_z_Hhs: "(~(\\A x:((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) == ?z_hhs" (is "?z_hhx == _")
 by (unfold bAll_def)
 have z_Hhx: "?z_hhx" (is "~(\\A x : ?z_hhz(x))")
 by (unfold z_Hhx_z_Hhs, fact z_Hhs)
 have z_Hia: "(\\E x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))" (is "\\E x : ?z_hib(x)")
 by (rule zenon_notallex_0 [of "?z_hhz", OF z_Hhx])
 have z_Hic: "?z_hib((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))))" (is "~(?z_hgi=>?z_hid)")
 by (rule zenon_ex_choose_0 [of "?z_hib", OF z_Hia])
 have z_Hgi: "?z_hgi"
 by (rule zenon_notimply_0 [OF z_Hic])
 have z_Hie: "(~?z_hid)"
 by (rule zenon_notimply_1 [OF z_Hic])
 let ?z_hfz = "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))"
 have z_Hif: "isAFcn(?z_hfz)" (is "?z_hif")
 proof (rule zenon_nnpp)
  assume z_Hig: "(~?z_hif)"
  show FALSE
  proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p])))" "((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" "((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=M)))", OF z_Hct])
   assume z_Hcu:"(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p])))" (is "?z_hcv&?z_hda")
   assume z_Hdc:"((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" (is "?z_hdd&?z_hdh")
   show FALSE
   by (rule zenon_L1_ [OF z_Hdc z_Hfe z_Hfm])
  next
   assume z_Hij:"(~(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p]))))" (is "~(?z_hcv&?z_hda)")
   assume z_Hex:"((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=M)))" (is "?z_hey&?z_hez")
   have z_Hez: "?z_hez" (is "?z_hfa&?z_hfd")
   by (rule zenon_and_1 [OF z_Hex])
   have z_Hfd: "?z_hfd"
   by (rule zenon_and_1 [OF z_Hez])
   have z_Hik: "?z_hhh(?z_hfz)" (is "?z_hfy=>?z_hgo")
   by (rule zenon_all_0 [of "?z_hhh" "?z_hfz", OF z_Hhe])
   show FALSE
   proof (rule zenon_imply [OF z_Hik])
    assume z_Hfx:"(~?z_hfy)"
    show FALSE
    by (rule zenon_L2_ [OF z_Hfd z_Hfx z_Hgi])
   next
    assume z_Hgo:"?z_hgo"
    have z_Hif: "?z_hif" using z_Hgo by auto
    let ?z_hgs = "<<''sigma'', ''op'', ''arg'', ''ret''>>"
    let ?z_hgt = "<<Idems, FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT}), FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet))), FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet))>>"
    show FALSE
    by (rule notE [OF z_Hig z_Hif])
   qed
  qed
 qed
 have z_Hil: "(DOMAIN(?z_hfz)={''sigma'', ''op'', ''arg'', ''ret''})" (is "?z_him=?z_hin")
 proof (rule zenon_nnpp)
  assume z_Hio: "(?z_him~=?z_hin)"
  show FALSE
  proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p])))" "((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" "((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=M)))", OF z_Hct])
   assume z_Hcu:"(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p])))" (is "?z_hcv&?z_hda")
   assume z_Hdc:"((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" (is "?z_hdd&?z_hdh")
   show FALSE
   by (rule zenon_L1_ [OF z_Hdc z_Hfe z_Hfm])
  next
   assume z_Hij:"(~(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p]))))" (is "~(?z_hcv&?z_hda)")
   assume z_Hex:"((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=M)))" (is "?z_hey&?z_hez")
   have z_Hez: "?z_hez" (is "?z_hfa&?z_hfd")
   by (rule zenon_and_1 [OF z_Hex])
   have z_Hfd: "?z_hfd"
   by (rule zenon_and_1 [OF z_Hez])
   have z_Hik: "?z_hhh(?z_hfz)" (is "?z_hfy=>?z_hgo")
   by (rule zenon_all_0 [of "?z_hhh" "?z_hfz", OF z_Hhe])
   show FALSE
   proof (rule zenon_imply [OF z_Hik])
    assume z_Hfx:"(~?z_hfy)"
    show FALSE
    by (rule zenon_L2_ [OF z_Hfd z_Hfx z_Hgi])
   next
    assume z_Hgo:"?z_hgo"
    have z_Hil: "(?z_him=?z_hin)" using z_Hgo by auto
    let ?z_hgs = "<<''sigma'', ''op'', ''arg'', ''ret''>>"
    let ?z_hgt = "<<Idems, FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT}), FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet))), FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet))>>"
    show FALSE
    by (rule notE [OF z_Hio z_Hil])
   qed
  qed
 qed
 have z_Hip: "((?z_hfz[''sigma'']) \\in Idems)" (is "?z_hip")
 proof (rule zenon_nnpp)
  assume z_Hir: "(~?z_hip)"
  show FALSE
  proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p])))" "((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" "((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=M)))", OF z_Hct])
   assume z_Hcu:"(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p])))" (is "?z_hcv&?z_hda")
   assume z_Hdc:"((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" (is "?z_hdd&?z_hdh")
   show FALSE
   by (rule zenon_L1_ [OF z_Hdc z_Hfe z_Hfm])
  next
   assume z_Hij:"(~(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p]))))" (is "~(?z_hcv&?z_hda)")
   assume z_Hex:"((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=M)))" (is "?z_hey&?z_hez")
   have z_Hez: "?z_hez" (is "?z_hfa&?z_hfd")
   by (rule zenon_and_1 [OF z_Hex])
   have z_Hfd: "?z_hfd"
   by (rule zenon_and_1 [OF z_Hez])
   have z_Hik: "?z_hhh(?z_hfz)" (is "?z_hfy=>?z_hgo")
   by (rule zenon_all_0 [of "?z_hhh" "?z_hfz", OF z_Hhe])
   show FALSE
   proof (rule zenon_imply [OF z_Hik])
    assume z_Hfx:"(~?z_hfy)"
    show FALSE
    by (rule zenon_L2_ [OF z_Hfd z_Hfx z_Hgi])
   next
    assume z_Hgo:"?z_hgo"
    let ?z_hgs = "<<''sigma'', ''op'', ''arg'', ''ret''>>"
    let ?z_hgt = "<<Idems, FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT}), FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet))), FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet))>>"
    have z_His: "(1 \\in DOMAIN(?z_hgs))" by auto
    have z_Hit: "((?z_hfz[(?z_hgs[1])]) \\in (?z_hgt[1]))" (is "?z_hit")
    by (rule zenon_in_recordset_field [OF z_Hgo z_His])
    have z_Hip: "?z_hip"
    using z_Hit by auto
    show FALSE
    by (rule notE [OF z_Hir z_Hip])
   qed
  qed
 qed
 have z_Hix: "((?z_hfz[''op'']) \\in FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT}))" (is "?z_hix")
 proof (rule zenon_nnpp)
  assume z_Hiz: "(~?z_hix)"
  show FALSE
  proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p])))" "((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" "((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=M)))", OF z_Hct])
   assume z_Hcu:"(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p])))" (is "?z_hcv&?z_hda")
   assume z_Hdc:"((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" (is "?z_hdd&?z_hdh")
   show FALSE
   by (rule zenon_L1_ [OF z_Hdc z_Hfe z_Hfm])
  next
   assume z_Hij:"(~(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p]))))" (is "~(?z_hcv&?z_hda)")
   assume z_Hex:"((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=M)))" (is "?z_hey&?z_hez")
   have z_Hez: "?z_hez" (is "?z_hfa&?z_hfd")
   by (rule zenon_and_1 [OF z_Hex])
   have z_Hfd: "?z_hfd"
   by (rule zenon_and_1 [OF z_Hez])
   have z_Hik: "?z_hhh(?z_hfz)" (is "?z_hfy=>?z_hgo")
   by (rule zenon_all_0 [of "?z_hhh" "?z_hfz", OF z_Hhe])
   show FALSE
   proof (rule zenon_imply [OF z_Hik])
    assume z_Hfx:"(~?z_hfy)"
    show FALSE
    by (rule zenon_L2_ [OF z_Hfd z_Hfx z_Hgi])
   next
    assume z_Hgo:"?z_hgo"
    let ?z_hgs = "<<''sigma'', ''op'', ''arg'', ''ret''>>"
    let ?z_hgt = "<<Idems, FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT}), FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet))), FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet))>>"
    have z_Hja: "(2 \\in DOMAIN(?z_hgs))" by auto
    have z_Hjb: "((?z_hfz[(?z_hgs[2])]) \\in (?z_hgt[2]))" (is "?z_hjb")
    by (rule zenon_in_recordset_field [OF z_Hgo z_Hja])
    have z_Hix: "?z_hix"
    using z_Hjb by auto
    show FALSE
    by (rule notE [OF z_Hiz z_Hix])
   qed
  qed
 qed
 have z_Hjf: "((?z_hfz[''arg'']) \\in FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>))))" (is "?z_hjf")
 proof (rule zenon_nnpp)
  assume z_Hjh: "(~?z_hjf)"
  show FALSE
  proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p])))" "((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" "((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=M)))", OF z_Hct])
   assume z_Hcu:"(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p])))" (is "?z_hcv&?z_hda")
   assume z_Hdc:"((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" (is "?z_hdd&?z_hdh")
   show FALSE
   by (rule zenon_L1_ [OF z_Hdc z_Hfe z_Hfm])
  next
   assume z_Hij:"(~(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p]))))" (is "~(?z_hcv&?z_hda)")
   assume z_Hex:"((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=M)))" (is "?z_hey&?z_hez")
   have z_Hez: "?z_hez" (is "?z_hfa&?z_hfd")
   by (rule zenon_and_1 [OF z_Hex])
   have z_Hfd: "?z_hfd"
   by (rule zenon_and_1 [OF z_Hez])
   have z_Hik: "?z_hhh(?z_hfz)" (is "?z_hfy=>?z_hgo")
   by (rule zenon_all_0 [of "?z_hhh" "?z_hfz", OF z_Hhe])
   show FALSE
   proof (rule zenon_imply [OF z_Hik])
    assume z_Hfx:"(~?z_hfy)"
    show FALSE
    by (rule zenon_L2_ [OF z_Hfd z_Hfx z_Hgi])
   next
    assume z_Hgo:"?z_hgo"
    let ?z_hgs = "<<''sigma'', ''op'', ''arg'', ''ret''>>"
    let ?z_hgt = "<<Idems, FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT}), FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet))), FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet))>>"
    have z_Hji: "(3 \\in DOMAIN(?z_hgs))" by auto
    have z_Hjk: "((?z_hfz[(?z_hgs[3])]) \\in (?z_hgt[3]))" (is "?z_hjk")
    by (rule zenon_in_recordset_field [OF z_Hgo z_Hji])
    have z_Hjo: "((?z_hfz[''arg'']) \\in FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet))))" (is "?z_hjo")
    using z_Hjk by auto
    have z_Hjf_z_Hjo: "?z_hjf == ?z_hjo" (is "_ == _")
    by (unfold prod_def)
    have z_Hjf: "?z_hjf"
    by (unfold z_Hjf_z_Hjo, fact z_Hjo)
    show FALSE
    by (rule notE [OF z_Hjh z_Hjf])
   qed
  qed
 qed
 have z_Hgq: "((?z_hfz[''ret'']) \\in FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))" (is "?z_hgq")
 proof (rule zenon_nnpp)
  assume z_Hgp: "(~?z_hgq)"
  show FALSE
  proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p])))" "((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" "((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=M)))", OF z_Hct])
   assume z_Hcu:"(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p])))" (is "?z_hcv&?z_hda")
   assume z_Hdc:"((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" (is "?z_hdd&?z_hdh")
   show FALSE
   by (rule zenon_L1_ [OF z_Hdc z_Hfe z_Hfm])
  next
   assume z_Hij:"(~(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p]))))" (is "~(?z_hcv&?z_hda)")
   assume z_Hex:"((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=M)))" (is "?z_hey&?z_hez")
   have z_Hez: "?z_hez" (is "?z_hfa&?z_hfd")
   by (rule zenon_and_1 [OF z_Hex])
   have z_Hfd: "?z_hfd"
   by (rule zenon_and_1 [OF z_Hez])
   have z_Hik: "?z_hhh(?z_hfz)" (is "?z_hfy=>?z_hgo")
   by (rule zenon_all_0 [of "?z_hhh" "?z_hfz", OF z_Hhe])
   show FALSE
   proof (rule zenon_imply [OF z_Hik])
    assume z_Hfx:"(~?z_hfy)"
    show FALSE
    by (rule zenon_L2_ [OF z_Hfd z_Hfx z_Hgi])
   next
    assume z_Hgo:"?z_hgo"
    show FALSE
    by (rule zenon_L3_ [OF z_Hgo z_Hgp])
   qed
  qed
 qed
 show FALSE by (rule notE [OF z_Hie],
                rule zenon_inrecordsetI4 [OF z_Hif z_Hil z_Hip z_Hix z_Hjf z_Hgq ])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 92"; *} qed
lemma ob'101:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes UF UF'
fixes u u'
fixes v v'
fixes a_iunde_ua a_iunde_ua'
fixes a_iunde_va a_iunde_va'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition NodeSet suppressed *)
(* usable definition varlist suppressed *)
(* usable definition Idems suppressed *)
(* usable definition NodeToIdFuncs suppressed *)
(* usable definition UFId_StateSet suppressed *)
(* usable definition SmallerRep suppressed *)
(* usable definition LargerRep suppressed *)
(* usable definition URep suppressed *)
(* usable definition CandID suppressed *)
(* usable definition IDUpdate suppressed *)
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition Configs suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitUF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition UFUnite suppressed *)
(* usable definition MetaConfigUnite suppressed *)
(* usable definition Init suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition S4 suppressed *)
(* usable definition S5 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition UFSSpec suppressed *)
(* usable definition PCTypeOK suppressed *)
(* usable definition UFTypeOK suppressed *)
(* usable definition uTypeOK suppressed *)
(* usable definition vTypeOK suppressed *)
(* usable definition i_uTypeOK suppressed *)
(* usable definition i_vTypeOK suppressed *)
(* usable definition cTypeOK suppressed *)
(* usable definition dTypeOK suppressed *)
(* usable definition MTypeOK suppressed *)
assumes v'68: "((PCTypeOK) & (UFTypeOK) & (uTypeOK) & (vTypeOK) & (a_iunde_uTypeOKa) & (a_iunde_vTypeOKa) & (cTypeOK) & (dTypeOK) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE), (BOT)}) \<union> (NodeSet)))]))) & (MTypeOK))"
fixes p
assumes p_in : "(p \<in> (PROCESSES))"
assumes v'70: "((Step ((p))))"
assumes v'85: "((((a_iunde_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))])))"
assumes v'86: "((((a_Mhash_primea :: c)) \<subseteq> (Configs)))"
assumes v'87: "((((CandID ((fapply ((u), (p)))))) \<subseteq> (((Nat) \<union> ({((0))})))))"
assumes v'89: "((((a_UFhash_primea :: c)) \<in> (a_UFIdunde_StateSeta)))"
assumes v'92: "((\<exists> newId \<in> ((IDUpdate ((fapply ((u), (p)))))) : ((((a_UFhash_primea :: c)) = (((''rep'' :> (fapply ((UF), (''rep'')))) @@ (''id'' :> (newId))))))) & (cond(((((less ((fapply (((a_iunde_uhash_primea :: c)), (p))), (fapply ((a_iunde_va), (p)))))) \<and> ((greater ((fapply (((a_iunde_uhash_primea :: c)), (p))), ((0))))))), (((((a_rethash_primea :: c)) = ([(ret) EXCEPT ![(p)] = (FALSE)]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''SR'')]))) & ((((a_Mhash_primea :: c)) = (subsetOf((Configs), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''ret''))) = ([(fapply ((told), (''ret''))) EXCEPT ![(p)] = (cond((((fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[0])))))) = (fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[Succ[0]])))))))), (TRUE), (FALSE)))]))) & (((fapply ((t), (''op''))) = (fapply ((told), (''op''))))) & (((fapply ((t), (''arg''))) = (fapply ((told), (''arg'')))))))))))), (((((a_rethash_primea :: c)) = (ret))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''S3'')]))) & ((((a_Mhash_primea :: c)) = (M)))))))"
assumes v'93: "(((fapply ((pc), (p))) = (''S6'')))"
assumes v'94: "((((a_iunde_uhash_primea :: c)) = ([(a_iunde_ua) EXCEPT ![(p)] = (cond((((fapply ((fapply ((UF), (''rep''))), (fapply ((u), (p))))) = (fapply ((u), (p))))), (fapply ((fapply ((UF), (''id''))), (fapply ((u), (p))))), ((0))))])))"
assumes v'95: "((((a_uhash_primea :: c)) = (u)))"
assumes v'96: "((((a_vhash_primea :: c)) = (v)))"
assumes v'97: "((((a_iunde_vhash_primea :: c)) = (a_iunde_va)))"
assumes v'98: "((((a_chash_primea :: c)) = (a_ca)))"
assumes v'99: "((((a_dhash_primea :: c)) = (d)))"
shows "((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE), (BOT)}) \<union> (NodeSet)))])))"(is "PROP ?ob'101")
proof -
ML_command {* writeln "*** TLAPS ENTER 101"; *}
show "PROP ?ob'101"

(* BEGIN ZENON INPUT
;; file=UFSTypeOK.tlaps/tlapm_d4d507.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >UFSTypeOK.tlaps/tlapm_d4d507.znn.out
;; obligation #101
$hyp "v'68" (/\ PCTypeOK UFTypeOK uTypeOK vTypeOK a_iunde_uTypeOKa
a_iunde_vTypeOKa cTypeOK dTypeOK (TLA.in ret
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F. BOT) NodeSet)))
MTypeOK)
$hyp "p_in" (TLA.in p PROCESSES)
$hyp "v'70" (Step p)
$hyp "v'85" (TLA.in a_iunde_uhash_primea
(TLA.FuncSet PROCESSES (TLA.cup arith.N
(TLA.set 0))))
$hyp "v'86" (TLA.subseteq a_Mhash_primea
Configs)
$hyp "v'87" (TLA.subseteq (CandID (TLA.fapply u p)) (TLA.cup arith.N
(TLA.set 0)))
$hyp "v'89" (TLA.in a_UFhash_primea
a_UFIdunde_StateSeta)
$hyp "v'92" (/\ (TLA.bEx (IDUpdate (TLA.fapply u p)) ((newId) (= a_UFhash_primea
(TLA.record "rep" (TLA.fapply UF "rep") "id" newId))))
(TLA.cond (/\ (arith.lt (TLA.fapply a_iunde_uhash_primea p)
(TLA.fapply a_iunde_va p)) (arith.lt 0
(TLA.fapply a_iunde_uhash_primea p))) (/\ (= a_rethash_primea
(TLA.except ret p F.)) (= a_pchash_primea (TLA.except pc p "SR"))
(= a_Mhash_primea
(TLA.subsetOf Configs ((t) (TLA.bEx M ((told) (/\ (= (TLA.fapply (TLA.fapply told "ret") p)
BOT) (= (TLA.fapply t "sigma") (TLA.fapply told "sigma"))
(= (TLA.fapply t "ret")
(TLA.except (TLA.fapply told "ret") p (TLA.cond (= (TLA.fapply (TLA.fapply told "sigma") (TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ 0)))
(TLA.fapply (TLA.fapply told "sigma") (TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))) T. F.)))
(= (TLA.fapply t "op") (TLA.fapply told "op")) (= (TLA.fapply t "arg")
(TLA.fapply told "arg"))))))))) (/\ (= a_rethash_primea ret)
(= a_pchash_primea (TLA.except pc p "S3")) (= a_Mhash_primea
M))))
$hyp "v'93" (= (TLA.fapply pc p) "S6")
$hyp "v'94" (= a_iunde_uhash_primea
(TLA.except a_iunde_ua p (TLA.cond (= (TLA.fapply (TLA.fapply UF "rep") (TLA.fapply u p))
(TLA.fapply u p)) (TLA.fapply (TLA.fapply UF "id") (TLA.fapply u p)) 0)))
$hyp "v'95" (= a_uhash_primea u)
$hyp "v'96" (= a_vhash_primea v)
$hyp "v'97" (= a_iunde_vhash_primea a_iunde_va)
$hyp "v'98" (= a_chash_primea a_ca)
$hyp "v'99" (= a_dhash_primea d)
$goal (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F. BOT)
NodeSet)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(PCTypeOK&(UFTypeOK&(uTypeOK&(vTypeOK&(a_iunde_uTypeOKa&(a_iunde_vTypeOKa&(cTypeOK&(dTypeOK&((ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))&MTypeOK)))))))))" (is "_&?z_hr")
 using v'68 by blast
 have z_Hj:"(a_iunde_uhash_primea=except(a_iunde_ua, p, cond((((UF[''rep''])[(u[p])])=(u[p])), ((UF[''id''])[(u[p])]), 0)))" (is "_=?z_hbt")
 using v'94 by blast
 have z_Hh:"(bEx(IDUpdate((u[p])), (\<lambda>newId. (a_UFhash_primea=(''rep'' :> ((UF[''rep''])) @@ ''id'' :> (newId)))))&cond((((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p]))), ((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg'']))))))))))))), ((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=M)))))" (is "?z_hci&?z_hcp")
 using v'92 by blast
 have z_Hd:"(a_iunde_uhash_primea \\in FuncSet(PROCESSES, (Nat \\cup {0})))" (is "?z_hd")
 using v'85 by blast
 have zenon_L1_: "(a_rethash_primea=except(ret, p, FALSE)) ==> (p~=(CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))))) ==> ((ret[(CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))))])~=(a_rethash_primea[(CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))))])) ==> ((CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, FALSE, BOT} \\cup NodeSet))))) \\in DOMAIN(ret)) ==> FALSE" (is "?z_hcx ==> ?z_hfh ==> ?z_hfp ==> ?z_hfs ==> FALSE")
 proof -
  assume z_Hcx:"?z_hcx" (is "_=?z_hcz")
  assume z_Hfh:"?z_hfh" (is "_~=?z_hfi")
  assume z_Hfp:"?z_hfp" (is "?z_hfq~=?z_hfr")
  assume z_Hfs:"?z_hfs"
  have z_Hfu: "(((isAFcn(a_rethash_primea)<=>isAFcn(?z_hcz))&(DOMAIN(a_rethash_primea)=DOMAIN(?z_hcz)))&(\\A zenon_Vcn:((a_rethash_primea[zenon_Vcn])=(?z_hcz[zenon_Vcn]))))" (is "?z_hfv&?z_hgc")
  by (rule zenon_funequal_0 [of "a_rethash_primea" "?z_hcz", OF z_Hcx])
  have z_Hgc: "?z_hgc" (is "\\A x : ?z_hgh(x)")
  by (rule zenon_and_1 [OF z_Hfu])
  have z_Hgi: "?z_hgh(?z_hfi)" (is "_=?z_hgj")
  by (rule zenon_all_0 [of "?z_hgh" "?z_hfi", OF z_Hgc])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vokb. (?z_hfr=zenon_Vokb))" "ret" "p" "FALSE" "?z_hfi", OF z_Hgi])
   assume z_Hfs:"?z_hfs"
   assume z_Hgn:"(p=?z_hfi)"
   assume z_Hgo:"(?z_hfr=FALSE)" (is "_=?z_hbo")
   show FALSE
   by (rule notE [OF z_Hfh z_Hgn])
  next
   assume z_Hfs:"?z_hfs"
   assume z_Hfh:"?z_hfh"
   assume z_Hgp:"(?z_hfr=?z_hfq)"
   show FALSE
   by (rule zenon_eqsym [OF z_Hgp z_Hfp])
  next
   assume z_Hgq:"(~?z_hfs)"
   show FALSE
   by (rule notE [OF z_Hgq z_Hfs])
  qed
 qed
 assume z_Hp:"(~(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE, BOT} \\cup NodeSet))))" (is "~?z_hgr")
 have z_Hr: "?z_hr" (is "_&?z_ht")
 by (rule zenon_and_1 [OF z_Ha])
 have z_Ht: "?z_ht" (is "_&?z_hv")
 by (rule zenon_and_1 [OF z_Hr])
 have z_Hv: "?z_hv" (is "_&?z_hx")
 by (rule zenon_and_1 [OF z_Ht])
 have z_Hx: "?z_hx" (is "_&?z_hz")
 by (rule zenon_and_1 [OF z_Hv])
 have z_Hz: "?z_hz" (is "_&?z_hbb")
 by (rule zenon_and_1 [OF z_Hx])
 have z_Hbb: "?z_hbb" (is "_&?z_hbd")
 by (rule zenon_and_1 [OF z_Hz])
 have z_Hbd: "?z_hbd" (is "_&?z_hbf")
 by (rule zenon_and_1 [OF z_Hbb])
 have z_Hbf: "?z_hbf" (is "?z_hbg&_")
 by (rule zenon_and_1 [OF z_Hbd])
 have z_Hbg: "?z_hbg"
 by (rule zenon_and_0 [OF z_Hbf])
 have z_Hcp: "?z_hcp"
 by (rule zenon_and_1 [OF z_Hh])
 have z_Hgs: "(DOMAIN(ret)=PROCESSES)" (is "?z_hft=_")
 by (rule zenon_in_funcset_1 [of "ret" "PROCESSES" "({ACK, TRUE, FALSE, BOT} \\cup NodeSet)", OF z_Hbg])
 have z_Hgt: "(?z_hbt \\in FuncSet(PROCESSES, (Nat \\cup {0})))" (is "?z_hgt")
 by (rule subst [where P="(\<lambda>zenon_Vruc. (zenon_Vruc \\in FuncSet(PROCESSES, (Nat \\cup {0}))))", OF z_Hj z_Hd])
 have z_Hgx: "(DOMAIN(?z_hbt)=PROCESSES)" (is "?z_hgy=_")
 by (rule zenon_in_funcset_1 [of "?z_hbt" "PROCESSES" "(Nat \\cup {0})", OF z_Hgt])
 show FALSE
 proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p])))" "((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" "((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=M)))", OF z_Hcp])
  assume z_Hcq:"(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p])))" (is "?z_hcr&?z_hcv")
  assume z_Hcw:"((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" (is "?z_hcx&?z_hda")
  have z_Hcx: "?z_hcx" (is "_=?z_hcz")
  by (rule zenon_and_0 [OF z_Hcw])
  show FALSE
  proof (rule zenon_notin_funcset [of "a_rethash_primea" "PROCESSES" "({ACK, TRUE, FALSE, BOT} \\cup NodeSet)", OF z_Hp])
   assume z_Hhb:"(~isAFcn(a_rethash_primea))" (is "~?z_hfx")
   have z_Hhc: "(~isAFcn(?z_hcz))" (is "~?z_hfy")
   by (rule subst [where P="(\<lambda>zenon_Viuc. (~isAFcn(zenon_Viuc)))", OF z_Hcx z_Hhb])
   show FALSE
   by (rule zenon_notisafcn_except [of "ret" "p" "FALSE", OF z_Hhc])
  next
   assume z_Hhh:"(DOMAIN(a_rethash_primea)~=PROCESSES)" (is "?z_hga~=_")
   have z_Hhi: "(DOMAIN(?z_hcz)~=PROCESSES)" (is "?z_hgb~=_")
   by (rule subst [where P="(\<lambda>zenon_Vmuc. (DOMAIN(zenon_Vmuc)~=PROCESSES))", OF z_Hcx z_Hhh])
   have z_Hhn: "(?z_hft~=PROCESSES)"
   by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vluc. (zenon_Vluc~=PROCESSES))" "ret" "p" "FALSE", OF z_Hhi])
   show FALSE
   by (rule notE [OF z_Hhn z_Hgs])
  next
   assume z_Hhr:"(~(\\A zenon_Vh:((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))))" (is "~(\\A x : ?z_hht(x))")
   have z_Hhu: "(\\E zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))))" (is "\\E x : ?z_hhv(x)")
   by (rule zenon_notallex_0 [of "?z_hht", OF z_Hhr])
   have z_Hhw: "?z_hhv((CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, FALSE, BOT} \\cup NodeSet))))))" (is "~(?z_hhx=>?z_hhy)")
   by (rule zenon_ex_choose_0 [of "?z_hhv", OF z_Hhu])
   have z_Hhx: "?z_hhx"
   by (rule zenon_notimply_0 [OF z_Hhw])
   have z_Hhz: "(~?z_hhy)"
   by (rule zenon_notimply_1 [OF z_Hhw])
   have z_Hia: "(~((a_rethash_primea[(CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))))]) \\in {ACK, TRUE, FALSE, BOT}))" (is "~?z_hib")
   by (rule zenon_notin_cup_0 [of "(a_rethash_primea[(CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))))])" "{ACK, TRUE, FALSE, BOT}" "NodeSet", OF z_Hhz])
   have z_Hic: "(~((a_rethash_primea[(CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))))]) \\in NodeSet))" (is "~?z_hid")
   by (rule zenon_notin_cup_1 [of "(a_rethash_primea[(CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))))])" "{ACK, TRUE, FALSE, BOT}" "NodeSet", OF z_Hhz])
   have z_Hie: "(~((a_rethash_primea[(CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))))]) \\in {TRUE, FALSE, BOT}))" (is "~?z_hif")
   by (rule zenon_notin_addElt_1 [of "(a_rethash_primea[(CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))))])" "ACK" "{TRUE, FALSE, BOT}", OF z_Hia])
   have z_Hih: "(~((a_rethash_primea[(CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))))]) \\in {FALSE, BOT}))" (is "~?z_hii")
   by (rule zenon_notin_addElt_1 [of "(a_rethash_primea[(CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))))])" "TRUE" "{FALSE, BOT}", OF z_Hie])
   have z_Hik: "((a_rethash_primea[(CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, FALSE, BOT} \\cup NodeSet)))))])~=FALSE)" (is "?z_hfr~=?z_hbo")
   by (rule zenon_notin_addElt_0 [of "?z_hfr" "?z_hbo" "{BOT}", OF z_Hih])
   have z_Hfs: "((CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, ?z_hbo, BOT} \\cup NodeSet))))) \\in ?z_hft)" (is "?z_hfs")
   by (rule ssubst [where P="(\<lambda>zenon_Vvn. ((CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, ?z_hbo, BOT} \\cup NodeSet))))) \\in zenon_Vvn))", OF z_Hgs z_Hhx])
   have z_Hip: "((CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, ?z_hbo, BOT} \\cup NodeSet))))) \\in ?z_hgy)" (is "?z_hip")
   by (rule ssubst [where P="(\<lambda>zenon_Vvn. ((CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, ?z_hbo, BOT} \\cup NodeSet))))) \\in zenon_Vvn))", OF z_Hgx z_Hhx])
   have z_Hiq: "((CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, ?z_hbo, BOT} \\cup NodeSet))))) \\in DOMAIN(a_iunde_ua))" (is "?z_hiq")
   by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vvn. ((CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, ?z_hbo, BOT} \\cup NodeSet))))) \\in zenon_Vvn))" "a_iunde_ua" "p" "cond((((UF[''rep''])[(u[p])])=(u[p])), ((UF[''id''])[(u[p])]), 0)", OF z_Hip])
   have z_His: "(\\A zenon_Vq:((zenon_Vq \\in PROCESSES)=>((a_iunde_uhash_primea[zenon_Vq]) \\in (Nat \\cup {0}))))" (is "\\A x : ?z_hiy(x)")
   by (rule zenon_in_funcset_2 [of "a_iunde_uhash_primea" "PROCESSES" "(Nat \\cup {0})", OF z_Hd])
   have z_Hiz: "?z_hiy((CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, ?z_hbo, BOT} \\cup NodeSet))))))" (is "_=>?z_hja")
   by (rule zenon_all_0 [of "?z_hiy" "(CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, ?z_hbo, BOT} \\cup NodeSet)))))", OF z_His])
   show FALSE
   proof (rule zenon_imply [OF z_Hiz])
    assume z_Hjb:"(~?z_hhx)"
    show FALSE
    by (rule notE [OF z_Hjb z_Hhx])
   next
    assume z_Hja:"?z_hja"
    have z_Hjc: "((?z_hbt[(CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, ?z_hbo, BOT} \\cup NodeSet)))))]) \\in (Nat \\cup {0}))" (is "?z_hjc")
    by (rule subst [where P="(\<lambda>zenon_Vtuc. ((zenon_Vtuc[(CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, ?z_hbo, BOT} \\cup NodeSet)))))]) \\in (Nat \\cup {0})))", OF z_Hj z_Hja])
    show FALSE
    proof (rule zenon_fapplyexcept [of "(\<lambda>x. (x \\in (Nat \\cup {0})))" "a_iunde_ua" "p" "cond((((UF[''rep''])[(u[p])])=(u[p])), ((UF[''id''])[(u[p])]), 0)" "(CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, ?z_hbo, BOT} \\cup NodeSet)))))", OF z_Hjc])
     assume z_Hiq:"?z_hiq"
     assume z_Hgn:"(p=(CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, ?z_hbo, BOT} \\cup NodeSet))))))" (is "_=?z_hfi")
     assume z_Hjl:"(cond((((UF[''rep''])[(u[p])])=(u[p])), ((UF[''id''])[(u[p])]), 0) \\in (Nat \\cup {0}))" (is "?z_hjl")
     have z_Hfu: "(((isAFcn(a_rethash_primea)<=>isAFcn(?z_hcz))&(DOMAIN(a_rethash_primea)=DOMAIN(?z_hcz)))&(\\A zenon_Vcn:((a_rethash_primea[zenon_Vcn])=(?z_hcz[zenon_Vcn]))))" (is "?z_hfv&?z_hgc")
     by (rule zenon_funequal_0 [of "a_rethash_primea" "?z_hcz", OF z_Hcx])
     have z_Hgc: "?z_hgc" (is "\\A x : ?z_hgh(x)")
     by (rule zenon_and_1 [OF z_Hfu])
     have z_Hgi: "?z_hgh(?z_hfi)" (is "_=?z_hgj")
     by (rule zenon_all_0 [of "?z_hgh" "?z_hfi", OF z_Hgc])
     show FALSE
     proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vokb. (?z_hfr=zenon_Vokb))" "ret" "p" "?z_hbo" "?z_hfi", OF z_Hgi])
      assume z_Hfs:"?z_hfs"
      assume z_Hgn:"(p=?z_hfi)"
      assume z_Hgo:"(?z_hfr=?z_hbo)"
      show FALSE
      by (rule notE [OF z_Hik z_Hgo])
     next
      assume z_Hfs:"?z_hfs"
      assume z_Hfh:"(p~=?z_hfi)"
      assume z_Hgp:"(?z_hfr=(ret[?z_hfi]))" (is "_=?z_hfq")
      show FALSE
      by (rule notE [OF z_Hfh z_Hgn])
     next
      assume z_Hgq:"(~?z_hfs)"
      show FALSE
      by (rule notE [OF z_Hgq z_Hfs])
     qed
    next
     assume z_Hiq:"?z_hiq"
     assume z_Hfh:"(p~=(CHOOSE zenon_Vh:(~((zenon_Vh \\in PROCESSES)=>((a_rethash_primea[zenon_Vh]) \\in ({ACK, TRUE, ?z_hbo, BOT} \\cup NodeSet))))))" (is "_~=?z_hfi")
     assume z_Hjm:"((a_iunde_ua[?z_hfi]) \\in (Nat \\cup {0}))" (is "?z_hjm")
     have z_Hjo: "(\\A zenon_Vy:((zenon_Vy \\in PROCESSES)=>((ret[zenon_Vy]) \\in ({ACK, TRUE, ?z_hbo, BOT} \\cup NodeSet))))" (is "\\A x : ?z_hju(x)")
     by (rule zenon_in_funcset_2 [of "ret" "PROCESSES" "({ACK, TRUE, ?z_hbo, BOT} \\cup NodeSet)", OF z_Hbg])
     have z_Hjv: "?z_hju(?z_hfi)" (is "_=>?z_hjw")
     by (rule zenon_all_0 [of "?z_hju" "?z_hfi", OF z_Hjo])
     show FALSE
     proof (rule zenon_imply [OF z_Hjv])
      assume z_Hjb:"(~?z_hhx)"
      show FALSE
      by (rule notE [OF z_Hjb z_Hhx])
     next
      assume z_Hjw:"?z_hjw"
      show FALSE
      proof (rule zenon_in_cup [of "(ret[?z_hfi])" "{ACK, TRUE, ?z_hbo, BOT}" "NodeSet", OF z_Hjw])
       assume z_Hjx:"((ret[?z_hfi]) \\in {ACK, TRUE, ?z_hbo, BOT})" (is "?z_hjx")
       show FALSE
       proof (rule notE [OF z_Hia])
        have z_Hjy: "((ret[?z_hfi])=?z_hfr)" (is "?z_hfq=_")
        proof (rule zenon_nnpp [of "(?z_hfq=?z_hfr)"])
         assume z_Hfp:"(?z_hfq~=?z_hfr)"
         show FALSE
         by (rule zenon_L1_ [OF z_Hcx z_Hfh z_Hfp z_Hfs])
        qed
        have z_Hib: "?z_hib"
        by (rule subst [where P="(\<lambda>zenon_Vuuc. (zenon_Vuuc \\in {ACK, TRUE, ?z_hbo, BOT}))", OF z_Hjy], fact z_Hjx)
        thus "?z_hib" .
       qed
      next
       assume z_Hkc:"((ret[?z_hfi]) \\in NodeSet)" (is "?z_hkc")
       show FALSE
       proof (rule notE [OF z_Hic])
        have z_Hjy: "((ret[?z_hfi])=?z_hfr)" (is "?z_hfq=_")
        proof (rule zenon_nnpp [of "(?z_hfq=?z_hfr)"])
         assume z_Hfp:"(?z_hfq~=?z_hfr)"
         show FALSE
         by (rule zenon_L1_ [OF z_Hcx z_Hfh z_Hfp z_Hfs])
        qed
        have z_Hid: "?z_hid"
        by (rule subst [where P="(\<lambda>zenon_Vvuc. (zenon_Vvuc \\in NodeSet))", OF z_Hjy], fact z_Hkc)
        thus "?z_hid" .
       qed
      qed
     qed
    next
     assume z_Hkg:"(~?z_hiq)"
     show FALSE
     by (rule notE [OF z_Hkg z_Hiq])
    qed
   qed
  qed
 next
  assume z_Hkh:"(~(((a_iunde_uhash_primea[p]) < (a_iunde_va[p]))&(0 < (a_iunde_uhash_primea[p]))))" (is "~(?z_hcr&?z_hcv)")
  assume z_Hew:"((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=M)))" (is "?z_hex&?z_hey")
  have z_Hex: "?z_hex"
  by (rule zenon_and_0 [OF z_Hew])
  show FALSE
  proof (rule notE [OF z_Hp])
   have z_Hki: "(ret=a_rethash_primea)"
   by (rule sym [OF z_Hex])
   have z_Hgr: "?z_hgr"
   by (rule subst [where P="(\<lambda>zenon_Vwuc. (zenon_Vwuc \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE, BOT} \\cup NodeSet))))", OF z_Hki], fact z_Hbg)
   thus "?z_hgr" .
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 101"; *} qed
lemma ob'109:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes UF UF'
fixes u u'
fixes v v'
fixes a_iunde_ua a_iunde_ua'
fixes a_iunde_va a_iunde_va'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition NodeSet suppressed *)
(* usable definition varlist suppressed *)
(* usable definition Idems suppressed *)
(* usable definition NodeToIdFuncs suppressed *)
(* usable definition UFId_StateSet suppressed *)
(* usable definition SmallerRep suppressed *)
(* usable definition LargerRep suppressed *)
(* usable definition URep suppressed *)
(* usable definition CandID suppressed *)
(* usable definition IDUpdate suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitUF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition UFUnite suppressed *)
(* usable definition MetaConfigUnite suppressed *)
(* usable definition Init suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition S4 suppressed *)
(* usable definition S5 suppressed *)
(* usable definition S6 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition UFSSpec suppressed *)
(* usable definition PCTypeOK suppressed *)
(* usable definition UFTypeOK suppressed *)
(* usable definition uTypeOK suppressed *)
(* usable definition vTypeOK suppressed *)
(* usable definition i_uTypeOK suppressed *)
(* usable definition i_vTypeOK suppressed *)
(* usable definition cTypeOK suppressed *)
(* usable definition dTypeOK suppressed *)
(* usable definition retTypeOK suppressed *)
assumes v'64: "((PCTypeOK) & (UFTypeOK) & (uTypeOK) & (vTypeOK) & (a_iunde_uTypeOKa) & (a_iunde_vTypeOKa) & (cTypeOK) & (dTypeOK) & (retTypeOK) & (((M) \<subseteq> ([''sigma'' : (Idems), ''op'' : ([(PROCESSES) \<rightarrow> ({(''F''), (''U''), (''S''), (BOT)})]), ''arg'' : ([(PROCESSES) \<rightarrow> ((((({(BOT)}) \<union> (NodeSet))) \<union> (((NodeSet) \<times> (NodeSet)))))]), ''ret'' : ([(PROCESSES) \<rightarrow> ((({(ACK), (BOT), (TRUE), (FALSE)}) \<union> (NodeSet)))])]))))"
fixes p
assumes p_in : "(p \<in> (PROCESSES))"
assumes v'66: "((Step ((p))))"
assumes v'85: "((((((((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''F1'')]))) & (\<exists> i \<in> (NodeSet) : (((((((a_chash_primea :: c)) = ([(a_ca) EXCEPT ![(p)] = (i)]))) & ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : (Idems), ''op'' : ([(PROCESSES) \<rightarrow> ({(''F''), (''U''), (''S''), (BOT)})]), ''arg'' : ([(PROCESSES) \<rightarrow> ((((({(BOT)}) \<union> (NodeSet))) \<union> (((NodeSet) \<times> (NodeSet)))))]), ''ret'' : ([(PROCESSES) \<rightarrow> ((({(ACK), (BOT), (TRUE), (FALSE)}) \<union> (NodeSet)))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((fapply ((told), (''op''))), (p))) = (BOT))) & (((fapply ((fapply ((told), (''arg''))), (p))) = (BOT))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''op''))) = ([(fapply ((told), (''op''))) EXCEPT ![(p)] = (''F'')]))) & (((fapply ((t), (''arg''))) = ([(fapply ((told), (''arg''))) EXCEPT ![(p)] = (fapply (((a_chash_primea :: c)), (p)))]))) & (((fapply ((t), (''ret''))) = (fapply ((told), (''ret'')))))))))))) \<and> (((((a_UFhash_primea :: c)) = (UF))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_iunde_uhash_primea :: c)) = (a_iunde_ua))) & ((((a_iunde_vhash_primea :: c)) = (a_iunde_va))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_rethash_primea :: c)) = (ret)))))))) \<or> (((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U1'')]))) & (\<exists> i \<in> (NodeSet) : (\<exists> j \<in> (NodeSet) : (((((((a_chash_primea :: c)) = ([(a_ca) EXCEPT ![(p)] = (i)]))) & ((((a_dhash_primea :: c)) = ([(d) EXCEPT ![(p)] = (j)]))) & ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : (Idems), ''op'' : ([(PROCESSES) \<rightarrow> ({(''F''), (''U''), (''S''), (BOT)})]), ''arg'' : ([(PROCESSES) \<rightarrow> ((((({(BOT)}) \<union> (NodeSet))) \<union> (((NodeSet) \<times> (NodeSet)))))]), ''ret'' : ([(PROCESSES) \<rightarrow> ((({(ACK), (BOT), (TRUE), (FALSE)}) \<union> (NodeSet)))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((fapply ((told), (''op''))), (p))) = (BOT))) & (((fapply ((fapply ((told), (''arg''))), (p))) = (BOT))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''op''))) = ([(fapply ((told), (''op''))) EXCEPT ![(p)] = (''U'')]))) & (((fapply ((t), (''arg''))) = ([(fapply ((told), (''arg''))) EXCEPT ![(p)] = (<<(fapply (((a_chash_primea :: c)), (p))), (fapply (((a_dhash_primea :: c)), (p)))>>)]))) & (((fapply ((t), (''ret''))) = (fapply ((told), (''ret'')))))))))))) \<and> (((((a_UFhash_primea :: c)) = (UF))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_iunde_uhash_primea :: c)) = (a_iunde_ua))) & ((((a_iunde_vhash_primea :: c)) = (a_iunde_va))) & ((((a_rethash_primea :: c)) = (ret))))))))))) \<or> (((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''S1'')]))) & ((((a_iunde_uhash_primea :: c)) = ([(a_iunde_ua) EXCEPT ![(p)] = ((0))]))) & ((((a_iunde_vhash_primea :: c)) = ([(a_iunde_va) EXCEPT ![(p)] = ((0))]))) & (\<exists> i \<in> (NodeSet) : (\<exists> j \<in> (NodeSet) : (((((a_chash_primea :: c)) = ([(a_ca) EXCEPT ![(p)] = (i)]))) & ((((a_dhash_primea :: c)) = ([(d) EXCEPT ![(p)] = (j)]))) & ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : (Idems), ''op'' : ([(PROCESSES) \<rightarrow> ({(''F''), (''U''), (''S''), (BOT)})]), ''arg'' : ([(PROCESSES) \<rightarrow> ((((({(BOT)}) \<union> (NodeSet))) \<union> (((NodeSet) \<times> (NodeSet)))))]), ''ret'' : ([(PROCESSES) \<rightarrow> ((({(ACK), (BOT), (TRUE), (FALSE)}) \<union> (NodeSet)))])]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((fapply ((told), (''op''))), (p))) = (BOT))) & (((fapply ((fapply ((told), (''arg''))), (p))) = (BOT))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''op''))) = ([(fapply ((told), (''op''))) EXCEPT ![(p)] = (''S'')]))) & (((fapply ((t), (''arg''))) = ([(fapply ((told), (''arg''))) EXCEPT ![(p)] = (<<(fapply (((a_chash_primea :: c)), (p))), (fapply (((a_dhash_primea :: c)), (p)))>>)]))) & (((fapply ((t), (''ret''))) = (fapply ((told), (''ret'')))))))))))))) & (((((a_UFhash_primea :: c)) = (UF))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_rethash_primea :: c)) = (ret))))))))"
assumes v'86: "(((fapply ((pc), (p))) = (''0'')))"
shows "((((a_Mhash_primea :: c)) \<subseteq> ([''sigma'' : (Idems), ''op'' : ([(PROCESSES) \<rightarrow> ({(''F''), (''U''), (''S''), (BOT)})]), ''arg'' : ([(PROCESSES) \<rightarrow> ((((({(BOT)}) \<union> (NodeSet))) \<union> (((NodeSet) \<times> (NodeSet)))))]), ''ret'' : ([(PROCESSES) \<rightarrow> ((({(ACK), (BOT), (TRUE), (FALSE)}) \<union> (NodeSet)))])])))"(is "PROP ?ob'109")
proof -
ML_command {* writeln "*** TLAPS ENTER 109"; *}
show "PROP ?ob'109"

(* BEGIN ZENON INPUT
;; file=UFSTypeOK.tlaps/tlapm_b55f78.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >UFSTypeOK.tlaps/tlapm_b55f78.znn.out
;; obligation #109
$hyp "v'64" (/\ PCTypeOK UFTypeOK uTypeOK vTypeOK a_iunde_uTypeOKa
a_iunde_vTypeOKa cTypeOK dTypeOK retTypeOK (TLA.subseteq M
(TLA.recordset "sigma" Idems "op" (TLA.FuncSet PROCESSES (TLA.set "F" "U" "S" BOT)) "arg" (TLA.FuncSet PROCESSES (TLA.cup (TLA.cup (TLA.set BOT)
NodeSet)
(TLA.prod NodeSet NodeSet))) "ret" (TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK BOT T. F.)
NodeSet)))))
$hyp "p_in" (TLA.in p PROCESSES)
$hyp "v'66" (Step p)
$hyp "v'85" (\/ (\/ (\/ (/\ (= a_pchash_primea (TLA.except pc p "F1"))
(TLA.bEx NodeSet ((i) (/\ (/\ (= a_chash_primea (TLA.except a_ca p i))
(= a_Mhash_primea
(TLA.subsetOf (TLA.recordset "sigma" Idems "op" (TLA.FuncSet PROCESSES (TLA.set "F" "U" "S" BOT)) "arg" (TLA.FuncSet PROCESSES (TLA.cup (TLA.cup (TLA.set BOT)
NodeSet)
(TLA.prod NodeSet NodeSet))) "ret" (TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK BOT T. F.)
NodeSet))) ((t) (TLA.bEx M ((told) (/\ (= (TLA.fapply (TLA.fapply told "ret") p)
BOT) (= (TLA.fapply (TLA.fapply told "op") p) BOT)
(= (TLA.fapply (TLA.fapply told "arg") p) BOT) (= (TLA.fapply t "sigma")
(TLA.fapply told "sigma")) (= (TLA.fapply t "op")
(TLA.except (TLA.fapply told "op") p "F")) (= (TLA.fapply t "arg")
(TLA.except (TLA.fapply told "arg") p (TLA.fapply a_chash_primea p)))
(= (TLA.fapply t "ret") (TLA.fapply told "ret")))))))))
(/\ (= a_UFhash_primea UF) (= a_uhash_primea u) (= a_vhash_primea v)
(= a_iunde_uhash_primea a_iunde_ua) (= a_iunde_vhash_primea a_iunde_va)
(= a_dhash_primea d) (= a_rethash_primea ret)))))) (/\ (= a_pchash_primea
(TLA.except pc p "U1"))
(TLA.bEx NodeSet ((i) (TLA.bEx NodeSet ((j) (/\ (/\ (= a_chash_primea
(TLA.except a_ca p i)) (= a_dhash_primea (TLA.except d p j))
(= a_Mhash_primea
(TLA.subsetOf (TLA.recordset "sigma" Idems "op" (TLA.FuncSet PROCESSES (TLA.set "F" "U" "S" BOT)) "arg" (TLA.FuncSet PROCESSES (TLA.cup (TLA.cup (TLA.set BOT)
NodeSet)
(TLA.prod NodeSet NodeSet))) "ret" (TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK BOT T. F.)
NodeSet))) ((t) (TLA.bEx M ((told) (/\ (= (TLA.fapply (TLA.fapply told "ret") p)
BOT) (= (TLA.fapply (TLA.fapply told "op") p) BOT)
(= (TLA.fapply (TLA.fapply told "arg") p) BOT) (= (TLA.fapply t "sigma")
(TLA.fapply told "sigma")) (= (TLA.fapply t "op")
(TLA.except (TLA.fapply told "op") p "U")) (= (TLA.fapply t "arg")
(TLA.except (TLA.fapply told "arg") p (TLA.tuple (TLA.fapply a_chash_primea p)
(TLA.fapply a_dhash_primea p)))) (= (TLA.fapply t "ret")
(TLA.fapply told "ret"))))))))) (/\ (= a_UFhash_primea UF) (= a_uhash_primea
u) (= a_vhash_primea v) (= a_iunde_uhash_primea a_iunde_ua)
(= a_iunde_vhash_primea a_iunde_va) (= a_rethash_primea ret)))))))))
(/\ (= a_pchash_primea (TLA.except pc p "S1")) (= a_iunde_uhash_primea
(TLA.except a_iunde_ua p 0)) (= a_iunde_vhash_primea
(TLA.except a_iunde_va p 0))
(TLA.bEx NodeSet ((i) (TLA.bEx NodeSet ((j) (/\ (= a_chash_primea
(TLA.except a_ca p i)) (= a_dhash_primea (TLA.except d p j))
(= a_Mhash_primea
(TLA.subsetOf (TLA.recordset "sigma" Idems "op" (TLA.FuncSet PROCESSES (TLA.set "F" "U" "S" BOT)) "arg" (TLA.FuncSet PROCESSES (TLA.cup (TLA.cup (TLA.set BOT)
NodeSet)
(TLA.prod NodeSet NodeSet))) "ret" (TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK BOT T. F.)
NodeSet))) ((t) (TLA.bEx M ((told) (/\ (= (TLA.fapply (TLA.fapply told "ret") p)
BOT) (= (TLA.fapply (TLA.fapply told "op") p) BOT)
(= (TLA.fapply (TLA.fapply told "arg") p) BOT) (= (TLA.fapply t "sigma")
(TLA.fapply told "sigma")) (= (TLA.fapply t "op")
(TLA.except (TLA.fapply told "op") p "S")) (= (TLA.fapply t "arg")
(TLA.except (TLA.fapply told "arg") p (TLA.tuple (TLA.fapply a_chash_primea p)
(TLA.fapply a_dhash_primea p)))) (= (TLA.fapply t "ret")
(TLA.fapply told "ret"))))))))))))) (/\ (= a_UFhash_primea UF)
(= a_uhash_primea u) (= a_vhash_primea v) (= a_rethash_primea
ret)))))
$hyp "v'86" (= (TLA.fapply pc p) "0")
$goal (TLA.subseteq a_Mhash_primea
(TLA.recordset "sigma" Idems "op" (TLA.FuncSet PROCESSES (TLA.set "F" "U" "S" BOT)) "arg" (TLA.FuncSet PROCESSES (TLA.cup (TLA.cup (TLA.set BOT)
NodeSet)
(TLA.prod NodeSet NodeSet))) "ret" (TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK BOT T. F.)
NodeSet))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"((((a_pchash_primea=except(pc, p, ''F1''))&bEx(NodeSet, (\<lambda>i. (((a_chash_primea=except(a_ca, p, i))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''F''))&(((t[''arg''])=except((told[''arg'']), p, (a_chash_primea[p])))&((t[''ret''])=(told[''ret'']))))))))))))))&((a_UFhash_primea=UF)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_iunde_uhash_primea=a_iunde_ua)&((a_iunde_vhash_primea=a_iunde_va)&((a_dhash_primea=d)&(a_rethash_primea=ret)))))))))))|((a_pchash_primea=except(pc, p, ''U1''))&bEx(NodeSet, (\<lambda>i. bEx(NodeSet, (\<lambda>j. (((a_chash_primea=except(a_ca, p, i))&((a_dhash_primea=except(d, p, j))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''U''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))))))&((a_UFhash_primea=UF)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_iunde_uhash_primea=a_iunde_ua)&((a_iunde_vhash_primea=a_iunde_va)&(a_rethash_primea=ret)))))))))))))|((a_pchash_primea=except(pc, p, ''S1''))&((a_iunde_uhash_primea=except(a_iunde_ua, p, 0))&((a_iunde_vhash_primea=except(a_iunde_va, p, 0))&(bEx(NodeSet, (\<lambda>i. bEx(NodeSet, (\<lambda>j. ((a_chash_primea=except(a_ca, p, i))&((a_dhash_primea=except(d, p, j))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''S''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))))))))))&((a_UFhash_primea=UF)&((a_uhash_primea=u)&((a_vhash_primea=v)&(a_rethash_primea=ret)))))))))" (is "?z_hg|?z_hfr")
 using v'85 by blast
 have zenon_L1_: "((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]) ==> (~isAFcn((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))))) ==> FALSE" (is "?z_hgy ==> ?z_hhk ==> FALSE")
 proof -
  assume z_Hgy:"?z_hgy"
  assume z_Hhk:"?z_hhk" (is "~?z_hhl")
  let ?z_hgz = "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))"
  have z_Hhl: "?z_hhl" using z_Hgy by auto
  let ?z_hhm = "<<''sigma'', ''op'', ''arg'', ''ret''>>"
  let ?z_hhn = "<<Idems, FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT}), FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet))), FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet))>>"
  show FALSE
  by (rule notE [OF z_Hhk z_Hhl])
 qed
 have zenon_L2_: "((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]) ==> (DOMAIN((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))))~={''sigma'', ''op'', ''arg'', ''ret''}) ==> FALSE" (is "?z_hgy ==> ?z_hho ==> FALSE")
 proof -
  assume z_Hgy:"?z_hgy"
  assume z_Hho:"?z_hho" (is "?z_hhp~=?z_hhq")
  let ?z_hgz = "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))"
  have z_Hhr: "(?z_hhp=?z_hhq)" using z_Hgy by auto
  let ?z_hhm = "<<''sigma'', ''op'', ''arg'', ''ret''>>"
  let ?z_hhn = "<<Idems, FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT}), FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet))), FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet))>>"
  show FALSE
  by (rule notE [OF z_Hho z_Hhr])
 qed
 have zenon_L3_: "((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]) ==> (~(((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))[''sigma'']) \\in Idems)) ==> FALSE" (is "?z_hgy ==> ?z_hhs ==> FALSE")
 proof -
  assume z_Hgy:"?z_hgy"
  assume z_Hhs:"?z_hhs" (is "~?z_hht")
  let ?z_hgz = "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))"
  let ?z_hhm = "<<''sigma'', ''op'', ''arg'', ''ret''>>"
  let ?z_hhn = "<<Idems, FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT}), FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet))), FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet))>>"
  have z_Hhv: "(1 \\in DOMAIN(?z_hhm))" by auto
  have z_Hhy: "((?z_hgz[(?z_hhm[1])]) \\in (?z_hhn[1]))" (is "?z_hhy")
  by (rule zenon_in_recordset_field [OF z_Hgy z_Hhv])
  have z_Hht: "?z_hht"
  using z_Hhy by auto
  show FALSE
  by (rule notE [OF z_Hhs z_Hht])
 qed
 have zenon_L4_: "((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]) ==> (~(((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))[''op'']) \\in FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT}))) ==> FALSE" (is "?z_hgy ==> ?z_hic ==> FALSE")
 proof -
  assume z_Hgy:"?z_hgy"
  assume z_Hic:"?z_hic" (is "~?z_hid")
  let ?z_hgz = "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))"
  let ?z_hhm = "<<''sigma'', ''op'', ''arg'', ''ret''>>"
  let ?z_hhn = "<<Idems, FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT}), FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet))), FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet))>>"
  have z_Hif: "(2 \\in DOMAIN(?z_hhm))" by auto
  have z_Hih: "((?z_hgz[(?z_hhm[2])]) \\in (?z_hhn[2]))" (is "?z_hih")
  by (rule zenon_in_recordset_field [OF z_Hgy z_Hif])
  have z_Hid: "?z_hid"
  using z_Hih by auto
  show FALSE
  by (rule notE [OF z_Hic z_Hid])
 qed
 have zenon_L5_: "((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]) ==> (~(((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))[''arg'']) \\in FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>))))) ==> FALSE" (is "?z_hgy ==> ?z_hil ==> FALSE")
 proof -
  assume z_Hgy:"?z_hgy"
  assume z_Hil:"?z_hil" (is "~?z_him")
  let ?z_hgz = "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))"
  let ?z_hhm = "<<''sigma'', ''op'', ''arg'', ''ret''>>"
  let ?z_hhn = "<<Idems, FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT}), FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet))), FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet))>>"
  have z_Hio: "(3 \\in DOMAIN(?z_hhm))" by auto
  have z_Hiq: "((?z_hgz[(?z_hhm[3])]) \\in (?z_hhn[3]))" (is "?z_hiq")
  by (rule zenon_in_recordset_field [OF z_Hgy z_Hio])
  have z_Hiu: "((?z_hgz[''arg'']) \\in FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet))))" (is "?z_hiu")
  using z_Hiq by auto
  have z_Him_z_Hiu: "?z_him == ?z_hiu" (is "_ == _")
  by (unfold prod_def)
  have z_Him: "?z_him"
  by (unfold z_Him_z_Hiu, fact z_Hiu)
  show FALSE
  by (rule notE [OF z_Hil z_Him])
 qed
 have zenon_L6_: "((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]) ==> (~(((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))[''ret'']) \\in FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))) ==> FALSE" (is "?z_hgy ==> ?z_hiv ==> FALSE")
 proof -
  assume z_Hgy:"?z_hgy"
  assume z_Hiv:"?z_hiv" (is "~?z_hiw")
  let ?z_hgz = "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))"
  let ?z_hhm = "<<''sigma'', ''op'', ''arg'', ''ret''>>"
  let ?z_hhn = "<<Idems, FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT}), FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet))), FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet))>>"
  have z_Hiy: "(4 \\in DOMAIN(?z_hhm))" by auto
  have z_Hja: "((?z_hgz[(?z_hhm[4])]) \\in (?z_hhn[4]))" (is "?z_hja")
  by (rule zenon_in_recordset_field [OF z_Hgy z_Hiy])
  have z_Hiw: "?z_hiw"
  using z_Hja by auto
  show FALSE
  by (rule notE [OF z_Hiv z_Hiw])
 qed
 assume z_Hf:"(~(a_Mhash_primea \\subseteq [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))" (is "~?z_hje")
 show FALSE
 proof (rule zenon_or [OF z_Hd])
  assume z_Hg:"?z_hg" (is "?z_hh|?z_heh")
  show FALSE
  proof (rule zenon_or [OF z_Hg])
   assume z_Hh:"?z_hh" (is "?z_hi&?z_ho")
   have z_Ho: "?z_ho"
   by (rule zenon_and_1 [OF z_Hh])
   have z_Hjf_z_Ho: "(\\E x:((x \\in NodeSet)&(((a_chash_primea=except(a_ca, p, x))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''F''))&(((t[''arg''])=except((told[''arg'']), p, (a_chash_primea[p])))&((t[''ret''])=(told[''ret'']))))))))))))))&((a_UFhash_primea=UF)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_iunde_uhash_primea=a_iunde_ua)&((a_iunde_vhash_primea=a_iunde_va)&((a_dhash_primea=d)&(a_rethash_primea=ret)))))))))) == ?z_ho" (is "?z_hjf == _")
   by (unfold bEx_def)
   have z_Hjf: "?z_hjf" (is "\\E x : ?z_hjm(x)")
   by (unfold z_Hjf_z_Ho, fact z_Ho)
   have z_Hjn: "?z_hjm((CHOOSE x:((x \\in NodeSet)&(((a_chash_primea=except(a_ca, p, x))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''F''))&(((t[''arg''])=except((told[''arg'']), p, (a_chash_primea[p])))&((t[''ret''])=(told[''ret'']))))))))))))))&((a_UFhash_primea=UF)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_iunde_uhash_primea=a_iunde_ua)&((a_iunde_vhash_primea=a_iunde_va)&((a_dhash_primea=d)&(a_rethash_primea=ret)))))))))))" (is "?z_hjp&?z_hjq")
   by (rule zenon_ex_choose_0 [of "?z_hjm", OF z_Hjf])
   have z_Hjq: "?z_hjq" (is "?z_hjr&?z_hdg")
   by (rule zenon_and_1 [OF z_Hjn])
   have z_Hjr: "?z_hjr" (is "?z_hjs&?z_hy")
   by (rule zenon_and_0 [OF z_Hjq])
   have z_Hy: "?z_hy" (is "_=?z_hba")
   by (rule zenon_and_1 [OF z_Hjr])
   have z_Hjt_z_Hf: "(~(a_Mhash_primea \\subseteq [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])) == (~?z_hje)" (is "?z_hjt == ?z_hf")
   by (unfold prod_def)
   have z_Hjt: "?z_hjt" (is "~?z_hju")
   by (unfold z_Hjt_z_Hf, fact z_Hf)
   have z_Hjv_z_Hjt: "(~bAll(a_Mhash_primea, (\<lambda>zenon_Vsb. (zenon_Vsb \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) == ?z_hjt" (is "?z_hjv == _")
   by (unfold subset_def)
   have z_Hjv: "?z_hjv" (is "~?z_hjw")
   by (unfold z_Hjv_z_Hjt, fact z_Hjt)
   have z_Hka_z_Hjv: "(~(\\A x:((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) == ?z_hjv" (is "?z_hka == _")
   by (unfold bAll_def)
   have z_Hka: "?z_hka" (is "~(\\A x : ?z_hkc(x))")
   by (unfold z_Hka_z_Hjv, fact z_Hjv)
   have z_Hkd: "(\\E x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))" (is "\\E x : ?z_hke(x)")
   by (rule zenon_notallex_0 [of "?z_hkc", OF z_Hka])
   have z_Hkf: "?z_hke((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))))" (is "~(?z_hkg=>?z_hkh)")
   by (rule zenon_ex_choose_0 [of "?z_hke", OF z_Hkd])
   have z_Hkg: "?z_hkg"
   by (rule zenon_notimply_0 [OF z_Hkf])
   have z_Hki: "(~?z_hkh)"
   by (rule zenon_notimply_1 [OF z_Hkf])
   let ?z_hgz = "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))"
   have z_Hhl: "isAFcn(?z_hgz)" (is "?z_hhl")
   proof (rule zenon_nnpp)
    assume z_Hhk: "(~?z_hhl)"
    have z_Hkj: "(?z_hgz \\in ?z_hba)" (is "?z_hkj")
    by (rule subst [where P="(\<lambda>zenon_Vkc. (?z_hgz \\in zenon_Vkc))", OF z_Hy z_Hkg])
    have z_Hgy: "(?z_hgz \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])" (is "?z_hgy")
    by (rule zenon_in_subsetof_0 [of "?z_hgz" "[''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''F''))&(((t[''arg''])=except((told[''arg'']), p, (a_chash_primea[p])))&((t[''ret''])=(told[''ret''])))))))))))", OF z_Hkj])
    show FALSE
    by (rule zenon_L1_ [OF z_Hgy z_Hhk])
   qed
   have z_Hhr: "(DOMAIN(?z_hgz)={''sigma'', ''op'', ''arg'', ''ret''})" (is "?z_hhp=?z_hhq")
   proof (rule zenon_nnpp)
    assume z_Hho: "(?z_hhp~=?z_hhq)"
    have z_Hkj: "(?z_hgz \\in ?z_hba)" (is "?z_hkj")
    by (rule subst [where P="(\<lambda>zenon_Vkc. (?z_hgz \\in zenon_Vkc))", OF z_Hy z_Hkg])
    have z_Hgy: "(?z_hgz \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])" (is "?z_hgy")
    by (rule zenon_in_subsetof_0 [of "?z_hgz" "[''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''F''))&(((t[''arg''])=except((told[''arg'']), p, (a_chash_primea[p])))&((t[''ret''])=(told[''ret''])))))))))))", OF z_Hkj])
    show FALSE
    by (rule zenon_L2_ [OF z_Hgy z_Hho])
   qed
   have z_Hht: "((?z_hgz[''sigma'']) \\in Idems)" (is "?z_hht")
   proof (rule zenon_nnpp)
    assume z_Hhs: "(~?z_hht)"
    have z_Hkj: "(?z_hgz \\in ?z_hba)" (is "?z_hkj")
    by (rule subst [where P="(\<lambda>zenon_Vkc. (?z_hgz \\in zenon_Vkc))", OF z_Hy z_Hkg])
    have z_Hgy: "(?z_hgz \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])" (is "?z_hgy")
    by (rule zenon_in_subsetof_0 [of "?z_hgz" "[''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''F''))&(((t[''arg''])=except((told[''arg'']), p, (a_chash_primea[p])))&((t[''ret''])=(told[''ret''])))))))))))", OF z_Hkj])
    show FALSE
    by (rule zenon_L3_ [OF z_Hgy z_Hhs])
   qed
   have z_Hid: "((?z_hgz[''op'']) \\in FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT}))" (is "?z_hid")
   proof (rule zenon_nnpp)
    assume z_Hic: "(~?z_hid)"
    have z_Hkj: "(?z_hgz \\in ?z_hba)" (is "?z_hkj")
    by (rule subst [where P="(\<lambda>zenon_Vkc. (?z_hgz \\in zenon_Vkc))", OF z_Hy z_Hkg])
    have z_Hgy: "(?z_hgz \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])" (is "?z_hgy")
    by (rule zenon_in_subsetof_0 [of "?z_hgz" "[''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''F''))&(((t[''arg''])=except((told[''arg'']), p, (a_chash_primea[p])))&((t[''ret''])=(told[''ret''])))))))))))", OF z_Hkj])
    show FALSE
    by (rule zenon_L4_ [OF z_Hgy z_Hic])
   qed
   have z_Him: "((?z_hgz[''arg'']) \\in FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>))))" (is "?z_him")
   proof (rule zenon_nnpp)
    assume z_Hil: "(~?z_him)"
    have z_Hkj: "(?z_hgz \\in ?z_hba)" (is "?z_hkj")
    by (rule subst [where P="(\<lambda>zenon_Vkc. (?z_hgz \\in zenon_Vkc))", OF z_Hy z_Hkg])
    have z_Hgy: "(?z_hgz \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])" (is "?z_hgy")
    by (rule zenon_in_subsetof_0 [of "?z_hgz" "[''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''F''))&(((t[''arg''])=except((told[''arg'']), p, (a_chash_primea[p])))&((t[''ret''])=(told[''ret''])))))))))))", OF z_Hkj])
    show FALSE
    by (rule zenon_L5_ [OF z_Hgy z_Hil])
   qed
   have z_Hiw: "((?z_hgz[''ret'']) \\in FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))" (is "?z_hiw")
   proof (rule zenon_nnpp)
    assume z_Hiv: "(~?z_hiw)"
    have z_Hkj: "(?z_hgz \\in ?z_hba)" (is "?z_hkj")
    by (rule subst [where P="(\<lambda>zenon_Vkc. (?z_hgz \\in zenon_Vkc))", OF z_Hy z_Hkg])
    have z_Hgy: "(?z_hgz \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])" (is "?z_hgy")
    by (rule zenon_in_subsetof_0 [of "?z_hgz" "[''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''F''))&(((t[''arg''])=except((told[''arg'']), p, (a_chash_primea[p])))&((t[''ret''])=(told[''ret''])))))))))))", OF z_Hkj])
    show FALSE
    by (rule zenon_L6_ [OF z_Hgy z_Hiv])
   qed
   show FALSE by (rule notE [OF z_Hki],
                  rule zenon_inrecordsetI4 [OF z_Hhl z_Hhr z_Hht z_Hid z_Him z_Hiw ])
  next
   assume z_Heh:"?z_heh" (is "?z_hei&?z_hel")
   have z_Hel: "?z_hel"
   by (rule zenon_and_1 [OF z_Heh])
   have z_Hkn_z_Hel: "(\\E x:((x \\in NodeSet)&bEx(NodeSet, (\<lambda>j. (((a_chash_primea=except(a_ca, p, x))&((a_dhash_primea=except(d, p, j))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''U''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))))))&((a_UFhash_primea=UF)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_iunde_uhash_primea=a_iunde_ua)&((a_iunde_vhash_primea=a_iunde_va)&(a_rethash_primea=ret))))))))))) == ?z_hel" (is "?z_hkn == _")
   by (unfold bEx_def)
   have z_Hkn: "?z_hkn" (is "\\E x : ?z_hkt(x)")
   by (unfold z_Hkn_z_Hel, fact z_Hel)
   have z_Hku: "?z_hkt((CHOOSE x:((x \\in NodeSet)&bEx(NodeSet, (\<lambda>j. (((a_chash_primea=except(a_ca, p, x))&((a_dhash_primea=except(d, p, j))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''U''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))))))&((a_UFhash_primea=UF)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_iunde_uhash_primea=a_iunde_ua)&((a_iunde_vhash_primea=a_iunde_va)&(a_rethash_primea=ret))))))))))))" (is "?z_hkw&?z_hkx")
   by (rule zenon_ex_choose_0 [of "?z_hkt", OF z_Hkn])
   have z_Hkx: "?z_hkx"
   by (rule zenon_and_1 [OF z_Hku])
   have z_Hky_z_Hkx: "(\\E x:((x \\in NodeSet)&(((a_chash_primea=except(a_ca, p, (CHOOSE x:((x \\in NodeSet)&bEx(NodeSet, (\<lambda>j. (((a_chash_primea=except(a_ca, p, x))&((a_dhash_primea=except(d, p, j))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''U''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))))))&((a_UFhash_primea=UF)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_iunde_uhash_primea=a_iunde_ua)&((a_iunde_vhash_primea=a_iunde_va)&(a_rethash_primea=ret)))))))))))))&((a_dhash_primea=except(d, p, x))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''U''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))))))&((a_UFhash_primea=UF)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_iunde_uhash_primea=a_iunde_ua)&((a_iunde_vhash_primea=a_iunde_va)&(a_rethash_primea=ret))))))))) == ?z_hkx" (is "?z_hky == _")
   by (unfold bEx_def)
   have z_Hky: "?z_hky" (is "\\E x : ?z_hlh(x)")
   by (unfold z_Hky_z_Hkx, fact z_Hkx)
   have z_Hli: "?z_hlh((CHOOSE x:((x \\in NodeSet)&(((a_chash_primea=except(a_ca, p, (CHOOSE x:((x \\in NodeSet)&bEx(NodeSet, (\<lambda>j. (((a_chash_primea=except(a_ca, p, x))&((a_dhash_primea=except(d, p, j))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''U''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))))))&((a_UFhash_primea=UF)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_iunde_uhash_primea=a_iunde_ua)&((a_iunde_vhash_primea=a_iunde_va)&(a_rethash_primea=ret)))))))))))))&((a_dhash_primea=except(d, p, x))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''U''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))))))&((a_UFhash_primea=UF)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_iunde_uhash_primea=a_iunde_ua)&((a_iunde_vhash_primea=a_iunde_va)&(a_rethash_primea=ret))))))))))" (is "?z_hlk&?z_hll")
   by (rule zenon_ex_choose_0 [of "?z_hlh", OF z_Hky])
   have z_Hll: "?z_hll" (is "?z_hlm&?z_hfm")
   by (rule zenon_and_1 [OF z_Hli])
   have z_Hlm: "?z_hlm" (is "?z_hlc&?z_hln")
   by (rule zenon_and_0 [OF z_Hll])
   have z_Hln: "?z_hln" (is "?z_hlo&?z_hev")
   by (rule zenon_and_1 [OF z_Hlm])
   have z_Hev: "?z_hev" (is "_=?z_hew")
   by (rule zenon_and_1 [OF z_Hln])
   have z_Hjt_z_Hf: "(~(a_Mhash_primea \\subseteq [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])) == (~?z_hje)" (is "?z_hjt == ?z_hf")
   by (unfold prod_def)
   have z_Hjt: "?z_hjt" (is "~?z_hju")
   by (unfold z_Hjt_z_Hf, fact z_Hf)
   have z_Hjv_z_Hjt: "(~bAll(a_Mhash_primea, (\<lambda>zenon_Vsb. (zenon_Vsb \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) == ?z_hjt" (is "?z_hjv == _")
   by (unfold subset_def)
   have z_Hjv: "?z_hjv" (is "~?z_hjw")
   by (unfold z_Hjv_z_Hjt, fact z_Hjt)
   have z_Hka_z_Hjv: "(~(\\A x:((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) == ?z_hjv" (is "?z_hka == _")
   by (unfold bAll_def)
   have z_Hka: "?z_hka" (is "~(\\A x : ?z_hkc(x))")
   by (unfold z_Hka_z_Hjv, fact z_Hjv)
   have z_Hkd: "(\\E x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))" (is "\\E x : ?z_hke(x)")
   by (rule zenon_notallex_0 [of "?z_hkc", OF z_Hka])
   have z_Hkf: "?z_hke((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))))" (is "~(?z_hkg=>?z_hkh)")
   by (rule zenon_ex_choose_0 [of "?z_hke", OF z_Hkd])
   have z_Hkg: "?z_hkg"
   by (rule zenon_notimply_0 [OF z_Hkf])
   have z_Hki: "(~?z_hkh)"
   by (rule zenon_notimply_1 [OF z_Hkf])
   let ?z_hgz = "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))"
   have z_Hhl: "isAFcn(?z_hgz)" (is "?z_hhl")
   proof (rule zenon_nnpp)
    assume z_Hhk: "(~?z_hhl)"
    have z_Hlp: "(?z_hgz \\in ?z_hew)" (is "?z_hlp")
    by (rule subst [where P="(\<lambda>zenon_Vkc. (?z_hgz \\in zenon_Vkc))", OF z_Hev z_Hkg])
    have z_Hgy: "(?z_hgz \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])" (is "?z_hgy")
    by (rule zenon_in_subsetof_0 [of "?z_hgz" "[''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''U''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))", OF z_Hlp])
    show FALSE
    by (rule zenon_L1_ [OF z_Hgy z_Hhk])
   qed
   have z_Hhr: "(DOMAIN(?z_hgz)={''sigma'', ''op'', ''arg'', ''ret''})" (is "?z_hhp=?z_hhq")
   proof (rule zenon_nnpp)
    assume z_Hho: "(?z_hhp~=?z_hhq)"
    have z_Hlp: "(?z_hgz \\in ?z_hew)" (is "?z_hlp")
    by (rule subst [where P="(\<lambda>zenon_Vkc. (?z_hgz \\in zenon_Vkc))", OF z_Hev z_Hkg])
    have z_Hgy: "(?z_hgz \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])" (is "?z_hgy")
    by (rule zenon_in_subsetof_0 [of "?z_hgz" "[''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''U''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))", OF z_Hlp])
    show FALSE
    by (rule zenon_L2_ [OF z_Hgy z_Hho])
   qed
   have z_Hht: "((?z_hgz[''sigma'']) \\in Idems)" (is "?z_hht")
   proof (rule zenon_nnpp)
    assume z_Hhs: "(~?z_hht)"
    have z_Hlp: "(?z_hgz \\in ?z_hew)" (is "?z_hlp")
    by (rule subst [where P="(\<lambda>zenon_Vkc. (?z_hgz \\in zenon_Vkc))", OF z_Hev z_Hkg])
    have z_Hgy: "(?z_hgz \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])" (is "?z_hgy")
    by (rule zenon_in_subsetof_0 [of "?z_hgz" "[''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''U''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))", OF z_Hlp])
    show FALSE
    by (rule zenon_L3_ [OF z_Hgy z_Hhs])
   qed
   have z_Hid: "((?z_hgz[''op'']) \\in FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT}))" (is "?z_hid")
   proof (rule zenon_nnpp)
    assume z_Hic: "(~?z_hid)"
    have z_Hlp: "(?z_hgz \\in ?z_hew)" (is "?z_hlp")
    by (rule subst [where P="(\<lambda>zenon_Vkc. (?z_hgz \\in zenon_Vkc))", OF z_Hev z_Hkg])
    have z_Hgy: "(?z_hgz \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])" (is "?z_hgy")
    by (rule zenon_in_subsetof_0 [of "?z_hgz" "[''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''U''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))", OF z_Hlp])
    show FALSE
    by (rule zenon_L4_ [OF z_Hgy z_Hic])
   qed
   have z_Him: "((?z_hgz[''arg'']) \\in FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>))))" (is "?z_him")
   proof (rule zenon_nnpp)
    assume z_Hil: "(~?z_him)"
    have z_Hlp: "(?z_hgz \\in ?z_hew)" (is "?z_hlp")
    by (rule subst [where P="(\<lambda>zenon_Vkc. (?z_hgz \\in zenon_Vkc))", OF z_Hev z_Hkg])
    have z_Hgy: "(?z_hgz \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])" (is "?z_hgy")
    by (rule zenon_in_subsetof_0 [of "?z_hgz" "[''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''U''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))", OF z_Hlp])
    show FALSE
    by (rule zenon_L5_ [OF z_Hgy z_Hil])
   qed
   have z_Hiw: "((?z_hgz[''ret'']) \\in FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))" (is "?z_hiw")
   proof (rule zenon_nnpp)
    assume z_Hiv: "(~?z_hiw)"
    have z_Hlp: "(?z_hgz \\in ?z_hew)" (is "?z_hlp")
    by (rule subst [where P="(\<lambda>zenon_Vkc. (?z_hgz \\in zenon_Vkc))", OF z_Hev z_Hkg])
    have z_Hgy: "(?z_hgz \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])" (is "?z_hgy")
    by (rule zenon_in_subsetof_0 [of "?z_hgz" "[''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''U''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))", OF z_Hlp])
    show FALSE
    by (rule zenon_L6_ [OF z_Hgy z_Hiv])
   qed
   show FALSE by (rule notE [OF z_Hki],
                  rule zenon_inrecordsetI4 [OF z_Hhl z_Hhr z_Hht z_Hid z_Him z_Hiw ])
  qed
 next
  assume z_Hfr:"?z_hfr" (is "?z_hfs&?z_hfv")
  have z_Hfv: "?z_hfv" (is "?z_hfw&?z_hfz")
  by (rule zenon_and_1 [OF z_Hfr])
  have z_Hfz: "?z_hfz" (is "?z_hga&?z_hgc")
  by (rule zenon_and_1 [OF z_Hfv])
  have z_Hgc: "?z_hgc" (is "?z_hgd&?z_hgv")
  by (rule zenon_and_1 [OF z_Hfz])
  have z_Hgd: "?z_hgd"
  by (rule zenon_and_0 [OF z_Hgc])
  have z_Hlq_z_Hgd: "(\\E x:((x \\in NodeSet)&bEx(NodeSet, (\<lambda>j. ((a_chash_primea=except(a_ca, p, x))&((a_dhash_primea=except(d, p, j))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''S''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret'']))))))))))))))))))) == ?z_hgd" (is "?z_hlq == _")
  by (unfold bEx_def)
  have z_Hlq: "?z_hlq" (is "\\E x : ?z_hlv(x)")
  by (unfold z_Hlq_z_Hgd, fact z_Hgd)
  have z_Hlw: "?z_hlv((CHOOSE x:((x \\in NodeSet)&bEx(NodeSet, (\<lambda>j. ((a_chash_primea=except(a_ca, p, x))&((a_dhash_primea=except(d, p, j))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''S''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret'']))))))))))))))))))))" (is "?z_hly&?z_hlz")
  by (rule zenon_ex_choose_0 [of "?z_hlv", OF z_Hlq])
  have z_Hlz: "?z_hlz"
  by (rule zenon_and_1 [OF z_Hlw])
  have z_Hma_z_Hlz: "(\\E x:((x \\in NodeSet)&((a_chash_primea=except(a_ca, p, (CHOOSE x:((x \\in NodeSet)&bEx(NodeSet, (\<lambda>j. ((a_chash_primea=except(a_ca, p, x))&((a_dhash_primea=except(d, p, j))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''S''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))))))))))))&((a_dhash_primea=except(d, p, x))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''S''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret'']))))))))))))))))) == ?z_hlz" (is "?z_hma == _")
  by (unfold bEx_def)
  have z_Hma: "?z_hma" (is "\\E x : ?z_hmg(x)")
  by (unfold z_Hma_z_Hlz, fact z_Hlz)
  have z_Hmh: "?z_hmg((CHOOSE x:((x \\in NodeSet)&((a_chash_primea=except(a_ca, p, (CHOOSE x:((x \\in NodeSet)&bEx(NodeSet, (\<lambda>j. ((a_chash_primea=except(a_ca, p, x))&((a_dhash_primea=except(d, p, j))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''S''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))))))))))))&((a_dhash_primea=except(d, p, x))&(a_Mhash_primea=subsetOf([''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))], (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''S''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret'']))))))))))))))))))" (is "?z_hmj&?z_hmk")
  by (rule zenon_ex_choose_0 [of "?z_hmg", OF z_Hma])
  have z_Hmk: "?z_hmk" (is "?z_hmd&?z_hml")
  by (rule zenon_and_1 [OF z_Hmh])
  have z_Hml: "?z_hml" (is "?z_hmm&?z_hgj")
  by (rule zenon_and_1 [OF z_Hmk])
  have z_Hgj: "?z_hgj" (is "_=?z_hgk")
  by (rule zenon_and_1 [OF z_Hml])
  have z_Hjt_z_Hf: "(~(a_Mhash_primea \\subseteq [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])) == (~?z_hje)" (is "?z_hjt == ?z_hf")
  by (unfold prod_def)
  have z_Hjt: "?z_hjt" (is "~?z_hju")
  by (unfold z_Hjt_z_Hf, fact z_Hf)
  have z_Hjv_z_Hjt: "(~bAll(a_Mhash_primea, (\<lambda>zenon_Vsb. (zenon_Vsb \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) == ?z_hjt" (is "?z_hjv == _")
  by (unfold subset_def)
  have z_Hjv: "?z_hjv" (is "~?z_hjw")
  by (unfold z_Hjv_z_Hjt, fact z_Hjt)
  have z_Hka_z_Hjv: "(~(\\A x:((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))) == ?z_hjv" (is "?z_hka == _")
  by (unfold bAll_def)
  have z_Hka: "?z_hka" (is "~(\\A x : ?z_hkc(x))")
  by (unfold z_Hka_z_Hjv, fact z_Hjv)
  have z_Hkd: "(\\E x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))" (is "\\E x : ?z_hke(x)")
  by (rule zenon_notallex_0 [of "?z_hkc", OF z_Hka])
  have z_Hkf: "?z_hke((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])))))" (is "~(?z_hkg=>?z_hkh)")
  by (rule zenon_ex_choose_0 [of "?z_hke", OF z_Hkd])
  have z_Hkg: "?z_hkg"
  by (rule zenon_notimply_0 [OF z_Hkf])
  have z_Hki: "(~?z_hkh)"
  by (rule zenon_notimply_1 [OF z_Hkf])
  let ?z_hgz = "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]))))"
  have z_Hhl: "isAFcn(?z_hgz)" (is "?z_hhl")
  proof (rule zenon_nnpp)
   assume z_Hhk: "(~?z_hhl)"
   have z_Hmn: "(?z_hgz \\in ?z_hgk)" (is "?z_hmn")
   by (rule subst [where P="(\<lambda>zenon_Vkc. (?z_hgz \\in zenon_Vkc))", OF z_Hgj z_Hkg])
   have z_Hgy: "(?z_hgz \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])" (is "?z_hgy")
   by (rule zenon_in_subsetof_0 [of "?z_hgz" "[''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''S''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))", OF z_Hmn])
   show FALSE
   by (rule zenon_L1_ [OF z_Hgy z_Hhk])
  qed
  have z_Hhr: "(DOMAIN(?z_hgz)={''sigma'', ''op'', ''arg'', ''ret''})" (is "?z_hhp=?z_hhq")
  proof (rule zenon_nnpp)
   assume z_Hho: "(?z_hhp~=?z_hhq)"
   have z_Hmn: "(?z_hgz \\in ?z_hgk)" (is "?z_hmn")
   by (rule subst [where P="(\<lambda>zenon_Vkc. (?z_hgz \\in zenon_Vkc))", OF z_Hgj z_Hkg])
   have z_Hgy: "(?z_hgz \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])" (is "?z_hgy")
   by (rule zenon_in_subsetof_0 [of "?z_hgz" "[''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''S''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))", OF z_Hmn])
   show FALSE
   by (rule zenon_L2_ [OF z_Hgy z_Hho])
  qed
  have z_Hht: "((?z_hgz[''sigma'']) \\in Idems)" (is "?z_hht")
  proof (rule zenon_nnpp)
   assume z_Hhs: "(~?z_hht)"
   have z_Hmn: "(?z_hgz \\in ?z_hgk)" (is "?z_hmn")
   by (rule subst [where P="(\<lambda>zenon_Vkc. (?z_hgz \\in zenon_Vkc))", OF z_Hgj z_Hkg])
   have z_Hgy: "(?z_hgz \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])" (is "?z_hgy")
   by (rule zenon_in_subsetof_0 [of "?z_hgz" "[''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''S''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))", OF z_Hmn])
   show FALSE
   by (rule zenon_L3_ [OF z_Hgy z_Hhs])
  qed
  have z_Hid: "((?z_hgz[''op'']) \\in FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT}))" (is "?z_hid")
  proof (rule zenon_nnpp)
   assume z_Hic: "(~?z_hid)"
   have z_Hmn: "(?z_hgz \\in ?z_hgk)" (is "?z_hmn")
   by (rule subst [where P="(\<lambda>zenon_Vkc. (?z_hgz \\in zenon_Vkc))", OF z_Hgj z_Hkg])
   have z_Hgy: "(?z_hgz \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])" (is "?z_hgy")
   by (rule zenon_in_subsetof_0 [of "?z_hgz" "[''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''S''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))", OF z_Hmn])
   show FALSE
   by (rule zenon_L4_ [OF z_Hgy z_Hic])
  qed
  have z_Him: "((?z_hgz[''arg'']) \\in FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup Product(<<NodeSet, NodeSet>>))))" (is "?z_him")
  proof (rule zenon_nnpp)
   assume z_Hil: "(~?z_him)"
   have z_Hmn: "(?z_hgz \\in ?z_hgk)" (is "?z_hmn")
   by (rule subst [where P="(\<lambda>zenon_Vkc. (?z_hgz \\in zenon_Vkc))", OF z_Hgj z_Hkg])
   have z_Hgy: "(?z_hgz \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])" (is "?z_hgy")
   by (rule zenon_in_subsetof_0 [of "?z_hgz" "[''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''S''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))", OF z_Hmn])
   show FALSE
   by (rule zenon_L5_ [OF z_Hgy z_Hil])
  qed
  have z_Hiw: "((?z_hgz[''ret'']) \\in FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))" (is "?z_hiw")
  proof (rule zenon_nnpp)
   assume z_Hiv: "(~?z_hiw)"
   have z_Hmn: "(?z_hgz \\in ?z_hgk)" (is "?z_hmn")
   by (rule subst [where P="(\<lambda>zenon_Vkc. (?z_hgz \\in zenon_Vkc))", OF z_Hgj z_Hkg])
   have z_Hgy: "(?z_hgz \\in [''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))])" (is "?z_hgy")
   by (rule zenon_in_subsetof_0 [of "?z_hgz" "[''sigma'' : (Idems), ''op'' : (FuncSet(PROCESSES, {''F'', ''U'', ''S'', BOT})), ''arg'' : (FuncSet(PROCESSES, (({BOT} \\cup NodeSet) \\cup prod(NodeSet, NodeSet)))), ''ret'' : (FuncSet(PROCESSES, ({ACK, BOT, TRUE, FALSE} \\cup NodeSet)))]" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&((((told[''op''])[p])=BOT)&((((told[''arg''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''op''])=except((told[''op'']), p, ''S''))&(((t[''arg''])=except((told[''arg'']), p, <<(a_chash_primea[p]), (a_dhash_primea[p])>>))&((t[''ret''])=(told[''ret''])))))))))))", OF z_Hmn])
   show FALSE
   by (rule zenon_L6_ [OF z_Hgy z_Hiv])
  qed
  show FALSE by (rule notE [OF z_Hki],
                 rule zenon_inrecordsetI4 [OF z_Hhl z_Hhr z_Hht z_Hid z_Him z_Hiw ])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 109"; *} qed
lemma ob'69:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes UF UF'
fixes u u'
fixes v v'
fixes a_iunde_ua a_iunde_ua'
fixes a_iunde_va a_iunde_va'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition NodeSet suppressed *)
(* usable definition varlist suppressed *)
(* usable definition Idems suppressed *)
(* usable definition NodeToIdFuncs suppressed *)
(* usable definition UFId_StateSet suppressed *)
(* usable definition SmallerRep suppressed *)
(* usable definition LargerRep suppressed *)
(* usable definition URep suppressed *)
(* usable definition CandID suppressed *)
(* usable definition IDUpdate suppressed *)
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitUF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition UFUnite suppressed *)
(* usable definition MetaConfigUnite suppressed *)
(* usable definition Init suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition S5 suppressed *)
(* usable definition S6 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition UFSSpec suppressed *)
assumes v'58: "((((pc) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''S4''), (''S5''), (''S6''), (''SR'')})]))) & (((UF) \<in> (a_UFIdunde_StateSeta))) & (((u) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((a_iunde_ua) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))]))) & (((a_iunde_va) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE), (BOT)}) \<union> (NodeSet)))]))) & (((M) \<subseteq> ([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]))))"
fixes p
assumes p_in : "(p \<in> (PROCESSES))"
assumes v'60: "((Step ((p))))"
assumes v'73: "((((a_iunde_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))])))"
assumes v'74: "((((a_Mhash_primea :: c)) \<subseteq> ([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)])))"
assumes v'75: "((((CandID ((fapply ((v), (p)))))) \<subseteq> (((Nat) \<union> ({((0))})))))"
assumes v'77: "((((a_UFhash_primea :: c)) \<in> (a_UFIdunde_StateSeta)))"
assumes v'78: "((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE), (BOT)}) \<union> (NodeSet)))])))"
assumes v'79: "((\<exists> newId \<in> ((IDUpdate ((fapply ((v), (p)))))) : ((((a_UFhash_primea :: c)) = (((''rep'' :> (fapply ((UF), (''rep'')))) @@ (''id'' :> (newId))))))) & (cond(((((greater ((fapply ((a_iunde_ua), (p))), (fapply (((a_iunde_vhash_primea :: c)), (p)))))) \<and> ((greater ((fapply (((a_iunde_vhash_primea :: c)), (p))), ((0))))))), (((((a_rethash_primea :: c)) = ([(ret) EXCEPT ![(p)] = (FALSE)]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''SR'')]))) & ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''ret''))) = ([(fapply ((told), (''ret''))) EXCEPT ![(p)] = (cond((((fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[0])))))) = (fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[Succ[0]])))))))), (TRUE), (FALSE)))]))) & (((fapply ((t), (''op''))) = (fapply ((told), (''op''))))) & (((fapply ((t), (''arg''))) = (fapply ((told), (''arg'')))))))))))), (((((a_rethash_primea :: c)) = (ret))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''S5'')]))) & ((((a_Mhash_primea :: c)) = (M)))))))"
assumes v'80: "(((fapply ((pc), (p))) = (''S4'')))"
assumes v'81: "((((a_iunde_vhash_primea :: c)) = ([(a_iunde_va) EXCEPT ![(p)] = (cond((((fapply ((fapply ((UF), (''rep''))), (fapply ((v), (p))))) = (fapply ((v), (p))))), (fapply ((fapply ((UF), (''id''))), (fapply ((v), (p))))), ((0))))])))"
assumes v'82: "((((a_uhash_primea :: c)) = (u)))"
assumes v'83: "((((a_vhash_primea :: c)) = (v)))"
assumes v'84: "((((a_iunde_uhash_primea :: c)) = (a_iunde_ua)))"
assumes v'85: "((((a_chash_primea :: c)) = (a_ca)))"
assumes v'86: "((((a_dhash_primea :: c)) = (d)))"
assumes v'87: "((((a_Mhash_primea :: c)) = (M)))"
shows "(((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''S4''), (''S5''), (''S6''), (''SR'')})]))) & ((((a_UFhash_primea :: c)) \<in> (a_UFIdunde_StateSeta))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & ((((a_iunde_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))]))) & ((((a_iunde_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE), (BOT)}) \<union> (NodeSet)))]))) & ((((a_Mhash_primea :: c)) \<subseteq> ([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]))))"(is "PROP ?ob'69")
proof -
ML_command {* writeln "*** TLAPS ENTER 69"; *}
show "PROP ?ob'69"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 69"; *} qed
lemma ob'82:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes UF UF'
fixes u u'
fixes v v'
fixes a_iunde_ua a_iunde_ua'
fixes a_iunde_va a_iunde_va'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition NodeSet suppressed *)
(* usable definition varlist suppressed *)
(* usable definition Idems suppressed *)
(* usable definition NodeToIdFuncs suppressed *)
(* usable definition UFId_StateSet suppressed *)
(* usable definition SmallerRep suppressed *)
(* usable definition LargerRep suppressed *)
(* usable definition URep suppressed *)
(* usable definition CandID suppressed *)
(* usable definition IDUpdate suppressed *)
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition Configs suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitUF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition UFUnite suppressed *)
(* usable definition MetaConfigUnite suppressed *)
(* usable definition Init suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition S5 suppressed *)
(* usable definition S6 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition UFSSpec suppressed *)
(* usable definition PCTypeOK suppressed *)
(* usable definition UFTypeOK suppressed *)
(* usable definition uTypeOK suppressed *)
(* usable definition vTypeOK suppressed *)
(* usable definition i_uTypeOK suppressed *)
(* usable definition i_vTypeOK suppressed *)
(* usable definition cTypeOK suppressed *)
(* usable definition dTypeOK suppressed *)
(* usable definition MTypeOK suppressed *)
assumes v'68: "((PCTypeOK) & (UFTypeOK) & (uTypeOK) & (vTypeOK) & (a_iunde_uTypeOKa) & (a_iunde_vTypeOKa) & (cTypeOK) & (dTypeOK) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE), (BOT)}) \<union> (NodeSet)))]))) & (MTypeOK))"
fixes p
assumes p_in : "(p \<in> (PROCESSES))"
assumes v'70: "((Step ((p))))"
assumes v'83: "((((a_iunde_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))])))"
assumes v'84: "((((a_Mhash_primea :: c)) \<subseteq> (Configs)))"
assumes v'85: "((((CandID ((fapply ((v), (p)))))) \<subseteq> (((Nat) \<union> ({((0))})))))"
assumes v'87: "((((a_UFhash_primea :: c)) \<in> (a_UFIdunde_StateSeta)))"
assumes v'90: "((\<exists> newId \<in> ((IDUpdate ((fapply ((v), (p)))))) : ((((a_UFhash_primea :: c)) = (((''rep'' :> (fapply ((UF), (''rep'')))) @@ (''id'' :> (newId))))))) & (cond(((((greater ((fapply ((a_iunde_ua), (p))), (fapply (((a_iunde_vhash_primea :: c)), (p)))))) \<and> ((greater ((fapply (((a_iunde_vhash_primea :: c)), (p))), ((0))))))), (((((a_rethash_primea :: c)) = ([(ret) EXCEPT ![(p)] = (FALSE)]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''SR'')]))) & ((((a_Mhash_primea :: c)) = (subsetOf((Configs), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''ret''))) = ([(fapply ((told), (''ret''))) EXCEPT ![(p)] = (cond((((fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[0])))))) = (fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[Succ[0]])))))))), (TRUE), (FALSE)))]))) & (((fapply ((t), (''op''))) = (fapply ((told), (''op''))))) & (((fapply ((t), (''arg''))) = (fapply ((told), (''arg'')))))))))))), (((((a_rethash_primea :: c)) = (ret))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''S5'')]))) & ((((a_Mhash_primea :: c)) = (M)))))))"
assumes v'91: "(((fapply ((pc), (p))) = (''S4'')))"
assumes v'92: "((((a_iunde_vhash_primea :: c)) = ([(a_iunde_va) EXCEPT ![(p)] = (cond((((fapply ((fapply ((UF), (''rep''))), (fapply ((v), (p))))) = (fapply ((v), (p))))), (fapply ((fapply ((UF), (''id''))), (fapply ((v), (p))))), ((0))))])))"
assumes v'93: "((((a_uhash_primea :: c)) = (u)))"
assumes v'94: "((((a_vhash_primea :: c)) = (v)))"
assumes v'95: "((((a_iunde_uhash_primea :: c)) = (a_iunde_ua)))"
assumes v'96: "((((a_chash_primea :: c)) = (a_ca)))"
assumes v'97: "((((a_dhash_primea :: c)) = (d)))"
assumes v'98: "((((a_Mhash_primea :: c)) = (M)))"
shows "((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE), (BOT)}) \<union> (NodeSet)))])))"(is "PROP ?ob'82")
proof -
ML_command {* writeln "*** TLAPS ENTER 82"; *}
show "PROP ?ob'82"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 82"; *} qed
lemma ob'107:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes UF UF'
fixes u u'
fixes v v'
fixes a_iunde_ua a_iunde_ua'
fixes a_iunde_va a_iunde_va'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition NodeSet suppressed *)
(* usable definition varlist suppressed *)
(* usable definition Idems suppressed *)
(* usable definition NodeToIdFuncs suppressed *)
(* usable definition UFId_StateSet suppressed *)
(* usable definition SmallerRep suppressed *)
(* usable definition LargerRep suppressed *)
(* usable definition URep suppressed *)
(* usable definition CandID suppressed *)
(* usable definition IDUpdate suppressed *)
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitUF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition UFUnite suppressed *)
(* usable definition MetaConfigUnite suppressed *)
(* usable definition Init suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition S4 suppressed *)
(* usable definition S5 suppressed *)
(* usable definition S6 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition UFSSpec suppressed *)
assumes v'58: "((((pc) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''S4''), (''S5''), (''S6''), (''SR'')})]))) & (((UF) \<in> (a_UFIdunde_StateSeta))) & (((u) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((a_iunde_ua) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))]))) & (((a_iunde_va) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE), (BOT)}) \<union> (NodeSet)))]))) & (((M) \<subseteq> ([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]))))"
fixes p
assumes p_in : "(p \<in> (PROCESSES))"
assumes v'60: "((Step ((p))))"
assumes v'77: "((((a_Mhash_primea :: c)) \<subseteq> ([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)])))"
assumes v'78: "((((((((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''F1'')]))) & (\<exists> i \<in> (NodeSet) : (((((((a_chash_primea :: c)) = ([(a_ca) EXCEPT ![(p)] = (i)]))) & ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((fapply ((told), (''op''))), (p))) = (BOT))) & (((fapply ((fapply ((told), (''arg''))), (p))) = (BOT))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''op''))) = ([(fapply ((told), (''op''))) EXCEPT ![(p)] = (''F'')]))) & (((fapply ((t), (''arg''))) = ([(fapply ((told), (''arg''))) EXCEPT ![(p)] = (fapply (((a_chash_primea :: c)), (p)))]))) & (((fapply ((t), (''ret''))) = (fapply ((told), (''ret'')))))))))))) \<and> (((((a_UFhash_primea :: c)) = (UF))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_iunde_uhash_primea :: c)) = (a_iunde_ua))) & ((((a_iunde_vhash_primea :: c)) = (a_iunde_va))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_rethash_primea :: c)) = (ret)))))))) \<or> (((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U1'')]))) & (\<exists> i \<in> (NodeSet) : (\<exists> j \<in> (NodeSet) : (((((((a_chash_primea :: c)) = ([(a_ca) EXCEPT ![(p)] = (i)]))) & ((((a_dhash_primea :: c)) = ([(d) EXCEPT ![(p)] = (j)]))) & ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((fapply ((told), (''op''))), (p))) = (BOT))) & (((fapply ((fapply ((told), (''arg''))), (p))) = (BOT))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''op''))) = ([(fapply ((told), (''op''))) EXCEPT ![(p)] = (''U'')]))) & (((fapply ((t), (''arg''))) = ([(fapply ((told), (''arg''))) EXCEPT ![(p)] = (<<(fapply (((a_chash_primea :: c)), (p))), (fapply (((a_dhash_primea :: c)), (p)))>>)]))) & (((fapply ((t), (''ret''))) = (fapply ((told), (''ret'')))))))))))) \<and> (((((a_UFhash_primea :: c)) = (UF))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_iunde_uhash_primea :: c)) = (a_iunde_ua))) & ((((a_iunde_vhash_primea :: c)) = (a_iunde_va))) & ((((a_rethash_primea :: c)) = (ret))))))))))) \<or> (((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''S1'')]))) & ((((a_iunde_uhash_primea :: c)) = ([(a_iunde_ua) EXCEPT ![(p)] = ((0))]))) & ((((a_iunde_vhash_primea :: c)) = ([(a_iunde_va) EXCEPT ![(p)] = ((0))]))) & (\<exists> i \<in> (NodeSet) : (\<exists> j \<in> (NodeSet) : (((((a_chash_primea :: c)) = ([(a_ca) EXCEPT ![(p)] = (i)]))) & ((((a_dhash_primea :: c)) = ([(d) EXCEPT ![(p)] = (j)]))) & ((((a_Mhash_primea :: c)) = (subsetOf(([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((fapply ((told), (''op''))), (p))) = (BOT))) & (((fapply ((fapply ((told), (''arg''))), (p))) = (BOT))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''op''))) = ([(fapply ((told), (''op''))) EXCEPT ![(p)] = (''S'')]))) & (((fapply ((t), (''arg''))) = ([(fapply ((told), (''arg''))) EXCEPT ![(p)] = (<<(fapply (((a_chash_primea :: c)), (p))), (fapply (((a_dhash_primea :: c)), (p)))>>)]))) & (((fapply ((t), (''ret''))) = (fapply ((told), (''ret'')))))))))))))) & (((((a_UFhash_primea :: c)) = (UF))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_rethash_primea :: c)) = (ret))))))))"
assumes v'79: "(((fapply ((pc), (p))) = (''0'')))"
shows "(((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''S4''), (''S5''), (''S6''), (''SR'')})]))) & ((((a_UFhash_primea :: c)) \<in> (a_UFIdunde_StateSeta))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & ((((a_iunde_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))]))) & ((((a_iunde_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (((Nat) \<union> ({((0))})))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE), (BOT)}) \<union> (NodeSet)))]))) & ((((a_Mhash_primea :: c)) \<subseteq> ([''sigma'' : (Idems), ''op'' : (OpSet), ''arg'' : (ArgSet), ''ret'' : (ReturnSet)]))))"(is "PROP ?ob'107")
proof -
ML_command {* writeln "*** TLAPS ENTER 107"; *}
show "PROP ?ob'107"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 107"; *} qed
end
