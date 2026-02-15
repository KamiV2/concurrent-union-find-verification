(* automatically generated -- do not edit manually *)
theory SameSetTypeOK imports Constant Zenon begin
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

lemma ob'2:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes F F'
fixes u u'
fixes v v'
fixes w w'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition NodeSet suppressed *)
(* usable definition varlist suppressed *)
(* usable definition PCSet suppressed *)
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition UFAbsSet suppressed *)
(* usable definition StateSet suppressed *)
(* usable definition Configs suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition UFUniteShared suppressed *)
(* usable definition UFSUnite suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition SameSetSpec suppressed *)
(* usable definition Valid_pc suppressed *)
(* usable definition Valid_F suppressed *)
(* usable definition Valid_u suppressed *)
(* usable definition Valid_v suppressed *)
(* usable definition Valid_w suppressed *)
(* usable definition Valid_c suppressed *)
(* usable definition Valid_d suppressed *)
(* usable definition Valid_M suppressed *)
(* usable definition Valid_ret suppressed *)
assumes v'57: "((((((pc) = ([ p \<in> (PROCESSES)  \<mapsto> (''0'')]))) & (((F) = (InitF))) & (((u) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((w) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> (NodeSet)))]))) & (((M) = ({(((''sigma'' :> (InitState)) @@ (''ret'' :> (InitRet)) @@ (''op'' :> (InitOp)) @@ (''arg'' :> (InitArg))))})))) \<Longrightarrow> ((a_Validunde_pca) & (a_Validunde_Fa) & (a_Validunde_ua) & (a_Validunde_va) & (a_Validunde_wa) & (a_Validunde_ca) & (a_Validunde_da) & (a_Validunde_Ma) & (a_Validunde_reta))))"
shows "((((((pc) = ([ p \<in> (PROCESSES)  \<mapsto> (''0'')]))) & (((F) = (InitF))) & (((u) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((w) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> (NodeSet)))]))) & (((M) = ({(((''sigma'' :> (InitState)) @@ (''ret'' :> (InitRet)) @@ (''op'' :> (InitOp)) @@ (''arg'' :> (InitArg))))})))) \<Rightarrow> ((a_Validunde_pca) & (a_Validunde_Fa) & (a_Validunde_ua) & (a_Validunde_va) & (a_Validunde_wa) & (a_Validunde_ca) & (a_Validunde_da) & (a_Validunde_Ma) & (a_Validunde_reta))))"(is "PROP ?ob'2")
proof -
ML_command {* writeln "*** TLAPS ENTER 2"; *}
show "PROP ?ob'2"

(* BEGIN ZENON INPUT
;; file=SameSetTypeOK.tlaps/tlapm_37d3a9.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >SameSetTypeOK.tlaps/tlapm_37d3a9.znn.out
;; obligation #2
$hyp "v'57" (=> (/\ (= pc (TLA.Fcn PROCESSES ((p) "0"))) (= F InitF)
(TLA.in u (TLA.FuncSet PROCESSES NodeSet)) (TLA.in v
(TLA.FuncSet PROCESSES NodeSet)) (TLA.in w (TLA.FuncSet PROCESSES NodeSet))
(TLA.in a_ca (TLA.FuncSet PROCESSES NodeSet)) (TLA.in d
(TLA.FuncSet PROCESSES NodeSet)) (TLA.in ret
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.) NodeSet))) (= M
(TLA.set (TLA.record "sigma" InitState "ret" InitRet "op" InitOp "arg" InitArg)))) (/\ a_Validunde_pca
a_Validunde_Fa a_Validunde_ua a_Validunde_va a_Validunde_wa a_Validunde_ca
a_Validunde_da a_Validunde_Ma a_Validunde_reta))
$goal (=> (/\ (= pc (TLA.Fcn PROCESSES ((p) "0"))) (= F InitF) (TLA.in u
(TLA.FuncSet PROCESSES NodeSet)) (TLA.in v (TLA.FuncSet PROCESSES NodeSet))
(TLA.in w (TLA.FuncSet PROCESSES NodeSet)) (TLA.in a_ca
(TLA.FuncSet PROCESSES NodeSet)) (TLA.in d (TLA.FuncSet PROCESSES NodeSet))
(TLA.in ret (TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.) NodeSet)))
(= M
(TLA.set (TLA.record "sigma" InitState "ret" InitRet "op" InitOp "arg" InitArg))))
(/\ a_Validunde_pca a_Validunde_Fa a_Validunde_ua a_Validunde_va
a_Validunde_wa a_Validunde_ca a_Validunde_da a_Validunde_Ma
a_Validunde_reta))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((pc=Fcn(PROCESSES, (\<lambda>p. ''0'')))&((F=InitF)&((u \\in FuncSet(PROCESSES, NodeSet))&((v \\in FuncSet(PROCESSES, NodeSet))&((w \\in FuncSet(PROCESSES, NodeSet))&((a_ca \\in FuncSet(PROCESSES, NodeSet))&((d \\in FuncSet(PROCESSES, NodeSet))&((ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup NodeSet)))&(M={(''sigma'' :> (InitState) @@ ''ret'' :> (InitRet) @@ ''op'' :> (InitOp) @@ ''arg'' :> (InitArg))})))))))))=>(a_Validunde_pca&(a_Validunde_Fa&(a_Validunde_ua&(a_Validunde_va&(a_Validunde_wa&(a_Validunde_ca&(a_Validunde_da&(a_Validunde_Ma&a_Validunde_reta)))))))))" (is "?z_hc=>?z_hbz")
 using v'57 by blast
 assume z_Hb:"(~(?z_hc=>?z_hbz))"
 show FALSE
 by (rule notE [OF z_Hb z_Ha])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 2"; *} qed
lemma ob'21:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes F F'
fixes u u'
fixes v v'
fixes w w'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition NodeSet suppressed *)
(* usable definition varlist suppressed *)
(* usable definition PCSet suppressed *)
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition UFAbsSet suppressed *)
(* usable definition StateSet suppressed *)
(* usable definition Configs suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition UFUniteShared suppressed *)
(* usable definition UFSUnite suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition SameSetSpec suppressed *)
(* usable definition Valid_pc suppressed *)
(* usable definition Valid_F suppressed *)
(* usable definition Valid_u suppressed *)
(* usable definition Valid_v suppressed *)
(* usable definition Valid_w suppressed *)
(* usable definition Valid_c suppressed *)
(* usable definition Valid_d suppressed *)
(* usable definition Valid_M suppressed *)
assumes v'56: "((((u) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((w) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> (NodeSet)))]))))"
assumes v'57: "(((pc) = ([ p \<in> (PROCESSES)  \<mapsto> (''0'')])))"
assumes v'58: "(((F) = (InitF)))"
assumes v'59: "(((M) = ({(((''sigma'' :> (InitState)) @@ (''ret'' :> (InitRet)) @@ (''op'' :> (InitOp)) @@ (''arg'' :> (InitArg))))})))"
shows "(((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> (NodeSet)))])))"(is "PROP ?ob'21")
proof -
ML_command {* writeln "*** TLAPS ENTER 21"; *}
show "PROP ?ob'21"

(* BEGIN ZENON INPUT
;; file=SameSetTypeOK.tlaps/tlapm_861aef.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >SameSetTypeOK.tlaps/tlapm_861aef.znn.out
;; obligation #21
$hyp "v'56" (/\ (TLA.in u (TLA.FuncSet PROCESSES NodeSet)) (TLA.in v
(TLA.FuncSet PROCESSES NodeSet)) (TLA.in w (TLA.FuncSet PROCESSES NodeSet))
(TLA.in a_ca (TLA.FuncSet PROCESSES NodeSet)) (TLA.in d
(TLA.FuncSet PROCESSES NodeSet)) (TLA.in ret
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
NodeSet))))
$hyp "v'57" (= pc (TLA.Fcn PROCESSES ((p) "0")))
$hyp "v'58" (= F InitF)
$hyp "v'59" (= M
(TLA.set (TLA.record "sigma" InitState "ret" InitRet "op" InitOp "arg" InitArg)))
$goal (TLA.in ret (TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
NodeSet)))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((u \\in FuncSet(PROCESSES, NodeSet))&((v \\in FuncSet(PROCESSES, NodeSet))&((w \\in FuncSet(PROCESSES, NodeSet))&((a_ca \\in FuncSet(PROCESSES, NodeSet))&((d \\in FuncSet(PROCESSES, NodeSet))&(ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup NodeSet))))))))" (is "?z_hf&?z_hk")
 using v'56 by blast
 assume z_He:"(~(ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup NodeSet))))" (is "~?z_hw")
 have z_Hk: "?z_hk" (is "?z_hl&?z_hn")
 by (rule zenon_and_1 [OF z_Ha])
 have z_Hn: "?z_hn" (is "?z_ho&?z_hq")
 by (rule zenon_and_1 [OF z_Hk])
 have z_Hq: "?z_hq" (is "?z_hr&?z_ht")
 by (rule zenon_and_1 [OF z_Hn])
 have z_Ht: "?z_ht" (is "?z_hu&_")
 by (rule zenon_and_1 [OF z_Hq])
 have z_Hw: "?z_hw"
 by (rule zenon_and_1 [OF z_Ht])
 show FALSE
 by (rule notE [OF z_He z_Hw])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 21"; *} qed
lemma ob'22:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes F F'
fixes u u'
fixes v v'
fixes w w'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition StateSet suppressed *)
(* usable definition Configs suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition Init suppressed *)
(* usable definition UFUniteShared suppressed *)
(* usable definition UFSUnite suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition SameSetSpec suppressed *)
assumes v'44: "((((((pc) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & (((F) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & (((u) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((w) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((M) \<in> ((SUBSET (Configs))))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))) \<and> (((\<exists> p \<in> (PROCESSES) : (((a_F1a ((p)))) | ((FR ((p)))) | ((a_U1a ((p)))) | ((UR ((p)))) | ((a_S1a ((p)))) | ((a_S2a ((p)))) | ((a_S3a ((p)))) | ((SR ((p)))) | ((Decide ((p)))))) \<or> (((((a_pchash_primea :: c)) = (pc))) & ((((a_Fhash_primea :: c)) = (F))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_whash_primea :: c)) = (w))) & ((((a_chash_primea :: c)) = (a_ca))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_Mhash_primea :: c)) = (M))) & ((((a_rethash_primea :: c)) = (ret))))))))"
assumes v'57: "((\<And> p :: c. p \<in> (PROCESSES) \<Longrightarrow> (((Decide ((p)))) \<Longrightarrow> (((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))))))"
assumes v'58: "((\<And> p :: c. p \<in> (PROCESSES) \<Longrightarrow> (((a_F1a ((p)))) \<Longrightarrow> (((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))))))"
assumes v'59: "((\<And> p :: c. p \<in> (PROCESSES) \<Longrightarrow> (((FR ((p)))) \<Longrightarrow> (((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))))))"
assumes v'60: "((\<And> p :: c. p \<in> (PROCESSES) \<Longrightarrow> (((a_U1a ((p)))) \<Longrightarrow> (((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))))))"
assumes v'61: "((\<And> p :: c. p \<in> (PROCESSES) \<Longrightarrow> (((UR ((p)))) \<Longrightarrow> (((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))))))"
assumes v'62: "((\<And> p :: c. p \<in> (PROCESSES) \<Longrightarrow> (((a_S1a ((p)))) \<Longrightarrow> (((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))))))"
assumes v'63: "((\<And> p :: c. p \<in> (PROCESSES) \<Longrightarrow> (((a_S2a ((p)))) \<Longrightarrow> (((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))))))"
assumes v'64: "((\<And> p :: c. p \<in> (PROCESSES) \<Longrightarrow> (((a_S3a ((p)))) \<Longrightarrow> (((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))))))"
assumes v'65: "((\<And> p :: c. p \<in> (PROCESSES) \<Longrightarrow> (((SR ((p)))) \<Longrightarrow> (((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))))))"
assumes v'66: "(((((((a_pchash_primea :: c)) = (pc))) & ((((a_Fhash_primea :: c)) = (F))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_whash_primea :: c)) = (w))) & ((((a_chash_primea :: c)) = (a_ca))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_Mhash_primea :: c)) = (M))) & ((((a_rethash_primea :: c)) = (ret)))) \<Longrightarrow> (((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))]))))))"
shows "(((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))]))))"(is "PROP ?ob'22")
proof -
ML_command {* writeln "*** TLAPS ENTER 22"; *}
show "PROP ?ob'22"

(* BEGIN ZENON INPUT
;; file=SameSetTypeOK.tlaps/tlapm_c487b9.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >SameSetTypeOK.tlaps/tlapm_c487b9.znn.out
;; obligation #22
$hyp "v'44" (/\ (/\ (TLA.in pc
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in F (TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i))))))) (TLA.in u
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in v
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in w
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_ca (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in d (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in M (TLA.SUBSET Configs)) (TLA.in ret
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0) N)))))
(\/ (TLA.bEx PROCESSES ((p) (\/ (a_F1a p) (FR p) (a_U1a p) (UR p) (a_S1a p)
(a_S2a p) (a_S3a p) (SR p) (Decide p)))) (/\ (= a_pchash_primea pc)
(= a_Fhash_primea F) (= a_uhash_primea u) (= a_vhash_primea v)
(= a_whash_primea w) (= a_chash_primea a_ca) (= a_dhash_primea d)
(= a_Mhash_primea M) (= a_rethash_primea
ret))))
$hyp "v'57" (TLA.bAll PROCESSES ((p) (=> (Decide p) (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N))))))))
$hyp "v'58" (TLA.bAll PROCESSES ((p) (=> (a_F1a p) (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N))))))))
$hyp "v'59" (TLA.bAll PROCESSES ((p) (=> (FR p) (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N))))))))
$hyp "v'60" (TLA.bAll PROCESSES ((p) (=> (a_U1a p) (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N))))))))
$hyp "v'61" (TLA.bAll PROCESSES ((p) (=> (UR p) (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N))))))))
$hyp "v'62" (TLA.bAll PROCESSES ((p) (=> (a_S1a p) (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N))))))))
$hyp "v'63" (TLA.bAll PROCESSES ((p) (=> (a_S2a p) (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N))))))))
$hyp "v'64" (TLA.bAll PROCESSES ((p) (=> (a_S3a p) (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N))))))))
$hyp "v'65" (TLA.bAll PROCESSES ((p) (=> (SR p) (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N))))))))
$hyp "v'66" (=> (/\ (= a_pchash_primea pc) (= a_Fhash_primea F)
(= a_uhash_primea u) (= a_vhash_primea v) (= a_whash_primea w)
(= a_chash_primea a_ca) (= a_dhash_primea d) (= a_Mhash_primea M)
(= a_rethash_primea ret)) (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N))))))
$goal (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((pc \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((F \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((u \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((v \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((w \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_ca \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((d \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((M \\in SUBSET(Configs))&(ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))))))))&(bEx(PROCESSES, (\<lambda>p. (a_F1a(p)|(FR(p)|(a_U1a(p)|(UR(p)|(a_S1a(p)|(a_S2a(p)|(a_S3a(p)|(SR(p)|Decide(p)))))))))))|((a_pchash_primea=pc)&((a_Fhash_primea=F)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_whash_primea=w)&((a_chash_primea=a_ca)&((a_dhash_primea=d)&((a_Mhash_primea=M)&(a_rethash_primea=ret)))))))))))" (is "?z_hm&?z_hcu")
 using v'44 by blast
 have z_Hb:"bAll(PROCESSES, (\<lambda>p. (Decide(p)=>((a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_Mhash_primea \\in SUBSET(Configs))&(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))))))))))))" (is "?z_hb")
 using v'57 by blast
 have z_Hd:"bAll(PROCESSES, (\<lambda>p. (FR(p)=>((a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_Mhash_primea \\in SUBSET(Configs))&(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))))))))))))" (is "?z_hd")
 using v'59 by blast
 have z_Hf:"bAll(PROCESSES, (\<lambda>p. (UR(p)=>((a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_Mhash_primea \\in SUBSET(Configs))&(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))))))))))))" (is "?z_hf")
 using v'61 by blast
 have z_Hh:"bAll(PROCESSES, (\<lambda>p. (a_S2a(p)=>((a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_Mhash_primea \\in SUBSET(Configs))&(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))))))))))))" (is "?z_hh")
 using v'63 by blast
 have z_Hj:"bAll(PROCESSES, (\<lambda>p. (SR(p)=>((a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_Mhash_primea \\in SUBSET(Configs))&(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))))))))))))" (is "?z_hj")
 using v'65 by blast
 have z_Hk:"(((a_pchash_primea=pc)&((a_Fhash_primea=F)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_whash_primea=w)&((a_chash_primea=a_ca)&((a_dhash_primea=d)&((a_Mhash_primea=M)&(a_rethash_primea=ret)))))))))=>((a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_Mhash_primea \\in SUBSET(Configs))&(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))))))))))" (is "?z_hdp=>?z_her")
 using v'66 by blast
 have z_Hi:"bAll(PROCESSES, (\<lambda>p. (a_S3a(p)=>?z_her)))" (is "?z_hi")
 using v'64 by blast
 have z_Hg:"bAll(PROCESSES, (\<lambda>p. (a_S1a(p)=>?z_her)))" (is "?z_hg")
 using v'62 by blast
 have z_He:"bAll(PROCESSES, (\<lambda>p. (a_U1a(p)=>?z_her)))" (is "?z_he")
 using v'60 by blast
 have z_Hc:"bAll(PROCESSES, (\<lambda>p. (a_F1a(p)=>?z_her)))" (is "?z_hc")
 using v'58 by blast
 assume z_Hl:"(~?z_her)" (is "~(?z_hes&?z_het)")
 have z_Hcu: "?z_hcu" (is "?z_hcv|_")
 by (rule zenon_and_1 [OF z_Ha])
 have z_Hfy_z_Hb: "(\\A x:((x \\in PROCESSES)=>(Decide(x)=>?z_her))) == ?z_hb" (is "?z_hfy == _")
 by (unfold bAll_def)
 have z_Hfy: "?z_hfy" (is "\\A x : ?z_hge(x)")
 by (unfold z_Hfy_z_Hb, fact z_Hb)
 have z_Hgf_z_Hc: "(\\A x:((x \\in PROCESSES)=>(a_F1a(x)=>?z_her))) == ?z_hc" (is "?z_hgf == _")
 by (unfold bAll_def)
 have z_Hgf: "?z_hgf" (is "\\A x : ?z_hgj(x)")
 by (unfold z_Hgf_z_Hc, fact z_Hc)
 have z_Hgk_z_Hd: "(\\A x:((x \\in PROCESSES)=>(FR(x)=>?z_her))) == ?z_hd" (is "?z_hgk == _")
 by (unfold bAll_def)
 have z_Hgk: "?z_hgk" (is "\\A x : ?z_hgo(x)")
 by (unfold z_Hgk_z_Hd, fact z_Hd)
 have z_Hgp_z_He: "(\\A x:((x \\in PROCESSES)=>(a_U1a(x)=>?z_her))) == ?z_he" (is "?z_hgp == _")
 by (unfold bAll_def)
 have z_Hgp: "?z_hgp" (is "\\A x : ?z_hgt(x)")
 by (unfold z_Hgp_z_He, fact z_He)
 have z_Hgu_z_Hf: "(\\A x:((x \\in PROCESSES)=>(UR(x)=>?z_her))) == ?z_hf" (is "?z_hgu == _")
 by (unfold bAll_def)
 have z_Hgu: "?z_hgu" (is "\\A x : ?z_hgy(x)")
 by (unfold z_Hgu_z_Hf, fact z_Hf)
 have z_Hgz_z_Hg: "(\\A x:((x \\in PROCESSES)=>(a_S1a(x)=>?z_her))) == ?z_hg" (is "?z_hgz == _")
 by (unfold bAll_def)
 have z_Hgz: "?z_hgz" (is "\\A x : ?z_hhd(x)")
 by (unfold z_Hgz_z_Hg, fact z_Hg)
 have z_Hhe_z_Hh: "(\\A x:((x \\in PROCESSES)=>(a_S2a(x)=>?z_her))) == ?z_hh" (is "?z_hhe == _")
 by (unfold bAll_def)
 have z_Hhe: "?z_hhe" (is "\\A x : ?z_hhi(x)")
 by (unfold z_Hhe_z_Hh, fact z_Hh)
 have z_Hhj_z_Hi: "(\\A x:((x \\in PROCESSES)=>(a_S3a(x)=>?z_her))) == ?z_hi" (is "?z_hhj == _")
 by (unfold bAll_def)
 have z_Hhj: "?z_hhj" (is "\\A x : ?z_hhn(x)")
 by (unfold z_Hhj_z_Hi, fact z_Hi)
 have z_Hho_z_Hj: "(\\A x:((x \\in PROCESSES)=>(SR(x)=>?z_her))) == ?z_hj" (is "?z_hho == _")
 by (unfold bAll_def)
 have z_Hho: "?z_hho" (is "\\A x : ?z_hhs(x)")
 by (unfold z_Hho_z_Hj, fact z_Hj)
 show FALSE
 proof (rule zenon_or [OF z_Hcu])
  assume z_Hcv:"?z_hcv"
  have z_Hht_z_Hcv: "(\\E x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x))))))))))) == ?z_hcv" (is "?z_hht == _")
  by (unfold bEx_def)
  have z_Hht: "?z_hht" (is "\\E x : ?z_hid(x)")
  by (unfold z_Hht_z_Hcv, fact z_Hcv)
  have z_Hie: "?z_hid((CHOOSE x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x))))))))))))" (is "?z_hig&?z_hih")
  by (rule zenon_ex_choose_0 [of "?z_hid", OF z_Hht])
  have z_Hig: "?z_hig"
  by (rule zenon_and_0 [OF z_Hie])
  have z_Hih: "?z_hih" (is "?z_hii|?z_hij")
  by (rule zenon_and_1 [OF z_Hie])
  show FALSE
  proof (rule zenon_or [OF z_Hih])
   assume z_Hii:"?z_hii"
   have z_Hik: "?z_hgj((CHOOSE x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x))))))))))))" (is "_=>?z_hil")
   by (rule zenon_all_0 [of "?z_hgj" "(CHOOSE x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x)))))))))))", OF z_Hgf])
   show FALSE
   proof (rule zenon_imply [OF z_Hik])
    assume z_Him:"(~?z_hig)"
    show FALSE
    by (rule notE [OF z_Him z_Hig])
   next
    assume z_Hil:"?z_hil"
    show FALSE
    proof (rule zenon_imply [OF z_Hil])
     assume z_Hin:"(~?z_hii)"
     show FALSE
     by (rule notE [OF z_Hin z_Hii])
    next
     assume z_Her:"?z_her"
     show FALSE
     by (rule notE [OF z_Hl z_Her])
    qed
   qed
  next
   assume z_Hij:"?z_hij" (is "?z_hio|?z_hip")
   show FALSE
   proof (rule zenon_or [OF z_Hij])
    assume z_Hio:"?z_hio"
    have z_Hiq: "?z_hgo((CHOOSE x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x))))))))))))" (is "_=>?z_hir")
    by (rule zenon_all_0 [of "?z_hgo" "(CHOOSE x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x)))))))))))", OF z_Hgk])
    show FALSE
    proof (rule zenon_imply [OF z_Hiq])
     assume z_Him:"(~?z_hig)"
     show FALSE
     by (rule notE [OF z_Him z_Hig])
    next
     assume z_Hir:"?z_hir"
     show FALSE
     proof (rule zenon_imply [OF z_Hir])
      assume z_His:"(~?z_hio)"
      show FALSE
      by (rule notE [OF z_His z_Hio])
     next
      assume z_Her:"?z_her"
      show FALSE
      by (rule notE [OF z_Hl z_Her])
     qed
    qed
   next
    assume z_Hip:"?z_hip" (is "?z_hit|?z_hiu")
    show FALSE
    proof (rule zenon_or [OF z_Hip])
     assume z_Hit:"?z_hit"
     have z_Hiv: "?z_hgt((CHOOSE x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x))))))))))))" (is "_=>?z_hiw")
     by (rule zenon_all_0 [of "?z_hgt" "(CHOOSE x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x)))))))))))", OF z_Hgp])
     show FALSE
     proof (rule zenon_imply [OF z_Hiv])
      assume z_Him:"(~?z_hig)"
      show FALSE
      by (rule notE [OF z_Him z_Hig])
     next
      assume z_Hiw:"?z_hiw"
      show FALSE
      proof (rule zenon_imply [OF z_Hiw])
       assume z_Hix:"(~?z_hit)"
       show FALSE
       by (rule notE [OF z_Hix z_Hit])
      next
       assume z_Her:"?z_her"
       show FALSE
       by (rule notE [OF z_Hl z_Her])
      qed
     qed
    next
     assume z_Hiu:"?z_hiu" (is "?z_hiy|?z_hiz")
     show FALSE
     proof (rule zenon_or [OF z_Hiu])
      assume z_Hiy:"?z_hiy"
      have z_Hja: "?z_hgy((CHOOSE x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x))))))))))))" (is "_=>?z_hjb")
      by (rule zenon_all_0 [of "?z_hgy" "(CHOOSE x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x)))))))))))", OF z_Hgu])
      show FALSE
      proof (rule zenon_imply [OF z_Hja])
       assume z_Him:"(~?z_hig)"
       show FALSE
       by (rule notE [OF z_Him z_Hig])
      next
       assume z_Hjb:"?z_hjb"
       show FALSE
       proof (rule zenon_imply [OF z_Hjb])
        assume z_Hjc:"(~?z_hiy)"
        show FALSE
        by (rule notE [OF z_Hjc z_Hiy])
       next
        assume z_Her:"?z_her"
        show FALSE
        by (rule notE [OF z_Hl z_Her])
       qed
      qed
     next
      assume z_Hiz:"?z_hiz" (is "?z_hjd|?z_hje")
      show FALSE
      proof (rule zenon_or [OF z_Hiz])
       assume z_Hjd:"?z_hjd"
       have z_Hjf: "?z_hhd((CHOOSE x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x))))))))))))" (is "_=>?z_hjg")
       by (rule zenon_all_0 [of "?z_hhd" "(CHOOSE x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x)))))))))))", OF z_Hgz])
       show FALSE
       proof (rule zenon_imply [OF z_Hjf])
        assume z_Him:"(~?z_hig)"
        show FALSE
        by (rule notE [OF z_Him z_Hig])
       next
        assume z_Hjg:"?z_hjg"
        show FALSE
        proof (rule zenon_imply [OF z_Hjg])
         assume z_Hjh:"(~?z_hjd)"
         show FALSE
         by (rule notE [OF z_Hjh z_Hjd])
        next
         assume z_Her:"?z_her"
         show FALSE
         by (rule notE [OF z_Hl z_Her])
        qed
       qed
      next
       assume z_Hje:"?z_hje" (is "?z_hji|?z_hjj")
       show FALSE
       proof (rule zenon_or [OF z_Hje])
        assume z_Hji:"?z_hji"
        have z_Hjk: "?z_hhi((CHOOSE x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x))))))))))))" (is "_=>?z_hjl")
        by (rule zenon_all_0 [of "?z_hhi" "(CHOOSE x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x)))))))))))", OF z_Hhe])
        show FALSE
        proof (rule zenon_imply [OF z_Hjk])
         assume z_Him:"(~?z_hig)"
         show FALSE
         by (rule notE [OF z_Him z_Hig])
        next
         assume z_Hjl:"?z_hjl"
         show FALSE
         proof (rule zenon_imply [OF z_Hjl])
          assume z_Hjm:"(~?z_hji)"
          show FALSE
          by (rule notE [OF z_Hjm z_Hji])
         next
          assume z_Her:"?z_her"
          show FALSE
          by (rule notE [OF z_Hl z_Her])
         qed
        qed
       next
        assume z_Hjj:"?z_hjj" (is "?z_hjn|?z_hjo")
        show FALSE
        proof (rule zenon_or [OF z_Hjj])
         assume z_Hjn:"?z_hjn"
         have z_Hjp: "?z_hhn((CHOOSE x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x))))))))))))" (is "_=>?z_hjq")
         by (rule zenon_all_0 [of "?z_hhn" "(CHOOSE x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x)))))))))))", OF z_Hhj])
         show FALSE
         proof (rule zenon_imply [OF z_Hjp])
          assume z_Him:"(~?z_hig)"
          show FALSE
          by (rule notE [OF z_Him z_Hig])
         next
          assume z_Hjq:"?z_hjq"
          show FALSE
          proof (rule zenon_imply [OF z_Hjq])
           assume z_Hjr:"(~?z_hjn)"
           show FALSE
           by (rule notE [OF z_Hjr z_Hjn])
          next
           assume z_Her:"?z_her"
           show FALSE
           by (rule notE [OF z_Hl z_Her])
          qed
         qed
        next
         assume z_Hjo:"?z_hjo" (is "?z_hjs|?z_hjt")
         show FALSE
         proof (rule zenon_or [OF z_Hjo])
          assume z_Hjs:"?z_hjs"
          have z_Hju: "?z_hhs((CHOOSE x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x))))))))))))" (is "_=>?z_hjv")
          by (rule zenon_all_0 [of "?z_hhs" "(CHOOSE x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x)))))))))))", OF z_Hho])
          show FALSE
          proof (rule zenon_imply [OF z_Hju])
           assume z_Him:"(~?z_hig)"
           show FALSE
           by (rule notE [OF z_Him z_Hig])
          next
           assume z_Hjv:"?z_hjv"
           show FALSE
           proof (rule zenon_imply [OF z_Hjv])
            assume z_Hjw:"(~?z_hjs)"
            show FALSE
            by (rule notE [OF z_Hjw z_Hjs])
           next
            assume z_Her:"?z_her"
            show FALSE
            by (rule notE [OF z_Hl z_Her])
           qed
          qed
         next
          assume z_Hjt:"?z_hjt"
          have z_Hjx: "?z_hge((CHOOSE x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x))))))))))))" (is "_=>?z_hjy")
          by (rule zenon_all_0 [of "?z_hge" "(CHOOSE x:((x \\in PROCESSES)&(a_F1a(x)|(FR(x)|(a_U1a(x)|(UR(x)|(a_S1a(x)|(a_S2a(x)|(a_S3a(x)|(SR(x)|Decide(x)))))))))))", OF z_Hfy])
          show FALSE
          proof (rule zenon_imply [OF z_Hjx])
           assume z_Him:"(~?z_hig)"
           show FALSE
           by (rule notE [OF z_Him z_Hig])
          next
           assume z_Hjy:"?z_hjy"
           show FALSE
           proof (rule zenon_imply [OF z_Hjy])
            assume z_Hjz:"(~?z_hjt)"
            show FALSE
            by (rule notE [OF z_Hjz z_Hjt])
           next
            assume z_Her:"?z_her"
            show FALSE
            by (rule notE [OF z_Hl z_Her])
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
 next
  assume z_Hdp:"?z_hdp" (is "?z_hdq&?z_hds")
  have z_Hdq: "?z_hdq"
  by (rule zenon_and_0 [OF z_Hdp])
  have z_Hds: "?z_hds" (is "?z_hdt&?z_hdv")
  by (rule zenon_and_1 [OF z_Hdp])
  have z_Hdt: "?z_hdt"
  by (rule zenon_and_0 [OF z_Hds])
  have z_Hdv: "?z_hdv" (is "?z_hdw&?z_hdy")
  by (rule zenon_and_1 [OF z_Hds])
  have z_Hdw: "?z_hdw"
  by (rule zenon_and_0 [OF z_Hdv])
  have z_Hdy: "?z_hdy" (is "?z_hdz&?z_heb")
  by (rule zenon_and_1 [OF z_Hdv])
  have z_Hdz: "?z_hdz"
  by (rule zenon_and_0 [OF z_Hdy])
  have z_Heb: "?z_heb" (is "?z_hec&?z_hee")
  by (rule zenon_and_1 [OF z_Hdy])
  have z_Hec: "?z_hec"
  by (rule zenon_and_0 [OF z_Heb])
  have z_Hee: "?z_hee" (is "?z_hef&?z_heh")
  by (rule zenon_and_1 [OF z_Heb])
  have z_Hef: "?z_hef"
  by (rule zenon_and_0 [OF z_Hee])
  have z_Heh: "?z_heh" (is "?z_hei&?z_hek")
  by (rule zenon_and_1 [OF z_Hee])
  have z_Hei: "?z_hei"
  by (rule zenon_and_0 [OF z_Heh])
  have z_Hek: "?z_hek" (is "?z_hel&?z_hen")
  by (rule zenon_and_1 [OF z_Heh])
  have z_Hel: "?z_hel"
  by (rule zenon_and_0 [OF z_Hek])
  have z_Hen: "?z_hen"
  by (rule zenon_and_1 [OF z_Hek])
  show FALSE
  proof (rule zenon_imply [OF z_Hk])
   assume z_Hka:"(~?z_hdp)"
   show FALSE
   proof (rule zenon_notand [OF z_Hka])
    assume z_Hkb:"(a_pchash_primea~=pc)"
    show FALSE
    by (rule notE [OF z_Hkb z_Hdq])
   next
    assume z_Hkc:"(~?z_hds)"
    show FALSE
    proof (rule zenon_notand [OF z_Hkc])
     assume z_Hkd:"(a_Fhash_primea~=F)"
     show FALSE
     by (rule notE [OF z_Hkd z_Hdt])
    next
     assume z_Hke:"(~?z_hdv)"
     show FALSE
     proof (rule zenon_notand [OF z_Hke])
      assume z_Hkf:"(a_uhash_primea~=u)"
      show FALSE
      by (rule notE [OF z_Hkf z_Hdw])
     next
      assume z_Hkg:"(~?z_hdy)"
      show FALSE
      proof (rule zenon_notand [OF z_Hkg])
       assume z_Hkh:"(a_vhash_primea~=v)"
       show FALSE
       by (rule notE [OF z_Hkh z_Hdz])
      next
       assume z_Hki:"(~?z_heb)"
       show FALSE
       proof (rule zenon_notand [OF z_Hki])
        assume z_Hkj:"(a_whash_primea~=w)"
        show FALSE
        by (rule notE [OF z_Hkj z_Hec])
       next
        assume z_Hkk:"(~?z_hee)"
        show FALSE
        proof (rule zenon_notand [OF z_Hkk])
         assume z_Hkl:"(a_chash_primea~=a_ca)"
         show FALSE
         by (rule notE [OF z_Hkl z_Hef])
        next
         assume z_Hkm:"(~?z_heh)"
         show FALSE
         proof (rule zenon_notand [OF z_Hkm])
          assume z_Hkn:"(a_dhash_primea~=d)"
          show FALSE
          by (rule notE [OF z_Hkn z_Hei])
         next
          assume z_Hko:"(~?z_hek)"
          show FALSE
          proof (rule zenon_notand [OF z_Hko])
           assume z_Hkp:"(a_Mhash_primea~=M)"
           show FALSE
           by (rule notE [OF z_Hkp z_Hel])
          next
           assume z_Hkq:"(a_rethash_primea~=ret)"
           show FALSE
           by (rule notE [OF z_Hkq z_Hen])
          qed
         qed
        qed
       qed
      qed
     qed
    qed
   qed
  next
   assume z_Her:"?z_her"
   show FALSE
   by (rule notE [OF z_Hl z_Her])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 22"; *} qed
lemma ob'33:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes F F'
fixes u u'
fixes v v'
fixes w w'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition StateSet suppressed *)
(* usable definition Configs suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition Init suppressed *)
(* usable definition UFUniteShared suppressed *)
(* usable definition UFSUnite suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Next suppressed *)
(* usable definition SameSetSpec suppressed *)
assumes v'45: "((((((((pc) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & (((F) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & (((u) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((w) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((M) \<in> ((SUBSET (Configs))))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))) \<and> (((Next) \<or> (((((a_pchash_primea :: c)) = (pc))) & ((((a_Fhash_primea :: c)) = (F))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_whash_primea :: c)) = (w))) & ((((a_chash_primea :: c)) = (a_ca))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_Mhash_primea :: c)) = (M))) & ((((a_rethash_primea :: c)) = (ret)))))))) \<Longrightarrow> (((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))]))))))"
shows "((((((((pc) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & (((F) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & (((u) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((w) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((M) \<in> ((SUBSET (Configs))))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))) \<and> (((Next) \<or> (((((a_pchash_primea :: c)) = (pc))) & ((((a_Fhash_primea :: c)) = (F))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_whash_primea :: c)) = (w))) & ((((a_chash_primea :: c)) = (a_ca))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_Mhash_primea :: c)) = (M))) & ((((a_rethash_primea :: c)) = (ret)))))))) \<Rightarrow> (((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))]))))))"(is "PROP ?ob'33")
proof -
ML_command {* writeln "*** TLAPS ENTER 33"; *}
show "PROP ?ob'33"

(* BEGIN ZENON INPUT
;; file=SameSetTypeOK.tlaps/tlapm_30cc52.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >SameSetTypeOK.tlaps/tlapm_30cc52.znn.out
;; obligation #33
$hyp "v'45" (=> (/\ (/\ (TLA.in pc
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in F (TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i))))))) (TLA.in u
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in v
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in w
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_ca (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in d (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in M (TLA.SUBSET Configs)) (TLA.in ret
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0) N))))) (\/ Next
(/\ (= a_pchash_primea pc) (= a_Fhash_primea F) (= a_uhash_primea u)
(= a_vhash_primea v) (= a_whash_primea w) (= a_chash_primea a_ca)
(= a_dhash_primea d) (= a_Mhash_primea M) (= a_rethash_primea
ret)))) (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0) N))))))
$goal (=> (/\ (/\ (TLA.in pc
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in F (TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i))))))) (TLA.in u
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in v
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in w
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_ca (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in d (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in M (TLA.SUBSET Configs)) (TLA.in ret
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0) N))))) (\/ Next
(/\ (= a_pchash_primea pc) (= a_Fhash_primea F) (= a_uhash_primea u)
(= a_vhash_primea v) (= a_whash_primea w) (= a_chash_primea a_ca)
(= a_dhash_primea d) (= a_Mhash_primea M) (= a_rethash_primea ret))))
(/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((pc \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((F \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((u \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((v \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((w \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_ca \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((d \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((M \\in SUBSET(Configs))&(ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))))))))&(Next|((a_pchash_primea=pc)&((a_Fhash_primea=F)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_whash_primea=w)&((a_chash_primea=a_ca)&((a_dhash_primea=d)&((a_Mhash_primea=M)&(a_rethash_primea=ret)))))))))))=>((a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_Mhash_primea \\in SUBSET(Configs))&(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))))))))))" (is "?z_hc=>?z_hdn")
 using v'45 by blast
 assume z_Hb:"(~(?z_hc=>?z_hdn))"
 show FALSE
 by (rule notE [OF z_Hb z_Ha])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 33"; *} qed
lemma ob'36:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes F F'
fixes u u'
fixes v v'
fixes w w'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition StateSet suppressed *)
(* usable definition Configs suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition Init suppressed *)
(* usable definition UFUniteShared suppressed *)
(* usable definition UFSUnite suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Next suppressed *)
(* usable definition SameSetSpec suppressed *)
assumes v'44: "((((((pc) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & (((F) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & (((u) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((w) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((M) \<in> ((SUBSET (Configs))))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))) \<and> (((Next) \<or> (((((a_pchash_primea :: c)) = (pc))) & ((((a_Fhash_primea :: c)) = (F))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_whash_primea :: c)) = (w))) & ((((a_chash_primea :: c)) = (a_ca))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_Mhash_primea :: c)) = (M))) & ((((a_rethash_primea :: c)) = (ret))))))))"
fixes p
assumes p_in : "(p \<in> (PROCESSES))"
assumes v'52: "(((fapply ((pc), (p))) = (''F1'')))"
assumes v'53: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''FR'')])))"
assumes v'54: "((((a_rethash_primea :: c)) = ([(ret) EXCEPT ![(p)] = (fapply ((F), (fapply ((a_ca), (p)))))])))"
assumes v'55: "((((a_Mhash_primea :: c)) = (subsetOf((Configs), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''ret''))) = ([(fapply ((told), (''ret''))) EXCEPT ![(p)] = (fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((told), (''arg''))), (p)))))]))) & (((fapply ((t), (''op''))) = (fapply ((told), (''op''))))) & (((fapply ((t), (''arg''))) = (fapply ((told), (''arg'')))))))))))"
assumes v'56: "((((a_Fhash_primea :: c)) = (F)))"
assumes v'57: "((((a_uhash_primea :: c)) = (u)))"
assumes v'58: "((((a_vhash_primea :: c)) = (v)))"
assumes v'59: "((((a_whash_primea :: c)) = (w)))"
assumes v'60: "((((a_chash_primea :: c)) = (a_ca)))"
assumes v'61: "((((a_dhash_primea :: c)) = (d)))"
shows "(((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))]))))"(is "PROP ?ob'36")
proof -
ML_command {* writeln "*** TLAPS ENTER 36"; *}
show "PROP ?ob'36"

(* BEGIN ZENON INPUT
;; file=SameSetTypeOK.tlaps/tlapm_459d77.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >SameSetTypeOK.tlaps/tlapm_459d77.znn.out
;; obligation #36
$hyp "v'44" (/\ (/\ (TLA.in pc
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in F (TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i))))))) (TLA.in u
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in v
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in w
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_ca (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in d (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in M (TLA.SUBSET Configs)) (TLA.in ret
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0) N))))) (\/ Next
(/\ (= a_pchash_primea pc) (= a_Fhash_primea F) (= a_uhash_primea u)
(= a_vhash_primea v) (= a_whash_primea w) (= a_chash_primea a_ca)
(= a_dhash_primea d) (= a_Mhash_primea M) (= a_rethash_primea
ret))))
$hyp "p_in" (TLA.in p PROCESSES)
$hyp "v'52" (= (TLA.fapply pc p) "F1")
$hyp "v'53" (= a_pchash_primea
(TLA.except pc p "FR"))
$hyp "v'54" (= a_rethash_primea
(TLA.except ret p (TLA.fapply F (TLA.fapply a_ca p))))
$hyp "v'55" (= a_Mhash_primea
(TLA.subsetOf Configs ((t) (TLA.bEx M ((told) (/\ (= (TLA.fapply (TLA.fapply told "ret") p)
BOT) (= (TLA.fapply t "sigma") (TLA.fapply told "sigma"))
(= (TLA.fapply t "ret")
(TLA.except (TLA.fapply told "ret") p (TLA.fapply (TLA.fapply told "sigma") (TLA.fapply (TLA.fapply told "arg") p))))
(= (TLA.fapply t "op") (TLA.fapply told "op")) (= (TLA.fapply t "arg")
(TLA.fapply told "arg"))))))))
$hyp "v'56" (= a_Fhash_primea F)
$hyp "v'57" (= a_uhash_primea u)
$hyp "v'58" (= a_vhash_primea v)
$hyp "v'59" (= a_whash_primea w)
$hyp "v'60" (= a_chash_primea a_ca)
$hyp "v'61" (= a_dhash_primea d)
$goal (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((pc \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((F \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((u \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((v \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((w \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_ca \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((d \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((M \\in SUBSET(Configs))&(ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))))))))&(Next|((a_pchash_primea=pc)&((a_Fhash_primea=F)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_whash_primea=w)&((a_chash_primea=a_ca)&((a_dhash_primea=d)&((a_Mhash_primea=M)&(a_rethash_primea=ret)))))))))))" (is "?z_hn&?z_hcv")
 using v'44 by blast
 have z_He:"(a_rethash_primea=except(ret, p, (F[(a_ca[p])])))" (is "_=?z_hdr")
 using v'54 by blast
 have z_Hf:"(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, ((told[''sigma''])[((told[''arg''])[p])])))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))" (is "_=?z_hdv")
 using v'55 by blast
 have z_Hl:"(a_dhash_primea=d)"
 using v'61 by blast
 have z_Hk:"(a_chash_primea=a_ca)"
 using v'60 by blast
 have z_Hj:"(a_whash_primea=w)"
 using v'59 by blast
 have z_Hi:"(a_vhash_primea=v)"
 using v'58 by blast
 have z_Hh:"(a_uhash_primea=u)"
 using v'57 by blast
 have z_Hg:"(a_Fhash_primea=F)"
 using v'56 by blast
 have z_Hd:"(a_pchash_primea=except(pc, p, ''FR''))" (is "_=?z_hfb")
 using v'53 by blast
 have zenon_L1_: "(a_pchash_primea=?z_hfb) ==> (~(a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))) ==> (pc \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''})) ==> FALSE" (is "?z_hd ==> ?z_hfc ==> ?z_ho ==> FALSE")
 proof -
  assume z_Hd:"?z_hd"
  assume z_Hfc:"?z_hfc" (is "~?z_hfd")
  assume z_Ho:"?z_ho"
  have z_Hfe: "(~(?z_hfb \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''})))" (is "~?z_hff")
  by (rule subst [where P="(\<lambda>zenon_Vega. (~(zenon_Vega \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))", OF z_Hd z_Hfc])
  show FALSE
  proof (rule zenon_except_notin_funcset [of "pc" "p" "''FR''" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hfe])
   assume z_Hfk:"(~?z_ho)"
   show FALSE
   by (rule notE [OF z_Hfk z_Ho])
  next
   assume z_Hfl:"(~(''FR'' \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hfm")
   have z_Hfn: "(~(''FR'' \\in {''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hfo")
   by (rule zenon_notin_addElt_1 [of "''FR''" "''0''" "{''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hfl])
   have z_Hfq: "(~(''FR'' \\in {''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hfr")
   by (rule zenon_notin_addElt_1 [of "''FR''" "''F1''" "{''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hfn])
   have z_Hft: "(''FR''~=''FR'')" (is "?z_hv~=_")
   by (rule zenon_notin_addElt_0 [of "?z_hv" "?z_hv" "{''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hfq])
   show FALSE
   by (rule zenon_noteq [OF z_Hft])
  qed
 qed
 have zenon_L2_: "(a_Fhash_primea=F) ==> (~(a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))) ==> (F \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i]))))))) ==> FALSE" (is "?z_hg ==> ?z_hfv ==> ?z_hbd ==> FALSE")
 proof -
  assume z_Hg:"?z_hg"
  assume z_Hfv:"?z_hfv" (is "~?z_hfw")
  assume z_Hbd:"?z_hbd"
  have z_Hfx: "(~?z_hbd)"
  by (rule subst [where P="(\<lambda>zenon_Vcga. (~(zenon_Vcga \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))))", OF z_Hg z_Hfv])
  show FALSE
  by (rule notE [OF z_Hfx z_Hbd])
 qed
 have zenon_L3_: "(a_uhash_primea=u) ==> (~(a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (u \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hh ==> ?z_hgc ==> ?z_hbt ==> FALSE")
 proof -
  assume z_Hh:"?z_hh"
  assume z_Hgc:"?z_hgc" (is "~?z_hgd")
  assume z_Hbt:"?z_hbt"
  have z_Hge: "(~?z_hbt)"
  by (rule subst [where P="(\<lambda>zenon_Vmga. (~(zenon_Vmga \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hh z_Hgc])
  show FALSE
  by (rule notE [OF z_Hge z_Hbt])
 qed
 have zenon_L4_: "(a_vhash_primea=v) ==> (~(a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (v \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hi ==> ?z_hgj ==> ?z_hbx ==> FALSE")
 proof -
  assume z_Hi:"?z_hi"
  assume z_Hgj:"?z_hgj" (is "~?z_hgk")
  assume z_Hbx:"?z_hbx"
  have z_Hgl: "(~?z_hbx)"
  by (rule subst [where P="(\<lambda>zenon_Vmga. (~(zenon_Vmga \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hi z_Hgj])
  show FALSE
  by (rule notE [OF z_Hgl z_Hbx])
 qed
 have zenon_L5_: "(a_whash_primea=w) ==> (~(a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (w \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hj ==> ?z_hgm ==> ?z_hca ==> FALSE")
 proof -
  assume z_Hj:"?z_hj"
  assume z_Hgm:"?z_hgm" (is "~?z_hgn")
  assume z_Hca:"?z_hca"
  have z_Hgo: "(~?z_hca)"
  by (rule subst [where P="(\<lambda>zenon_Vmga. (~(zenon_Vmga \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hj z_Hgm])
  show FALSE
  by (rule notE [OF z_Hgo z_Hca])
 qed
 have zenon_L6_: "(a_chash_primea=a_ca) ==> (~(a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (a_ca \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hk ==> ?z_hgp ==> ?z_hcd ==> FALSE")
 proof -
  assume z_Hk:"?z_hk"
  assume z_Hgp:"?z_hgp" (is "~?z_hgq")
  assume z_Hcd:"?z_hcd"
  have z_Hgr: "(~?z_hcd)"
  by (rule subst [where P="(\<lambda>zenon_Vmga. (~(zenon_Vmga \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hk z_Hgp])
  show FALSE
  by (rule notE [OF z_Hgr z_Hcd])
 qed
 have zenon_L7_: "(a_dhash_primea=d) ==> (~(a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (d \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hl ==> ?z_hgs ==> ?z_hcg ==> FALSE")
 proof -
  assume z_Hl:"?z_hl"
  assume z_Hgs:"?z_hgs" (is "~?z_hgt")
  assume z_Hcg:"?z_hcg"
  have z_Hgu: "(~?z_hcg)"
  by (rule subst [where P="(\<lambda>zenon_Vmga. (~(zenon_Vmga \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hl z_Hgs])
  show FALSE
  by (rule notE [OF z_Hgu z_Hcg])
 qed
 have zenon_L8_: "((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))) \\in ?z_hdv) ==> (~((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))) \\in Configs)) ==> FALSE" (is "?z_hgv ==> ?z_hhc ==> FALSE")
 proof -
  assume z_Hgv:"?z_hgv"
  assume z_Hhc:"?z_hhc" (is "~?z_hhd")
  have z_Hhd: "?z_hhd"
  by (rule zenon_in_subsetof_0 [of "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))" "Configs" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, ((told[''sigma''])[((told[''arg''])[p])])))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))", OF z_Hgv])
  show FALSE
  by (rule notE [OF z_Hhc z_Hhd])
 qed
 assume z_Hm:"(~((a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_Mhash_primea \\in SUBSET(Configs))&(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))))))))))" (is "~(?z_hfd&?z_hhf)")
 have z_Hn: "?z_hn" (is "?z_ho&?z_hbc")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Ho: "?z_ho"
 by (rule zenon_and_0 [OF z_Hn])
 have z_Hbc: "?z_hbc" (is "?z_hbd&?z_hbs")
 by (rule zenon_and_1 [OF z_Hn])
 have z_Hbd: "?z_hbd"
 by (rule zenon_and_0 [OF z_Hbc])
 have z_Hbs: "?z_hbs" (is "?z_hbt&?z_hbw")
 by (rule zenon_and_1 [OF z_Hbc])
 have z_Hbt: "?z_hbt"
 by (rule zenon_and_0 [OF z_Hbs])
 have z_Hbw: "?z_hbw" (is "?z_hbx&?z_hbz")
 by (rule zenon_and_1 [OF z_Hbs])
 have z_Hbx: "?z_hbx"
 by (rule zenon_and_0 [OF z_Hbw])
 have z_Hbz: "?z_hbz" (is "?z_hca&?z_hcc")
 by (rule zenon_and_1 [OF z_Hbw])
 have z_Hca: "?z_hca"
 by (rule zenon_and_0 [OF z_Hbz])
 have z_Hcc: "?z_hcc" (is "?z_hcd&?z_hcf")
 by (rule zenon_and_1 [OF z_Hbz])
 have z_Hcd: "?z_hcd"
 by (rule zenon_and_0 [OF z_Hcc])
 have z_Hcf: "?z_hcf" (is "?z_hcg&?z_hci")
 by (rule zenon_and_1 [OF z_Hcc])
 have z_Hcg: "?z_hcg"
 by (rule zenon_and_0 [OF z_Hcf])
 have z_Hci: "?z_hci" (is "?z_hcj&?z_hcn")
 by (rule zenon_and_1 [OF z_Hcf])
 have z_Hcn: "?z_hcn"
 by (rule zenon_and_1 [OF z_Hci])
 have z_Hho: "(F \\in FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)))" (is "?z_hho")
 by (rule zenon_in_subsetof_0 [of "F" "FuncSet(isa'dotdot(1, N), isa'dotdot(1, N))" "(\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))", OF z_Hbd])
 show FALSE
 proof (rule zenon_notand [OF z_Hm])
  assume z_Hfc:"(~?z_hfd)"
  show FALSE
  by (rule zenon_L1_ [OF z_Hd z_Hfc z_Ho])
 next
  assume z_Hhp:"(~?z_hhf)" (is "~(?z_hfw&?z_hhg)")
  show FALSE
  proof (rule zenon_notand [OF z_Hhp])
   assume z_Hfv:"(~?z_hfw)"
   show FALSE
   by (rule zenon_L2_ [OF z_Hg z_Hfv z_Hbd])
  next
   assume z_Hhq:"(~?z_hhg)" (is "~(?z_hgd&?z_hhh)")
   show FALSE
   proof (rule zenon_notand [OF z_Hhq])
    assume z_Hgc:"(~?z_hgd)"
    show FALSE
    by (rule zenon_L3_ [OF z_Hh z_Hgc z_Hbt])
   next
    assume z_Hhr:"(~?z_hhh)" (is "~(?z_hgk&?z_hhi)")
    show FALSE
    proof (rule zenon_notand [OF z_Hhr])
     assume z_Hgj:"(~?z_hgk)"
     show FALSE
     by (rule zenon_L4_ [OF z_Hi z_Hgj z_Hbx])
    next
     assume z_Hhs:"(~?z_hhi)" (is "~(?z_hgn&?z_hhj)")
     show FALSE
     proof (rule zenon_notand [OF z_Hhs])
      assume z_Hgm:"(~?z_hgn)"
      show FALSE
      by (rule zenon_L5_ [OF z_Hj z_Hgm z_Hca])
     next
      assume z_Hht:"(~?z_hhj)" (is "~(?z_hgq&?z_hhk)")
      show FALSE
      proof (rule zenon_notand [OF z_Hht])
       assume z_Hgp:"(~?z_hgq)"
       show FALSE
       by (rule zenon_L6_ [OF z_Hk z_Hgp z_Hcd])
      next
       assume z_Hhu:"(~?z_hhk)" (is "~(?z_hgt&?z_hhl)")
       show FALSE
       proof (rule zenon_notand [OF z_Hhu])
        assume z_Hgs:"(~?z_hgt)"
        show FALSE
        by (rule zenon_L7_ [OF z_Hl z_Hgs z_Hcg])
       next
        assume z_Hhv:"(~?z_hhl)" (is "~(?z_hhm&?z_hhn)")
        show FALSE
        proof (rule zenon_notand [OF z_Hhv])
         assume z_Hhw:"(~?z_hhm)"
         have z_Hhx: "(~(a_Mhash_primea \\subseteq Configs))" (is "~?z_hhy")
         by (rule zenon_notin_SUBSET_0 [of "a_Mhash_primea" "Configs", OF z_Hhw])
         have z_Hhz_z_Hhx: "(~bAll(a_Mhash_primea, (\<lambda>x. (x \\in Configs)))) == (~?z_hhy)" (is "?z_hhz == ?z_hhx")
         by (unfold subset_def)
         have z_Hhz: "?z_hhz" (is "~?z_hia")
         by (unfold z_Hhz_z_Hhx, fact z_Hhx)
         have z_Hic_z_Hhz: "(~(\\A x:((x \\in a_Mhash_primea)=>(x \\in Configs)))) == ?z_hhz" (is "?z_hic == _")
         by (unfold bAll_def)
         have z_Hic: "?z_hic" (is "~(\\A x : ?z_hie(x))")
         by (unfold z_Hic_z_Hhz, fact z_Hhz)
         have z_Hif: "(\\E x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))" (is "\\E x : ?z_hig(x)")
         by (rule zenon_notallex_0 [of "?z_hie", OF z_Hic])
         have z_Hih: "?z_hig((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))))" (is "~(?z_hii=>?z_hhd)")
         by (rule zenon_ex_choose_0 [of "?z_hig", OF z_Hif])
         have z_Hii: "?z_hii"
         by (rule zenon_notimply_0 [OF z_Hih])
         have z_Hhc: "(~?z_hhd)"
         by (rule zenon_notimply_1 [OF z_Hih])
         have z_Hgv: "((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))) \\in ?z_hdv)" (is "?z_hgv")
         by (rule subst [where P="(\<lambda>zenon_Vli. ((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))) \\in zenon_Vli))", OF z_Hf z_Hii])
         show FALSE
         by (rule zenon_L8_ [OF z_Hgv z_Hhc])
        next
         assume z_Him:"(~?z_hhn)"
         have z_Hin: "(~(?z_hdr \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))" (is "~?z_hio")
         by (rule subst [where P="(\<lambda>zenon_Vyga. (~(zenon_Vyga \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))", OF z_He z_Him])
         have z_Hit: "(DOMAIN(ret)=PROCESSES)" (is "?z_hiu=_")
         by (rule zenon_in_funcset_1 [of "ret" "PROCESSES" "({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))", OF z_Hcn])
         show FALSE
         proof (rule zenon_except_notin_funcset [of "ret" "p" "(F[(a_ca[p])])" "PROCESSES" "({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))", OF z_Hin])
          assume z_Hiv:"(~?z_hcn)"
          show FALSE
          by (rule notE [OF z_Hiv z_Hcn])
         next
          assume z_Hiw:"(~((F[(a_ca[p])]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))" (is "~?z_hix")
          have z_Hiy: "(~((F[(a_ca[p])]) \\in isa'dotdot(1, N)))" (is "~?z_hiz")
          by (rule zenon_notin_cup_1 [of "(F[(a_ca[p])])" "{ACK, TRUE, FALSE}" "isa'dotdot(1, N)", OF z_Hiw])
          show FALSE
          proof (rule zenon_notin_funcset [of "?z_hdr" "PROCESSES" "({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))", OF z_Hin])
           assume z_Hja:"(~isAFcn(?z_hdr))" (is "~?z_hjb")
           show FALSE
           by (rule zenon_notisafcn_except [of "ret" "p" "(F[(a_ca[p])])", OF z_Hja])
          next
           assume z_Hjc:"(DOMAIN(?z_hdr)~=PROCESSES)" (is "?z_hjd~=_")
           have z_Hje: "(?z_hiu~=PROCESSES)"
           by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vyea. (zenon_Vyea~=PROCESSES))" "ret" "p" "(F[(a_ca[p])])", OF z_Hjc])
           show FALSE
           by (rule notE [OF z_Hje z_Hit])
          next
           assume z_Hji:"(~(\\A zenon_Vnb:((zenon_Vnb \\in PROCESSES)=>((?z_hdr[zenon_Vnb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))" (is "~(\\A x : ?z_hjp(x))")
           have z_Hjq: "(\\E zenon_Vnb:(~((zenon_Vnb \\in PROCESSES)=>((?z_hdr[zenon_Vnb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))" (is "\\E x : ?z_hjs(x)")
           by (rule zenon_notallex_0 [of "?z_hjp", OF z_Hji])
           have z_Hjt: "?z_hjs((CHOOSE zenon_Vnb:(~((zenon_Vnb \\in PROCESSES)=>((?z_hdr[zenon_Vnb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))))" (is "~(?z_hjv=>?z_hjw)")
           by (rule zenon_ex_choose_0 [of "?z_hjs", OF z_Hjq])
           have z_Hjv: "?z_hjv"
           by (rule zenon_notimply_0 [OF z_Hjt])
           have z_Hjx: "(~?z_hjw)"
           by (rule zenon_notimply_1 [OF z_Hjt])
           have z_Hjy: "(~((?z_hdr[(CHOOSE zenon_Vnb:(~((zenon_Vnb \\in PROCESSES)=>((?z_hdr[zenon_Vnb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))]) \\in {ACK, TRUE, FALSE}))" (is "~?z_hjz")
           by (rule zenon_notin_cup_0 [of "(?z_hdr[(CHOOSE zenon_Vnb:(~((zenon_Vnb \\in PROCESSES)=>((?z_hdr[zenon_Vnb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))])" "{ACK, TRUE, FALSE}" "isa'dotdot(1, N)", OF z_Hjx])
           have z_Hkb: "(~((?z_hdr[(CHOOSE zenon_Vnb:(~((zenon_Vnb \\in PROCESSES)=>((?z_hdr[zenon_Vnb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))]) \\in {TRUE, FALSE}))" (is "~?z_hkc")
           by (rule zenon_notin_addElt_1 [of "(?z_hdr[(CHOOSE zenon_Vnb:(~((zenon_Vnb \\in PROCESSES)=>((?z_hdr[zenon_Vnb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))])" "ACK" "{TRUE, FALSE}", OF z_Hjy])
           have z_Hke: "((?z_hdr[(CHOOSE zenon_Vnb:(~((zenon_Vnb \\in PROCESSES)=>((?z_hdr[zenon_Vnb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))])~=TRUE)" (is "?z_hka~=?z_hct")
           by (rule zenon_notin_addElt_0 [of "?z_hka" "?z_hct" "{FALSE}", OF z_Hkb])
           have z_Hkg: "(~?z_hka)"
           by (rule zenon_noteq_x_true_0 [of "?z_hka", OF z_Hke])
           have z_Hkh: "((CHOOSE zenon_Vnb:(~((zenon_Vnb \\in PROCESSES)=>((?z_hdr[zenon_Vnb]) \\in ({ACK, ?z_hct, FALSE} \\cup isa'dotdot(1, N)))))) \\in ?z_hiu)" (is "?z_hkh")
           by (rule ssubst [where P="(\<lambda>zenon_Vbp. ((CHOOSE zenon_Vnb:(~((zenon_Vnb \\in PROCESSES)=>((?z_hdr[zenon_Vnb]) \\in ({ACK, ?z_hct, FALSE} \\cup isa'dotdot(1, N)))))) \\in zenon_Vbp))", OF z_Hit z_Hjv])
           show FALSE
           proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vlo. (~zenon_Vlo))" "ret" "p" "(F[(a_ca[p])])" "(CHOOSE zenon_Vnb:(~((zenon_Vnb \\in PROCESSES)=>((?z_hdr[zenon_Vnb]) \\in ({ACK, ?z_hct, FALSE} \\cup isa'dotdot(1, N))))))", OF z_Hkg])
            assume z_Hkh:"?z_hkh"
            assume z_Hko:"(p=(CHOOSE zenon_Vnb:(~((zenon_Vnb \\in PROCESSES)=>((?z_hdr[zenon_Vnb]) \\in ({ACK, ?z_hct, FALSE} \\cup isa'dotdot(1, N)))))))" (is "_=?z_hju")
            assume z_Hkp:"(~(F[(a_ca[p])]))" (is "~?z_hdt")
            have z_Hkq: "(\\A zenon_Vv:((zenon_Vv \\in PROCESSES)=>((a_ca[zenon_Vv]) \\in isa'dotdot(1, N))))" (is "\\A x : ?z_hkw(x)")
            by (rule zenon_in_funcset_2 [of "a_ca" "PROCESSES" "isa'dotdot(1, N)", OF z_Hcd])
            have z_Hkx: "?z_hkw(?z_hju)" (is "_=>?z_hky")
            by (rule zenon_all_0 [of "?z_hkw" "?z_hju", OF z_Hkq])
            show FALSE
            proof (rule zenon_imply [OF z_Hkx])
             assume z_Hkz:"(~?z_hjv)"
             show FALSE
             by (rule notE [OF z_Hkz z_Hjv])
            next
             assume z_Hky:"?z_hky"
             have z_Hla: "(\\A zenon_Vna:((zenon_Vna \\in isa'dotdot(1, N))=>((F[zenon_Vna]) \\in isa'dotdot(1, N))))" (is "\\A x : ?z_hlg(x)")
             by (rule zenon_in_funcset_2 [of "F" "isa'dotdot(1, N)" "isa'dotdot(1, N)", OF z_Hho])
             have z_Hlh: "?z_hlg((a_ca[p]))" (is "?z_hli=>_")
             by (rule zenon_all_0 [of "?z_hlg" "(a_ca[p])", OF z_Hla])
             show FALSE
             proof (rule zenon_imply [OF z_Hlh])
              assume z_Hlj:"(~?z_hli)"
              show FALSE
              proof (rule notE [OF z_Hlj])
               have z_Hlk: "((a_ca[?z_hju])=(a_ca[p]))" (is "?z_hll=?z_hdu")
               proof (rule zenon_nnpp [of "(?z_hll=?z_hdu)"])
               assume z_Hlm:"(?z_hll~=?z_hdu)"
               show FALSE
               proof (rule zenon_noteq [of "?z_hdu"])
               have z_Hln: "(?z_hju=p)"
               by (rule sym [OF z_Hko])
               have z_Hlo: "(?z_hdu~=?z_hdu)"
               by (rule subst [where P="(\<lambda>zenon_Vzga. ((a_ca[zenon_Vzga])~=?z_hdu))", OF z_Hln], fact z_Hlm)
               thus "(?z_hdu~=?z_hdu)" .
               qed
               qed
               have z_Hli: "?z_hli"
               by (rule subst [where P="(\<lambda>zenon_Vaha. (zenon_Vaha \\in isa'dotdot(1, N)))", OF z_Hlk], fact z_Hky)
               thus "?z_hli" .
              qed
             next
              assume z_Hiz:"?z_hiz"
              show FALSE
              by (rule notE [OF z_Hiy z_Hiz])
             qed
            qed
           next
            assume z_Hkh:"?z_hkh"
            assume z_Hlw:"(p~=(CHOOSE zenon_Vnb:(~((zenon_Vnb \\in PROCESSES)=>((?z_hdr[zenon_Vnb]) \\in ({ACK, ?z_hct, FALSE} \\cup isa'dotdot(1, N)))))))" (is "_~=?z_hju")
            assume z_Hlx:"(~(ret[?z_hju]))" (is "~?z_hly")
            show FALSE
            proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vlo. (~(zenon_Vlo \\in ({ACK, ?z_hct, FALSE} \\cup isa'dotdot(1, N)))))" "ret" "p" "(F[(a_ca[p])])" "?z_hju", OF z_Hjx])
             assume z_Hkh:"?z_hkh"
             assume z_Hko:"(p=?z_hju)"
             assume z_Hiw:"(~?z_hix)"
             show FALSE
             by (rule notE [OF z_Hlw z_Hko])
            next
             assume z_Hkh:"?z_hkh"
             assume z_Hlw:"(p~=?z_hju)"
             assume z_Hmc:"(~(?z_hly \\in ({ACK, ?z_hct, FALSE} \\cup isa'dotdot(1, N))))" (is "~?z_hmd")
             have z_Hme: "(\\A zenon_Vn:((zenon_Vn \\in PROCESSES)=>((ret[zenon_Vn]) \\in ({ACK, ?z_hct, FALSE} \\cup isa'dotdot(1, N)))))" (is "\\A x : ?z_hmk(x)")
             by (rule zenon_in_funcset_2 [of "ret" "PROCESSES" "({ACK, ?z_hct, FALSE} \\cup isa'dotdot(1, N))", OF z_Hcn])
             have z_Hml: "?z_hmk(?z_hju)"
             by (rule zenon_all_0 [of "?z_hmk" "?z_hju", OF z_Hme])
             show FALSE
             proof (rule zenon_imply [OF z_Hml])
              assume z_Hkz:"(~?z_hjv)"
              show FALSE
              by (rule notE [OF z_Hkz z_Hjv])
             next
              assume z_Hmd:"?z_hmd"
              show FALSE
              by (rule notE [OF z_Hmc z_Hmd])
             qed
            next
             assume z_Hmm:"(~?z_hkh)"
             show FALSE
             by (rule notE [OF z_Hmm z_Hkh])
            qed
           next
            assume z_Hmm:"(~?z_hkh)"
            show FALSE
            by (rule notE [OF z_Hmm z_Hkh])
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
ML_command {* writeln "*** TLAPS EXIT 36"; *} qed
lemma ob'38:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes F F'
fixes u u'
fixes v v'
fixes w w'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition StateSet suppressed *)
(* usable definition Configs suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition Init suppressed *)
(* usable definition UFUniteShared suppressed *)
(* usable definition UFSUnite suppressed *)
(* usable definition F1 suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Next suppressed *)
(* usable definition SameSetSpec suppressed *)
assumes v'44: "((((((pc) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & (((F) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & (((u) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((w) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((M) \<in> ((SUBSET (Configs))))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))) \<and> (((Next) \<or> (((((a_pchash_primea :: c)) = (pc))) & ((((a_Fhash_primea :: c)) = (F))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_whash_primea :: c)) = (w))) & ((((a_chash_primea :: c)) = (a_ca))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_Mhash_primea :: c)) = (M))) & ((((a_rethash_primea :: c)) = (ret))))))))"
fixes p
assumes p_in : "(p \<in> (PROCESSES))"
assumes v'53: "(((fapply ((pc), (p))) = (''FR'')))"
assumes v'54: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''0'')])))"
assumes v'55: "((((a_Mhash_primea :: c)) = (subsetOf((Configs), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (fapply ((ret), (p))))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''ret''))) = ([(fapply ((told), (''ret''))) EXCEPT ![(p)] = (BOT)]))) & (((fapply ((t), (''op''))) = ([(fapply ((told), (''op''))) EXCEPT ![(p)] = (BOT)]))) & (((fapply ((t), (''arg''))) = ([(fapply ((told), (''arg''))) EXCEPT ![(p)] = (BOT)])))))))))"
assumes v'56: "((((a_Fhash_primea :: c)) = (F)))"
assumes v'57: "((((a_uhash_primea :: c)) = (u)))"
assumes v'58: "((((a_vhash_primea :: c)) = (v)))"
assumes v'59: "((((a_whash_primea :: c)) = (w)))"
assumes v'60: "((((a_chash_primea :: c)) = (a_ca)))"
assumes v'61: "((((a_dhash_primea :: c)) = (d)))"
assumes v'62: "((((a_rethash_primea :: c)) = (ret)))"
shows "(((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))]))))"(is "PROP ?ob'38")
proof -
ML_command {* writeln "*** TLAPS ENTER 38"; *}
show "PROP ?ob'38"

(* BEGIN ZENON INPUT
;; file=SameSetTypeOK.tlaps/tlapm_1a3e3e.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >SameSetTypeOK.tlaps/tlapm_1a3e3e.znn.out
;; obligation #38
$hyp "v'44" (/\ (/\ (TLA.in pc
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in F (TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i))))))) (TLA.in u
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in v
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in w
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_ca (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in d (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in M (TLA.SUBSET Configs)) (TLA.in ret
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0) N))))) (\/ Next
(/\ (= a_pchash_primea pc) (= a_Fhash_primea F) (= a_uhash_primea u)
(= a_vhash_primea v) (= a_whash_primea w) (= a_chash_primea a_ca)
(= a_dhash_primea d) (= a_Mhash_primea M) (= a_rethash_primea
ret))))
$hyp "p_in" (TLA.in p PROCESSES)
$hyp "v'53" (= (TLA.fapply pc p) "FR")
$hyp "v'54" (= a_pchash_primea
(TLA.except pc p "0"))
$hyp "v'55" (= a_Mhash_primea
(TLA.subsetOf Configs ((t) (TLA.bEx M ((told) (/\ (= (TLA.fapply (TLA.fapply told "ret") p)
(TLA.fapply ret p)) (= (TLA.fapply t "sigma") (TLA.fapply told "sigma"))
(= (TLA.fapply t "ret") (TLA.except (TLA.fapply told "ret") p BOT))
(= (TLA.fapply t "op") (TLA.except (TLA.fapply told "op") p BOT))
(= (TLA.fapply t "arg")
(TLA.except (TLA.fapply told "arg") p BOT))))))))
$hyp "v'56" (= a_Fhash_primea F)
$hyp "v'57" (= a_uhash_primea u)
$hyp "v'58" (= a_vhash_primea v)
$hyp "v'59" (= a_whash_primea w)
$hyp "v'60" (= a_chash_primea a_ca)
$hyp "v'61" (= a_dhash_primea d)
$hyp "v'62" (= a_rethash_primea ret)
$goal (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((pc \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((F \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((u \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((v \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((w \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_ca \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((d \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((M \\in SUBSET(Configs))&(ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))))))))&(Next|((a_pchash_primea=pc)&((a_Fhash_primea=F)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_whash_primea=w)&((a_chash_primea=a_ca)&((a_dhash_primea=d)&((a_Mhash_primea=M)&(a_rethash_primea=ret)))))))))))" (is "?z_hn&?z_hcv")
 using v'44 by blast
 have z_Hd:"(a_pchash_primea=except(pc, p, ''0''))" (is "_=?z_hdq")
 using v'54 by blast
 have z_Hf:"(a_Fhash_primea=F)"
 using v'56 by blast
 have z_Hg:"(a_uhash_primea=u)"
 using v'57 by blast
 have z_Hh:"(a_vhash_primea=v)"
 using v'58 by blast
 have z_Hi:"(a_whash_primea=w)"
 using v'59 by blast
 have z_Hj:"(a_chash_primea=a_ca)"
 using v'60 by blast
 have z_Hk:"(a_dhash_primea=d)"
 using v'61 by blast
 have z_He:"(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=(ret[p]))&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, BOT))&(((t[''op''])=except((told[''op'']), p, BOT))&((t[''arg''])=except((told[''arg'']), p, BOT)))))))))))" (is "_=?z_hds")
 using v'55 by blast
 have z_Hl:"(a_rethash_primea=ret)"
 using v'62 by blast
 have zenon_L1_: "(a_pchash_primea=?z_hdq) ==> (~(a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))) ==> (pc \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''})) ==> FALSE" (is "?z_hd ==> ?z_hez ==> ?z_ho ==> FALSE")
 proof -
  assume z_Hd:"?z_hd"
  assume z_Hez:"?z_hez" (is "~?z_hfa")
  assume z_Ho:"?z_ho"
  have z_Hfb: "(~(?z_hdq \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''})))" (is "~?z_hfc")
  by (rule subst [where P="(\<lambda>zenon_Vad. (~(zenon_Vad \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))", OF z_Hd z_Hez])
  show FALSE
  proof (rule zenon_except_notin_funcset [of "pc" "p" "''0''" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hfb])
   assume z_Hfh:"(~?z_ho)"
   show FALSE
   by (rule notE [OF z_Hfh z_Ho])
  next
   assume z_Hfi:"(~(''0'' \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hfj")
   have z_Hfk: "(''0''~=''0'')" (is "?z_ht~=_")
   by (rule zenon_notin_addElt_0 [of "?z_ht" "?z_ht" "{''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hfi])
   show FALSE
   by (rule zenon_noteq [OF z_Hfk])
  qed
 qed
 have zenon_L2_: "(a_Fhash_primea=F) ==> (~(a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))) ==> (F \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i]))))))) ==> FALSE" (is "?z_hf ==> ?z_hfm ==> ?z_hbd ==> FALSE")
 proof -
  assume z_Hf:"?z_hf"
  assume z_Hfm:"?z_hfm" (is "~?z_hfn")
  assume z_Hbd:"?z_hbd"
  have z_Hfo: "(~?z_hbd)"
  by (rule subst [where P="(\<lambda>zenon_Voc. (~(zenon_Voc \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))))", OF z_Hf z_Hfm])
  show FALSE
  by (rule notE [OF z_Hfo z_Hbd])
 qed
 have zenon_L3_: "(a_uhash_primea=u) ==> (~(a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (u \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hg ==> ?z_hft ==> ?z_hbt ==> FALSE")
 proof -
  assume z_Hg:"?z_hg"
  assume z_Hft:"?z_hft" (is "~?z_hfu")
  assume z_Hbt:"?z_hbt"
  have z_Hfv: "(~?z_hbt)"
  by (rule subst [where P="(\<lambda>zenon_Vzb. (~(zenon_Vzb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hg z_Hft])
  show FALSE
  by (rule notE [OF z_Hfv z_Hbt])
 qed
 have zenon_L4_: "(a_vhash_primea=v) ==> (~(a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (v \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hh ==> ?z_hga ==> ?z_hbx ==> FALSE")
 proof -
  assume z_Hh:"?z_hh"
  assume z_Hga:"?z_hga" (is "~?z_hgb")
  assume z_Hbx:"?z_hbx"
  have z_Hgc: "(~?z_hbx)"
  by (rule subst [where P="(\<lambda>zenon_Vzb. (~(zenon_Vzb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hh z_Hga])
  show FALSE
  by (rule notE [OF z_Hgc z_Hbx])
 qed
 have zenon_L5_: "(a_whash_primea=w) ==> (~(a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (w \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hi ==> ?z_hgd ==> ?z_hca ==> FALSE")
 proof -
  assume z_Hi:"?z_hi"
  assume z_Hgd:"?z_hgd" (is "~?z_hge")
  assume z_Hca:"?z_hca"
  have z_Hgf: "(~?z_hca)"
  by (rule subst [where P="(\<lambda>zenon_Vzb. (~(zenon_Vzb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hi z_Hgd])
  show FALSE
  by (rule notE [OF z_Hgf z_Hca])
 qed
 have zenon_L6_: "(a_chash_primea=a_ca) ==> (~(a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (a_ca \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hj ==> ?z_hgg ==> ?z_hcd ==> FALSE")
 proof -
  assume z_Hj:"?z_hj"
  assume z_Hgg:"?z_hgg" (is "~?z_hgh")
  assume z_Hcd:"?z_hcd"
  have z_Hgi: "(~?z_hcd)"
  by (rule subst [where P="(\<lambda>zenon_Vzb. (~(zenon_Vzb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hj z_Hgg])
  show FALSE
  by (rule notE [OF z_Hgi z_Hcd])
 qed
 have zenon_L7_: "(a_dhash_primea=d) ==> (~(a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (d \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hk ==> ?z_hgj ==> ?z_hcg ==> FALSE")
 proof -
  assume z_Hk:"?z_hk"
  assume z_Hgj:"?z_hgj" (is "~?z_hgk")
  assume z_Hcg:"?z_hcg"
  have z_Hgl: "(~?z_hcg)"
  by (rule subst [where P="(\<lambda>zenon_Vzb. (~(zenon_Vzb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hk z_Hgj])
  show FALSE
  by (rule notE [OF z_Hgl z_Hcg])
 qed
 have zenon_L8_: "((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))) \\in ?z_hds) ==> (~((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))) \\in Configs)) ==> FALSE" (is "?z_hgm ==> ?z_hgt ==> FALSE")
 proof -
  assume z_Hgm:"?z_hgm"
  assume z_Hgt:"?z_hgt" (is "~?z_hgu")
  have z_Hgu: "?z_hgu"
  by (rule zenon_in_subsetof_0 [of "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))" "Configs" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=(ret[p]))&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, BOT))&(((t[''op''])=except((told[''op'']), p, BOT))&((t[''arg''])=except((told[''arg'']), p, BOT)))))))))", OF z_Hgm])
  show FALSE
  by (rule notE [OF z_Hgt z_Hgu])
 qed
 have zenon_L9_: "(a_rethash_primea=ret) ==> (~(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))) ==> (ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))) ==> FALSE" (is "?z_hl ==> ?z_hgv ==> ?z_hcn ==> FALSE")
 proof -
  assume z_Hl:"?z_hl"
  assume z_Hgv:"?z_hgv" (is "~?z_hgw")
  assume z_Hcn:"?z_hcn"
  have z_Hgx: "(~?z_hcn)"
  by (rule subst [where P="(\<lambda>zenon_Vgb. (~(zenon_Vgb \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))", OF z_Hl z_Hgv])
  show FALSE
  by (rule notE [OF z_Hgx z_Hcn])
 qed
 assume z_Hm:"(~((a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_Mhash_primea \\in SUBSET(Configs))&(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))))))))))" (is "~(?z_hfa&?z_hhd)")
 have z_Hn: "?z_hn" (is "?z_ho&?z_hbc")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Ho: "?z_ho"
 by (rule zenon_and_0 [OF z_Hn])
 have z_Hbc: "?z_hbc" (is "?z_hbd&?z_hbs")
 by (rule zenon_and_1 [OF z_Hn])
 have z_Hbd: "?z_hbd"
 by (rule zenon_and_0 [OF z_Hbc])
 have z_Hbs: "?z_hbs" (is "?z_hbt&?z_hbw")
 by (rule zenon_and_1 [OF z_Hbc])
 have z_Hbt: "?z_hbt"
 by (rule zenon_and_0 [OF z_Hbs])
 have z_Hbw: "?z_hbw" (is "?z_hbx&?z_hbz")
 by (rule zenon_and_1 [OF z_Hbs])
 have z_Hbx: "?z_hbx"
 by (rule zenon_and_0 [OF z_Hbw])
 have z_Hbz: "?z_hbz" (is "?z_hca&?z_hcc")
 by (rule zenon_and_1 [OF z_Hbw])
 have z_Hca: "?z_hca"
 by (rule zenon_and_0 [OF z_Hbz])
 have z_Hcc: "?z_hcc" (is "?z_hcd&?z_hcf")
 by (rule zenon_and_1 [OF z_Hbz])
 have z_Hcd: "?z_hcd"
 by (rule zenon_and_0 [OF z_Hcc])
 have z_Hcf: "?z_hcf" (is "?z_hcg&?z_hci")
 by (rule zenon_and_1 [OF z_Hcc])
 have z_Hcg: "?z_hcg"
 by (rule zenon_and_0 [OF z_Hcf])
 have z_Hci: "?z_hci" (is "?z_hcj&?z_hcn")
 by (rule zenon_and_1 [OF z_Hcf])
 have z_Hcn: "?z_hcn"
 by (rule zenon_and_1 [OF z_Hci])
 show FALSE
 proof (rule zenon_notand [OF z_Hm])
  assume z_Hez:"(~?z_hfa)"
  show FALSE
  by (rule zenon_L1_ [OF z_Hd z_Hez z_Ho])
 next
  assume z_Hhl:"(~?z_hhd)" (is "~(?z_hfn&?z_hhe)")
  show FALSE
  proof (rule zenon_notand [OF z_Hhl])
   assume z_Hfm:"(~?z_hfn)"
   show FALSE
   by (rule zenon_L2_ [OF z_Hf z_Hfm z_Hbd])
  next
   assume z_Hhm:"(~?z_hhe)" (is "~(?z_hfu&?z_hhf)")
   show FALSE
   proof (rule zenon_notand [OF z_Hhm])
    assume z_Hft:"(~?z_hfu)"
    show FALSE
    by (rule zenon_L3_ [OF z_Hg z_Hft z_Hbt])
   next
    assume z_Hhn:"(~?z_hhf)" (is "~(?z_hgb&?z_hhg)")
    show FALSE
    proof (rule zenon_notand [OF z_Hhn])
     assume z_Hga:"(~?z_hgb)"
     show FALSE
     by (rule zenon_L4_ [OF z_Hh z_Hga z_Hbx])
    next
     assume z_Hho:"(~?z_hhg)" (is "~(?z_hge&?z_hhh)")
     show FALSE
     proof (rule zenon_notand [OF z_Hho])
      assume z_Hgd:"(~?z_hge)"
      show FALSE
      by (rule zenon_L5_ [OF z_Hi z_Hgd z_Hca])
     next
      assume z_Hhp:"(~?z_hhh)" (is "~(?z_hgh&?z_hhi)")
      show FALSE
      proof (rule zenon_notand [OF z_Hhp])
       assume z_Hgg:"(~?z_hgh)"
       show FALSE
       by (rule zenon_L6_ [OF z_Hj z_Hgg z_Hcd])
      next
       assume z_Hhq:"(~?z_hhi)" (is "~(?z_hgk&?z_hhj)")
       show FALSE
       proof (rule zenon_notand [OF z_Hhq])
        assume z_Hgj:"(~?z_hgk)"
        show FALSE
        by (rule zenon_L7_ [OF z_Hk z_Hgj z_Hcg])
       next
        assume z_Hhr:"(~?z_hhj)" (is "~(?z_hhk&?z_hgw)")
        show FALSE
        proof (rule zenon_notand [OF z_Hhr])
         assume z_Hhs:"(~?z_hhk)"
         have z_Hht: "(~(a_Mhash_primea \\subseteq Configs))" (is "~?z_hhu")
         by (rule zenon_notin_SUBSET_0 [of "a_Mhash_primea" "Configs", OF z_Hhs])
         have z_Hhv_z_Hht: "(~bAll(a_Mhash_primea, (\<lambda>x. (x \\in Configs)))) == (~?z_hhu)" (is "?z_hhv == ?z_hht")
         by (unfold subset_def)
         have z_Hhv: "?z_hhv" (is "~?z_hhw")
         by (unfold z_Hhv_z_Hht, fact z_Hht)
         have z_Hhy_z_Hhv: "(~(\\A x:((x \\in a_Mhash_primea)=>(x \\in Configs)))) == ?z_hhv" (is "?z_hhy == _")
         by (unfold bAll_def)
         have z_Hhy: "?z_hhy" (is "~(\\A x : ?z_hia(x))")
         by (unfold z_Hhy_z_Hhv, fact z_Hhv)
         have z_Hib: "(\\E x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))" (is "\\E x : ?z_hic(x)")
         by (rule zenon_notallex_0 [of "?z_hia", OF z_Hhy])
         have z_Hid: "?z_hic((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))))" (is "~(?z_hie=>?z_hgu)")
         by (rule zenon_ex_choose_0 [of "?z_hic", OF z_Hib])
         have z_Hie: "?z_hie"
         by (rule zenon_notimply_0 [OF z_Hid])
         have z_Hgt: "(~?z_hgu)"
         by (rule zenon_notimply_1 [OF z_Hid])
         have z_Hgm: "((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))) \\in ?z_hds)" (is "?z_hgm")
         by (rule subst [where P="(\<lambda>zenon_Vtb. ((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))) \\in zenon_Vtb))", OF z_He z_Hie])
         show FALSE
         by (rule zenon_L8_ [OF z_Hgm z_Hgt])
        next
         assume z_Hgv:"(~?z_hgw)"
         show FALSE
         by (rule zenon_L9_ [OF z_Hl z_Hgv z_Hcn])
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
ML_command {* writeln "*** TLAPS EXIT 38"; *} qed
lemma ob'40:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes F F'
fixes u u'
fixes v v'
fixes w w'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition StateSet suppressed *)
(* usable definition Configs suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition Init suppressed *)
(* usable definition UFSUnite suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Next suppressed *)
(* usable definition SameSetSpec suppressed *)
assumes v'43: "((((((pc) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & (((F) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & (((u) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((w) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((M) \<in> ((SUBSET (Configs))))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))) \<and> (((Next) \<or> (((((a_pchash_primea :: c)) = (pc))) & ((((a_Fhash_primea :: c)) = (F))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_whash_primea :: c)) = (w))) & ((((a_chash_primea :: c)) = (a_ca))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_Mhash_primea :: c)) = (M))) & ((((a_rethash_primea :: c)) = (ret))))))))"
fixes p
assumes p_in : "(p \<in> (PROCESSES))"
assumes v'53: "((((((((F) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) \<and> (((fapply ((a_ca), (p))) \<in> ((isa_peri_peri_a (((Succ[0])), (N)))))))) \<and> (((fapply ((d), (p))) \<in> ((isa_peri_peri_a (((Succ[0])), (N)))))))) & (((((a_Fhash_primea :: c)) = ([ i \<in> ((isa_peri_peri_a (((Succ[0])), (N))))  \<mapsto> (cond((((fapply ((F), (i))) = (fapply ((F), (fapply ((a_ca), (p))))))), (fapply ((F), (fapply ((d), (p))))), (fapply ((F), (i)))))]))) | ((((a_Fhash_primea :: c)) = ([ i \<in> ((isa_peri_peri_a (((Succ[0])), (N))))  \<mapsto> (cond((((fapply ((F), (i))) = (fapply ((F), (fapply ((d), (p))))))), (fapply ((F), (fapply ((a_ca), (p))))), (fapply ((F), (i)))))])))))"
assumes v'54: "(((fapply ((pc), (p))) = (''U1'')))"
assumes v'55: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''UR'')])))"
assumes v'56: "((((a_rethash_primea :: c)) = ([(ret) EXCEPT ![(p)] = (ACK)])))"
assumes v'57: "((((a_Mhash_primea :: c)) = (subsetOf((Configs), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((t), (''ret''))) = ([(fapply ((told), (''ret''))) EXCEPT ![(p)] = (ACK)]))) & (cond(((((a_Fhash_primea :: c)) = ([ i \<in> ((isa_peri_peri_a (((Succ[0])), (N))))  \<mapsto> (cond((((fapply ((F), (i))) = (fapply ((F), (fapply ((a_ca), (p))))))), (fapply ((F), (fapply ((d), (p))))), (fapply ((F), (i)))))]))), ((UFSUnite ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[0])))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[Succ[0]])))), (fapply ((t), (''sigma'')))))), ((UFSUnite ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[Succ[0]])))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[0])))), (fapply ((t), (''sigma'')))))))) & (((fapply ((t), (''op''))) = (fapply ((told), (''op''))))) & (((fapply ((t), (''arg''))) = (fapply ((told), (''arg'')))))))))))"
assumes v'58: "((((a_uhash_primea :: c)) = (u)))"
assumes v'59: "((((a_vhash_primea :: c)) = (v)))"
assumes v'60: "((((a_whash_primea :: c)) = (w)))"
assumes v'61: "((((a_chash_primea :: c)) = (a_ca)))"
assumes v'62: "((((a_dhash_primea :: c)) = (d)))"
assumes v'72: "((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})])))"
assumes v'73: "((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))])))"
assumes v'74: "((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))])))"
assumes v'75: "((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))])))"
assumes v'76: "((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))])))"
assumes v'77: "((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))])))"
assumes v'78: "((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs)))))"
assumes v'79: "((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))"
assumes v'80: "((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i))))))))))"
shows "(((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))]))))"(is "PROP ?ob'40")
proof -
ML_command {* writeln "*** TLAPS ENTER 40"; *}
show "PROP ?ob'40"

(* BEGIN ZENON INPUT
;; file=SameSetTypeOK.tlaps/tlapm_a72b00.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >SameSetTypeOK.tlaps/tlapm_a72b00.znn.out
;; obligation #40
$hyp "v'43" (/\ (/\ (TLA.in pc
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in F (TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i))))))) (TLA.in u
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in v
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in w
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_ca (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in d (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in M (TLA.SUBSET Configs)) (TLA.in ret
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0) N))))) (\/ Next
(/\ (= a_pchash_primea pc) (= a_Fhash_primea F) (= a_uhash_primea u)
(= a_vhash_primea v) (= a_whash_primea w) (= a_chash_primea a_ca)
(= a_dhash_primea d) (= a_Mhash_primea M) (= a_rethash_primea
ret))))
$hyp "p_in" (TLA.in p PROCESSES)
$hyp "v'53" (/\ (/\ (/\ (TLA.in F
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in (TLA.fapply a_ca p) (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in (TLA.fapply d p) (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(\/ (= a_Fhash_primea (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (TLA.cond (= (TLA.fapply F i)
(TLA.fapply F (TLA.fapply a_ca p))) (TLA.fapply F (TLA.fapply d p)) (TLA.fapply F i)))))
(= a_Fhash_primea (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (TLA.cond (= (TLA.fapply F i)
(TLA.fapply F (TLA.fapply d p))) (TLA.fapply F (TLA.fapply a_ca p)) (TLA.fapply F i)))))))
$hyp "v'54" (= (TLA.fapply pc p) "U1")
$hyp "v'55" (= a_pchash_primea
(TLA.except pc p "UR"))
$hyp "v'56" (= a_rethash_primea
(TLA.except ret p ACK))
$hyp "v'57" (= a_Mhash_primea
(TLA.subsetOf Configs ((t) (TLA.bEx M ((told) (/\ (= (TLA.fapply (TLA.fapply told "ret") p)
BOT) (= (TLA.fapply t "ret") (TLA.except (TLA.fapply told "ret") p ACK))
(TLA.cond (= a_Fhash_primea (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (TLA.cond (= (TLA.fapply F i)
(TLA.fapply F (TLA.fapply a_ca p))) (TLA.fapply F (TLA.fapply d p)) (TLA.fapply F i))))) (UFSUnite (TLA.fapply told "sigma")
(TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ 0))
(TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
(TLA.fapply t "sigma")) (UFSUnite (TLA.fapply told "sigma")
(TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
(TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ 0))
(TLA.fapply t "sigma"))) (= (TLA.fapply t "op") (TLA.fapply told "op"))
(= (TLA.fapply t "arg")
(TLA.fapply told "arg"))))))))
$hyp "v'58" (= a_uhash_primea u)
$hyp "v'59" (= a_vhash_primea v)
$hyp "v'60" (= a_whash_primea w)
$hyp "v'61" (= a_chash_primea a_ca)
$hyp "v'62" (= a_dhash_primea d)
$hyp "v'72" (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
$hyp "v'73" (TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N)))
$hyp "v'74" (TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N)))
$hyp "v'75" (TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N)))
$hyp "v'76" (TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N)))
$hyp "v'77" (TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N)))
$hyp "v'78" (TLA.in a_Mhash_primea
(TLA.SUBSET Configs))
$hyp "v'79" (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N))))
$hyp "v'80" (TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i))
(TLA.fapply A i)))))))
$goal (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hm:"(a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "?z_hm")
 using v'72 by blast
 have z_Hu:"(a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))" (is "?z_hu")
 using v'80 by blast
 have z_Hn:"(a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))" (is "?z_hn")
 using v'73 by blast
 have z_Ho:"(a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))" (is "?z_ho")
 using v'74 by blast
 have z_Hp:"(a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))" (is "?z_hp")
 using v'75 by blast
 have z_Hq:"(a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))" (is "?z_hq")
 using v'76 by blast
 have z_Hr:"(a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))" (is "?z_hr")
 using v'77 by blast
 have z_Hs:"(a_Mhash_primea \\in SUBSET(Configs))" (is "?z_hs")
 using v'78 by blast
 have z_Ht:"(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))" (is "?z_ht")
 using v'79 by blast
 assume z_Hv:"(~(?z_hm&(?z_hu&(?z_hn&(?z_ho&(?z_hp&(?z_hq&(?z_hr&(?z_hs&?z_ht)))))))))" (is "~(_&?z_hco)")
 show FALSE
 proof (rule zenon_notand [OF z_Hv])
  assume z_Hcv:"(~?z_hm)"
  show FALSE
  by (rule notE [OF z_Hcv z_Hm])
 next
  assume z_Hcw:"(~?z_hco)" (is "~(_&?z_hcp)")
  show FALSE
  proof (rule zenon_notand [OF z_Hcw])
   assume z_Hcx:"(~?z_hu)"
   show FALSE
   by (rule notE [OF z_Hcx z_Hu])
  next
   assume z_Hcy:"(~?z_hcp)" (is "~(_&?z_hcq)")
   show FALSE
   proof (rule zenon_notand [OF z_Hcy])
    assume z_Hcz:"(~?z_hn)"
    show FALSE
    by (rule notE [OF z_Hcz z_Hn])
   next
    assume z_Hda:"(~?z_hcq)" (is "~(_&?z_hcr)")
    show FALSE
    proof (rule zenon_notand [OF z_Hda])
     assume z_Hdb:"(~?z_ho)"
     show FALSE
     by (rule notE [OF z_Hdb z_Ho])
    next
     assume z_Hdc:"(~?z_hcr)" (is "~(_&?z_hcs)")
     show FALSE
     proof (rule zenon_notand [OF z_Hdc])
      assume z_Hdd:"(~?z_hp)"
      show FALSE
      by (rule notE [OF z_Hdd z_Hp])
     next
      assume z_Hde:"(~?z_hcs)" (is "~(_&?z_hct)")
      show FALSE
      proof (rule zenon_notand [OF z_Hde])
       assume z_Hdf:"(~?z_hq)"
       show FALSE
       by (rule notE [OF z_Hdf z_Hq])
      next
       assume z_Hdg:"(~?z_hct)" (is "~(_&?z_hcu)")
       show FALSE
       proof (rule zenon_notand [OF z_Hdg])
        assume z_Hdh:"(~?z_hr)"
        show FALSE
        by (rule notE [OF z_Hdh z_Hr])
       next
        assume z_Hdi:"(~?z_hcu)"
        show FALSE
        proof (rule zenon_notand [OF z_Hdi])
         assume z_Hdj:"(~?z_hs)"
         show FALSE
         by (rule notE [OF z_Hdj z_Hs])
        next
         assume z_Hdk:"(~?z_ht)"
         show FALSE
         by (rule notE [OF z_Hdk z_Ht])
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
ML_command {* writeln "*** TLAPS EXIT 40"; *} qed
lemma ob'58:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes F F'
fixes u u'
fixes v v'
fixes w w'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition StateSet suppressed *)
(* usable definition Configs suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition Init suppressed *)
(* usable definition UFSUnite suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Next suppressed *)
(* usable definition SameSetSpec suppressed *)
assumes v'43: "((((((pc) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & (((F) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & (((u) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((w) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((M) \<in> ((SUBSET (Configs))))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))) \<and> (((Next) \<or> (((((a_pchash_primea :: c)) = (pc))) & ((((a_Fhash_primea :: c)) = (F))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_whash_primea :: c)) = (w))) & ((((a_chash_primea :: c)) = (a_ca))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_Mhash_primea :: c)) = (M))) & ((((a_rethash_primea :: c)) = (ret))))))))"
fixes p
assumes p_in : "(p \<in> (PROCESSES))"
assumes v'53: "((((((((F) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) \<and> (((fapply ((a_ca), (p))) \<in> ((isa_peri_peri_a (((Succ[0])), (N)))))))) \<and> (((fapply ((d), (p))) \<in> ((isa_peri_peri_a (((Succ[0])), (N)))))))) & (((((a_Fhash_primea :: c)) = ([ i \<in> ((isa_peri_peri_a (((Succ[0])), (N))))  \<mapsto> (cond((((fapply ((F), (i))) = (fapply ((F), (fapply ((a_ca), (p))))))), (fapply ((F), (fapply ((d), (p))))), (fapply ((F), (i)))))]))) | ((((a_Fhash_primea :: c)) = ([ i \<in> ((isa_peri_peri_a (((Succ[0])), (N))))  \<mapsto> (cond((((fapply ((F), (i))) = (fapply ((F), (fapply ((d), (p))))))), (fapply ((F), (fapply ((a_ca), (p))))), (fapply ((F), (i)))))])))))"
assumes v'54: "(((fapply ((pc), (p))) = (''U1'')))"
assumes v'55: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''UR'')])))"
assumes v'56: "((((a_rethash_primea :: c)) = ([(ret) EXCEPT ![(p)] = (ACK)])))"
assumes v'57: "((((a_Mhash_primea :: c)) = (subsetOf((Configs), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((t), (''ret''))) = ([(fapply ((told), (''ret''))) EXCEPT ![(p)] = (ACK)]))) & (cond(((((a_Fhash_primea :: c)) = ([ i \<in> ((isa_peri_peri_a (((Succ[0])), (N))))  \<mapsto> (cond((((fapply ((F), (i))) = (fapply ((F), (fapply ((a_ca), (p))))))), (fapply ((F), (fapply ((d), (p))))), (fapply ((F), (i)))))]))), ((UFSUnite ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[0])))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[Succ[0]])))), (fapply ((t), (''sigma'')))))), ((UFSUnite ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[Succ[0]])))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[0])))), (fapply ((t), (''sigma'')))))))) & (((fapply ((t), (''op''))) = (fapply ((told), (''op''))))) & (((fapply ((t), (''arg''))) = (fapply ((told), (''arg'')))))))))))"
assumes v'58: "((((a_uhash_primea :: c)) = (u)))"
assumes v'59: "((((a_vhash_primea :: c)) = (v)))"
assumes v'60: "((((a_whash_primea :: c)) = (w)))"
assumes v'61: "((((a_chash_primea :: c)) = (a_ca)))"
assumes v'62: "((((a_dhash_primea :: c)) = (d)))"
shows "((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))"(is "PROP ?ob'58")
proof -
ML_command {* writeln "*** TLAPS ENTER 58"; *}
show "PROP ?ob'58"

(* BEGIN ZENON INPUT
;; file=SameSetTypeOK.tlaps/tlapm_4e2baa.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >SameSetTypeOK.tlaps/tlapm_4e2baa.znn.out
;; obligation #58
$hyp "v'43" (/\ (/\ (TLA.in pc
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in F (TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i))))))) (TLA.in u
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in v
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in w
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_ca (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in d (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in M (TLA.SUBSET Configs)) (TLA.in ret
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0) N))))) (\/ Next
(/\ (= a_pchash_primea pc) (= a_Fhash_primea F) (= a_uhash_primea u)
(= a_vhash_primea v) (= a_whash_primea w) (= a_chash_primea a_ca)
(= a_dhash_primea d) (= a_Mhash_primea M) (= a_rethash_primea
ret))))
$hyp "p_in" (TLA.in p PROCESSES)
$hyp "v'53" (/\ (/\ (/\ (TLA.in F
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in (TLA.fapply a_ca p) (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in (TLA.fapply d p) (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(\/ (= a_Fhash_primea (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (TLA.cond (= (TLA.fapply F i)
(TLA.fapply F (TLA.fapply a_ca p))) (TLA.fapply F (TLA.fapply d p)) (TLA.fapply F i)))))
(= a_Fhash_primea (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (TLA.cond (= (TLA.fapply F i)
(TLA.fapply F (TLA.fapply d p))) (TLA.fapply F (TLA.fapply a_ca p)) (TLA.fapply F i)))))))
$hyp "v'54" (= (TLA.fapply pc p) "U1")
$hyp "v'55" (= a_pchash_primea
(TLA.except pc p "UR"))
$hyp "v'56" (= a_rethash_primea
(TLA.except ret p ACK))
$hyp "v'57" (= a_Mhash_primea
(TLA.subsetOf Configs ((t) (TLA.bEx M ((told) (/\ (= (TLA.fapply (TLA.fapply told "ret") p)
BOT) (= (TLA.fapply t "ret") (TLA.except (TLA.fapply told "ret") p ACK))
(TLA.cond (= a_Fhash_primea (TLA.Fcn (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (TLA.cond (= (TLA.fapply F i)
(TLA.fapply F (TLA.fapply a_ca p))) (TLA.fapply F (TLA.fapply d p)) (TLA.fapply F i))))) (UFSUnite (TLA.fapply told "sigma")
(TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ 0))
(TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
(TLA.fapply t "sigma")) (UFSUnite (TLA.fapply told "sigma")
(TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0)))
(TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ 0))
(TLA.fapply t "sigma"))) (= (TLA.fapply t "op") (TLA.fapply told "op"))
(= (TLA.fapply t "arg")
(TLA.fapply told "arg"))))))))
$hyp "v'58" (= a_uhash_primea u)
$hyp "v'59" (= a_vhash_primea v)
$hyp "v'60" (= a_whash_primea w)
$hyp "v'61" (= a_chash_primea a_ca)
$hyp "v'62" (= a_dhash_primea d)
$goal (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((pc \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((F \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((u \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((v \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((w \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_ca \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((d \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((M \\in SUBSET(Configs))&(ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))))))))&(Next|((a_pchash_primea=pc)&((a_Fhash_primea=F)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_whash_primea=w)&((a_chash_primea=a_ca)&((a_dhash_primea=d)&((a_Mhash_primea=M)&(a_rethash_primea=ret)))))))))))" (is "?z_hn&?z_hcv")
 using v'43 by blast
 have z_Hf:"(a_rethash_primea=except(ret, p, ACK))" (is "_=?z_hds")
 using v'56 by blast
 assume z_Hm:"(~(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))" (is "~?z_hdu")
 have z_Hn: "?z_hn" (is "?z_ho&?z_hbc")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hbc: "?z_hbc" (is "?z_hbd&?z_hbs")
 by (rule zenon_and_1 [OF z_Hn])
 have z_Hbs: "?z_hbs" (is "?z_hbt&?z_hbw")
 by (rule zenon_and_1 [OF z_Hbc])
 have z_Hbw: "?z_hbw" (is "?z_hbx&?z_hbz")
 by (rule zenon_and_1 [OF z_Hbs])
 have z_Hbz: "?z_hbz" (is "?z_hca&?z_hcc")
 by (rule zenon_and_1 [OF z_Hbw])
 have z_Hcc: "?z_hcc" (is "?z_hcd&?z_hcf")
 by (rule zenon_and_1 [OF z_Hbz])
 have z_Hcf: "?z_hcf" (is "?z_hcg&?z_hci")
 by (rule zenon_and_1 [OF z_Hcc])
 have z_Hci: "?z_hci" (is "?z_hcj&?z_hcn")
 by (rule zenon_and_1 [OF z_Hcf])
 have z_Hcn: "?z_hcn"
 by (rule zenon_and_1 [OF z_Hci])
 have z_Hdv: "(~(?z_hds \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))" (is "~?z_hdw")
 by (rule subst [where P="(\<lambda>zenon_Vf. (~(zenon_Vf \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))", OF z_Hf z_Hm])
 show FALSE
 proof (rule zenon_except_notin_funcset [of "ret" "p" "ACK" "PROCESSES" "({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))", OF z_Hdv])
  assume z_Heb:"(~?z_hcn)"
  show FALSE
  by (rule notE [OF z_Heb z_Hcn])
 next
  assume z_Hec:"(~(ACK \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))" (is "~?z_hed")
  have z_Hee: "(~(ACK \\in {ACK, TRUE, FALSE}))" (is "~?z_hef")
  by (rule zenon_notin_cup_0 [of "ACK" "{ACK, TRUE, FALSE}" "isa'dotdot(1, N)", OF z_Hec])
  have z_Heg: "(ACK~=ACK)"
  by (rule zenon_notin_addElt_0 [of "ACK" "ACK" "{TRUE, FALSE}", OF z_Hee])
  show FALSE
  by (rule zenon_noteq [OF z_Heg])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 58"; *} qed
lemma ob'66:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes F F'
fixes u u'
fixes v v'
fixes w w'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition StateSet suppressed *)
(* usable definition Configs suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition Init suppressed *)
(* usable definition UFUniteShared suppressed *)
(* usable definition UFSUnite suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Next suppressed *)
(* usable definition SameSetSpec suppressed *)
assumes v'44: "((((((pc) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & (((F) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & (((u) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((w) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((M) \<in> ((SUBSET (Configs))))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))) \<and> (((Next) \<or> (((((a_pchash_primea :: c)) = (pc))) & ((((a_Fhash_primea :: c)) = (F))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_whash_primea :: c)) = (w))) & ((((a_chash_primea :: c)) = (a_ca))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_Mhash_primea :: c)) = (M))) & ((((a_rethash_primea :: c)) = (ret))))))))"
fixes p
assumes p_in : "(p \<in> (PROCESSES))"
assumes v'55: "(((fapply ((pc), (p))) = (''UR'')))"
assumes v'56: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''0'')])))"
assumes v'57: "((((a_Mhash_primea :: c)) = (subsetOf((Configs), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (fapply ((ret), (p))))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''ret''))) = ([(fapply ((told), (''ret''))) EXCEPT ![(p)] = (BOT)]))) & (((fapply ((t), (''op''))) = ([(fapply ((told), (''op''))) EXCEPT ![(p)] = (BOT)]))) & (((fapply ((t), (''arg''))) = ([(fapply ((told), (''arg''))) EXCEPT ![(p)] = (BOT)])))))))))"
assumes v'58: "((((a_Fhash_primea :: c)) = (F)))"
assumes v'59: "((((a_uhash_primea :: c)) = (u)))"
assumes v'60: "((((a_vhash_primea :: c)) = (v)))"
assumes v'61: "((((a_whash_primea :: c)) = (w)))"
assumes v'62: "((((a_chash_primea :: c)) = (a_ca)))"
assumes v'63: "((((a_dhash_primea :: c)) = (d)))"
assumes v'64: "((((a_rethash_primea :: c)) = (ret)))"
shows "(((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))]))))"(is "PROP ?ob'66")
proof -
ML_command {* writeln "*** TLAPS ENTER 66"; *}
show "PROP ?ob'66"

(* BEGIN ZENON INPUT
;; file=SameSetTypeOK.tlaps/tlapm_632745.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >SameSetTypeOK.tlaps/tlapm_632745.znn.out
;; obligation #66
$hyp "v'44" (/\ (/\ (TLA.in pc
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in F (TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i))))))) (TLA.in u
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in v
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in w
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_ca (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in d (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in M (TLA.SUBSET Configs)) (TLA.in ret
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0) N))))) (\/ Next
(/\ (= a_pchash_primea pc) (= a_Fhash_primea F) (= a_uhash_primea u)
(= a_vhash_primea v) (= a_whash_primea w) (= a_chash_primea a_ca)
(= a_dhash_primea d) (= a_Mhash_primea M) (= a_rethash_primea
ret))))
$hyp "p_in" (TLA.in p PROCESSES)
$hyp "v'55" (= (TLA.fapply pc p) "UR")
$hyp "v'56" (= a_pchash_primea
(TLA.except pc p "0"))
$hyp "v'57" (= a_Mhash_primea
(TLA.subsetOf Configs ((t) (TLA.bEx M ((told) (/\ (= (TLA.fapply (TLA.fapply told "ret") p)
(TLA.fapply ret p)) (= (TLA.fapply t "sigma") (TLA.fapply told "sigma"))
(= (TLA.fapply t "ret") (TLA.except (TLA.fapply told "ret") p BOT))
(= (TLA.fapply t "op") (TLA.except (TLA.fapply told "op") p BOT))
(= (TLA.fapply t "arg")
(TLA.except (TLA.fapply told "arg") p BOT))))))))
$hyp "v'58" (= a_Fhash_primea F)
$hyp "v'59" (= a_uhash_primea u)
$hyp "v'60" (= a_vhash_primea v)
$hyp "v'61" (= a_whash_primea w)
$hyp "v'62" (= a_chash_primea a_ca)
$hyp "v'63" (= a_dhash_primea d)
$hyp "v'64" (= a_rethash_primea ret)
$goal (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((pc \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((F \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((u \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((v \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((w \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_ca \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((d \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((M \\in SUBSET(Configs))&(ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))))))))&(Next|((a_pchash_primea=pc)&((a_Fhash_primea=F)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_whash_primea=w)&((a_chash_primea=a_ca)&((a_dhash_primea=d)&((a_Mhash_primea=M)&(a_rethash_primea=ret)))))))))))" (is "?z_hn&?z_hcv")
 using v'44 by blast
 have z_Hd:"(a_pchash_primea=except(pc, p, ''0''))" (is "_=?z_hdq")
 using v'56 by blast
 have z_Hf:"(a_Fhash_primea=F)"
 using v'58 by blast
 have z_Hg:"(a_uhash_primea=u)"
 using v'59 by blast
 have z_Hh:"(a_vhash_primea=v)"
 using v'60 by blast
 have z_Hi:"(a_whash_primea=w)"
 using v'61 by blast
 have z_Hj:"(a_chash_primea=a_ca)"
 using v'62 by blast
 have z_Hk:"(a_dhash_primea=d)"
 using v'63 by blast
 have z_He:"(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=(ret[p]))&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, BOT))&(((t[''op''])=except((told[''op'']), p, BOT))&((t[''arg''])=except((told[''arg'']), p, BOT)))))))))))" (is "_=?z_hds")
 using v'57 by blast
 have z_Hl:"(a_rethash_primea=ret)"
 using v'64 by blast
 have zenon_L1_: "(a_pchash_primea=?z_hdq) ==> (~(a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))) ==> (pc \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''})) ==> FALSE" (is "?z_hd ==> ?z_hez ==> ?z_ho ==> FALSE")
 proof -
  assume z_Hd:"?z_hd"
  assume z_Hez:"?z_hez" (is "~?z_hfa")
  assume z_Ho:"?z_ho"
  have z_Hfb: "(~(?z_hdq \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''})))" (is "~?z_hfc")
  by (rule subst [where P="(\<lambda>zenon_Vad. (~(zenon_Vad \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))", OF z_Hd z_Hez])
  show FALSE
  proof (rule zenon_except_notin_funcset [of "pc" "p" "''0''" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hfb])
   assume z_Hfh:"(~?z_ho)"
   show FALSE
   by (rule notE [OF z_Hfh z_Ho])
  next
   assume z_Hfi:"(~(''0'' \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hfj")
   have z_Hfk: "(''0''~=''0'')" (is "?z_ht~=_")
   by (rule zenon_notin_addElt_0 [of "?z_ht" "?z_ht" "{''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hfi])
   show FALSE
   by (rule zenon_noteq [OF z_Hfk])
  qed
 qed
 have zenon_L2_: "(a_Fhash_primea=F) ==> (~(a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))) ==> (F \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i]))))))) ==> FALSE" (is "?z_hf ==> ?z_hfm ==> ?z_hbd ==> FALSE")
 proof -
  assume z_Hf:"?z_hf"
  assume z_Hfm:"?z_hfm" (is "~?z_hfn")
  assume z_Hbd:"?z_hbd"
  have z_Hfo: "(~?z_hbd)"
  by (rule subst [where P="(\<lambda>zenon_Voc. (~(zenon_Voc \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))))", OF z_Hf z_Hfm])
  show FALSE
  by (rule notE [OF z_Hfo z_Hbd])
 qed
 have zenon_L3_: "(a_uhash_primea=u) ==> (~(a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (u \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hg ==> ?z_hft ==> ?z_hbt ==> FALSE")
 proof -
  assume z_Hg:"?z_hg"
  assume z_Hft:"?z_hft" (is "~?z_hfu")
  assume z_Hbt:"?z_hbt"
  have z_Hfv: "(~?z_hbt)"
  by (rule subst [where P="(\<lambda>zenon_Vzb. (~(zenon_Vzb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hg z_Hft])
  show FALSE
  by (rule notE [OF z_Hfv z_Hbt])
 qed
 have zenon_L4_: "(a_vhash_primea=v) ==> (~(a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (v \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hh ==> ?z_hga ==> ?z_hbx ==> FALSE")
 proof -
  assume z_Hh:"?z_hh"
  assume z_Hga:"?z_hga" (is "~?z_hgb")
  assume z_Hbx:"?z_hbx"
  have z_Hgc: "(~?z_hbx)"
  by (rule subst [where P="(\<lambda>zenon_Vzb. (~(zenon_Vzb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hh z_Hga])
  show FALSE
  by (rule notE [OF z_Hgc z_Hbx])
 qed
 have zenon_L5_: "(a_whash_primea=w) ==> (~(a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (w \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hi ==> ?z_hgd ==> ?z_hca ==> FALSE")
 proof -
  assume z_Hi:"?z_hi"
  assume z_Hgd:"?z_hgd" (is "~?z_hge")
  assume z_Hca:"?z_hca"
  have z_Hgf: "(~?z_hca)"
  by (rule subst [where P="(\<lambda>zenon_Vzb. (~(zenon_Vzb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hi z_Hgd])
  show FALSE
  by (rule notE [OF z_Hgf z_Hca])
 qed
 have zenon_L6_: "(a_chash_primea=a_ca) ==> (~(a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (a_ca \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hj ==> ?z_hgg ==> ?z_hcd ==> FALSE")
 proof -
  assume z_Hj:"?z_hj"
  assume z_Hgg:"?z_hgg" (is "~?z_hgh")
  assume z_Hcd:"?z_hcd"
  have z_Hgi: "(~?z_hcd)"
  by (rule subst [where P="(\<lambda>zenon_Vzb. (~(zenon_Vzb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hj z_Hgg])
  show FALSE
  by (rule notE [OF z_Hgi z_Hcd])
 qed
 have zenon_L7_: "(a_dhash_primea=d) ==> (~(a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (d \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hk ==> ?z_hgj ==> ?z_hcg ==> FALSE")
 proof -
  assume z_Hk:"?z_hk"
  assume z_Hgj:"?z_hgj" (is "~?z_hgk")
  assume z_Hcg:"?z_hcg"
  have z_Hgl: "(~?z_hcg)"
  by (rule subst [where P="(\<lambda>zenon_Vzb. (~(zenon_Vzb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hk z_Hgj])
  show FALSE
  by (rule notE [OF z_Hgl z_Hcg])
 qed
 have zenon_L8_: "((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))) \\in ?z_hds) ==> (~((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))) \\in Configs)) ==> FALSE" (is "?z_hgm ==> ?z_hgt ==> FALSE")
 proof -
  assume z_Hgm:"?z_hgm"
  assume z_Hgt:"?z_hgt" (is "~?z_hgu")
  have z_Hgu: "?z_hgu"
  by (rule zenon_in_subsetof_0 [of "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))" "Configs" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=(ret[p]))&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, BOT))&(((t[''op''])=except((told[''op'']), p, BOT))&((t[''arg''])=except((told[''arg'']), p, BOT)))))))))", OF z_Hgm])
  show FALSE
  by (rule notE [OF z_Hgt z_Hgu])
 qed
 have zenon_L9_: "(a_rethash_primea=ret) ==> (~(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))) ==> (ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))) ==> FALSE" (is "?z_hl ==> ?z_hgv ==> ?z_hcn ==> FALSE")
 proof -
  assume z_Hl:"?z_hl"
  assume z_Hgv:"?z_hgv" (is "~?z_hgw")
  assume z_Hcn:"?z_hcn"
  have z_Hgx: "(~?z_hcn)"
  by (rule subst [where P="(\<lambda>zenon_Vgb. (~(zenon_Vgb \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))", OF z_Hl z_Hgv])
  show FALSE
  by (rule notE [OF z_Hgx z_Hcn])
 qed
 assume z_Hm:"(~((a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_Mhash_primea \\in SUBSET(Configs))&(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))))))))))" (is "~(?z_hfa&?z_hhd)")
 have z_Hn: "?z_hn" (is "?z_ho&?z_hbc")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Ho: "?z_ho"
 by (rule zenon_and_0 [OF z_Hn])
 have z_Hbc: "?z_hbc" (is "?z_hbd&?z_hbs")
 by (rule zenon_and_1 [OF z_Hn])
 have z_Hbd: "?z_hbd"
 by (rule zenon_and_0 [OF z_Hbc])
 have z_Hbs: "?z_hbs" (is "?z_hbt&?z_hbw")
 by (rule zenon_and_1 [OF z_Hbc])
 have z_Hbt: "?z_hbt"
 by (rule zenon_and_0 [OF z_Hbs])
 have z_Hbw: "?z_hbw" (is "?z_hbx&?z_hbz")
 by (rule zenon_and_1 [OF z_Hbs])
 have z_Hbx: "?z_hbx"
 by (rule zenon_and_0 [OF z_Hbw])
 have z_Hbz: "?z_hbz" (is "?z_hca&?z_hcc")
 by (rule zenon_and_1 [OF z_Hbw])
 have z_Hca: "?z_hca"
 by (rule zenon_and_0 [OF z_Hbz])
 have z_Hcc: "?z_hcc" (is "?z_hcd&?z_hcf")
 by (rule zenon_and_1 [OF z_Hbz])
 have z_Hcd: "?z_hcd"
 by (rule zenon_and_0 [OF z_Hcc])
 have z_Hcf: "?z_hcf" (is "?z_hcg&?z_hci")
 by (rule zenon_and_1 [OF z_Hcc])
 have z_Hcg: "?z_hcg"
 by (rule zenon_and_0 [OF z_Hcf])
 have z_Hci: "?z_hci" (is "?z_hcj&?z_hcn")
 by (rule zenon_and_1 [OF z_Hcf])
 have z_Hcn: "?z_hcn"
 by (rule zenon_and_1 [OF z_Hci])
 show FALSE
 proof (rule zenon_notand [OF z_Hm])
  assume z_Hez:"(~?z_hfa)"
  show FALSE
  by (rule zenon_L1_ [OF z_Hd z_Hez z_Ho])
 next
  assume z_Hhl:"(~?z_hhd)" (is "~(?z_hfn&?z_hhe)")
  show FALSE
  proof (rule zenon_notand [OF z_Hhl])
   assume z_Hfm:"(~?z_hfn)"
   show FALSE
   by (rule zenon_L2_ [OF z_Hf z_Hfm z_Hbd])
  next
   assume z_Hhm:"(~?z_hhe)" (is "~(?z_hfu&?z_hhf)")
   show FALSE
   proof (rule zenon_notand [OF z_Hhm])
    assume z_Hft:"(~?z_hfu)"
    show FALSE
    by (rule zenon_L3_ [OF z_Hg z_Hft z_Hbt])
   next
    assume z_Hhn:"(~?z_hhf)" (is "~(?z_hgb&?z_hhg)")
    show FALSE
    proof (rule zenon_notand [OF z_Hhn])
     assume z_Hga:"(~?z_hgb)"
     show FALSE
     by (rule zenon_L4_ [OF z_Hh z_Hga z_Hbx])
    next
     assume z_Hho:"(~?z_hhg)" (is "~(?z_hge&?z_hhh)")
     show FALSE
     proof (rule zenon_notand [OF z_Hho])
      assume z_Hgd:"(~?z_hge)"
      show FALSE
      by (rule zenon_L5_ [OF z_Hi z_Hgd z_Hca])
     next
      assume z_Hhp:"(~?z_hhh)" (is "~(?z_hgh&?z_hhi)")
      show FALSE
      proof (rule zenon_notand [OF z_Hhp])
       assume z_Hgg:"(~?z_hgh)"
       show FALSE
       by (rule zenon_L6_ [OF z_Hj z_Hgg z_Hcd])
      next
       assume z_Hhq:"(~?z_hhi)" (is "~(?z_hgk&?z_hhj)")
       show FALSE
       proof (rule zenon_notand [OF z_Hhq])
        assume z_Hgj:"(~?z_hgk)"
        show FALSE
        by (rule zenon_L7_ [OF z_Hk z_Hgj z_Hcg])
       next
        assume z_Hhr:"(~?z_hhj)" (is "~(?z_hhk&?z_hgw)")
        show FALSE
        proof (rule zenon_notand [OF z_Hhr])
         assume z_Hhs:"(~?z_hhk)"
         have z_Hht: "(~(a_Mhash_primea \\subseteq Configs))" (is "~?z_hhu")
         by (rule zenon_notin_SUBSET_0 [of "a_Mhash_primea" "Configs", OF z_Hhs])
         have z_Hhv_z_Hht: "(~bAll(a_Mhash_primea, (\<lambda>x. (x \\in Configs)))) == (~?z_hhu)" (is "?z_hhv == ?z_hht")
         by (unfold subset_def)
         have z_Hhv: "?z_hhv" (is "~?z_hhw")
         by (unfold z_Hhv_z_Hht, fact z_Hht)
         have z_Hhy_z_Hhv: "(~(\\A x:((x \\in a_Mhash_primea)=>(x \\in Configs)))) == ?z_hhv" (is "?z_hhy == _")
         by (unfold bAll_def)
         have z_Hhy: "?z_hhy" (is "~(\\A x : ?z_hia(x))")
         by (unfold z_Hhy_z_Hhv, fact z_Hhv)
         have z_Hib: "(\\E x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))" (is "\\E x : ?z_hic(x)")
         by (rule zenon_notallex_0 [of "?z_hia", OF z_Hhy])
         have z_Hid: "?z_hic((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))))" (is "~(?z_hie=>?z_hgu)")
         by (rule zenon_ex_choose_0 [of "?z_hic", OF z_Hib])
         have z_Hie: "?z_hie"
         by (rule zenon_notimply_0 [OF z_Hid])
         have z_Hgt: "(~?z_hgu)"
         by (rule zenon_notimply_1 [OF z_Hid])
         have z_Hgm: "((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))) \\in ?z_hds)" (is "?z_hgm")
         by (rule subst [where P="(\<lambda>zenon_Vtb. ((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))) \\in zenon_Vtb))", OF z_He z_Hie])
         show FALSE
         by (rule zenon_L8_ [OF z_Hgm z_Hgt])
        next
         assume z_Hgv:"(~?z_hgw)"
         show FALSE
         by (rule zenon_L9_ [OF z_Hl z_Hgv z_Hcn])
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
ML_command {* writeln "*** TLAPS EXIT 66"; *} qed
lemma ob'68:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes F F'
fixes u u'
fixes v v'
fixes w w'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition StateSet suppressed *)
(* usable definition Configs suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition Init suppressed *)
(* usable definition UFUniteShared suppressed *)
(* usable definition UFSUnite suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Next suppressed *)
(* usable definition SameSetSpec suppressed *)
assumes v'44: "((((((pc) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & (((F) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & (((u) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((w) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((M) \<in> ((SUBSET (Configs))))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))) \<and> (((Next) \<or> (((((a_pchash_primea :: c)) = (pc))) & ((((a_Fhash_primea :: c)) = (F))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_whash_primea :: c)) = (w))) & ((((a_chash_primea :: c)) = (a_ca))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_Mhash_primea :: c)) = (M))) & ((((a_rethash_primea :: c)) = (ret))))))))"
fixes p
assumes p_in : "(p \<in> (PROCESSES))"
assumes v'56: "(((fapply ((pc), (p))) = (''S1'')))"
assumes v'57: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''S2'')])))"
assumes v'58: "((((a_uhash_primea :: c)) = ([(u) EXCEPT ![(p)] = (fapply ((F), (fapply ((a_ca), (p)))))])))"
assumes v'59: "((((a_vhash_primea :: c)) = ([(v) EXCEPT ![(p)] = (fapply ((d), (p)))])))"
assumes v'60: "((((a_Mhash_primea :: c)) = (M)))"
assumes v'61: "((((a_Fhash_primea :: c)) = (F)))"
assumes v'62: "((((a_whash_primea :: c)) = (w)))"
assumes v'63: "((((a_chash_primea :: c)) = (a_ca)))"
assumes v'64: "((((a_dhash_primea :: c)) = (d)))"
assumes v'65: "((((a_rethash_primea :: c)) = (ret)))"
shows "(((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))]))))"(is "PROP ?ob'68")
proof -
ML_command {* writeln "*** TLAPS ENTER 68"; *}
show "PROP ?ob'68"

(* BEGIN ZENON INPUT
;; file=SameSetTypeOK.tlaps/tlapm_c7a3ed.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >SameSetTypeOK.tlaps/tlapm_c7a3ed.znn.out
;; obligation #68
$hyp "v'44" (/\ (/\ (TLA.in pc
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in F (TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i))))))) (TLA.in u
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in v
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in w
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_ca (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in d (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in M (TLA.SUBSET Configs)) (TLA.in ret
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0) N))))) (\/ Next
(/\ (= a_pchash_primea pc) (= a_Fhash_primea F) (= a_uhash_primea u)
(= a_vhash_primea v) (= a_whash_primea w) (= a_chash_primea a_ca)
(= a_dhash_primea d) (= a_Mhash_primea M) (= a_rethash_primea
ret))))
$hyp "p_in" (TLA.in p PROCESSES)
$hyp "v'56" (= (TLA.fapply pc p) "S1")
$hyp "v'57" (= a_pchash_primea
(TLA.except pc p "S2"))
$hyp "v'58" (= a_uhash_primea
(TLA.except u p (TLA.fapply F (TLA.fapply a_ca p))))
$hyp "v'59" (= a_vhash_primea
(TLA.except v p (TLA.fapply d p)))
$hyp "v'60" (= a_Mhash_primea M)
$hyp "v'61" (= a_Fhash_primea F)
$hyp "v'62" (= a_whash_primea w)
$hyp "v'63" (= a_chash_primea a_ca)
$hyp "v'64" (= a_dhash_primea d)
$hyp "v'65" (= a_rethash_primea ret)
$goal (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((pc \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((F \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((u \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((v \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((w \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_ca \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((d \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((M \\in SUBSET(Configs))&(ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))))))))&(Next|((a_pchash_primea=pc)&((a_Fhash_primea=F)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_whash_primea=w)&((a_chash_primea=a_ca)&((a_dhash_primea=d)&((a_Mhash_primea=M)&(a_rethash_primea=ret)))))))))))" (is "?z_hn&?z_hcv")
 using v'44 by blast
 have z_Hd:"(a_pchash_primea=except(pc, p, ''S2''))" (is "_=?z_hdr")
 using v'57 by blast
 have z_Hh:"(a_Fhash_primea=F)"
 using v'61 by blast
 have z_He:"(a_uhash_primea=except(u, p, (F[(a_ca[p])])))" (is "_=?z_hdt")
 using v'58 by blast
 have z_Hf:"(a_vhash_primea=except(v, p, (d[p])))" (is "_=?z_hdw")
 using v'59 by blast
 have z_Hi:"(a_whash_primea=w)"
 using v'62 by blast
 have z_Hj:"(a_chash_primea=a_ca)"
 using v'63 by blast
 have z_Hk:"(a_dhash_primea=d)"
 using v'64 by blast
 have z_Hg:"(a_Mhash_primea=M)"
 using v'60 by blast
 have z_Hl:"(a_rethash_primea=ret)"
 using v'65 by blast
 have z_Hb:"(p \\in PROCESSES)" (is "?z_hb")
 using p_in by blast
 have zenon_L1_: "(a_pchash_primea=?z_hdr) ==> (~(a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))) ==> (pc \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''})) ==> FALSE" (is "?z_hd ==> ?z_hdy ==> ?z_ho ==> FALSE")
 proof -
  assume z_Hd:"?z_hd"
  assume z_Hdy:"?z_hdy" (is "~?z_hdz")
  assume z_Ho:"?z_ho"
  have z_Hea: "(~(?z_hdr \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''})))" (is "~?z_heb")
  by (rule subst [where P="(\<lambda>zenon_Vvib. (~(zenon_Vvib \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))", OF z_Hd z_Hdy])
  show FALSE
  proof (rule zenon_except_notin_funcset [of "pc" "p" "''S2''" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hea])
   assume z_Heg:"(~?z_ho)"
   show FALSE
   by (rule notE [OF z_Heg z_Ho])
  next
   assume z_Heh:"(~(''S2'' \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hei")
   have z_Hej: "(~(''S2'' \\in {''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hek")
   by (rule zenon_notin_addElt_1 [of "''S2''" "''0''" "{''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Heh])
   have z_Hem: "(~(''S2'' \\in {''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hen")
   by (rule zenon_notin_addElt_1 [of "''S2''" "''F1''" "{''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hej])
   have z_Hep: "(~(''S2'' \\in {''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_heq")
   by (rule zenon_notin_addElt_1 [of "''S2''" "''FR''" "{''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hem])
   have z_Hes: "(~(''S2'' \\in {''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_het")
   by (rule zenon_notin_addElt_1 [of "''S2''" "''U1''" "{''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hep])
   have z_Hev: "(~(''S2'' \\in {''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hew")
   by (rule zenon_notin_addElt_1 [of "''S2''" "''UR''" "{''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hes])
   have z_Hey: "(~(''S2'' \\in {''S2'', ''S3'', ''SR''}))" (is "~?z_hez")
   by (rule zenon_notin_addElt_1 [of "''S2''" "''S1''" "{''S2'', ''S3'', ''SR''}", OF z_Hev])
   have z_Hfb: "(''S2''~=''S2'')" (is "?z_hz~=_")
   by (rule zenon_notin_addElt_0 [of "?z_hz" "?z_hz" "{''S3'', ''SR''}", OF z_Hey])
   show FALSE
   by (rule zenon_noteq [OF z_Hfb])
  qed
 qed
 have zenon_L2_: "(a_Fhash_primea=F) ==> (~(a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))) ==> (F \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i]))))))) ==> FALSE" (is "?z_hh ==> ?z_hfd ==> ?z_hbd ==> FALSE")
 proof -
  assume z_Hh:"?z_hh"
  assume z_Hfd:"?z_hfd" (is "~?z_hfe")
  assume z_Hbd:"?z_hbd"
  have z_Hff: "(~?z_hbd)"
  by (rule subst [where P="(\<lambda>zenon_Vtib. (~(zenon_Vtib \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))))", OF z_Hh z_Hfd])
  show FALSE
  by (rule notE [OF z_Hff z_Hbd])
 qed
 have zenon_L3_: "(a_vhash_primea=?z_hdw) ==> (~(a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> ?z_hb ==> (d \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> (v \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hf ==> ?z_hfk ==> _ ==> ?z_hcg ==> ?z_hbx ==> FALSE")
 proof -
  assume z_Hf:"?z_hf"
  assume z_Hfk:"?z_hfk" (is "~?z_hfl")
  assume z_Hb:"?z_hb"
  assume z_Hcg:"?z_hcg"
  assume z_Hbx:"?z_hbx"
  have z_Hfm: "(~(?z_hdw \\in FuncSet(PROCESSES, isa'dotdot(1, N))))" (is "~?z_hfn")
  by (rule subst [where P="(\<lambda>zenon_Vdjb. (~(zenon_Vdjb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hf z_Hfk])
  show FALSE
  proof (rule zenon_except_notin_funcset [of "v" "p" "(d[p])" "PROCESSES" "isa'dotdot(1, N)", OF z_Hfm])
   assume z_Hfs:"(~?z_hbx)"
   show FALSE
   by (rule notE [OF z_Hfs z_Hbx])
  next
   assume z_Hft:"(~((d[p]) \\in isa'dotdot(1, N)))" (is "~?z_hfu")
   have z_Hfv: "(\\A zenon_Vs:((zenon_Vs \\in PROCESSES)=>((d[zenon_Vs]) \\in isa'dotdot(1, N))))" (is "\\A x : ?z_hgb(x)")
   by (rule zenon_in_funcset_2 [of "d" "PROCESSES" "isa'dotdot(1, N)", OF z_Hcg])
   have z_Hgc: "?z_hgb(p)"
   by (rule zenon_all_0 [of "?z_hgb" "p", OF z_Hfv])
   show FALSE
   proof (rule zenon_imply [OF z_Hgc])
    assume z_Hgd:"(~?z_hb)"
    show FALSE
    by (rule notE [OF z_Hgd z_Hb])
   next
    assume z_Hfu:"?z_hfu"
    show FALSE
    by (rule notE [OF z_Hft z_Hfu])
   qed
  qed
 qed
 have zenon_L4_: "(a_whash_primea=w) ==> (~(a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (w \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hi ==> ?z_hge ==> ?z_hca ==> FALSE")
 proof -
  assume z_Hi:"?z_hi"
  assume z_Hge:"?z_hge" (is "~?z_hgf")
  assume z_Hca:"?z_hca"
  have z_Hgg: "(~?z_hca)"
  by (rule subst [where P="(\<lambda>zenon_Vdjb. (~(zenon_Vdjb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hi z_Hge])
  show FALSE
  by (rule notE [OF z_Hgg z_Hca])
 qed
 have zenon_L5_: "(a_chash_primea=a_ca) ==> (~(a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (a_ca \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hj ==> ?z_hgh ==> ?z_hcd ==> FALSE")
 proof -
  assume z_Hj:"?z_hj"
  assume z_Hgh:"?z_hgh" (is "~?z_hgi")
  assume z_Hcd:"?z_hcd"
  have z_Hgj: "(~?z_hcd)"
  by (rule subst [where P="(\<lambda>zenon_Vdjb. (~(zenon_Vdjb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hj z_Hgh])
  show FALSE
  by (rule notE [OF z_Hgj z_Hcd])
 qed
 have zenon_L6_: "(a_dhash_primea=d) ==> (~(a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (d \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hk ==> ?z_hgk ==> ?z_hcg ==> FALSE")
 proof -
  assume z_Hk:"?z_hk"
  assume z_Hgk:"?z_hgk" (is "~?z_hgl")
  assume z_Hcg:"?z_hcg"
  have z_Hgm: "(~?z_hcg)"
  by (rule subst [where P="(\<lambda>zenon_Vdjb. (~(zenon_Vdjb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hk z_Hgk])
  show FALSE
  by (rule notE [OF z_Hgm z_Hcg])
 qed
 have zenon_L7_: "(a_Mhash_primea=M) ==> (~(a_Mhash_primea \\in SUBSET(Configs))) ==> bAll(M, (\<lambda>x. (x \\in Configs))) ==> FALSE" (is "?z_hg ==> ?z_hgn ==> ?z_hgp ==> FALSE")
 proof -
  assume z_Hg:"?z_hg"
  assume z_Hgn:"?z_hgn" (is "~?z_hgo")
  assume z_Hgp:"?z_hgp"
  have z_Hgt: "(~(a_Mhash_primea \\subseteq Configs))" (is "~?z_hgu")
  by (rule zenon_notin_SUBSET_0 [of "a_Mhash_primea" "Configs", OF z_Hgn])
  have z_Hgv_z_Hgt: "(~bAll(a_Mhash_primea, (\<lambda>x. (x \\in Configs)))) == (~?z_hgu)" (is "?z_hgv == ?z_hgt")
  by (unfold subset_def)
  have z_Hgv: "?z_hgv" (is "~?z_hgw")
  by (unfold z_Hgv_z_Hgt, fact z_Hgt)
  have z_Hgx: "(~?z_hgp)"
  by (rule subst [where P="(\<lambda>zenon_Vnjb. (~bAll(zenon_Vnjb, (\<lambda>x. (x \\in Configs)))))", OF z_Hg z_Hgv])
  show FALSE
  by (rule notE [OF z_Hgx z_Hgp])
 qed
 have zenon_L8_: "(a_rethash_primea=ret) ==> (~(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))) ==> (ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))) ==> FALSE" (is "?z_hl ==> ?z_hhc ==> ?z_hcn ==> FALSE")
 proof -
  assume z_Hl:"?z_hl"
  assume z_Hhc:"?z_hhc" (is "~?z_hhd")
  assume z_Hcn:"?z_hcn"
  have z_Hhe: "(~?z_hcn)"
  by (rule subst [where P="(\<lambda>zenon_Vpjb. (~(zenon_Vpjb \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))", OF z_Hl z_Hhc])
  show FALSE
  by (rule notE [OF z_Hhe z_Hcn])
 qed
 assume z_Hm:"(~((a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_Mhash_primea \\in SUBSET(Configs))&(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))))))))))" (is "~(?z_hdz&?z_hhk)")
 have z_Hn: "?z_hn" (is "?z_ho&?z_hbc")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Ho: "?z_ho"
 by (rule zenon_and_0 [OF z_Hn])
 have z_Hbc: "?z_hbc" (is "?z_hbd&?z_hbs")
 by (rule zenon_and_1 [OF z_Hn])
 have z_Hbd: "?z_hbd"
 by (rule zenon_and_0 [OF z_Hbc])
 have z_Hbs: "?z_hbs" (is "?z_hbt&?z_hbw")
 by (rule zenon_and_1 [OF z_Hbc])
 have z_Hbt: "?z_hbt"
 by (rule zenon_and_0 [OF z_Hbs])
 have z_Hbw: "?z_hbw" (is "?z_hbx&?z_hbz")
 by (rule zenon_and_1 [OF z_Hbs])
 have z_Hbx: "?z_hbx"
 by (rule zenon_and_0 [OF z_Hbw])
 have z_Hbz: "?z_hbz" (is "?z_hca&?z_hcc")
 by (rule zenon_and_1 [OF z_Hbw])
 have z_Hca: "?z_hca"
 by (rule zenon_and_0 [OF z_Hbz])
 have z_Hcc: "?z_hcc" (is "?z_hcd&?z_hcf")
 by (rule zenon_and_1 [OF z_Hbz])
 have z_Hcd: "?z_hcd"
 by (rule zenon_and_0 [OF z_Hcc])
 have z_Hcf: "?z_hcf" (is "?z_hcg&?z_hci")
 by (rule zenon_and_1 [OF z_Hcc])
 have z_Hcg: "?z_hcg"
 by (rule zenon_and_0 [OF z_Hcf])
 have z_Hci: "?z_hci" (is "?z_hcj&?z_hcn")
 by (rule zenon_and_1 [OF z_Hcf])
 have z_Hcj: "?z_hcj"
 by (rule zenon_and_0 [OF z_Hci])
 have z_Hcn: "?z_hcn"
 by (rule zenon_and_1 [OF z_Hci])
 have z_Hhs: "(F \\in FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)))" (is "?z_hhs")
 by (rule zenon_in_subsetof_0 [of "F" "FuncSet(isa'dotdot(1, N), isa'dotdot(1, N))" "(\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))", OF z_Hbd])
 have z_Hht: "(M \\subseteq Configs)" (is "?z_hht")
 by (rule zenon_in_SUBSET_0 [of "M" "Configs", OF z_Hcj])
 have z_Hgp_z_Hht: "bAll(M, (\<lambda>x. (x \\in Configs))) == ?z_hht" (is "?z_hgp == _")
 by (unfold subset_def)
 have z_Hgp: "?z_hgp"
 by (unfold z_Hgp_z_Hht, fact z_Hht)
 show FALSE
 proof (rule zenon_notand [OF z_Hm])
  assume z_Hdy:"(~?z_hdz)"
  show FALSE
  by (rule zenon_L1_ [OF z_Hd z_Hdy z_Ho])
 next
  assume z_Hhu:"(~?z_hhk)" (is "~(?z_hfe&?z_hhl)")
  show FALSE
  proof (rule zenon_notand [OF z_Hhu])
   assume z_Hfd:"(~?z_hfe)"
   show FALSE
   by (rule zenon_L2_ [OF z_Hh z_Hfd z_Hbd])
  next
   assume z_Hhv:"(~?z_hhl)" (is "~(?z_hhm&?z_hhn)")
   show FALSE
   proof (rule zenon_notand [OF z_Hhv])
    assume z_Hhw:"(~?z_hhm)"
    have z_Hhx: "(~(?z_hdt \\in FuncSet(PROCESSES, isa'dotdot(1, N))))" (is "~?z_hhy")
    by (rule subst [where P="(\<lambda>zenon_Vdjb. (~(zenon_Vdjb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_He z_Hhw])
    have z_Hhz: "(DOMAIN(u)=PROCESSES)" (is "?z_hia=_")
    by (rule zenon_in_funcset_1 [of "u" "PROCESSES" "isa'dotdot(1, N)", OF z_Hbt])
    show FALSE
    proof (rule zenon_except_notin_funcset [of "u" "p" "(F[(a_ca[p])])" "PROCESSES" "isa'dotdot(1, N)", OF z_Hhx])
     assume z_Hib:"(~?z_hbt)"
     show FALSE
     by (rule notE [OF z_Hib z_Hbt])
    next
     assume z_Hic:"(~((F[(a_ca[p])]) \\in isa'dotdot(1, N)))" (is "~?z_hid")
     show FALSE
     proof (rule zenon_notin_funcset [of "?z_hdt" "PROCESSES" "isa'dotdot(1, N)", OF z_Hhx])
      assume z_Hie:"(~isAFcn(?z_hdt))" (is "~?z_hif")
      show FALSE
      by (rule zenon_notisafcn_except [of "u" "p" "(F[(a_ca[p])])", OF z_Hie])
     next
      assume z_Hig:"(DOMAIN(?z_hdt)~=PROCESSES)" (is "?z_hih~=_")
      have z_Hii: "(?z_hia~=PROCESSES)"
      by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vrib. (zenon_Vrib~=PROCESSES))" "u" "p" "(F[(a_ca[p])])", OF z_Hig])
      show FALSE
      by (rule notE [OF z_Hii z_Hhz])
     next
      assume z_Him:"(~(\\A zenon_Vvl:((zenon_Vvl \\in PROCESSES)=>((?z_hdt[zenon_Vvl]) \\in isa'dotdot(1, N)))))" (is "~(\\A x : ?z_hit(x))")
      have z_Hiu: "(\\E zenon_Vvl:(~((zenon_Vvl \\in PROCESSES)=>((?z_hdt[zenon_Vvl]) \\in isa'dotdot(1, N)))))" (is "\\E x : ?z_hiw(x)")
      by (rule zenon_notallex_0 [of "?z_hit", OF z_Him])
      have z_Hix: "?z_hiw((CHOOSE zenon_Vvl:(~((zenon_Vvl \\in PROCESSES)=>((?z_hdt[zenon_Vvl]) \\in isa'dotdot(1, N))))))" (is "~(?z_hiz=>?z_hja)")
      by (rule zenon_ex_choose_0 [of "?z_hiw", OF z_Hiu])
      have z_Hiz: "?z_hiz"
      by (rule zenon_notimply_0 [OF z_Hix])
      have z_Hjb: "(~?z_hja)"
      by (rule zenon_notimply_1 [OF z_Hix])
      have z_Hjc: "((CHOOSE zenon_Vvl:(~((zenon_Vvl \\in PROCESSES)=>((?z_hdt[zenon_Vvl]) \\in isa'dotdot(1, N))))) \\in ?z_hia)" (is "?z_hjc")
      by (rule ssubst [where P="(\<lambda>zenon_Vko. ((CHOOSE zenon_Vvl:(~((zenon_Vvl \\in PROCESSES)=>((?z_hdt[zenon_Vvl]) \\in isa'dotdot(1, N))))) \\in zenon_Vko))", OF z_Hhz z_Hiz])
      show FALSE
      proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vte. (~(zenon_Vte \\in isa'dotdot(1, N))))" "u" "p" "(F[(a_ca[p])])" "(CHOOSE zenon_Vvl:(~((zenon_Vvl \\in PROCESSES)=>((?z_hdt[zenon_Vvl]) \\in isa'dotdot(1, N)))))", OF z_Hjb])
       assume z_Hjc:"?z_hjc"
       assume z_Hjk:"(p=(CHOOSE zenon_Vvl:(~((zenon_Vvl \\in PROCESSES)=>((?z_hdt[zenon_Vvl]) \\in isa'dotdot(1, N))))))" (is "_=?z_hiy")
       assume z_Hic:"(~?z_hid)"
       have z_Hjl: "(\\A zenon_Vv:((zenon_Vv \\in PROCESSES)=>((a_ca[zenon_Vv]) \\in isa'dotdot(1, N))))" (is "\\A x : ?z_hjr(x)")
       by (rule zenon_in_funcset_2 [of "a_ca" "PROCESSES" "isa'dotdot(1, N)", OF z_Hcd])
       have z_Hjs: "?z_hjr(?z_hiy)" (is "_=>?z_hjt")
       by (rule zenon_all_0 [of "?z_hjr" "?z_hiy", OF z_Hjl])
       show FALSE
       proof (rule zenon_imply [OF z_Hjs])
        assume z_Hju:"(~?z_hiz)"
        show FALSE
        by (rule notE [OF z_Hju z_Hiz])
       next
        assume z_Hjt:"?z_hjt"
        have z_Hjv: "(\\A zenon_Vna:((zenon_Vna \\in isa'dotdot(1, N))=>((F[zenon_Vna]) \\in isa'dotdot(1, N))))" (is "\\A x : ?z_hkb(x)")
        by (rule zenon_in_funcset_2 [of "F" "isa'dotdot(1, N)" "isa'dotdot(1, N)", OF z_Hhs])
        have z_Hkc: "?z_hkb((a_ca[p]))" (is "?z_hkd=>_")
        by (rule zenon_all_0 [of "?z_hkb" "(a_ca[p])", OF z_Hjv])
        show FALSE
        proof (rule zenon_imply [OF z_Hkc])
         assume z_Hke:"(~?z_hkd)"
         show FALSE
         proof (rule notE [OF z_Hke])
          have z_Hkf: "((a_ca[?z_hiy])=(a_ca[p]))" (is "?z_hkg=?z_hdv")
          proof (rule zenon_nnpp [of "(?z_hkg=?z_hdv)"])
           assume z_Hkh:"(?z_hkg~=?z_hdv)"
           show FALSE
           proof (rule zenon_noteq [of "?z_hdv"])
            have z_Hki: "(?z_hiy=p)"
            by (rule sym [OF z_Hjk])
            have z_Hkj: "(?z_hdv~=?z_hdv)"
            by (rule subst [where P="(\<lambda>zenon_Vqjb. ((a_ca[zenon_Vqjb])~=?z_hdv))", OF z_Hki], fact z_Hkh)
            thus "(?z_hdv~=?z_hdv)" .
           qed
          qed
          have z_Hkd: "?z_hkd"
          by (rule subst [where P="(\<lambda>zenon_Vrjb. (zenon_Vrjb \\in isa'dotdot(1, N)))", OF z_Hkf], fact z_Hjt)
          thus "?z_hkd" .
         qed
        next
         assume z_Hid:"?z_hid"
         show FALSE
         by (rule notE [OF z_Hic z_Hid])
        qed
       qed
      next
       assume z_Hjc:"?z_hjc"
       assume z_Hkr:"(p~=(CHOOSE zenon_Vvl:(~((zenon_Vvl \\in PROCESSES)=>((?z_hdt[zenon_Vvl]) \\in isa'dotdot(1, N))))))" (is "_~=?z_hiy")
       assume z_Hks:"(~((u[?z_hiy]) \\in isa'dotdot(1, N)))" (is "~?z_hkt")
       have z_Hkv: "(\\A zenon_Vea:((zenon_Vea \\in PROCESSES)=>((u[zenon_Vea]) \\in isa'dotdot(1, N))))" (is "\\A x : ?z_hlb(x)")
       by (rule zenon_in_funcset_2 [of "u" "PROCESSES" "isa'dotdot(1, N)", OF z_Hbt])
       have z_Hlc: "?z_hlb(?z_hiy)"
       by (rule zenon_all_0 [of "?z_hlb" "?z_hiy", OF z_Hkv])
       show FALSE
       proof (rule zenon_imply [OF z_Hlc])
        assume z_Hju:"(~?z_hiz)"
        show FALSE
        by (rule notE [OF z_Hju z_Hiz])
       next
        assume z_Hkt:"?z_hkt"
        show FALSE
        by (rule notE [OF z_Hks z_Hkt])
       qed
      next
       assume z_Hld:"(~?z_hjc)"
       show FALSE
       by (rule notE [OF z_Hld z_Hjc])
      qed
     qed
    qed
   next
    assume z_Hle:"(~?z_hhn)" (is "~(?z_hfl&?z_hho)")
    show FALSE
    proof (rule zenon_notand [OF z_Hle])
     assume z_Hfk:"(~?z_hfl)"
     show FALSE
     by (rule zenon_L3_ [OF z_Hf z_Hfk z_Hb z_Hcg z_Hbx])
    next
     assume z_Hlf:"(~?z_hho)" (is "~(?z_hgf&?z_hhp)")
     show FALSE
     proof (rule zenon_notand [OF z_Hlf])
      assume z_Hge:"(~?z_hgf)"
      show FALSE
      by (rule zenon_L4_ [OF z_Hi z_Hge z_Hca])
     next
      assume z_Hlg:"(~?z_hhp)" (is "~(?z_hgi&?z_hhq)")
      show FALSE
      proof (rule zenon_notand [OF z_Hlg])
       assume z_Hgh:"(~?z_hgi)"
       show FALSE
       by (rule zenon_L5_ [OF z_Hj z_Hgh z_Hcd])
      next
       assume z_Hlh:"(~?z_hhq)" (is "~(?z_hgl&?z_hhr)")
       show FALSE
       proof (rule zenon_notand [OF z_Hlh])
        assume z_Hgk:"(~?z_hgl)"
        show FALSE
        by (rule zenon_L6_ [OF z_Hk z_Hgk z_Hcg])
       next
        assume z_Hli:"(~?z_hhr)" (is "~(?z_hgo&?z_hhd)")
        show FALSE
        proof (rule zenon_notand [OF z_Hli])
         assume z_Hgn:"(~?z_hgo)"
         show FALSE
         by (rule zenon_L7_ [OF z_Hg z_Hgn z_Hgp])
        next
         assume z_Hhc:"(~?z_hhd)"
         show FALSE
         by (rule zenon_L8_ [OF z_Hl z_Hhc z_Hcn])
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
ML_command {* writeln "*** TLAPS EXIT 68"; *} qed
lemma ob'74:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes F F'
fixes u u'
fixes v v'
fixes w w'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition StateSet suppressed *)
(* usable definition Configs suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition Init suppressed *)
(* usable definition UFUniteShared suppressed *)
(* usable definition UFSUnite suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Next suppressed *)
(* usable definition SameSetSpec suppressed *)
assumes v'44: "((((((pc) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & (((F) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & (((u) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((w) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((M) \<in> ((SUBSET (Configs))))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))) \<and> (((Next) \<or> (((((a_pchash_primea :: c)) = (pc))) & ((((a_Fhash_primea :: c)) = (F))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_whash_primea :: c)) = (w))) & ((((a_chash_primea :: c)) = (a_ca))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_Mhash_primea :: c)) = (M))) & ((((a_rethash_primea :: c)) = (ret))))))))"
fixes p
assumes p_in : "(p \<in> (PROCESSES))"
assumes v'59: "(((fapply ((pc), (p))) = (''SR'')))"
assumes v'60: "((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''0'')])))"
assumes v'61: "((((a_Mhash_primea :: c)) = (subsetOf((Configs), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (fapply ((ret), (p))))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''ret''))) = ([(fapply ((told), (''ret''))) EXCEPT ![(p)] = (BOT)]))) & (((fapply ((t), (''op''))) = ([(fapply ((told), (''op''))) EXCEPT ![(p)] = (BOT)]))) & (((fapply ((t), (''arg''))) = ([(fapply ((told), (''arg''))) EXCEPT ![(p)] = (BOT)])))))))))"
assumes v'62: "((((a_Fhash_primea :: c)) = (F)))"
assumes v'63: "((((a_uhash_primea :: c)) = (u)))"
assumes v'64: "((((a_vhash_primea :: c)) = (v)))"
assumes v'65: "((((a_whash_primea :: c)) = (w)))"
assumes v'66: "((((a_chash_primea :: c)) = (a_ca)))"
assumes v'67: "((((a_dhash_primea :: c)) = (d)))"
assumes v'68: "((((a_rethash_primea :: c)) = (ret)))"
shows "(((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))]))))"(is "PROP ?ob'74")
proof -
ML_command {* writeln "*** TLAPS ENTER 74"; *}
show "PROP ?ob'74"

(* BEGIN ZENON INPUT
;; file=SameSetTypeOK.tlaps/tlapm_4616a1.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >SameSetTypeOK.tlaps/tlapm_4616a1.znn.out
;; obligation #74
$hyp "v'44" (/\ (/\ (TLA.in pc
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in F (TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i))))))) (TLA.in u
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in v
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in w
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_ca (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in d (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in M (TLA.SUBSET Configs)) (TLA.in ret
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0) N))))) (\/ Next
(/\ (= a_pchash_primea pc) (= a_Fhash_primea F) (= a_uhash_primea u)
(= a_vhash_primea v) (= a_whash_primea w) (= a_chash_primea a_ca)
(= a_dhash_primea d) (= a_Mhash_primea M) (= a_rethash_primea
ret))))
$hyp "p_in" (TLA.in p PROCESSES)
$hyp "v'59" (= (TLA.fapply pc p) "SR")
$hyp "v'60" (= a_pchash_primea
(TLA.except pc p "0"))
$hyp "v'61" (= a_Mhash_primea
(TLA.subsetOf Configs ((t) (TLA.bEx M ((told) (/\ (= (TLA.fapply (TLA.fapply told "ret") p)
(TLA.fapply ret p)) (= (TLA.fapply t "sigma") (TLA.fapply told "sigma"))
(= (TLA.fapply t "ret") (TLA.except (TLA.fapply told "ret") p BOT))
(= (TLA.fapply t "op") (TLA.except (TLA.fapply told "op") p BOT))
(= (TLA.fapply t "arg")
(TLA.except (TLA.fapply told "arg") p BOT))))))))
$hyp "v'62" (= a_Fhash_primea F)
$hyp "v'63" (= a_uhash_primea u)
$hyp "v'64" (= a_vhash_primea v)
$hyp "v'65" (= a_whash_primea w)
$hyp "v'66" (= a_chash_primea a_ca)
$hyp "v'67" (= a_dhash_primea d)
$hyp "v'68" (= a_rethash_primea ret)
$goal (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((pc \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((F \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((u \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((v \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((w \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_ca \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((d \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((M \\in SUBSET(Configs))&(ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))))))))&(Next|((a_pchash_primea=pc)&((a_Fhash_primea=F)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_whash_primea=w)&((a_chash_primea=a_ca)&((a_dhash_primea=d)&((a_Mhash_primea=M)&(a_rethash_primea=ret)))))))))))" (is "?z_hn&?z_hcv")
 using v'44 by blast
 have z_Hd:"(a_pchash_primea=except(pc, p, ''0''))" (is "_=?z_hdq")
 using v'60 by blast
 have z_Hf:"(a_Fhash_primea=F)"
 using v'62 by blast
 have z_Hg:"(a_uhash_primea=u)"
 using v'63 by blast
 have z_Hh:"(a_vhash_primea=v)"
 using v'64 by blast
 have z_Hi:"(a_whash_primea=w)"
 using v'65 by blast
 have z_Hj:"(a_chash_primea=a_ca)"
 using v'66 by blast
 have z_Hk:"(a_dhash_primea=d)"
 using v'67 by blast
 have z_He:"(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=(ret[p]))&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, BOT))&(((t[''op''])=except((told[''op'']), p, BOT))&((t[''arg''])=except((told[''arg'']), p, BOT)))))))))))" (is "_=?z_hds")
 using v'61 by blast
 have z_Hl:"(a_rethash_primea=ret)"
 using v'68 by blast
 have zenon_L1_: "(a_pchash_primea=?z_hdq) ==> (~(a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))) ==> (pc \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''})) ==> FALSE" (is "?z_hd ==> ?z_hez ==> ?z_ho ==> FALSE")
 proof -
  assume z_Hd:"?z_hd"
  assume z_Hez:"?z_hez" (is "~?z_hfa")
  assume z_Ho:"?z_ho"
  have z_Hfb: "(~(?z_hdq \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''})))" (is "~?z_hfc")
  by (rule subst [where P="(\<lambda>zenon_Vad. (~(zenon_Vad \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))", OF z_Hd z_Hez])
  show FALSE
  proof (rule zenon_except_notin_funcset [of "pc" "p" "''0''" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hfb])
   assume z_Hfh:"(~?z_ho)"
   show FALSE
   by (rule notE [OF z_Hfh z_Ho])
  next
   assume z_Hfi:"(~(''0'' \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hfj")
   have z_Hfk: "(''0''~=''0'')" (is "?z_ht~=_")
   by (rule zenon_notin_addElt_0 [of "?z_ht" "?z_ht" "{''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hfi])
   show FALSE
   by (rule zenon_noteq [OF z_Hfk])
  qed
 qed
 have zenon_L2_: "(a_Fhash_primea=F) ==> (~(a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))) ==> (F \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i]))))))) ==> FALSE" (is "?z_hf ==> ?z_hfm ==> ?z_hbd ==> FALSE")
 proof -
  assume z_Hf:"?z_hf"
  assume z_Hfm:"?z_hfm" (is "~?z_hfn")
  assume z_Hbd:"?z_hbd"
  have z_Hfo: "(~?z_hbd)"
  by (rule subst [where P="(\<lambda>zenon_Voc. (~(zenon_Voc \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))))", OF z_Hf z_Hfm])
  show FALSE
  by (rule notE [OF z_Hfo z_Hbd])
 qed
 have zenon_L3_: "(a_uhash_primea=u) ==> (~(a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (u \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hg ==> ?z_hft ==> ?z_hbt ==> FALSE")
 proof -
  assume z_Hg:"?z_hg"
  assume z_Hft:"?z_hft" (is "~?z_hfu")
  assume z_Hbt:"?z_hbt"
  have z_Hfv: "(~?z_hbt)"
  by (rule subst [where P="(\<lambda>zenon_Vzb. (~(zenon_Vzb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hg z_Hft])
  show FALSE
  by (rule notE [OF z_Hfv z_Hbt])
 qed
 have zenon_L4_: "(a_vhash_primea=v) ==> (~(a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (v \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hh ==> ?z_hga ==> ?z_hbx ==> FALSE")
 proof -
  assume z_Hh:"?z_hh"
  assume z_Hga:"?z_hga" (is "~?z_hgb")
  assume z_Hbx:"?z_hbx"
  have z_Hgc: "(~?z_hbx)"
  by (rule subst [where P="(\<lambda>zenon_Vzb. (~(zenon_Vzb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hh z_Hga])
  show FALSE
  by (rule notE [OF z_Hgc z_Hbx])
 qed
 have zenon_L5_: "(a_whash_primea=w) ==> (~(a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (w \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hi ==> ?z_hgd ==> ?z_hca ==> FALSE")
 proof -
  assume z_Hi:"?z_hi"
  assume z_Hgd:"?z_hgd" (is "~?z_hge")
  assume z_Hca:"?z_hca"
  have z_Hgf: "(~?z_hca)"
  by (rule subst [where P="(\<lambda>zenon_Vzb. (~(zenon_Vzb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hi z_Hgd])
  show FALSE
  by (rule notE [OF z_Hgf z_Hca])
 qed
 have zenon_L6_: "(a_chash_primea=a_ca) ==> (~(a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (a_ca \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hj ==> ?z_hgg ==> ?z_hcd ==> FALSE")
 proof -
  assume z_Hj:"?z_hj"
  assume z_Hgg:"?z_hgg" (is "~?z_hgh")
  assume z_Hcd:"?z_hcd"
  have z_Hgi: "(~?z_hcd)"
  by (rule subst [where P="(\<lambda>zenon_Vzb. (~(zenon_Vzb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hj z_Hgg])
  show FALSE
  by (rule notE [OF z_Hgi z_Hcd])
 qed
 have zenon_L7_: "(a_dhash_primea=d) ==> (~(a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (d \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hk ==> ?z_hgj ==> ?z_hcg ==> FALSE")
 proof -
  assume z_Hk:"?z_hk"
  assume z_Hgj:"?z_hgj" (is "~?z_hgk")
  assume z_Hcg:"?z_hcg"
  have z_Hgl: "(~?z_hcg)"
  by (rule subst [where P="(\<lambda>zenon_Vzb. (~(zenon_Vzb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hk z_Hgj])
  show FALSE
  by (rule notE [OF z_Hgl z_Hcg])
 qed
 have zenon_L8_: "((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))) \\in ?z_hds) ==> (~((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))) \\in Configs)) ==> FALSE" (is "?z_hgm ==> ?z_hgt ==> FALSE")
 proof -
  assume z_Hgm:"?z_hgm"
  assume z_Hgt:"?z_hgt" (is "~?z_hgu")
  have z_Hgu: "?z_hgu"
  by (rule zenon_in_subsetof_0 [of "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))" "Configs" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=(ret[p]))&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, BOT))&(((t[''op''])=except((told[''op'']), p, BOT))&((t[''arg''])=except((told[''arg'']), p, BOT)))))))))", OF z_Hgm])
  show FALSE
  by (rule notE [OF z_Hgt z_Hgu])
 qed
 have zenon_L9_: "(a_rethash_primea=ret) ==> (~(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))) ==> (ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))) ==> FALSE" (is "?z_hl ==> ?z_hgv ==> ?z_hcn ==> FALSE")
 proof -
  assume z_Hl:"?z_hl"
  assume z_Hgv:"?z_hgv" (is "~?z_hgw")
  assume z_Hcn:"?z_hcn"
  have z_Hgx: "(~?z_hcn)"
  by (rule subst [where P="(\<lambda>zenon_Vgb. (~(zenon_Vgb \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))", OF z_Hl z_Hgv])
  show FALSE
  by (rule notE [OF z_Hgx z_Hcn])
 qed
 assume z_Hm:"(~((a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_Mhash_primea \\in SUBSET(Configs))&(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))))))))))" (is "~(?z_hfa&?z_hhd)")
 have z_Hn: "?z_hn" (is "?z_ho&?z_hbc")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Ho: "?z_ho"
 by (rule zenon_and_0 [OF z_Hn])
 have z_Hbc: "?z_hbc" (is "?z_hbd&?z_hbs")
 by (rule zenon_and_1 [OF z_Hn])
 have z_Hbd: "?z_hbd"
 by (rule zenon_and_0 [OF z_Hbc])
 have z_Hbs: "?z_hbs" (is "?z_hbt&?z_hbw")
 by (rule zenon_and_1 [OF z_Hbc])
 have z_Hbt: "?z_hbt"
 by (rule zenon_and_0 [OF z_Hbs])
 have z_Hbw: "?z_hbw" (is "?z_hbx&?z_hbz")
 by (rule zenon_and_1 [OF z_Hbs])
 have z_Hbx: "?z_hbx"
 by (rule zenon_and_0 [OF z_Hbw])
 have z_Hbz: "?z_hbz" (is "?z_hca&?z_hcc")
 by (rule zenon_and_1 [OF z_Hbw])
 have z_Hca: "?z_hca"
 by (rule zenon_and_0 [OF z_Hbz])
 have z_Hcc: "?z_hcc" (is "?z_hcd&?z_hcf")
 by (rule zenon_and_1 [OF z_Hbz])
 have z_Hcd: "?z_hcd"
 by (rule zenon_and_0 [OF z_Hcc])
 have z_Hcf: "?z_hcf" (is "?z_hcg&?z_hci")
 by (rule zenon_and_1 [OF z_Hcc])
 have z_Hcg: "?z_hcg"
 by (rule zenon_and_0 [OF z_Hcf])
 have z_Hci: "?z_hci" (is "?z_hcj&?z_hcn")
 by (rule zenon_and_1 [OF z_Hcf])
 have z_Hcn: "?z_hcn"
 by (rule zenon_and_1 [OF z_Hci])
 show FALSE
 proof (rule zenon_notand [OF z_Hm])
  assume z_Hez:"(~?z_hfa)"
  show FALSE
  by (rule zenon_L1_ [OF z_Hd z_Hez z_Ho])
 next
  assume z_Hhl:"(~?z_hhd)" (is "~(?z_hfn&?z_hhe)")
  show FALSE
  proof (rule zenon_notand [OF z_Hhl])
   assume z_Hfm:"(~?z_hfn)"
   show FALSE
   by (rule zenon_L2_ [OF z_Hf z_Hfm z_Hbd])
  next
   assume z_Hhm:"(~?z_hhe)" (is "~(?z_hfu&?z_hhf)")
   show FALSE
   proof (rule zenon_notand [OF z_Hhm])
    assume z_Hft:"(~?z_hfu)"
    show FALSE
    by (rule zenon_L3_ [OF z_Hg z_Hft z_Hbt])
   next
    assume z_Hhn:"(~?z_hhf)" (is "~(?z_hgb&?z_hhg)")
    show FALSE
    proof (rule zenon_notand [OF z_Hhn])
     assume z_Hga:"(~?z_hgb)"
     show FALSE
     by (rule zenon_L4_ [OF z_Hh z_Hga z_Hbx])
    next
     assume z_Hho:"(~?z_hhg)" (is "~(?z_hge&?z_hhh)")
     show FALSE
     proof (rule zenon_notand [OF z_Hho])
      assume z_Hgd:"(~?z_hge)"
      show FALSE
      by (rule zenon_L5_ [OF z_Hi z_Hgd z_Hca])
     next
      assume z_Hhp:"(~?z_hhh)" (is "~(?z_hgh&?z_hhi)")
      show FALSE
      proof (rule zenon_notand [OF z_Hhp])
       assume z_Hgg:"(~?z_hgh)"
       show FALSE
       by (rule zenon_L6_ [OF z_Hj z_Hgg z_Hcd])
      next
       assume z_Hhq:"(~?z_hhi)" (is "~(?z_hgk&?z_hhj)")
       show FALSE
       proof (rule zenon_notand [OF z_Hhq])
        assume z_Hgj:"(~?z_hgk)"
        show FALSE
        by (rule zenon_L7_ [OF z_Hk z_Hgj z_Hcg])
       next
        assume z_Hhr:"(~?z_hhj)" (is "~(?z_hhk&?z_hgw)")
        show FALSE
        proof (rule zenon_notand [OF z_Hhr])
         assume z_Hhs:"(~?z_hhk)"
         have z_Hht: "(~(a_Mhash_primea \\subseteq Configs))" (is "~?z_hhu")
         by (rule zenon_notin_SUBSET_0 [of "a_Mhash_primea" "Configs", OF z_Hhs])
         have z_Hhv_z_Hht: "(~bAll(a_Mhash_primea, (\<lambda>x. (x \\in Configs)))) == (~?z_hhu)" (is "?z_hhv == ?z_hht")
         by (unfold subset_def)
         have z_Hhv: "?z_hhv" (is "~?z_hhw")
         by (unfold z_Hhv_z_Hht, fact z_Hht)
         have z_Hhy_z_Hhv: "(~(\\A x:((x \\in a_Mhash_primea)=>(x \\in Configs)))) == ?z_hhv" (is "?z_hhy == _")
         by (unfold bAll_def)
         have z_Hhy: "?z_hhy" (is "~(\\A x : ?z_hia(x))")
         by (unfold z_Hhy_z_Hhv, fact z_Hhv)
         have z_Hib: "(\\E x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))" (is "\\E x : ?z_hic(x)")
         by (rule zenon_notallex_0 [of "?z_hia", OF z_Hhy])
         have z_Hid: "?z_hic((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))))" (is "~(?z_hie=>?z_hgu)")
         by (rule zenon_ex_choose_0 [of "?z_hic", OF z_Hib])
         have z_Hie: "?z_hie"
         by (rule zenon_notimply_0 [OF z_Hid])
         have z_Hgt: "(~?z_hgu)"
         by (rule zenon_notimply_1 [OF z_Hid])
         have z_Hgm: "((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))) \\in ?z_hds)" (is "?z_hgm")
         by (rule subst [where P="(\<lambda>zenon_Vtb. ((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))) \\in zenon_Vtb))", OF z_He z_Hie])
         show FALSE
         by (rule zenon_L8_ [OF z_Hgm z_Hgt])
        next
         assume z_Hgv:"(~?z_hgw)"
         show FALSE
         by (rule zenon_L9_ [OF z_Hl z_Hgv z_Hcn])
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
ML_command {* writeln "*** TLAPS EXIT 74"; *} qed
lemma ob'76:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes F F'
fixes u u'
fixes v v'
fixes w w'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition StateSet suppressed *)
(* usable definition Configs suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition Init suppressed *)
(* usable definition UFUniteShared suppressed *)
(* usable definition UFSUnite suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Next suppressed *)
(* usable definition SameSetSpec suppressed *)
assumes v'45: "((((((pc) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & (((F) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & (((u) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((w) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((M) \<in> ((SUBSET (Configs))))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))) \<and> (((Next) \<or> (((((a_pchash_primea :: c)) = (pc))) & ((((a_Fhash_primea :: c)) = (F))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_whash_primea :: c)) = (w))) & ((((a_chash_primea :: c)) = (a_ca))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_Mhash_primea :: c)) = (M))) & ((((a_rethash_primea :: c)) = (ret))))))))"
assumes v'60: "((((a_pchash_primea :: c)) = (pc)))"
assumes v'61: "((((a_Fhash_primea :: c)) = (F)))"
assumes v'62: "((((a_uhash_primea :: c)) = (u)))"
assumes v'63: "((((a_vhash_primea :: c)) = (v)))"
assumes v'64: "((((a_whash_primea :: c)) = (w)))"
assumes v'65: "((((a_chash_primea :: c)) = (a_ca)))"
assumes v'66: "((((a_dhash_primea :: c)) = (d)))"
assumes v'67: "((((a_Mhash_primea :: c)) = (M)))"
assumes v'68: "((((a_rethash_primea :: c)) = (ret)))"
shows "(((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))]))))"(is "PROP ?ob'76")
proof -
ML_command {* writeln "*** TLAPS ENTER 76"; *}
show "PROP ?ob'76"

(* BEGIN ZENON INPUT
;; file=SameSetTypeOK.tlaps/tlapm_3856f6.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >SameSetTypeOK.tlaps/tlapm_3856f6.znn.out
;; obligation #76
$hyp "v'45" (/\ (/\ (TLA.in pc
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in F (TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i))))))) (TLA.in u
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in v
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in w
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_ca (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in d (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in M (TLA.SUBSET Configs)) (TLA.in ret
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0) N))))) (\/ Next
(/\ (= a_pchash_primea pc) (= a_Fhash_primea F) (= a_uhash_primea u)
(= a_vhash_primea v) (= a_whash_primea w) (= a_chash_primea a_ca)
(= a_dhash_primea d) (= a_Mhash_primea M) (= a_rethash_primea
ret))))
$hyp "v'60" (= a_pchash_primea pc)
$hyp "v'61" (= a_Fhash_primea F)
$hyp "v'62" (= a_uhash_primea u)
$hyp "v'63" (= a_vhash_primea v)
$hyp "v'64" (= a_whash_primea w)
$hyp "v'65" (= a_chash_primea a_ca)
$hyp "v'66" (= a_dhash_primea d)
$hyp "v'67" (= a_Mhash_primea M)
$hyp "v'68" (= a_rethash_primea ret)
$goal (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((pc \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((F \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((u \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((v \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((w \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_ca \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((d \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((M \\in SUBSET(Configs))&(ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))))))))&(Next|((a_pchash_primea=pc)&((a_Fhash_primea=F)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_whash_primea=w)&((a_chash_primea=a_ca)&((a_dhash_primea=d)&((a_Mhash_primea=M)&(a_rethash_primea=ret)))))))))))" (is "?z_hl&?z_hct")
 using v'45 by blast
 have z_Hb:"(a_pchash_primea=pc)"
 using v'60 by blast
 have z_Hc:"(a_Fhash_primea=F)"
 using v'61 by blast
 have z_Hd:"(a_uhash_primea=u)"
 using v'62 by blast
 have z_He:"(a_vhash_primea=v)"
 using v'63 by blast
 have z_Hf:"(a_whash_primea=w)"
 using v'64 by blast
 have z_Hg:"(a_chash_primea=a_ca)"
 using v'65 by blast
 have z_Hh:"(a_dhash_primea=d)"
 using v'66 by blast
 have z_Hi:"(a_Mhash_primea=M)"
 using v'67 by blast
 have z_Hj:"(a_rethash_primea=ret)"
 using v'68 by blast
 assume z_Hk:"(~((a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_Mhash_primea \\in SUBSET(Configs))&(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))))))))))" (is "~(?z_hdn&?z_hdo)")
 have z_Hl: "?z_hl" (is "?z_hm&?z_hba")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hm: "?z_hm"
 by (rule zenon_and_0 [OF z_Hl])
 have z_Hba: "?z_hba" (is "?z_hbb&?z_hbq")
 by (rule zenon_and_1 [OF z_Hl])
 have z_Hbb: "?z_hbb"
 by (rule zenon_and_0 [OF z_Hba])
 have z_Hbq: "?z_hbq" (is "?z_hbr&?z_hbu")
 by (rule zenon_and_1 [OF z_Hba])
 have z_Hbr: "?z_hbr"
 by (rule zenon_and_0 [OF z_Hbq])
 have z_Hbu: "?z_hbu" (is "?z_hbv&?z_hbx")
 by (rule zenon_and_1 [OF z_Hbq])
 have z_Hbv: "?z_hbv"
 by (rule zenon_and_0 [OF z_Hbu])
 have z_Hbx: "?z_hbx" (is "?z_hby&?z_hca")
 by (rule zenon_and_1 [OF z_Hbu])
 have z_Hby: "?z_hby"
 by (rule zenon_and_0 [OF z_Hbx])
 have z_Hca: "?z_hca" (is "?z_hcb&?z_hcd")
 by (rule zenon_and_1 [OF z_Hbx])
 have z_Hcb: "?z_hcb"
 by (rule zenon_and_0 [OF z_Hca])
 have z_Hcd: "?z_hcd" (is "?z_hce&?z_hcg")
 by (rule zenon_and_1 [OF z_Hca])
 have z_Hce: "?z_hce"
 by (rule zenon_and_0 [OF z_Hcd])
 have z_Hcg: "?z_hcg" (is "?z_hch&?z_hcl")
 by (rule zenon_and_1 [OF z_Hcd])
 have z_Hch: "?z_hch"
 by (rule zenon_and_0 [OF z_Hcg])
 have z_Hcl: "?z_hcl"
 by (rule zenon_and_1 [OF z_Hcg])
 have z_Hed: "(M \\subseteq Configs)" (is "?z_hed")
 by (rule zenon_in_SUBSET_0 [of "M" "Configs", OF z_Hch])
 have z_Hee_z_Hed: "bAll(M, (\<lambda>x. (x \\in Configs))) == ?z_hed" (is "?z_hee == _")
 by (unfold subset_def)
 have z_Hee: "?z_hee"
 by (unfold z_Hee_z_Hed, fact z_Hed)
 show FALSE
 proof (rule zenon_notand [OF z_Hk])
  assume z_Hei:"(~?z_hdn)"
  have z_Hej: "(~?z_hm)"
  by (rule subst [where P="(\<lambda>zenon_Vqc. (~(zenon_Vqc \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))", OF z_Hb z_Hei])
  show FALSE
  by (rule notE [OF z_Hej z_Hm])
 next
  assume z_Heo:"(~?z_hdo)" (is "~(?z_hdp&?z_hdq)")
  show FALSE
  proof (rule zenon_notand [OF z_Heo])
   assume z_Hep:"(~?z_hdp)"
   have z_Heq: "(~?z_hbb)"
   by (rule subst [where P="(\<lambda>zenon_Vec. (~(zenon_Vec \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))))", OF z_Hc z_Hep])
   show FALSE
   by (rule notE [OF z_Heq z_Hbb])
  next
   assume z_Hev:"(~?z_hdq)" (is "~(?z_hdr&?z_hds)")
   show FALSE
   proof (rule zenon_notand [OF z_Hev])
    assume z_Hew:"(~?z_hdr)"
    have z_Hex: "(~?z_hbr)"
    by (rule subst [where P="(\<lambda>zenon_Vpb. (~(zenon_Vpb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hd z_Hew])
    show FALSE
    by (rule notE [OF z_Hex z_Hbr])
   next
    assume z_Hfc:"(~?z_hds)" (is "~(?z_hdt&?z_hdu)")
    show FALSE
    proof (rule zenon_notand [OF z_Hfc])
     assume z_Hfd:"(~?z_hdt)"
     have z_Hfe: "(~?z_hbv)"
     by (rule subst [where P="(\<lambda>zenon_Vpb. (~(zenon_Vpb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_He z_Hfd])
     show FALSE
     by (rule notE [OF z_Hfe z_Hbv])
    next
     assume z_Hff:"(~?z_hdu)" (is "~(?z_hdv&?z_hdw)")
     show FALSE
     proof (rule zenon_notand [OF z_Hff])
      assume z_Hfg:"(~?z_hdv)"
      have z_Hfh: "(~?z_hby)"
      by (rule subst [where P="(\<lambda>zenon_Vpb. (~(zenon_Vpb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hf z_Hfg])
      show FALSE
      by (rule notE [OF z_Hfh z_Hby])
     next
      assume z_Hfi:"(~?z_hdw)" (is "~(?z_hdx&?z_hdy)")
      show FALSE
      proof (rule zenon_notand [OF z_Hfi])
       assume z_Hfj:"(~?z_hdx)"
       have z_Hfk: "(~?z_hcb)"
       by (rule subst [where P="(\<lambda>zenon_Vpb. (~(zenon_Vpb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hg z_Hfj])
       show FALSE
       by (rule notE [OF z_Hfk z_Hcb])
      next
       assume z_Hfl:"(~?z_hdy)" (is "~(?z_hdz&?z_hea)")
       show FALSE
       proof (rule zenon_notand [OF z_Hfl])
        assume z_Hfm:"(~?z_hdz)"
        have z_Hfn: "(~?z_hce)"
        by (rule subst [where P="(\<lambda>zenon_Vpb. (~(zenon_Vpb \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hh z_Hfm])
        show FALSE
        by (rule notE [OF z_Hfn z_Hce])
       next
        assume z_Hfo:"(~?z_hea)" (is "~(?z_heb&?z_hec)")
        show FALSE
        proof (rule zenon_notand [OF z_Hfo])
         assume z_Hfp:"(~?z_heb)"
         have z_Hfq: "(~(a_Mhash_primea \\subseteq Configs))" (is "~?z_hfr")
         by (rule zenon_notin_SUBSET_0 [of "a_Mhash_primea" "Configs", OF z_Hfp])
         have z_Hfs_z_Hfq: "(~bAll(a_Mhash_primea, (\<lambda>x. (x \\in Configs)))) == (~?z_hfr)" (is "?z_hfs == ?z_hfq")
         by (unfold subset_def)
         have z_Hfs: "?z_hfs" (is "~?z_hft")
         by (unfold z_Hfs_z_Hfq, fact z_Hfq)
         have z_Hfu: "(~?z_hee)"
         by (rule subst [where P="(\<lambda>zenon_Vfb. (~bAll(zenon_Vfb, (\<lambda>x. (x \\in Configs)))))", OF z_Hi z_Hfs])
         show FALSE
         by (rule notE [OF z_Hfu z_Hee])
        next
         assume z_Hfz:"(~?z_hec)"
         have z_Hga: "(~?z_hcl)"
         by (rule subst [where P="(\<lambda>zenon_Vza. (~(zenon_Vza \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))", OF z_Hj z_Hfz])
         show FALSE
         by (rule notE [OF z_Hga z_Hcl])
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
ML_command {* writeln "*** TLAPS EXIT 76"; *} qed
lemma ob'70:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes F F'
fixes u u'
fixes v v'
fixes w w'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition StateSet suppressed *)
(* usable definition Configs suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition Init suppressed *)
(* usable definition UFUniteShared suppressed *)
(* usable definition UFSUnite suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Next suppressed *)
(* usable definition SameSetSpec suppressed *)
assumes v'44: "((((((pc) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & (((F) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & (((u) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((w) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((M) \<in> ((SUBSET (Configs))))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))) \<and> (((Next) \<or> (((((a_pchash_primea :: c)) = (pc))) & ((((a_Fhash_primea :: c)) = (F))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_whash_primea :: c)) = (w))) & ((((a_chash_primea :: c)) = (a_ca))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_Mhash_primea :: c)) = (M))) & ((((a_rethash_primea :: c)) = (ret))))))))"
fixes p
assumes p_in : "(p \<in> (PROCESSES))"
assumes v'57: "(cond((((fapply (((a_uhash_primea :: c)), (p))) = (fapply (((a_vhash_primea :: c)), (p))))), (((((a_rethash_primea :: c)) = ([(ret) EXCEPT ![(p)] = (TRUE)]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''SR'')]))) & ((((a_Mhash_primea :: c)) = (subsetOf((Configs), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''ret''))) = ([(fapply ((told), (''ret''))) EXCEPT ![(p)] = (cond((((fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[0])))))) = (fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[Succ[0]])))))))), (TRUE), (FALSE)))]))) & (((fapply ((t), (''op''))) = (fapply ((told), (''op''))))) & (((fapply ((t), (''arg''))) = (fapply ((told), (''arg'')))))))))))), (((((a_rethash_primea :: c)) = (ret))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''S3'')]))) & ((((a_Mhash_primea :: c)) = (subsetOf((Configs), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((((fapply ((F), (fapply ((u), (p))))) = (fapply ((u), (p))))) & (((fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[0])))))) \<noteq> (fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[Succ[0]])))))))) & (((fapply ((t), (''ret''))) = ([(fapply ((told), (''ret''))) EXCEPT ![(p)] = (cond((((fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[0])))))) = (fapply ((fapply ((told), (''sigma''))), (fapply ((fapply ((fapply ((told), (''arg''))), (p))), ((Succ[Succ[0]])))))))), (TRUE), (FALSE)))])))) | (((fapply ((t), (''ret''))) = (fapply ((told), (''ret'')))))) & (((fapply ((t), (''op''))) = (fapply ((told), (''op''))))) & (((fapply ((t), (''arg''))) = (fapply ((told), (''arg''))))))))))))))"
assumes v'58: "(((fapply ((pc), (p))) = (''S2'')))"
assumes v'59: "((((a_vhash_primea :: c)) = ([(v) EXCEPT ![(p)] = (fapply ((F), (fapply ((v), (p)))))])))"
assumes v'60: "((((a_Fhash_primea :: c)) = (F)))"
assumes v'61: "((((a_uhash_primea :: c)) = (u)))"
assumes v'62: "((((a_whash_primea :: c)) = (w)))"
assumes v'63: "((((a_chash_primea :: c)) = (a_ca)))"
assumes v'64: "((((a_dhash_primea :: c)) = (d)))"
shows "(((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))]))))"(is "PROP ?ob'70")
proof -
ML_command {* writeln "*** TLAPS ENTER 70"; *}
show "PROP ?ob'70"

(* BEGIN ZENON INPUT
;; file=SameSetTypeOK.tlaps/tlapm_f8e1a8.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >SameSetTypeOK.tlaps/tlapm_f8e1a8.znn.out
;; obligation #70
$hyp "v'44" (/\ (/\ (TLA.in pc
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in F (TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i))))))) (TLA.in u
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in v
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in w
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_ca (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in d (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in M (TLA.SUBSET Configs)) (TLA.in ret
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0) N))))) (\/ Next
(/\ (= a_pchash_primea pc) (= a_Fhash_primea F) (= a_uhash_primea u)
(= a_vhash_primea v) (= a_whash_primea w) (= a_chash_primea a_ca)
(= a_dhash_primea d) (= a_Mhash_primea M) (= a_rethash_primea
ret))))
$hyp "p_in" (TLA.in p PROCESSES)
$hyp "v'57" (TLA.cond (= (TLA.fapply a_uhash_primea p)
(TLA.fapply a_vhash_primea p)) (/\ (= a_rethash_primea (TLA.except ret p T.))
(= a_pchash_primea (TLA.except pc p "SR")) (= a_Mhash_primea
(TLA.subsetOf Configs ((t) (TLA.bEx M ((told) (/\ (= (TLA.fapply (TLA.fapply told "ret") p)
BOT) (= (TLA.fapply t "sigma") (TLA.fapply told "sigma"))
(= (TLA.fapply t "ret")
(TLA.except (TLA.fapply told "ret") p (TLA.cond (= (TLA.fapply (TLA.fapply told "sigma") (TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ 0)))
(TLA.fapply (TLA.fapply told "sigma") (TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))) T. F.)))
(= (TLA.fapply t "op") (TLA.fapply told "op")) (= (TLA.fapply t "arg")
(TLA.fapply told "arg"))))))))) (/\ (= a_rethash_primea ret)
(= a_pchash_primea (TLA.except pc p "S3")) (= a_Mhash_primea
(TLA.subsetOf Configs ((t) (TLA.bEx M ((told) (/\ (= (TLA.fapply (TLA.fapply told "ret") p)
BOT) (= (TLA.fapply t "sigma") (TLA.fapply told "sigma"))
(\/ (/\ (= (TLA.fapply F (TLA.fapply u p)) (TLA.fapply u p))
(-. (= (TLA.fapply (TLA.fapply told "sigma") (TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ 0)))
(TLA.fapply (TLA.fapply told "sigma") (TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))))
(= (TLA.fapply t "ret")
(TLA.except (TLA.fapply told "ret") p (TLA.cond (= (TLA.fapply (TLA.fapply told "sigma") (TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ 0)))
(TLA.fapply (TLA.fapply told "sigma") (TLA.fapply (TLA.fapply (TLA.fapply told "arg") p) (TLA.fapply TLA.Succ (TLA.fapply TLA.Succ 0))))) T. F.))))
(= (TLA.fapply t "ret") (TLA.fapply told "ret"))) (= (TLA.fapply t "op")
(TLA.fapply told "op")) (= (TLA.fapply t "arg")
(TLA.fapply told "arg"))))))))))
$hyp "v'58" (= (TLA.fapply pc p) "S2")
$hyp "v'59" (= a_vhash_primea
(TLA.except v p (TLA.fapply F (TLA.fapply v p))))
$hyp "v'60" (= a_Fhash_primea F)
$hyp "v'61" (= a_uhash_primea u)
$hyp "v'62" (= a_whash_primea w)
$hyp "v'63" (= a_chash_primea a_ca)
$hyp "v'64" (= a_dhash_primea d)
$goal (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((pc \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((F \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((u \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((v \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((w \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_ca \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((d \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((M \\in SUBSET(Configs))&(ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))))))))&(Next|((a_pchash_primea=pc)&((a_Fhash_primea=F)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_whash_primea=w)&((a_chash_primea=a_ca)&((a_dhash_primea=d)&((a_Mhash_primea=M)&(a_rethash_primea=ret)))))))))))" (is "?z_hl&?z_hct")
 using v'44 by blast
 have z_Hj:"(a_dhash_primea=d)"
 using v'64 by blast
 have z_Hi:"(a_chash_primea=a_ca)"
 using v'63 by blast
 have z_Hh:"(a_whash_primea=w)"
 using v'62 by blast
 have z_He:"(a_vhash_primea=except(v, p, (F[(v[p])])))" (is "_=?z_hdq")
 using v'59 by blast
 have z_Hg:"(a_uhash_primea=u)"
 using v'61 by blast
 have z_Hf:"(a_Fhash_primea=F)"
 using v'60 by blast
 have z_Hc:"cond(((a_uhash_primea[p])=(a_vhash_primea[p])), ((a_rethash_primea=except(ret, p, TRUE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg'']))))))))))))), ((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((((F[(u[p])])=(u[p]))&((((told[''sigma''])[(((told[''arg''])[p])[1])])~=((told[''sigma''])[(((told[''arg''])[p])[2])]))&((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))))|((t[''ret''])=(told[''ret''])))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg'']))))))))))))))" (is "?z_hc")
 using v'57 by blast
 have zenon_L1_: "(a_pchash_primea=except(pc, p, ''SR'')) ==> (~isAFcn(a_pchash_primea)) ==> FALSE" (is "?z_heb ==> ?z_hgk ==> FALSE")
 proof -
  assume z_Heb:"?z_heb" (is "_=?z_hec")
  assume z_Hgk:"?z_hgk" (is "~?z_hgl")
  have z_Hgm: "(~isAFcn(?z_hec))" (is "~?z_hgn")
  by (rule subst [where P="(\<lambda>zenon_Vjqa. (~isAFcn(zenon_Vjqa)))", OF z_Heb z_Hgk])
  show FALSE
  by (rule zenon_notisafcn_except [of "pc" "p" "''SR''", OF z_Hgm])
 qed
 have zenon_L2_: "(a_pchash_primea=except(pc, p, ''SR'')) ==> (DOMAIN(a_pchash_primea)~=PROCESSES) ==> (DOMAIN(pc)=PROCESSES) ==> FALSE" (is "?z_heb ==> ?z_hgs ==> ?z_hgu ==> FALSE")
 proof -
  assume z_Heb:"?z_heb" (is "_=?z_hec")
  assume z_Hgs:"?z_hgs" (is "?z_hgt~=_")
  assume z_Hgu:"?z_hgu" (is "?z_hgv=_")
  have z_Hgw: "(DOMAIN(?z_hec)~=PROCESSES)" (is "?z_hgx~=_")
  by (rule subst [where P="(\<lambda>zenon_Vnqa. (DOMAIN(zenon_Vnqa)~=PROCESSES))", OF z_Heb z_Hgs])
  have z_Hhc: "(?z_hgv~=PROCESSES)"
  by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vmqa. (zenon_Vmqa~=PROCESSES))" "pc" "p" "''SR''", OF z_Hgw])
  show FALSE
  by (rule notE [OF z_Hhc z_Hgu])
 qed
 have zenon_L3_: "(a_pchash_primea=except(pc, p, ''S3'')) ==> (~isAFcn(a_pchash_primea)) ==> FALSE" (is "?z_hfs ==> ?z_hgk ==> FALSE")
 proof -
  assume z_Hfs:"?z_hfs" (is "_=?z_hft")
  assume z_Hgk:"?z_hgk" (is "~?z_hgl")
  have z_Hhg: "(~isAFcn(?z_hft))" (is "~?z_hhh")
  by (rule subst [where P="(\<lambda>zenon_Vjqa. (~isAFcn(zenon_Vjqa)))", OF z_Hfs z_Hgk])
  show FALSE
  by (rule zenon_notisafcn_except [of "pc" "p" "''S3''", OF z_Hhg])
 qed
 have zenon_L4_: "(a_pchash_primea=except(pc, p, ''S3'')) ==> (DOMAIN(a_pchash_primea)~=PROCESSES) ==> (DOMAIN(pc)=PROCESSES) ==> FALSE" (is "?z_hfs ==> ?z_hgs ==> ?z_hgu ==> FALSE")
 proof -
  assume z_Hfs:"?z_hfs" (is "_=?z_hft")
  assume z_Hgs:"?z_hgs" (is "?z_hgt~=_")
  assume z_Hgu:"?z_hgu" (is "?z_hgv=_")
  have z_Hhi: "(DOMAIN(?z_hft)~=PROCESSES)" (is "?z_hhj~=_")
  by (rule subst [where P="(\<lambda>zenon_Vnqa. (DOMAIN(zenon_Vnqa)~=PROCESSES))", OF z_Hfs z_Hgs])
  have z_Hhc: "(?z_hgv~=PROCESSES)"
  by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vmqa. (zenon_Vmqa~=PROCESSES))" "pc" "p" "''S3''", OF z_Hhi])
  show FALSE
  by (rule notE [OF z_Hhc z_Hgu])
 qed
 have zenon_L5_: "(a_Fhash_primea=F) ==> (~(a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))) ==> (F \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i]))))))) ==> FALSE" (is "?z_hf ==> ?z_hhk ==> ?z_hbb ==> FALSE")
 proof -
  assume z_Hf:"?z_hf"
  assume z_Hhk:"?z_hhk" (is "~?z_hhl")
  assume z_Hbb:"?z_hbb"
  have z_Hhm: "(~?z_hbb)"
  by (rule subst [where P="(\<lambda>zenon_Vcvj. (~(zenon_Vcvj \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))))", OF z_Hf z_Hhk])
  show FALSE
  by (rule notE [OF z_Hhm z_Hbb])
 qed
 have zenon_L6_: "(a_uhash_primea=u) ==> (~(a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (u \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hg ==> ?z_hhr ==> ?z_hbr ==> FALSE")
 proof -
  assume z_Hg:"?z_hg"
  assume z_Hhr:"?z_hhr" (is "~?z_hhs")
  assume z_Hbr:"?z_hbr"
  have z_Hht: "(~?z_hbr)"
  by (rule subst [where P="(\<lambda>zenon_Vevj. (~(zenon_Vevj \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hg z_Hhr])
  show FALSE
  by (rule notE [OF z_Hht z_Hbr])
 qed
 have zenon_L7_: "(a_whash_primea=w) ==> (~(a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (w \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hh ==> ?z_hhy ==> ?z_hby ==> FALSE")
 proof -
  assume z_Hh:"?z_hh"
  assume z_Hhy:"?z_hhy" (is "~?z_hhz")
  assume z_Hby:"?z_hby"
  have z_Hia: "(~?z_hby)"
  by (rule subst [where P="(\<lambda>zenon_Vevj. (~(zenon_Vevj \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hh z_Hhy])
  show FALSE
  by (rule notE [OF z_Hia z_Hby])
 qed
 have zenon_L8_: "(a_chash_primea=a_ca) ==> (~(a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (a_ca \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hi ==> ?z_hib ==> ?z_hcb ==> FALSE")
 proof -
  assume z_Hi:"?z_hi"
  assume z_Hib:"?z_hib" (is "~?z_hic")
  assume z_Hcb:"?z_hcb"
  have z_Hid: "(~?z_hcb)"
  by (rule subst [where P="(\<lambda>zenon_Vevj. (~(zenon_Vevj \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hi z_Hib])
  show FALSE
  by (rule notE [OF z_Hid z_Hcb])
 qed
 have zenon_L9_: "(a_dhash_primea=d) ==> (~(a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (d \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hj ==> ?z_hie ==> ?z_hce ==> FALSE")
 proof -
  assume z_Hj:"?z_hj"
  assume z_Hie:"?z_hie" (is "~?z_hif")
  assume z_Hce:"?z_hce"
  have z_Hig: "(~?z_hce)"
  by (rule subst [where P="(\<lambda>zenon_Vevj. (~(zenon_Vevj \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hj z_Hie])
  show FALSE
  by (rule notE [OF z_Hig z_Hce])
 qed
 have zenon_L10_: "(a_pchash_primea=except(pc, p, ''SR'')) ==> (a_rethash_primea=except(ret, p, TRUE)) ==> ((a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))])~=TRUE) ==> ((CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))) \\in DOMAIN(ret)) ==> ((ret[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))])~=(a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))])) ==> ((CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))) \\in DOMAIN(pc)) ==> FALSE" (is "?z_heb ==> ?z_hdy ==> ?z_hih ==> ?z_hiq ==> ?z_his ==> ?z_hiu ==> FALSE")
 proof -
  assume z_Heb:"?z_heb" (is "_=?z_hec")
  assume z_Hdy:"?z_hdy" (is "_=?z_hdz")
  assume z_Hih:"?z_hih" (is "?z_hii~=?z_hcr")
  assume z_Hiq:"?z_hiq"
  assume z_His:"?z_his" (is "?z_hit~=_")
  assume z_Hiu:"?z_hiu"
  have z_Hiv: "(((isAFcn(a_pchash_primea)<=>isAFcn(?z_hec))&(DOMAIN(a_pchash_primea)=DOMAIN(?z_hec)))&(\\A zenon_Vwqa:((a_pchash_primea[zenon_Vwqa])=(?z_hec[zenon_Vwqa]))))" (is "?z_hiw&?z_hiz")
  by (rule zenon_funequal_0 [of "a_pchash_primea" "?z_hec", OF z_Heb])
  have z_Hiz: "?z_hiz" (is "\\A x : ?z_hje(x)")
  by (rule zenon_and_1 [OF z_Hiv])
  have z_Hjf: "?z_hje((CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, ?z_hcr, FALSE} \\cup isa'dotdot(1, N)))))))" (is "?z_hjg=?z_hjh")
  by (rule zenon_all_0 [of "?z_hje" "(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, ?z_hcr, FALSE} \\cup isa'dotdot(1, N))))))", OF z_Hiz])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vsmc. (?z_hjg=zenon_Vsmc))" "pc" "p" "''SR''" "(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, ?z_hcr, FALSE} \\cup isa'dotdot(1, N))))))", OF z_Hjf])
   assume z_Hiu:"?z_hiu"
   assume z_Hjl:"(p=(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, ?z_hcr, FALSE} \\cup isa'dotdot(1, N)))))))" (is "_=?z_hij")
   assume z_Hjm:"(?z_hjg=''SR'')" (is "_=?z_hz")
   have z_Hjn: "(((isAFcn(a_rethash_primea)<=>isAFcn(?z_hdz))&(DOMAIN(a_rethash_primea)=DOMAIN(?z_hdz)))&(\\A zenon_Vyqa:((a_rethash_primea[zenon_Vyqa])=(?z_hdz[zenon_Vyqa]))))" (is "?z_hjo&?z_hjv")
   by (rule zenon_funequal_0 [of "a_rethash_primea" "?z_hdz", OF z_Hdy])
   have z_Hjv: "?z_hjv" (is "\\A x : ?z_hka(x)")
   by (rule zenon_and_1 [OF z_Hjn])
   have z_Hkb: "?z_hka(?z_hij)" (is "_=?z_hkc")
   by (rule zenon_all_0 [of "?z_hka" "?z_hij", OF z_Hjv])
   show FALSE
   proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vetc. (?z_hii=zenon_Vetc))" "ret" "p" "?z_hcr" "?z_hij", OF z_Hkb])
    assume z_Hiq:"?z_hiq"
    assume z_Hjl:"(p=?z_hij)"
    assume z_Hkg:"(?z_hii=?z_hcr)"
    show FALSE
    by (rule notE [OF z_Hih z_Hkg])
   next
    assume z_Hiq:"?z_hiq"
    assume z_Hkh:"(p~=?z_hij)"
    assume z_Hki:"(?z_hii=?z_hit)"
    show FALSE
    by (rule notE [OF z_Hkh z_Hjl])
   next
    assume z_Hkj:"(~?z_hiq)"
    show FALSE
    by (rule notE [OF z_Hkj z_Hiq])
   qed
  next
   assume z_Hiu:"?z_hiu"
   assume z_Hkh:"(p~=(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, ?z_hcr, FALSE} \\cup isa'dotdot(1, N)))))))" (is "_~=?z_hij")
   assume z_Hkk:"(?z_hjg=(pc[?z_hij]))" (is "_=?z_hkl")
   have z_Hjn: "(((isAFcn(a_rethash_primea)<=>isAFcn(?z_hdz))&(DOMAIN(a_rethash_primea)=DOMAIN(?z_hdz)))&(\\A zenon_Vyqa:((a_rethash_primea[zenon_Vyqa])=(?z_hdz[zenon_Vyqa]))))" (is "?z_hjo&?z_hjv")
   by (rule zenon_funequal_0 [of "a_rethash_primea" "?z_hdz", OF z_Hdy])
   have z_Hjv: "?z_hjv" (is "\\A x : ?z_hka(x)")
   by (rule zenon_and_1 [OF z_Hjn])
   have z_Hkb: "?z_hka(?z_hij)" (is "_=?z_hkc")
   by (rule zenon_all_0 [of "?z_hka" "?z_hij", OF z_Hjv])
   show FALSE
   proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vetc. (?z_hii=zenon_Vetc))" "ret" "p" "?z_hcr" "?z_hij", OF z_Hkb])
    assume z_Hiq:"?z_hiq"
    assume z_Hjl:"(p=?z_hij)"
    assume z_Hkg:"(?z_hii=?z_hcr)"
    show FALSE
    by (rule notE [OF z_Hkh z_Hjl])
   next
    assume z_Hiq:"?z_hiq"
    assume z_Hkh:"(p~=?z_hij)"
    assume z_Hki:"(?z_hii=?z_hit)"
    show FALSE
    by (rule zenon_eqsym [OF z_Hki z_His])
   next
    assume z_Hkj:"(~?z_hiq)"
    show FALSE
    by (rule notE [OF z_Hkj z_Hiq])
   qed
  next
   assume z_Hkm:"(~?z_hiu)"
   show FALSE
   by (rule notE [OF z_Hkm z_Hiu])
  qed
 qed
 have zenon_L11_: "(~(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))) ==> (ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))) ==> (a_rethash_primea=ret) ==> FALSE" (is "?z_hkn ==> ?z_hcl ==> ?z_hdo ==> FALSE")
 proof -
  assume z_Hkn:"?z_hkn" (is "~?z_hko")
  assume z_Hcl:"?z_hcl"
  assume z_Hdo:"?z_hdo"
  show FALSE
  proof (rule notE [OF z_Hkn])
   have z_Hkp: "(ret=a_rethash_primea)"
   by (rule sym [OF z_Hdo])
   have z_Hko: "?z_hko"
   by (rule subst [where P="(\<lambda>zenon_Vnvj. (zenon_Vnvj \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))", OF z_Hkp], fact z_Hcl)
   thus "?z_hko" .
  qed
 qed
 assume z_Hk:"(~((a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_Mhash_primea \\in SUBSET(Configs))&(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))))))))))" (is "~(?z_hku&?z_hkv)")
 have z_Hl: "?z_hl" (is "?z_hm&?z_hba")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hm: "?z_hm"
 by (rule zenon_and_0 [OF z_Hl])
 have z_Hba: "?z_hba" (is "?z_hbb&?z_hbq")
 by (rule zenon_and_1 [OF z_Hl])
 have z_Hbb: "?z_hbb"
 by (rule zenon_and_0 [OF z_Hba])
 have z_Hbq: "?z_hbq" (is "?z_hbr&?z_hbu")
 by (rule zenon_and_1 [OF z_Hba])
 have z_Hbr: "?z_hbr"
 by (rule zenon_and_0 [OF z_Hbq])
 have z_Hbu: "?z_hbu" (is "?z_hbv&?z_hbx")
 by (rule zenon_and_1 [OF z_Hbq])
 have z_Hbv: "?z_hbv"
 by (rule zenon_and_0 [OF z_Hbu])
 have z_Hbx: "?z_hbx" (is "?z_hby&?z_hca")
 by (rule zenon_and_1 [OF z_Hbu])
 have z_Hby: "?z_hby"
 by (rule zenon_and_0 [OF z_Hbx])
 have z_Hca: "?z_hca" (is "?z_hcb&?z_hcd")
 by (rule zenon_and_1 [OF z_Hbx])
 have z_Hcb: "?z_hcb"
 by (rule zenon_and_0 [OF z_Hca])
 have z_Hcd: "?z_hcd" (is "?z_hce&?z_hcg")
 by (rule zenon_and_1 [OF z_Hca])
 have z_Hce: "?z_hce"
 by (rule zenon_and_0 [OF z_Hcd])
 have z_Hcg: "?z_hcg" (is "?z_hch&?z_hcl")
 by (rule zenon_and_1 [OF z_Hcd])
 have z_Hcl: "?z_hcl"
 by (rule zenon_and_1 [OF z_Hcg])
 have z_Hle: "(F \\in FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)))" (is "?z_hle")
 by (rule zenon_in_subsetof_0 [of "F" "FuncSet(isa'dotdot(1, N), isa'dotdot(1, N))" "(\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))", OF z_Hbb])
 show FALSE
 proof (rule zenon_notand [OF z_Hk])
  assume z_Hlf:"(~?z_hku)"
  have z_Hgu: "(DOMAIN(pc)=PROCESSES)" (is "?z_hgv=_")
  by (rule zenon_in_funcset_1 [of "pc" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hm])
  show FALSE
  proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "((a_uhash_primea[p])=(a_vhash_primea[p]))" "((a_rethash_primea=except(ret, p, TRUE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" "((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((((F[(u[p])])=(u[p]))&((((told[''sigma''])[(((told[''arg''])[p])[1])])~=((told[''sigma''])[(((told[''arg''])[p])[2])]))&((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))))|((t[''ret''])=(told[''ret''])))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))", OF z_Hc])
   assume z_Hdu:"((a_uhash_primea[p])=(a_vhash_primea[p]))" (is "?z_hdv=?z_hdw")
   assume z_Hdx:"((a_rethash_primea=except(ret, p, TRUE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" (is "?z_hdy&?z_hea")
   have z_Hea: "?z_hea" (is "?z_heb&?z_hed")
   by (rule zenon_and_1 [OF z_Hdx])
   have z_Heb: "?z_heb" (is "_=?z_hec")
   by (rule zenon_and_0 [OF z_Hea])
   have z_Hgu: "(?z_hgv=PROCESSES)"
   by (rule zenon_in_funcset_1 [of "pc" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hm])
   have z_Hli: "(\\A zenon_Vka:((zenon_Vka \\in PROCESSES)=>((pc[zenon_Vka]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''})))" (is "\\A x : ?z_hlo(x)")
   by (rule zenon_in_funcset_2 [of "pc" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hm])
   show FALSE
   proof (rule zenon_notin_funcset [of "a_pchash_primea" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hlf])
    assume z_Hgk:"(~isAFcn(a_pchash_primea))" (is "~?z_hgl")
    show FALSE
    by (rule zenon_L1_ [OF z_Heb z_Hgk])
   next
    assume z_Hgs:"(DOMAIN(a_pchash_primea)~=PROCESSES)" (is "?z_hgt~=_")
    show FALSE
    by (rule zenon_L2_ [OF z_Heb z_Hgs z_Hgu])
   next
    assume z_Hlp:"(~(\\A zenon_Vufa:((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))" (is "~(\\A x : ?z_hlw(x))")
    have z_Hlx: "(\\E zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))" (is "\\E x : ?z_hlz(x)")
    by (rule zenon_notallex_0 [of "?z_hlw", OF z_Hlp])
    have z_Hma: "?z_hlz((CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''})))))" (is "~(?z_hmc=>?z_hmd)")
    by (rule zenon_ex_choose_0 [of "?z_hlz", OF z_Hlx])
    have z_Hmc: "?z_hmc"
    by (rule zenon_notimply_0 [OF z_Hma])
    have z_Hme: "(~?z_hmd)"
    by (rule zenon_notimply_1 [OF z_Hma])
    have z_Hmf: "(~((a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hmg")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''0''" "{''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hme])
    have z_Hmj: "(~((a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hmk")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''F1''" "{''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hmf])
    have z_Hmm: "(~((a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hmn")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''FR''" "{''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hmj])
    have z_Hmp: "(~((a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hmq")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''U1''" "{''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hmm])
    have z_Hms: "(~((a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hmt")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''UR''" "{''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hmp])
    have z_Hmv: "(~((a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''S2'', ''S3'', ''SR''}))" (is "~?z_hmw")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''S1''" "{''S2'', ''S3'', ''SR''}", OF z_Hms])
    have z_Hmy: "(~((a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''S3'', ''SR''}))" (is "~?z_hmz")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''S2''" "{''S3'', ''SR''}", OF z_Hmv])
    have z_Hnb: "(~((a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''SR''}))" (is "~?z_hnc")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''S3''" "{''SR''}", OF z_Hmy])
    have z_Hne: "((a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])~=''SR'')" (is "?z_hmh~=?z_hz")
    by (rule zenon_notin_addElt_0 [of "?z_hmh" "?z_hz" "{}", OF z_Hnb])
    have z_Hng: "((CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz})))) \\in ?z_hgv)" (is "?z_hng")
    by (rule ssubst [where P="(\<lambda>zenon_Vwwf. ((CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz})))) \\in zenon_Vwwf))", OF z_Hgu z_Hmc])
    have z_Hnk: "?z_hlo((CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz})))))" (is "_=>?z_hnl")
    by (rule zenon_all_0 [of "?z_hlo" "(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz}))))", OF z_Hli])
    show FALSE
    proof (rule zenon_imply [OF z_Hnk])
     assume z_Hnm:"(~?z_hmc)"
     show FALSE
     by (rule notE [OF z_Hnm z_Hmc])
    next
     assume z_Hnl:"?z_hnl"
     show FALSE
     proof (rule notE [OF z_Hme])
      have z_Hnn: "((pc[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz}))))])=?z_hmh)" (is "?z_hno=_")
      proof (rule zenon_nnpp [of "(?z_hno=?z_hmh)"])
       assume z_Hnp:"(?z_hno~=?z_hmh)"
       have z_Hiv: "(((isAFcn(a_pchash_primea)<=>isAFcn(?z_hec))&(DOMAIN(a_pchash_primea)=DOMAIN(?z_hec)))&(\\A zenon_Vwqa:((a_pchash_primea[zenon_Vwqa])=(?z_hec[zenon_Vwqa]))))" (is "?z_hiw&?z_hiz")
       by (rule zenon_funequal_0 [of "a_pchash_primea" "?z_hec", OF z_Heb])
       have z_Hiz: "?z_hiz" (is "\\A x : ?z_hje(x)")
       by (rule zenon_and_1 [OF z_Hiv])
       have z_Hnq: "?z_hje((CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz})))))" (is "_=?z_hnr")
       by (rule zenon_all_0 [of "?z_hje" "(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz}))))", OF z_Hiz])
       show FALSE
       proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vxmg. (?z_hmh=zenon_Vxmg))" "pc" "p" "?z_hz" "(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz}))))", OF z_Hnq])
        assume z_Hng:"?z_hng"
        assume z_Hnv:"(p=(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz})))))" (is "_=?z_hmb")
        assume z_Hnw:"(?z_hmh=?z_hz)"
        show FALSE
        by (rule notE [OF z_Hne z_Hnw])
       next
        assume z_Hng:"?z_hng"
        assume z_Hnx:"(p~=(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz})))))" (is "_~=?z_hmb")
        assume z_Hny:"(?z_hmh=?z_hno)"
        show FALSE
        by (rule zenon_eqsym [OF z_Hny z_Hnp])
       next
        assume z_Hnz:"(~?z_hng)"
        show FALSE
        by (rule notE [OF z_Hnz z_Hng])
       qed
      qed
      have z_Hmd: "?z_hmd"
      by (rule subst [where P="(\<lambda>zenon_Vovj. (zenon_Vovj \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz}))", OF z_Hnn], fact z_Hnl)
      thus "?z_hmd" .
     qed
    qed
   qed
  next
   assume z_Hod:"((a_uhash_primea[p])~=(a_vhash_primea[p]))" (is "?z_hdv~=?z_hdw")
   assume z_Hfq:"((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((((F[(u[p])])=(u[p]))&((((told[''sigma''])[(((told[''arg''])[p])[1])])~=((told[''sigma''])[(((told[''arg''])[p])[2])]))&((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))))|((t[''ret''])=(told[''ret''])))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" (is "?z_hdo&?z_hfr")
   have z_Hfr: "?z_hfr" (is "?z_hfs&?z_hfu")
   by (rule zenon_and_1 [OF z_Hfq])
   have z_Hfs: "?z_hfs" (is "_=?z_hft")
   by (rule zenon_and_0 [OF z_Hfr])
   have z_Hgu: "(?z_hgv=PROCESSES)"
   by (rule zenon_in_funcset_1 [of "pc" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hm])
   have z_Hli: "(\\A zenon_Vka:((zenon_Vka \\in PROCESSES)=>((pc[zenon_Vka]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''})))" (is "\\A x : ?z_hlo(x)")
   by (rule zenon_in_funcset_2 [of "pc" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hm])
   show FALSE
   proof (rule zenon_notin_funcset [of "a_pchash_primea" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hlf])
    assume z_Hgk:"(~isAFcn(a_pchash_primea))" (is "~?z_hgl")
    show FALSE
    by (rule zenon_L3_ [OF z_Hfs z_Hgk])
   next
    assume z_Hgs:"(DOMAIN(a_pchash_primea)~=PROCESSES)" (is "?z_hgt~=_")
    show FALSE
    by (rule zenon_L4_ [OF z_Hfs z_Hgs z_Hgu])
   next
    assume z_Hlp:"(~(\\A zenon_Vufa:((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))" (is "~(\\A x : ?z_hlw(x))")
    have z_Hlx: "(\\E zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))" (is "\\E x : ?z_hlz(x)")
    by (rule zenon_notallex_0 [of "?z_hlw", OF z_Hlp])
    have z_Hma: "?z_hlz((CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''})))))" (is "~(?z_hmc=>?z_hmd)")
    by (rule zenon_ex_choose_0 [of "?z_hlz", OF z_Hlx])
    have z_Hmc: "?z_hmc"
    by (rule zenon_notimply_0 [OF z_Hma])
    have z_Hme: "(~?z_hmd)"
    by (rule zenon_notimply_1 [OF z_Hma])
    have z_Hmf: "(~((a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hmg")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''0''" "{''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hme])
    have z_Hmj: "(~((a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hmk")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''F1''" "{''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hmf])
    have z_Hmm: "(~((a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hmn")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''FR''" "{''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hmj])
    have z_Hmp: "(~((a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hmq")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''U1''" "{''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hmm])
    have z_Hms: "(~((a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hmt")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''UR''" "{''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hmp])
    have z_Hmv: "(~((a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''S2'', ''S3'', ''SR''}))" (is "~?z_hmw")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''S1''" "{''S2'', ''S3'', ''SR''}", OF z_Hms])
    have z_Hmy: "(~((a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''S3'', ''SR''}))" (is "~?z_hmz")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''S2''" "{''S3'', ''SR''}", OF z_Hmv])
    have z_Hoe: "((a_pchash_primea[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])~=''S3'')" (is "?z_hmh~=?z_hy")
    by (rule zenon_notin_addElt_0 [of "?z_hmh" "?z_hy" "{''SR''}", OF z_Hmy])
    have z_Hng: "((CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hy, ''SR''})))) \\in ?z_hgv)" (is "?z_hng")
    by (rule ssubst [where P="(\<lambda>zenon_Vwwf. ((CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hy, ''SR''})))) \\in zenon_Vwwf))", OF z_Hgu z_Hmc])
    have z_Hnk: "?z_hlo((CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hy, ''SR''})))))" (is "_=>?z_hnl")
    by (rule zenon_all_0 [of "?z_hlo" "(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hy, ''SR''}))))", OF z_Hli])
    show FALSE
    proof (rule zenon_imply [OF z_Hnk])
     assume z_Hnm:"(~?z_hmc)"
     show FALSE
     by (rule notE [OF z_Hnm z_Hmc])
    next
     assume z_Hnl:"?z_hnl"
     show FALSE
     proof (rule notE [OF z_Hme])
      have z_Hnn: "((pc[(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hy, ''SR''}))))])=?z_hmh)" (is "?z_hno=_")
      proof (rule zenon_nnpp [of "(?z_hno=?z_hmh)"])
       assume z_Hnp:"(?z_hno~=?z_hmh)"
       have z_Hof: "(((isAFcn(a_pchash_primea)<=>isAFcn(?z_hft))&(DOMAIN(a_pchash_primea)=DOMAIN(?z_hft)))&(\\A zenon_Vpcd:((a_pchash_primea[zenon_Vpcd])=(?z_hft[zenon_Vpcd]))))" (is "?z_hog&?z_hoj")
       by (rule zenon_funequal_0 [of "a_pchash_primea" "?z_hft", OF z_Hfs])
       have z_Hoj: "?z_hoj" (is "\\A x : ?z_hoo(x)")
       by (rule zenon_and_1 [OF z_Hof])
       have z_Hop: "?z_hoo((CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hy, ''SR''})))))" (is "_=?z_hoq")
       by (rule zenon_all_0 [of "?z_hoo" "(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hy, ''SR''}))))", OF z_Hoj])
       show FALSE
       proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vxmg. (?z_hmh=zenon_Vxmg))" "pc" "p" "?z_hy" "(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hy, ''SR''}))))", OF z_Hop])
        assume z_Hng:"?z_hng"
        assume z_Hnv:"(p=(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hy, ''SR''})))))" (is "_=?z_hmb")
        assume z_Hor:"(?z_hmh=?z_hy)"
        show FALSE
        by (rule notE [OF z_Hoe z_Hor])
       next
        assume z_Hng:"?z_hng"
        assume z_Hnx:"(p~=(CHOOSE zenon_Vufa:(~((zenon_Vufa \\in PROCESSES)=>((a_pchash_primea[zenon_Vufa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hy, ''SR''})))))" (is "_~=?z_hmb")
        assume z_Hny:"(?z_hmh=?z_hno)"
        show FALSE
        by (rule zenon_eqsym [OF z_Hny z_Hnp])
       next
        assume z_Hnz:"(~?z_hng)"
        show FALSE
        by (rule notE [OF z_Hnz z_Hng])
       qed
      qed
      have z_Hmd: "?z_hmd"
      by (rule subst [where P="(\<lambda>zenon_Vovj. (zenon_Vovj \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ?z_hy, ''SR''}))", OF z_Hnn], fact z_Hnl)
      thus "?z_hmd" .
     qed
    qed
   qed
  qed
 next
  assume z_Hos:"(~?z_hkv)" (is "~(?z_hhl&?z_hkw)")
  show FALSE
  proof (rule zenon_notand [OF z_Hos])
   assume z_Hhk:"(~?z_hhl)"
   show FALSE
   by (rule zenon_L5_ [OF z_Hf z_Hhk z_Hbb])
  next
   assume z_Hot:"(~?z_hkw)" (is "~(?z_hhs&?z_hkx)")
   show FALSE
   proof (rule zenon_notand [OF z_Hot])
    assume z_Hhr:"(~?z_hhs)"
    show FALSE
    by (rule zenon_L6_ [OF z_Hg z_Hhr z_Hbr])
   next
    assume z_Hou:"(~?z_hkx)" (is "~(?z_hky&?z_hkz)")
    show FALSE
    proof (rule zenon_notand [OF z_Hou])
     assume z_Hov:"(~?z_hky)"
     have z_How: "(~(?z_hdq \\in FuncSet(PROCESSES, isa'dotdot(1, N))))" (is "~?z_hox")
     by (rule subst [where P="(\<lambda>zenon_Vevj. (~(zenon_Vevj \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_He z_Hov])
     have z_Hoy: "(DOMAIN(v)=PROCESSES)" (is "?z_hoz=_")
     by (rule zenon_in_funcset_1 [of "v" "PROCESSES" "isa'dotdot(1, N)", OF z_Hbv])
     show FALSE
     proof (rule zenon_except_notin_funcset [of "v" "p" "(F[(v[p])])" "PROCESSES" "isa'dotdot(1, N)", OF z_How])
      assume z_Hpa:"(~?z_hbv)"
      show FALSE
      by (rule notE [OF z_Hpa z_Hbv])
     next
      assume z_Hpb:"(~((F[(v[p])]) \\in isa'dotdot(1, N)))" (is "~?z_hpc")
      show FALSE
      proof (rule zenon_notin_funcset [of "?z_hdq" "PROCESSES" "isa'dotdot(1, N)", OF z_How])
       assume z_Hpd:"(~isAFcn(?z_hdq))" (is "~?z_hpe")
       show FALSE
       by (rule zenon_notisafcn_except [of "v" "p" "(F[(v[p])])", OF z_Hpd])
      next
       assume z_Hpf:"(DOMAIN(?z_hdq)~=PROCESSES)" (is "?z_hpg~=_")
       have z_Hph: "(?z_hoz~=PROCESSES)"
       by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vmqa. (zenon_Vmqa~=PROCESSES))" "v" "p" "(F[(v[p])])", OF z_Hpf])
       show FALSE
       by (rule notE [OF z_Hph z_Hoy])
      next
       assume z_Hpi:"(~(\\A zenon_Vnr:((zenon_Vnr \\in PROCESSES)=>((?z_hdq[zenon_Vnr]) \\in isa'dotdot(1, N)))))" (is "~(\\A x : ?z_hpp(x))")
       have z_Hpq: "(\\E zenon_Vnr:(~((zenon_Vnr \\in PROCESSES)=>((?z_hdq[zenon_Vnr]) \\in isa'dotdot(1, N)))))" (is "\\E x : ?z_hps(x)")
       by (rule zenon_notallex_0 [of "?z_hpp", OF z_Hpi])
       have z_Hpt: "?z_hps((CHOOSE zenon_Vnr:(~((zenon_Vnr \\in PROCESSES)=>((?z_hdq[zenon_Vnr]) \\in isa'dotdot(1, N))))))" (is "~(?z_hpv=>?z_hpw)")
       by (rule zenon_ex_choose_0 [of "?z_hps", OF z_Hpq])
       have z_Hpv: "?z_hpv"
       by (rule zenon_notimply_0 [OF z_Hpt])
       have z_Hpx: "(~?z_hpw)"
       by (rule zenon_notimply_1 [OF z_Hpt])
       have z_Hpy: "((CHOOSE zenon_Vnr:(~((zenon_Vnr \\in PROCESSES)=>((?z_hdq[zenon_Vnr]) \\in isa'dotdot(1, N))))) \\in ?z_hoz)" (is "?z_hpy")
       by (rule ssubst [where P="(\<lambda>zenon_Vawe. ((CHOOSE zenon_Vnr:(~((zenon_Vnr \\in PROCESSES)=>((?z_hdq[zenon_Vnr]) \\in isa'dotdot(1, N))))) \\in zenon_Vawe))", OF z_Hoy z_Hpv])
       show FALSE
       proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vmt. (~(zenon_Vmt \\in isa'dotdot(1, N))))" "v" "p" "(F[(v[p])])" "(CHOOSE zenon_Vnr:(~((zenon_Vnr \\in PROCESSES)=>((?z_hdq[zenon_Vnr]) \\in isa'dotdot(1, N)))))", OF z_Hpx])
        assume z_Hpy:"?z_hpy"
        assume z_Hqg:"(p=(CHOOSE zenon_Vnr:(~((zenon_Vnr \\in PROCESSES)=>((?z_hdq[zenon_Vnr]) \\in isa'dotdot(1, N))))))" (is "_=?z_hpu")
        assume z_Hpb:"(~?z_hpc)"
        have z_Hqh: "(\\A zenon_Vca:((zenon_Vca \\in PROCESSES)=>((v[zenon_Vca]) \\in isa'dotdot(1, N))))" (is "\\A x : ?z_hqn(x)")
        by (rule zenon_in_funcset_2 [of "v" "PROCESSES" "isa'dotdot(1, N)", OF z_Hbv])
        have z_Hqo: "?z_hqn(?z_hpu)" (is "_=>?z_hqp")
        by (rule zenon_all_0 [of "?z_hqn" "?z_hpu", OF z_Hqh])
        show FALSE
        proof (rule zenon_imply [OF z_Hqo])
         assume z_Hqq:"(~?z_hpv)"
         show FALSE
         by (rule notE [OF z_Hqq z_Hpv])
        next
         assume z_Hqp:"?z_hqp"
         have z_Hqr: "(\\A zenon_Voa:((zenon_Voa \\in isa'dotdot(1, N))=>((F[zenon_Voa]) \\in isa'dotdot(1, N))))" (is "\\A x : ?z_hqx(x)")
         by (rule zenon_in_funcset_2 [of "F" "isa'dotdot(1, N)" "isa'dotdot(1, N)", OF z_Hle])
         have z_Hqy: "?z_hqx((v[p]))" (is "?z_hqz=>_")
         by (rule zenon_all_0 [of "?z_hqx" "(v[p])", OF z_Hqr])
         show FALSE
         proof (rule zenon_imply [OF z_Hqy])
          assume z_Hra:"(~?z_hqz)"
          show FALSE
          proof (rule notE [OF z_Hra])
           have z_Hrb: "((v[?z_hpu])=(v[p]))" (is "?z_hrc=?z_hdt")
           proof (rule zenon_nnpp [of "(?z_hrc=?z_hdt)"])
            assume z_Hrd:"(?z_hrc~=?z_hdt)"
            show FALSE
            proof (rule zenon_noteq [of "?z_hdt"])
             have z_Hre: "(?z_hpu=p)"
             by (rule sym [OF z_Hqg])
             have z_Hrf: "(?z_hdt~=?z_hdt)"
             by (rule subst [where P="(\<lambda>zenon_Vqvj. ((v[zenon_Vqvj])~=?z_hdt))", OF z_Hre], fact z_Hrd)
             thus "(?z_hdt~=?z_hdt)" .
            qed
           qed
           have z_Hqz: "?z_hqz"
           by (rule subst [where P="(\<lambda>zenon_Vrvj. (zenon_Vrvj \\in isa'dotdot(1, N)))", OF z_Hrb], fact z_Hqp)
           thus "?z_hqz" .
          qed
         next
          assume z_Hpc:"?z_hpc"
          show FALSE
          by (rule notE [OF z_Hpb z_Hpc])
         qed
        qed
       next
        assume z_Hpy:"?z_hpy"
        assume z_Hrn:"(p~=(CHOOSE zenon_Vnr:(~((zenon_Vnr \\in PROCESSES)=>((?z_hdq[zenon_Vnr]) \\in isa'dotdot(1, N))))))" (is "_~=?z_hpu")
        assume z_Hro:"(~((v[?z_hpu]) \\in isa'dotdot(1, N)))" (is "~?z_hqp")
        have z_Hqh: "(\\A zenon_Vca:((zenon_Vca \\in PROCESSES)=>((v[zenon_Vca]) \\in isa'dotdot(1, N))))" (is "\\A x : ?z_hqn(x)")
        by (rule zenon_in_funcset_2 [of "v" "PROCESSES" "isa'dotdot(1, N)", OF z_Hbv])
        have z_Hqo: "?z_hqn(?z_hpu)"
        by (rule zenon_all_0 [of "?z_hqn" "?z_hpu", OF z_Hqh])
        show FALSE
        proof (rule zenon_imply [OF z_Hqo])
         assume z_Hqq:"(~?z_hpv)"
         show FALSE
         by (rule notE [OF z_Hqq z_Hpv])
        next
         assume z_Hqp:"?z_hqp"
         show FALSE
         by (rule notE [OF z_Hro z_Hqp])
        qed
       next
        assume z_Hrp:"(~?z_hpy)"
        show FALSE
        by (rule notE [OF z_Hrp z_Hpy])
       qed
      qed
     qed
    next
     assume z_Hrq:"(~?z_hkz)" (is "~(?z_hhz&?z_hla)")
     show FALSE
     proof (rule zenon_notand [OF z_Hrq])
      assume z_Hhy:"(~?z_hhz)"
      show FALSE
      by (rule zenon_L7_ [OF z_Hh z_Hhy z_Hby])
     next
      assume z_Hrr:"(~?z_hla)" (is "~(?z_hic&?z_hlb)")
      show FALSE
      proof (rule zenon_notand [OF z_Hrr])
       assume z_Hib:"(~?z_hic)"
       show FALSE
       by (rule zenon_L8_ [OF z_Hi z_Hib z_Hcb])
      next
       assume z_Hrs:"(~?z_hlb)" (is "~(?z_hif&?z_hlc)")
       show FALSE
       proof (rule zenon_notand [OF z_Hrs])
        assume z_Hie:"(~?z_hif)"
        show FALSE
        by (rule zenon_L9_ [OF z_Hj z_Hie z_Hce])
       next
        assume z_Hrt:"(~?z_hlc)" (is "~(?z_hld&?z_hko)")
        show FALSE
        proof (rule zenon_notand [OF z_Hrt])
         assume z_Hru:"(~?z_hld)"
         have z_Hrv: "(~(a_Mhash_primea \\subseteq Configs))" (is "~?z_hrw")
         by (rule zenon_notin_SUBSET_0 [of "a_Mhash_primea" "Configs", OF z_Hru])
         have z_Hrx_z_Hrv: "(~bAll(a_Mhash_primea, (\<lambda>x. (x \\in Configs)))) == (~?z_hrw)" (is "?z_hrx == ?z_hrv")
         by (unfold subset_def)
         have z_Hrx: "?z_hrx" (is "~?z_hry")
         by (unfold z_Hrx_z_Hrv, fact z_Hrv)
         have z_Hsc_z_Hrx: "(~(\\A x:((x \\in a_Mhash_primea)=>(x \\in Configs)))) == ?z_hrx" (is "?z_hsc == _")
         by (unfold bAll_def)
         have z_Hsc: "?z_hsc" (is "~(\\A x : ?z_hsg(x))")
         by (unfold z_Hsc_z_Hrx, fact z_Hrx)
         have z_Hsh: "(\\E x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))" (is "\\E x : ?z_hsj(x)")
         by (rule zenon_notallex_0 [of "?z_hsg", OF z_Hsc])
         have z_Hsk: "?z_hsj((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))))" (is "~(?z_hsm=>?z_hsn)")
         by (rule zenon_ex_choose_0 [of "?z_hsj", OF z_Hsh])
         have z_Hsm: "?z_hsm"
         by (rule zenon_notimply_0 [OF z_Hsk])
         have z_Hso: "(~?z_hsn)"
         by (rule zenon_notimply_1 [OF z_Hsk])
         show FALSE
         proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "((a_uhash_primea[p])=(a_vhash_primea[p]))" "((a_rethash_primea=except(ret, p, TRUE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" "((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((((F[(u[p])])=(u[p]))&((((told[''sigma''])[(((told[''arg''])[p])[1])])~=((told[''sigma''])[(((told[''arg''])[p])[2])]))&((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))))|((t[''ret''])=(told[''ret''])))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))", OF z_Hc])
          assume z_Hdu:"((a_uhash_primea[p])=(a_vhash_primea[p]))" (is "?z_hdv=?z_hdw")
          assume z_Hdx:"((a_rethash_primea=except(ret, p, TRUE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" (is "?z_hdy&?z_hea")
          have z_Hea: "?z_hea" (is "?z_heb&?z_hed")
          by (rule zenon_and_1 [OF z_Hdx])
          have z_Hed: "?z_hed" (is "_=?z_hee")
          by (rule zenon_and_1 [OF z_Hea])
          have z_Hsp: "(\\A zenon_Vuqa:((zenon_Vuqa \\in a_Mhash_primea)<=>(zenon_Vuqa \\in ?z_hee)))" (is "\\A x : ?z_hsu(x)")
          by (rule zenon_setequal_0 [of "a_Mhash_primea" "?z_hee", OF z_Hed])
          have z_Hsv: "?z_hsu((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))))" (is "_<=>?z_hsw")
          by (rule zenon_all_0 [of "?z_hsu" "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))", OF z_Hsp])
          show FALSE
          proof (rule zenon_equiv [OF z_Hsv])
           assume z_Hsx:"(~?z_hsm)"
           assume z_Hsy:"(~?z_hsw)"
           show FALSE
           by (rule notE [OF z_Hsx z_Hsm])
          next
           assume z_Hsm:"?z_hsm"
           assume z_Hsw:"?z_hsw"
           have z_Hsn: "?z_hsn"
           by (rule zenon_in_subsetof_0 [of "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))" "Configs" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))", OF z_Hsw])
           show FALSE
           by (rule notE [OF z_Hso z_Hsn])
          qed
         next
          assume z_Hod:"((a_uhash_primea[p])~=(a_vhash_primea[p]))" (is "?z_hdv~=?z_hdw")
          assume z_Hfq:"((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((((F[(u[p])])=(u[p]))&((((told[''sigma''])[(((told[''arg''])[p])[1])])~=((told[''sigma''])[(((told[''arg''])[p])[2])]))&((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))))|((t[''ret''])=(told[''ret''])))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" (is "?z_hdo&?z_hfr")
          have z_Hfr: "?z_hfr" (is "?z_hfs&?z_hfu")
          by (rule zenon_and_1 [OF z_Hfq])
          have z_Hfu: "?z_hfu" (is "_=?z_hfv")
          by (rule zenon_and_1 [OF z_Hfr])
          have z_Hsz: "(\\A zenon_Vncd:((zenon_Vncd \\in a_Mhash_primea)<=>(zenon_Vncd \\in ?z_hfv)))" (is "\\A x : ?z_hte(x)")
          by (rule zenon_setequal_0 [of "a_Mhash_primea" "?z_hfv", OF z_Hfu])
          have z_Htf: "?z_hte((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))))" (is "_<=>?z_htg")
          by (rule zenon_all_0 [of "?z_hte" "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))", OF z_Hsz])
          show FALSE
          proof (rule zenon_equiv [OF z_Htf])
           assume z_Hsx:"(~?z_hsm)"
           assume z_Hth:"(~?z_htg)"
           show FALSE
           by (rule notE [OF z_Hsx z_Hsm])
          next
           assume z_Hsm:"?z_hsm"
           assume z_Htg:"?z_htg"
           have z_Hsn: "?z_hsn"
           by (rule zenon_in_subsetof_0 [of "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))" "Configs" "(\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((((F[(u[p])])=(u[p]))&((((told[''sigma''])[(((told[''arg''])[p])[1])])~=((told[''sigma''])[(((told[''arg''])[p])[2])]))&((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))))|((t[''ret''])=(told[''ret''])))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))", OF z_Htg])
           show FALSE
           by (rule notE [OF z_Hso z_Hsn])
          qed
         qed
        next
         assume z_Hkn:"(~?z_hko)"
         have z_Hgu: "(DOMAIN(pc)=PROCESSES)" (is "?z_hgv=_")
         by (rule zenon_in_funcset_1 [of "pc" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hm])
         have z_Hti: "(DOMAIN(ret)=PROCESSES)" (is "?z_hir=_")
         by (rule zenon_in_funcset_1 [of "ret" "PROCESSES" "({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))", OF z_Hcl])
         show FALSE
         proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "((a_uhash_primea[p])=(a_vhash_primea[p]))" "((a_rethash_primea=except(ret, p, TRUE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" "((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((((F[(u[p])])=(u[p]))&((((told[''sigma''])[(((told[''arg''])[p])[1])])~=((told[''sigma''])[(((told[''arg''])[p])[2])]))&((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))))|((t[''ret''])=(told[''ret''])))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))", OF z_Hc])
          assume z_Hdu:"((a_uhash_primea[p])=(a_vhash_primea[p]))" (is "?z_hdv=?z_hdw")
          assume z_Hdx:"((a_rethash_primea=except(ret, p, TRUE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" (is "?z_hdy&?z_hea")
          have z_Hdy: "?z_hdy" (is "_=?z_hdz")
          by (rule zenon_and_0 [OF z_Hdx])
          have z_Hea: "?z_hea" (is "?z_heb&?z_hed")
          by (rule zenon_and_1 [OF z_Hdx])
          have z_Heb: "?z_heb" (is "_=?z_hec")
          by (rule zenon_and_0 [OF z_Hea])
          have z_Hti: "(?z_hir=PROCESSES)"
          by (rule zenon_in_funcset_1 [of "ret" "PROCESSES" "({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))", OF z_Hcl])
          have z_Htj: "(\\A zenon_Vo:((zenon_Vo \\in PROCESSES)=>((ret[zenon_Vo]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))" (is "\\A x : ?z_htp(x)")
          by (rule zenon_in_funcset_2 [of "ret" "PROCESSES" "({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))", OF z_Hcl])
          show FALSE
          proof (rule zenon_notin_funcset [of "a_rethash_primea" "PROCESSES" "({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))", OF z_Hkn])
           assume z_Htq:"(~isAFcn(a_rethash_primea))" (is "~?z_hjq")
           have z_Htr: "(~isAFcn(?z_hdz))" (is "~?z_hjr")
           by (rule subst [where P="(\<lambda>zenon_Vjqa. (~isAFcn(zenon_Vjqa)))", OF z_Hdy z_Htq])
           show FALSE
           by (rule zenon_notisafcn_except [of "ret" "p" "TRUE", OF z_Htr])
          next
           assume z_Hts:"(DOMAIN(a_rethash_primea)~=PROCESSES)" (is "?z_hjt~=_")
           have z_Htt: "(DOMAIN(?z_hdz)~=PROCESSES)" (is "?z_hju~=_")
           by (rule subst [where P="(\<lambda>zenon_Vnqa. (DOMAIN(zenon_Vnqa)~=PROCESSES))", OF z_Hdy z_Hts])
           have z_Htu: "(?z_hir~=PROCESSES)"
           by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vmqa. (zenon_Vmqa~=PROCESSES))" "ret" "p" "TRUE", OF z_Htt])
           show FALSE
           by (rule notE [OF z_Htu z_Hti])
          next
           assume z_Htv:"(~(\\A zenon_Vhb:((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))" (is "~(\\A x : ?z_htx(x))")
           have z_Hty: "(\\E zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))" (is "\\E x : ?z_htz(x)")
           by (rule zenon_notallex_0 [of "?z_htx", OF z_Htv])
           have z_Hua: "?z_htz((CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))))" (is "~(?z_hub=>?z_huc)")
           by (rule zenon_ex_choose_0 [of "?z_htz", OF z_Hty])
           have z_Hub: "?z_hub"
           by (rule zenon_notimply_0 [OF z_Hua])
           have z_Hud: "(~?z_huc)"
           by (rule zenon_notimply_1 [OF z_Hua])
           have z_Hue: "(~((a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))]) \\in {ACK, TRUE, FALSE}))" (is "~?z_huf")
           by (rule zenon_notin_cup_0 [of "(a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))])" "{ACK, TRUE, FALSE}" "isa'dotdot(1, N)", OF z_Hud])
           have z_Hug: "(~((a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))]) \\in isa'dotdot(1, N)))" (is "~?z_huh")
           by (rule zenon_notin_cup_1 [of "(a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))])" "{ACK, TRUE, FALSE}" "isa'dotdot(1, N)", OF z_Hud])
           have z_Hui: "(~((a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))]) \\in {TRUE, FALSE}))" (is "~?z_huj")
           by (rule zenon_notin_addElt_1 [of "(a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))])" "ACK" "{TRUE, FALSE}", OF z_Hue])
           have z_Hih: "((a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))])~=TRUE)" (is "?z_hii~=?z_hcr")
           by (rule zenon_notin_addElt_0 [of "?z_hii" "?z_hcr" "{FALSE}", OF z_Hui])
           have z_Hiu: "((CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, ?z_hcr, FALSE} \\cup isa'dotdot(1, N)))))) \\in ?z_hgv)" (is "?z_hiu")
           by (rule ssubst [where P="(\<lambda>zenon_Vebb. ((CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, ?z_hcr, FALSE} \\cup isa'dotdot(1, N)))))) \\in zenon_Vebb))", OF z_Hgu z_Hub])
           have z_Hiq: "((CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, ?z_hcr, FALSE} \\cup isa'dotdot(1, N)))))) \\in ?z_hir)" (is "?z_hiq")
           by (rule ssubst [where P="(\<lambda>zenon_Vebb. ((CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, ?z_hcr, FALSE} \\cup isa'dotdot(1, N)))))) \\in zenon_Vebb))", OF z_Hti z_Hub])
           have z_Hup: "?z_htp((CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, ?z_hcr, FALSE} \\cup isa'dotdot(1, N)))))))" (is "_=>?z_huq")
           by (rule zenon_all_0 [of "?z_htp" "(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, ?z_hcr, FALSE} \\cup isa'dotdot(1, N))))))", OF z_Htj])
           show FALSE
           proof (rule zenon_imply [OF z_Hup])
            assume z_Hur:"(~?z_hub)"
            show FALSE
            by (rule notE [OF z_Hur z_Hub])
           next
            assume z_Huq:"?z_huq"
            show FALSE
            proof (rule zenon_in_cup [of "(ret[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, ?z_hcr, FALSE} \\cup isa'dotdot(1, N))))))])" "{ACK, ?z_hcr, FALSE}" "isa'dotdot(1, N)", OF z_Huq])
             assume z_Hus:"((ret[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, ?z_hcr, FALSE} \\cup isa'dotdot(1, N))))))]) \\in {ACK, ?z_hcr, FALSE})" (is "?z_hus")
             show FALSE
             proof (rule notE [OF z_Hue])
              have z_Hut: "((ret[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, ?z_hcr, FALSE} \\cup isa'dotdot(1, N))))))])=?z_hii)" (is "?z_hit=_")
              proof (rule zenon_nnpp [of "(?z_hit=?z_hii)"])
               assume z_His:"(?z_hit~=?z_hii)"
               show FALSE
               by (rule zenon_L10_ [OF z_Heb z_Hdy z_Hih z_Hiq z_His z_Hiu])
              qed
              have z_Huf: "?z_huf"
              by (rule subst [where P="(\<lambda>zenon_Vsvj. (zenon_Vsvj \\in {ACK, ?z_hcr, FALSE}))", OF z_Hut], fact z_Hus)
              thus "?z_huf" .
             qed
            next
             assume z_Hux:"((ret[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, ?z_hcr, FALSE} \\cup isa'dotdot(1, N))))))]) \\in isa'dotdot(1, N))" (is "?z_hux")
             show FALSE
             proof (rule notE [OF z_Hug])
              have z_Hut: "((ret[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, ?z_hcr, FALSE} \\cup isa'dotdot(1, N))))))])=?z_hii)" (is "?z_hit=_")
              proof (rule zenon_nnpp [of "(?z_hit=?z_hii)"])
               assume z_His:"(?z_hit~=?z_hii)"
               show FALSE
               by (rule zenon_L10_ [OF z_Heb z_Hdy z_Hih z_Hiq z_His z_Hiu])
              qed
              have z_Huh: "?z_huh"
              by (rule subst [where P="(\<lambda>zenon_Vrvj. (zenon_Vrvj \\in isa'dotdot(1, N)))", OF z_Hut], fact z_Hux)
              thus "?z_huh" .
             qed
            qed
           qed
          qed
         next
          assume z_Hod:"((a_uhash_primea[p])~=(a_vhash_primea[p]))" (is "?z_hdv~=?z_hdw")
          assume z_Hfq:"((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S3''))&(a_Mhash_primea=subsetOf(Configs, (\<lambda>t. bEx(M, (\<lambda>told. ((((told[''ret''])[p])=BOT)&(((t[''sigma''])=(told[''sigma'']))&(((((F[(u[p])])=(u[p]))&((((told[''sigma''])[(((told[''arg''])[p])[1])])~=((told[''sigma''])[(((told[''arg''])[p])[2])]))&((t[''ret''])=except((told[''ret'']), p, cond((((told[''sigma''])[(((told[''arg''])[p])[1])])=((told[''sigma''])[(((told[''arg''])[p])[2])])), TRUE, FALSE)))))|((t[''ret''])=(told[''ret''])))&(((t[''op''])=(told[''op'']))&((t[''arg''])=(told[''arg''])))))))))))))" (is "?z_hdo&?z_hfr")
          have z_Hdo: "?z_hdo"
          by (rule zenon_and_0 [OF z_Hfq])
          show FALSE
          by (rule zenon_L11_ [OF z_Hkn z_Hcl z_Hdo])
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
ML_command {* writeln "*** TLAPS EXIT 70"; *} qed
lemma ob'72:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes F F'
fixes u u'
fixes v v'
fixes w w'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition StateSet suppressed *)
(* usable definition Configs suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition Init suppressed *)
(* usable definition UFUniteShared suppressed *)
(* usable definition UFSUnite suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Next suppressed *)
(* usable definition SameSetSpec suppressed *)
assumes v'44: "((((((pc) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & (((F) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & (((u) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((w) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((M) \<in> ((SUBSET (Configs))))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))) \<and> (((Next) \<or> (((((a_pchash_primea :: c)) = (pc))) & ((((a_Fhash_primea :: c)) = (F))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_whash_primea :: c)) = (w))) & ((((a_chash_primea :: c)) = (a_ca))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_Mhash_primea :: c)) = (M))) & ((((a_rethash_primea :: c)) = (ret))))))))"
fixes p
assumes p_in : "(p \<in> (PROCESSES))"
assumes v'58: "(cond((((fapply (((a_uhash_primea :: c)), (p))) = (fapply (((a_whash_primea :: c)), (p))))), (((((a_rethash_primea :: c)) = ([(ret) EXCEPT ![(p)] = (FALSE)]))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''SR'')]))) & ((((a_Mhash_primea :: c)) = (subsetOf((M), %told. (((fapply ((fapply ((told), (''ret''))), (p))) = (FALSE)))))))), (((((a_rethash_primea :: c)) = (ret))) & ((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''S1'')]))) & ((((a_Mhash_primea :: c)) = (subsetOf((M), %told. (((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))))))))))"
assumes v'59: "(((fapply ((pc), (p))) = (''S3'')))"
assumes v'60: "((((a_whash_primea :: c)) = ([(w) EXCEPT ![(p)] = (fapply ((F), (fapply ((u), (p)))))])))"
assumes v'61: "((((a_Fhash_primea :: c)) = (F)))"
assumes v'62: "((((a_uhash_primea :: c)) = (u)))"
assumes v'63: "((((a_vhash_primea :: c)) = (v)))"
assumes v'64: "((((a_chash_primea :: c)) = (a_ca)))"
assumes v'65: "((((a_dhash_primea :: c)) = (d)))"
shows "(((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))]))))"(is "PROP ?ob'72")
proof -
ML_command {* writeln "*** TLAPS ENTER 72"; *}
show "PROP ?ob'72"

(* BEGIN ZENON INPUT
;; file=SameSetTypeOK.tlaps/tlapm_5cfeab.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >SameSetTypeOK.tlaps/tlapm_5cfeab.znn.out
;; obligation #72
$hyp "v'44" (/\ (/\ (TLA.in pc
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in F (TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i))))))) (TLA.in u
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in v
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N))) (TLA.in w
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_ca (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in d (TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0)
N))) (TLA.in M (TLA.SUBSET Configs)) (TLA.in ret
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0) N))))) (\/ Next
(/\ (= a_pchash_primea pc) (= a_Fhash_primea F) (= a_uhash_primea u)
(= a_vhash_primea v) (= a_whash_primea w) (= a_chash_primea a_ca)
(= a_dhash_primea d) (= a_Mhash_primea M) (= a_rethash_primea
ret))))
$hyp "p_in" (TLA.in p PROCESSES)
$hyp "v'58" (TLA.cond (= (TLA.fapply a_uhash_primea p)
(TLA.fapply a_whash_primea p)) (/\ (= a_rethash_primea (TLA.except ret p F.))
(= a_pchash_primea (TLA.except pc p "SR")) (= a_Mhash_primea
(TLA.subsetOf M ((told) (= (TLA.fapply (TLA.fapply told "ret") p)
F.))))) (/\ (= a_rethash_primea ret) (= a_pchash_primea
(TLA.except pc p "S1")) (= a_Mhash_primea
(TLA.subsetOf M ((told) (= (TLA.fapply (TLA.fapply told "ret") p)
BOT))))))
$hyp "v'59" (= (TLA.fapply pc p) "S3")
$hyp "v'60" (= a_whash_primea
(TLA.except w p (TLA.fapply F (TLA.fapply u p))))
$hyp "v'61" (= a_Fhash_primea F)
$hyp "v'62" (= a_uhash_primea u)
$hyp "v'63" (= a_vhash_primea v)
$hyp "v'64" (= a_chash_primea a_ca)
$hyp "v'65" (= a_dhash_primea d)
$goal (/\ (TLA.in a_pchash_primea
(TLA.FuncSet PROCESSES (TLA.set "0" "F1" "FR" "U1" "UR" "S1" "S2" "S3" "SR")))
(TLA.in a_Fhash_primea
(TLA.subsetOf (TLA.FuncSet (arith.intrange (TLA.fapply TLA.Succ 0)
N) (arith.intrange (TLA.fapply TLA.Succ 0)
N)) ((A) (TLA.bAll (arith.intrange (TLA.fapply TLA.Succ 0)
N) ((i) (= (TLA.fapply A (TLA.fapply A i)) (TLA.fapply A i)))))))
(TLA.in a_uhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_vhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_whash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_chash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_dhash_primea
(TLA.FuncSet PROCESSES (arith.intrange (TLA.fapply TLA.Succ 0) N)))
(TLA.in a_Mhash_primea (TLA.SUBSET Configs)) (TLA.in a_rethash_primea
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.)
(arith.intrange (TLA.fapply TLA.Succ 0)
N)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((pc \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((F \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((u \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((v \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((w \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_ca \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((d \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((M \\in SUBSET(Configs))&(ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))))))))&(Next|((a_pchash_primea=pc)&((a_Fhash_primea=F)&((a_uhash_primea=u)&((a_vhash_primea=v)&((a_whash_primea=w)&((a_chash_primea=a_ca)&((a_dhash_primea=d)&((a_Mhash_primea=M)&(a_rethash_primea=ret)))))))))))" (is "?z_hl&?z_hct")
 using v'44 by blast
 have z_Hj:"(a_dhash_primea=d)"
 using v'65 by blast
 have z_Hi:"(a_chash_primea=a_ca)"
 using v'64 by blast
 have z_He:"(a_whash_primea=except(w, p, (F[(u[p])])))" (is "_=?z_hdq")
 using v'60 by blast
 have z_Hh:"(a_vhash_primea=v)"
 using v'63 by blast
 have z_Hg:"(a_uhash_primea=u)"
 using v'62 by blast
 have z_Hf:"(a_Fhash_primea=F)"
 using v'61 by blast
 have z_Hb:"(p \\in PROCESSES)" (is "?z_hb")
 using p_in by blast
 have z_Hc:"cond(((a_uhash_primea[p])=(a_whash_primea[p])), ((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf(M, (\<lambda>told. (((told[''ret''])[p])=FALSE)))))), ((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S1''))&(a_Mhash_primea=subsetOf(M, (\<lambda>told. (((told[''ret''])[p])=BOT)))))))" (is "?z_hc")
 using v'58 by blast
 have zenon_L1_: "(a_pchash_primea=except(pc, p, ''SR'')) ==> (~isAFcn(a_pchash_primea)) ==> FALSE" (is "?z_heb ==> ?z_heu ==> FALSE")
 proof -
  assume z_Heb:"?z_heb" (is "_=?z_hec")
  assume z_Heu:"?z_heu" (is "~?z_hev")
  have z_Hew: "(~isAFcn(?z_hec))" (is "~?z_hex")
  by (rule subst [where P="(\<lambda>zenon_Vdla. (~isAFcn(zenon_Vdla)))", OF z_Heb z_Heu])
  show FALSE
  by (rule zenon_notisafcn_except [of "pc" "p" "''SR''", OF z_Hew])
 qed
 have zenon_L2_: "(a_pchash_primea=except(pc, p, ''SR'')) ==> (DOMAIN(a_pchash_primea)~=PROCESSES) ==> (DOMAIN(pc)=PROCESSES) ==> FALSE" (is "?z_heb ==> ?z_hfc ==> ?z_hfe ==> FALSE")
 proof -
  assume z_Heb:"?z_heb" (is "_=?z_hec")
  assume z_Hfc:"?z_hfc" (is "?z_hfd~=_")
  assume z_Hfe:"?z_hfe" (is "?z_hff=_")
  have z_Hfg: "(DOMAIN(?z_hec)~=PROCESSES)" (is "?z_hfh~=_")
  by (rule subst [where P="(\<lambda>zenon_Vhla. (DOMAIN(zenon_Vhla)~=PROCESSES))", OF z_Heb z_Hfc])
  have z_Hfm: "(?z_hff~=PROCESSES)"
  by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vgla. (zenon_Vgla~=PROCESSES))" "pc" "p" "''SR''", OF z_Hfg])
  show FALSE
  by (rule notE [OF z_Hfm z_Hfe])
 qed
 have zenon_L3_: "(a_pchash_primea=except(pc, p, ''S1'')) ==> (~isAFcn(a_pchash_primea)) ==> FALSE" (is "?z_hen ==> ?z_heu ==> FALSE")
 proof -
  assume z_Hen:"?z_hen" (is "_=?z_heo")
  assume z_Heu:"?z_heu" (is "~?z_hev")
  have z_Hfq: "(~isAFcn(?z_heo))" (is "~?z_hfr")
  by (rule subst [where P="(\<lambda>zenon_Vdla. (~isAFcn(zenon_Vdla)))", OF z_Hen z_Heu])
  show FALSE
  by (rule zenon_notisafcn_except [of "pc" "p" "''S1''", OF z_Hfq])
 qed
 have zenon_L4_: "(a_pchash_primea=except(pc, p, ''S1'')) ==> (DOMAIN(a_pchash_primea)~=PROCESSES) ==> (DOMAIN(pc)=PROCESSES) ==> FALSE" (is "?z_hen ==> ?z_hfc ==> ?z_hfe ==> FALSE")
 proof -
  assume z_Hen:"?z_hen" (is "_=?z_heo")
  assume z_Hfc:"?z_hfc" (is "?z_hfd~=_")
  assume z_Hfe:"?z_hfe" (is "?z_hff=_")
  have z_Hfs: "(DOMAIN(?z_heo)~=PROCESSES)" (is "?z_hft~=_")
  by (rule subst [where P="(\<lambda>zenon_Vhla. (DOMAIN(zenon_Vhla)~=PROCESSES))", OF z_Hen z_Hfc])
  have z_Hfm: "(?z_hff~=PROCESSES)"
  by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vgla. (zenon_Vgla~=PROCESSES))" "pc" "p" "''S1''", OF z_Hfs])
  show FALSE
  by (rule notE [OF z_Hfm z_Hfe])
 qed
 have zenon_L5_: "(a_Fhash_primea=F) ==> (~(a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))) ==> (F \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i]))))))) ==> FALSE" (is "?z_hf ==> ?z_hfu ==> ?z_hbb ==> FALSE")
 proof -
  assume z_Hf:"?z_hf"
  assume z_Hfu:"?z_hfu" (is "~?z_hfv")
  assume z_Hbb:"?z_hbb"
  have z_Hfw: "(~?z_hbb)"
  by (rule subst [where P="(\<lambda>zenon_Vaej. (~(zenon_Vaej \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))))", OF z_Hf z_Hfu])
  show FALSE
  by (rule notE [OF z_Hfw z_Hbb])
 qed
 have zenon_L6_: "(a_uhash_primea=u) ==> (~(a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (u \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hg ==> ?z_hgb ==> ?z_hbr ==> FALSE")
 proof -
  assume z_Hg:"?z_hg"
  assume z_Hgb:"?z_hgb" (is "~?z_hgc")
  assume z_Hbr:"?z_hbr"
  have z_Hgd: "(~?z_hbr)"
  by (rule subst [where P="(\<lambda>zenon_Vcej. (~(zenon_Vcej \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hg z_Hgb])
  show FALSE
  by (rule notE [OF z_Hgd z_Hbr])
 qed
 have zenon_L7_: "(a_vhash_primea=v) ==> (~(a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (v \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hh ==> ?z_hgi ==> ?z_hbv ==> FALSE")
 proof -
  assume z_Hh:"?z_hh"
  assume z_Hgi:"?z_hgi" (is "~?z_hgj")
  assume z_Hbv:"?z_hbv"
  have z_Hgk: "(~?z_hbv)"
  by (rule subst [where P="(\<lambda>zenon_Vcej. (~(zenon_Vcej \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hh z_Hgi])
  show FALSE
  by (rule notE [OF z_Hgk z_Hbv])
 qed
 have zenon_L8_: "(a_chash_primea=a_ca) ==> (~(a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (a_ca \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hi ==> ?z_hgl ==> ?z_hcb ==> FALSE")
 proof -
  assume z_Hi:"?z_hi"
  assume z_Hgl:"?z_hgl" (is "~?z_hgm")
  assume z_Hcb:"?z_hcb"
  have z_Hgn: "(~?z_hcb)"
  by (rule subst [where P="(\<lambda>zenon_Vcej. (~(zenon_Vcej \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hi z_Hgl])
  show FALSE
  by (rule notE [OF z_Hgn z_Hcb])
 qed
 have zenon_L9_: "(a_dhash_primea=d) ==> (~(a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))) ==> (d \\in FuncSet(PROCESSES, isa'dotdot(1, N))) ==> FALSE" (is "?z_hj ==> ?z_hgo ==> ?z_hce ==> FALSE")
 proof -
  assume z_Hj:"?z_hj"
  assume z_Hgo:"?z_hgo" (is "~?z_hgp")
  assume z_Hce:"?z_hce"
  have z_Hgq: "(~?z_hce)"
  by (rule subst [where P="(\<lambda>zenon_Vcej. (~(zenon_Vcej \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_Hj z_Hgo])
  show FALSE
  by (rule notE [OF z_Hgq z_Hce])
 qed
 have zenon_L10_: "(a_pchash_primea=except(pc, p, ''SR'')) ==> (a_rethash_primea=except(ret, p, FALSE)) ==> ((a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))])~=FALSE) ==> ((CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))) \\in DOMAIN(ret)) ==> ((ret[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))])~=(a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))])) ==> ((CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))) \\in DOMAIN(pc)) ==> FALSE" (is "?z_heb ==> ?z_hdy ==> ?z_hgr ==> ?z_hha ==> ?z_hhc ==> ?z_hhe ==> FALSE")
 proof -
  assume z_Heb:"?z_heb" (is "_=?z_hec")
  assume z_Hdy:"?z_hdy" (is "_=?z_hdz")
  assume z_Hgr:"?z_hgr" (is "?z_hgs~=?z_hcs")
  assume z_Hha:"?z_hha"
  assume z_Hhc:"?z_hhc" (is "?z_hhd~=_")
  assume z_Hhe:"?z_hhe"
  have z_Hhf: "(((isAFcn(a_pchash_primea)<=>isAFcn(?z_hec))&(DOMAIN(a_pchash_primea)=DOMAIN(?z_hec)))&(\\A zenon_Vqla:((a_pchash_primea[zenon_Vqla])=(?z_hec[zenon_Vqla]))))" (is "?z_hhg&?z_hhj")
  by (rule zenon_funequal_0 [of "a_pchash_primea" "?z_hec", OF z_Heb])
  have z_Hhj: "?z_hhj" (is "\\A x : ?z_hho(x)")
  by (rule zenon_and_1 [OF z_Hhf])
  have z_Hhp: "?z_hho((CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, ?z_hcs} \\cup isa'dotdot(1, N)))))))" (is "?z_hhq=?z_hhr")
  by (rule zenon_all_0 [of "?z_hho" "(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, ?z_hcs} \\cup isa'dotdot(1, N))))))", OF z_Hhj])
  show FALSE
  proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vmjc. (?z_hhq=zenon_Vmjc))" "pc" "p" "''SR''" "(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, ?z_hcs} \\cup isa'dotdot(1, N))))))", OF z_Hhp])
   assume z_Hhe:"?z_hhe"
   assume z_Hhv:"(p=(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, ?z_hcs} \\cup isa'dotdot(1, N)))))))" (is "_=?z_hgt")
   assume z_Hhw:"(?z_hhq=''SR'')" (is "_=?z_hz")
   have z_Hhx: "(((isAFcn(a_rethash_primea)<=>isAFcn(?z_hdz))&(DOMAIN(a_rethash_primea)=DOMAIN(?z_hdz)))&(\\A zenon_Vsla:((a_rethash_primea[zenon_Vsla])=(?z_hdz[zenon_Vsla]))))" (is "?z_hhy&?z_hif")
   by (rule zenon_funequal_0 [of "a_rethash_primea" "?z_hdz", OF z_Hdy])
   have z_Hif: "?z_hif" (is "\\A x : ?z_hik(x)")
   by (rule zenon_and_1 [OF z_Hhx])
   have z_Hil: "?z_hik(?z_hgt)" (is "_=?z_him")
   by (rule zenon_all_0 [of "?z_hik" "?z_hgt", OF z_Hif])
   show FALSE
   proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vqpc. (?z_hgs=zenon_Vqpc))" "ret" "p" "?z_hcs" "?z_hgt", OF z_Hil])
    assume z_Hha:"?z_hha"
    assume z_Hhv:"(p=?z_hgt)"
    assume z_Hiq:"(?z_hgs=?z_hcs)"
    show FALSE
    by (rule notE [OF z_Hgr z_Hiq])
   next
    assume z_Hha:"?z_hha"
    assume z_Hir:"(p~=?z_hgt)"
    assume z_His:"(?z_hgs=?z_hhd)"
    show FALSE
    by (rule notE [OF z_Hir z_Hhv])
   next
    assume z_Hit:"(~?z_hha)"
    show FALSE
    by (rule notE [OF z_Hit z_Hha])
   qed
  next
   assume z_Hhe:"?z_hhe"
   assume z_Hir:"(p~=(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, ?z_hcs} \\cup isa'dotdot(1, N)))))))" (is "_~=?z_hgt")
   assume z_Hiu:"(?z_hhq=(pc[?z_hgt]))" (is "_=?z_hiv")
   have z_Hhx: "(((isAFcn(a_rethash_primea)<=>isAFcn(?z_hdz))&(DOMAIN(a_rethash_primea)=DOMAIN(?z_hdz)))&(\\A zenon_Vsla:((a_rethash_primea[zenon_Vsla])=(?z_hdz[zenon_Vsla]))))" (is "?z_hhy&?z_hif")
   by (rule zenon_funequal_0 [of "a_rethash_primea" "?z_hdz", OF z_Hdy])
   have z_Hif: "?z_hif" (is "\\A x : ?z_hik(x)")
   by (rule zenon_and_1 [OF z_Hhx])
   have z_Hil: "?z_hik(?z_hgt)" (is "_=?z_him")
   by (rule zenon_all_0 [of "?z_hik" "?z_hgt", OF z_Hif])
   show FALSE
   proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vqpc. (?z_hgs=zenon_Vqpc))" "ret" "p" "?z_hcs" "?z_hgt", OF z_Hil])
    assume z_Hha:"?z_hha"
    assume z_Hhv:"(p=?z_hgt)"
    assume z_Hiq:"(?z_hgs=?z_hcs)"
    show FALSE
    by (rule notE [OF z_Hir z_Hhv])
   next
    assume z_Hha:"?z_hha"
    assume z_Hir:"(p~=?z_hgt)"
    assume z_His:"(?z_hgs=?z_hhd)"
    show FALSE
    by (rule zenon_eqsym [OF z_His z_Hhc])
   next
    assume z_Hit:"(~?z_hha)"
    show FALSE
    by (rule notE [OF z_Hit z_Hha])
   qed
  next
   assume z_Hiw:"(~?z_hhe)"
   show FALSE
   by (rule notE [OF z_Hiw z_Hhe])
  qed
 qed
 have zenon_L11_: "(~(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))) ==> (ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))) ==> (a_rethash_primea=ret) ==> FALSE" (is "?z_hix ==> ?z_hcl ==> ?z_hdo ==> FALSE")
 proof -
  assume z_Hix:"?z_hix" (is "~?z_hiy")
  assume z_Hcl:"?z_hcl"
  assume z_Hdo:"?z_hdo"
  show FALSE
  proof (rule notE [OF z_Hix])
   have z_Hiz: "(ret=a_rethash_primea)"
   by (rule sym [OF z_Hdo])
   have z_Hiy: "?z_hiy"
   by (rule subst [where P="(\<lambda>zenon_Vlej. (zenon_Vlej \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))", OF z_Hiz], fact z_Hcl)
   thus "?z_hiy" .
  qed
 qed
 assume z_Hk:"(~((a_pchash_primea \\in FuncSet(PROCESSES, {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))&((a_Fhash_primea \\in subsetOf(FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)), (\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))))&((a_uhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_vhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_whash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_chash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_dhash_primea \\in FuncSet(PROCESSES, isa'dotdot(1, N)))&((a_Mhash_primea \\in SUBSET(Configs))&(a_rethash_primea \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))))))))))" (is "~(?z_hje&?z_hjf)")
 have z_Hl: "?z_hl" (is "?z_hm&?z_hba")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hm: "?z_hm"
 by (rule zenon_and_0 [OF z_Hl])
 have z_Hba: "?z_hba" (is "?z_hbb&?z_hbq")
 by (rule zenon_and_1 [OF z_Hl])
 have z_Hbb: "?z_hbb"
 by (rule zenon_and_0 [OF z_Hba])
 have z_Hbq: "?z_hbq" (is "?z_hbr&?z_hbu")
 by (rule zenon_and_1 [OF z_Hba])
 have z_Hbr: "?z_hbr"
 by (rule zenon_and_0 [OF z_Hbq])
 have z_Hbu: "?z_hbu" (is "?z_hbv&?z_hbx")
 by (rule zenon_and_1 [OF z_Hbq])
 have z_Hbv: "?z_hbv"
 by (rule zenon_and_0 [OF z_Hbu])
 have z_Hbx: "?z_hbx" (is "?z_hby&?z_hca")
 by (rule zenon_and_1 [OF z_Hbu])
 have z_Hby: "?z_hby"
 by (rule zenon_and_0 [OF z_Hbx])
 have z_Hca: "?z_hca" (is "?z_hcb&?z_hcd")
 by (rule zenon_and_1 [OF z_Hbx])
 have z_Hcb: "?z_hcb"
 by (rule zenon_and_0 [OF z_Hca])
 have z_Hcd: "?z_hcd" (is "?z_hce&?z_hcg")
 by (rule zenon_and_1 [OF z_Hca])
 have z_Hce: "?z_hce"
 by (rule zenon_and_0 [OF z_Hcd])
 have z_Hcg: "?z_hcg" (is "?z_hch&?z_hcl")
 by (rule zenon_and_1 [OF z_Hcd])
 have z_Hch: "?z_hch"
 by (rule zenon_and_0 [OF z_Hcg])
 have z_Hcl: "?z_hcl"
 by (rule zenon_and_1 [OF z_Hcg])
 have z_Hjo: "(F \\in FuncSet(isa'dotdot(1, N), isa'dotdot(1, N)))" (is "?z_hjo")
 by (rule zenon_in_subsetof_0 [of "F" "FuncSet(isa'dotdot(1, N), isa'dotdot(1, N))" "(\<lambda>A. bAll(isa'dotdot(1, N), (\<lambda>i. ((A[(A[i])])=(A[i])))))", OF z_Hbb])
 have z_Hjp: "(M \\subseteq Configs)" (is "?z_hjp")
 by (rule zenon_in_SUBSET_0 [of "M" "Configs", OF z_Hch])
 have z_Hjq_z_Hjp: "bAll(M, (\<lambda>x. (x \\in Configs))) == ?z_hjp" (is "?z_hjq == _")
 by (unfold subset_def)
 have z_Hjq: "?z_hjq"
 by (unfold z_Hjq_z_Hjp, fact z_Hjp)
 have z_Hju_z_Hjq: "(\\A x:((x \\in M)=>(x \\in Configs))) == ?z_hjq" (is "?z_hju == _")
 by (unfold bAll_def)
 have z_Hju: "?z_hju" (is "\\A x : ?z_hjx(x)")
 by (unfold z_Hju_z_Hjq, fact z_Hjq)
 show FALSE
 proof (rule zenon_notand [OF z_Hk])
  assume z_Hjy:"(~?z_hje)"
  have z_Hfe: "(DOMAIN(pc)=PROCESSES)" (is "?z_hff=_")
  by (rule zenon_in_funcset_1 [of "pc" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hm])
  show FALSE
  proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "((a_uhash_primea[p])=(a_whash_primea[p]))" "((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf(M, (\<lambda>told. (((told[''ret''])[p])=FALSE))))))" "((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S1''))&(a_Mhash_primea=subsetOf(M, (\<lambda>told. (((told[''ret''])[p])=BOT))))))", OF z_Hc])
   assume z_Hdu:"((a_uhash_primea[p])=(a_whash_primea[p]))" (is "?z_hdv=?z_hdw")
   assume z_Hdx:"((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf(M, (\<lambda>told. (((told[''ret''])[p])=FALSE))))))" (is "?z_hdy&?z_hea")
   have z_Hea: "?z_hea" (is "?z_heb&?z_hed")
   by (rule zenon_and_1 [OF z_Hdx])
   have z_Heb: "?z_heb" (is "_=?z_hec")
   by (rule zenon_and_0 [OF z_Hea])
   have z_Hfe: "(?z_hff=PROCESSES)"
   by (rule zenon_in_funcset_1 [of "pc" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hm])
   have z_Hkb: "(\\A zenon_Vka:((zenon_Vka \\in PROCESSES)=>((pc[zenon_Vka]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''})))" (is "\\A x : ?z_hkh(x)")
   by (rule zenon_in_funcset_2 [of "pc" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hm])
   show FALSE
   proof (rule zenon_notin_funcset [of "a_pchash_primea" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hjy])
    assume z_Heu:"(~isAFcn(a_pchash_primea))" (is "~?z_hev")
    show FALSE
    by (rule zenon_L1_ [OF z_Heb z_Heu])
   next
    assume z_Hfc:"(DOMAIN(a_pchash_primea)~=PROCESSES)" (is "?z_hfd~=_")
    show FALSE
    by (rule zenon_L2_ [OF z_Heb z_Hfc z_Hfe])
   next
    assume z_Hki:"(~(\\A zenon_Vyaa:((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))" (is "~(\\A x : ?z_hkp(x))")
    have z_Hkq: "(\\E zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))" (is "\\E x : ?z_hks(x)")
    by (rule zenon_notallex_0 [of "?z_hkp", OF z_Hki])
    have z_Hkt: "?z_hks((CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''})))))" (is "~(?z_hkv=>?z_hkw)")
    by (rule zenon_ex_choose_0 [of "?z_hks", OF z_Hkq])
    have z_Hkv: "?z_hkv"
    by (rule zenon_notimply_0 [OF z_Hkt])
    have z_Hkx: "(~?z_hkw)"
    by (rule zenon_notimply_1 [OF z_Hkt])
    have z_Hky: "(~((a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hkz")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''0''" "{''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hkx])
    have z_Hlc: "(~((a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hld")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''F1''" "{''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hky])
    have z_Hlf: "(~((a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hlg")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''FR''" "{''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hlc])
    have z_Hli: "(~((a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hlj")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''U1''" "{''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hlf])
    have z_Hll: "(~((a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hlm")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''UR''" "{''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hli])
    have z_Hlo: "(~((a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''S2'', ''S3'', ''SR''}))" (is "~?z_hlp")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''S1''" "{''S2'', ''S3'', ''SR''}", OF z_Hll])
    have z_Hlr: "(~((a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''S3'', ''SR''}))" (is "~?z_hls")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''S2''" "{''S3'', ''SR''}", OF z_Hlo])
    have z_Hlu: "(~((a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''SR''}))" (is "~?z_hlv")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''S3''" "{''SR''}", OF z_Hlr])
    have z_Hlx: "((a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])~=''SR'')" (is "?z_hla~=?z_hz")
    by (rule zenon_notin_addElt_0 [of "?z_hla" "?z_hz" "{}", OF z_Hlu])
    have z_Hlz: "((CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz})))) \\in ?z_hff)" (is "?z_hlz")
    by (rule ssubst [where P="(\<lambda>zenon_Vekf. ((CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz})))) \\in zenon_Vekf))", OF z_Hfe z_Hkv])
    have z_Hmd: "?z_hkh((CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz})))))" (is "_=>?z_hme")
    by (rule zenon_all_0 [of "?z_hkh" "(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz}))))", OF z_Hkb])
    show FALSE
    proof (rule zenon_imply [OF z_Hmd])
     assume z_Hmf:"(~?z_hkv)"
     show FALSE
     by (rule notE [OF z_Hmf z_Hkv])
    next
     assume z_Hme:"?z_hme"
     show FALSE
     proof (rule notE [OF z_Hkx])
      have z_Hmg: "((pc[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz}))))])=?z_hla)" (is "?z_hmh=_")
      proof (rule zenon_nnpp [of "(?z_hmh=?z_hla)"])
       assume z_Hmi:"(?z_hmh~=?z_hla)"
       have z_Hhf: "(((isAFcn(a_pchash_primea)<=>isAFcn(?z_hec))&(DOMAIN(a_pchash_primea)=DOMAIN(?z_hec)))&(\\A zenon_Vqla:((a_pchash_primea[zenon_Vqla])=(?z_hec[zenon_Vqla]))))" (is "?z_hhg&?z_hhj")
       by (rule zenon_funequal_0 [of "a_pchash_primea" "?z_hec", OF z_Heb])
       have z_Hhj: "?z_hhj" (is "\\A x : ?z_hho(x)")
       by (rule zenon_and_1 [OF z_Hhf])
       have z_Hmj: "?z_hho((CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz})))))" (is "_=?z_hmk")
       by (rule zenon_all_0 [of "?z_hho" "(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz}))))", OF z_Hhj])
       show FALSE
       proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vvzf. (?z_hla=zenon_Vvzf))" "pc" "p" "?z_hz" "(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz}))))", OF z_Hmj])
        assume z_Hlz:"?z_hlz"
        assume z_Hmo:"(p=(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz})))))" (is "_=?z_hku")
        assume z_Hmp:"(?z_hla=?z_hz)"
        show FALSE
        by (rule notE [OF z_Hlx z_Hmp])
       next
        assume z_Hlz:"?z_hlz"
        assume z_Hmq:"(p~=(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz})))))" (is "_~=?z_hku")
        assume z_Hmr:"(?z_hla=?z_hmh)"
        show FALSE
        by (rule zenon_eqsym [OF z_Hmr z_Hmi])
       next
        assume z_Hms:"(~?z_hlz)"
        show FALSE
        by (rule notE [OF z_Hms z_Hlz])
       qed
      qed
      have z_Hkw: "?z_hkw"
      by (rule subst [where P="(\<lambda>zenon_Vmej. (zenon_Vmej \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ?z_hz}))", OF z_Hmg], fact z_Hme)
      thus "?z_hkw" .
     qed
    qed
   qed
  next
   assume z_Hmw:"((a_uhash_primea[p])~=(a_whash_primea[p]))" (is "?z_hdv~=?z_hdw")
   assume z_Hel:"((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S1''))&(a_Mhash_primea=subsetOf(M, (\<lambda>told. (((told[''ret''])[p])=BOT))))))" (is "?z_hdo&?z_hem")
   have z_Hem: "?z_hem" (is "?z_hen&?z_hep")
   by (rule zenon_and_1 [OF z_Hel])
   have z_Hen: "?z_hen" (is "_=?z_heo")
   by (rule zenon_and_0 [OF z_Hem])
   have z_Hfe: "(?z_hff=PROCESSES)"
   by (rule zenon_in_funcset_1 [of "pc" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hm])
   have z_Hkb: "(\\A zenon_Vka:((zenon_Vka \\in PROCESSES)=>((pc[zenon_Vka]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''})))" (is "\\A x : ?z_hkh(x)")
   by (rule zenon_in_funcset_2 [of "pc" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hm])
   show FALSE
   proof (rule zenon_notin_funcset [of "a_pchash_primea" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hjy])
    assume z_Heu:"(~isAFcn(a_pchash_primea))" (is "~?z_hev")
    show FALSE
    by (rule zenon_L3_ [OF z_Hen z_Heu])
   next
    assume z_Hfc:"(DOMAIN(a_pchash_primea)~=PROCESSES)" (is "?z_hfd~=_")
    show FALSE
    by (rule zenon_L4_ [OF z_Hen z_Hfc z_Hfe])
   next
    assume z_Hki:"(~(\\A zenon_Vyaa:((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))" (is "~(\\A x : ?z_hkp(x))")
    have z_Hkq: "(\\E zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))" (is "\\E x : ?z_hks(x)")
    by (rule zenon_notallex_0 [of "?z_hkp", OF z_Hki])
    have z_Hkt: "?z_hks((CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''})))))" (is "~(?z_hkv=>?z_hkw)")
    by (rule zenon_ex_choose_0 [of "?z_hks", OF z_Hkq])
    have z_Hkv: "?z_hkv"
    by (rule zenon_notimply_0 [OF z_Hkt])
    have z_Hkx: "(~?z_hkw)"
    by (rule zenon_notimply_1 [OF z_Hkt])
    have z_Hky: "(~((a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hkz")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''0''" "{''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hkx])
    have z_Hlc: "(~((a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hld")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''F1''" "{''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hky])
    have z_Hlf: "(~((a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hlg")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''FR''" "{''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hlc])
    have z_Hli: "(~((a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hlj")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''U1''" "{''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hlf])
    have z_Hll: "(~((a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))]) \\in {''S1'', ''S2'', ''S3'', ''SR''}))" (is "~?z_hlm")
    by (rule zenon_notin_addElt_1 [of "(a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])" "''UR''" "{''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hli])
    have z_Hmx: "((a_pchash_primea[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}))))])~=''S1'')" (is "?z_hla~=?z_hw")
    by (rule zenon_notin_addElt_0 [of "?z_hla" "?z_hw" "{''S2'', ''S3'', ''SR''}", OF z_Hll])
    have z_Hlz: "((CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ?z_hw, ''S2'', ''S3'', ''SR''})))) \\in ?z_hff)" (is "?z_hlz")
    by (rule ssubst [where P="(\<lambda>zenon_Vekf. ((CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ?z_hw, ''S2'', ''S3'', ''SR''})))) \\in zenon_Vekf))", OF z_Hfe z_Hkv])
    have z_Hmd: "?z_hkh((CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ?z_hw, ''S2'', ''S3'', ''SR''})))))" (is "_=>?z_hme")
    by (rule zenon_all_0 [of "?z_hkh" "(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ?z_hw, ''S2'', ''S3'', ''SR''}))))", OF z_Hkb])
    show FALSE
    proof (rule zenon_imply [OF z_Hmd])
     assume z_Hmf:"(~?z_hkv)"
     show FALSE
     by (rule notE [OF z_Hmf z_Hkv])
    next
     assume z_Hme:"?z_hme"
     show FALSE
     proof (rule notE [OF z_Hkx])
      have z_Hmg: "((pc[(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ?z_hw, ''S2'', ''S3'', ''SR''}))))])=?z_hla)" (is "?z_hmh=_")
      proof (rule zenon_nnpp [of "(?z_hmh=?z_hla)"])
       assume z_Hmi:"(?z_hmh~=?z_hla)"
       have z_Hmy: "(((isAFcn(a_pchash_primea)<=>isAFcn(?z_heo))&(DOMAIN(a_pchash_primea)=DOMAIN(?z_heo)))&(\\A zenon_Vtyc:((a_pchash_primea[zenon_Vtyc])=(?z_heo[zenon_Vtyc]))))" (is "?z_hmz&?z_hnc")
       by (rule zenon_funequal_0 [of "a_pchash_primea" "?z_heo", OF z_Hen])
       have z_Hnc: "?z_hnc" (is "\\A x : ?z_hnh(x)")
       by (rule zenon_and_1 [OF z_Hmy])
       have z_Hni: "?z_hnh((CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ?z_hw, ''S2'', ''S3'', ''SR''})))))" (is "_=?z_hnj")
       by (rule zenon_all_0 [of "?z_hnh" "(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ?z_hw, ''S2'', ''S3'', ''SR''}))))", OF z_Hnc])
       show FALSE
       proof (rule zenon_fapplyexcept [of "(\<lambda>zenon_Vvzf. (?z_hla=zenon_Vvzf))" "pc" "p" "?z_hw" "(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ?z_hw, ''S2'', ''S3'', ''SR''}))))", OF z_Hni])
        assume z_Hlz:"?z_hlz"
        assume z_Hmo:"(p=(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ?z_hw, ''S2'', ''S3'', ''SR''})))))" (is "_=?z_hku")
        assume z_Hnk:"(?z_hla=?z_hw)"
        show FALSE
        by (rule notE [OF z_Hmx z_Hnk])
       next
        assume z_Hlz:"?z_hlz"
        assume z_Hmq:"(p~=(CHOOSE zenon_Vyaa:(~((zenon_Vyaa \\in PROCESSES)=>((a_pchash_primea[zenon_Vyaa]) \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ?z_hw, ''S2'', ''S3'', ''SR''})))))" (is "_~=?z_hku")
        assume z_Hmr:"(?z_hla=?z_hmh)"
        show FALSE
        by (rule zenon_eqsym [OF z_Hmr z_Hmi])
       next
        assume z_Hms:"(~?z_hlz)"
        show FALSE
        by (rule notE [OF z_Hms z_Hlz])
       qed
      qed
      have z_Hkw: "?z_hkw"
      by (rule subst [where P="(\<lambda>zenon_Vmej. (zenon_Vmej \\in {''0'', ''F1'', ''FR'', ''U1'', ''UR'', ?z_hw, ''S2'', ''S3'', ''SR''}))", OF z_Hmg], fact z_Hme)
      thus "?z_hkw" .
     qed
    qed
   qed
  qed
 next
  assume z_Hnl:"(~?z_hjf)" (is "~(?z_hfv&?z_hjg)")
  show FALSE
  proof (rule zenon_notand [OF z_Hnl])
   assume z_Hfu:"(~?z_hfv)"
   show FALSE
   by (rule zenon_L5_ [OF z_Hf z_Hfu z_Hbb])
  next
   assume z_Hnm:"(~?z_hjg)" (is "~(?z_hgc&?z_hjh)")
   show FALSE
   proof (rule zenon_notand [OF z_Hnm])
    assume z_Hgb:"(~?z_hgc)"
    show FALSE
    by (rule zenon_L6_ [OF z_Hg z_Hgb z_Hbr])
   next
    assume z_Hnn:"(~?z_hjh)" (is "~(?z_hgj&?z_hji)")
    show FALSE
    proof (rule zenon_notand [OF z_Hnn])
     assume z_Hgi:"(~?z_hgj)"
     show FALSE
     by (rule zenon_L7_ [OF z_Hh z_Hgi z_Hbv])
    next
     assume z_Hno:"(~?z_hji)" (is "~(?z_hjj&?z_hjk)")
     show FALSE
     proof (rule zenon_notand [OF z_Hno])
      assume z_Hnp:"(~?z_hjj)"
      have z_Hnq: "(~(?z_hdq \\in FuncSet(PROCESSES, isa'dotdot(1, N))))" (is "~?z_hnr")
      by (rule subst [where P="(\<lambda>zenon_Vcej. (~(zenon_Vcej \\in FuncSet(PROCESSES, isa'dotdot(1, N)))))", OF z_He z_Hnp])
      show FALSE
      proof (rule zenon_except_notin_funcset [of "w" "p" "(F[(u[p])])" "PROCESSES" "isa'dotdot(1, N)", OF z_Hnq])
       assume z_Hns:"(~?z_hby)"
       show FALSE
       by (rule notE [OF z_Hns z_Hby])
      next
       assume z_Hnt:"(~((F[(u[p])]) \\in isa'dotdot(1, N)))" (is "~?z_hnu")
       have z_Hnv: "(\\A zenon_Vfa:((zenon_Vfa \\in PROCESSES)=>((u[zenon_Vfa]) \\in isa'dotdot(1, N))))" (is "\\A x : ?z_hob(x)")
       by (rule zenon_in_funcset_2 [of "u" "PROCESSES" "isa'dotdot(1, N)", OF z_Hbr])
       have z_Hoc: "(\\A zenon_Voa:((zenon_Voa \\in isa'dotdot(1, N))=>((F[zenon_Voa]) \\in isa'dotdot(1, N))))" (is "\\A x : ?z_hoi(x)")
       by (rule zenon_in_funcset_2 [of "F" "isa'dotdot(1, N)" "isa'dotdot(1, N)", OF z_Hjo])
       have z_Hoj: "?z_hoi((u[p]))" (is "?z_hok=>_")
       by (rule zenon_all_0 [of "?z_hoi" "(u[p])", OF z_Hoc])
       show FALSE
       proof (rule zenon_imply [OF z_Hoj])
        assume z_Hol:"(~?z_hok)"
        have z_Hom: "?z_hob(p)"
        by (rule zenon_all_0 [of "?z_hob" "p", OF z_Hnv])
        show FALSE
        proof (rule zenon_imply [OF z_Hom])
         assume z_Hon:"(~?z_hb)"
         show FALSE
         by (rule notE [OF z_Hon z_Hb])
        next
         assume z_Hok:"?z_hok"
         show FALSE
         by (rule notE [OF z_Hol z_Hok])
        qed
       next
        assume z_Hnu:"?z_hnu"
        show FALSE
        by (rule notE [OF z_Hnt z_Hnu])
       qed
      qed
     next
      assume z_Hoo:"(~?z_hjk)" (is "~(?z_hgm&?z_hjl)")
      show FALSE
      proof (rule zenon_notand [OF z_Hoo])
       assume z_Hgl:"(~?z_hgm)"
       show FALSE
       by (rule zenon_L8_ [OF z_Hi z_Hgl z_Hcb])
      next
       assume z_Hop:"(~?z_hjl)" (is "~(?z_hgp&?z_hjm)")
       show FALSE
       proof (rule zenon_notand [OF z_Hop])
        assume z_Hgo:"(~?z_hgp)"
        show FALSE
        by (rule zenon_L9_ [OF z_Hj z_Hgo z_Hce])
       next
        assume z_Hoq:"(~?z_hjm)" (is "~(?z_hjn&?z_hiy)")
        show FALSE
        proof (rule zenon_notand [OF z_Hoq])
         assume z_Hor:"(~?z_hjn)"
         have z_Hos: "(~(a_Mhash_primea \\subseteq Configs))" (is "~?z_hot")
         by (rule zenon_notin_SUBSET_0 [of "a_Mhash_primea" "Configs", OF z_Hor])
         have z_Hou_z_Hos: "(~bAll(a_Mhash_primea, (\<lambda>x. (x \\in Configs)))) == (~?z_hot)" (is "?z_hou == ?z_hos")
         by (unfold subset_def)
         have z_Hou: "?z_hou" (is "~?z_hov")
         by (unfold z_Hou_z_Hos, fact z_Hos)
         have z_How_z_Hou: "(~(\\A x:((x \\in a_Mhash_primea)=>(x \\in Configs)))) == ?z_hou" (is "?z_how == _")
         by (unfold bAll_def)
         have z_How: "?z_how" (is "~(\\A x : ?z_hpa(x))")
         by (unfold z_How_z_Hou, fact z_Hou)
         have z_Hpb: "(\\E x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))" (is "\\E x : ?z_hpd(x)")
         by (rule zenon_notallex_0 [of "?z_hpa", OF z_How])
         have z_Hpe: "?z_hpd((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))))" (is "~(?z_hpg=>?z_hph)")
         by (rule zenon_ex_choose_0 [of "?z_hpd", OF z_Hpb])
         have z_Hpg: "?z_hpg"
         by (rule zenon_notimply_0 [OF z_Hpe])
         have z_Hpi: "(~?z_hph)"
         by (rule zenon_notimply_1 [OF z_Hpe])
         show FALSE
         proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "((a_uhash_primea[p])=(a_whash_primea[p]))" "((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf(M, (\<lambda>told. (((told[''ret''])[p])=FALSE))))))" "((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S1''))&(a_Mhash_primea=subsetOf(M, (\<lambda>told. (((told[''ret''])[p])=BOT))))))", OF z_Hc])
          assume z_Hdu:"((a_uhash_primea[p])=(a_whash_primea[p]))" (is "?z_hdv=?z_hdw")
          assume z_Hdx:"((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf(M, (\<lambda>told. (((told[''ret''])[p])=FALSE))))))" (is "?z_hdy&?z_hea")
          have z_Hea: "?z_hea" (is "?z_heb&?z_hed")
          by (rule zenon_and_1 [OF z_Hdx])
          have z_Hed: "?z_hed" (is "_=?z_hee")
          by (rule zenon_and_1 [OF z_Hea])
          have z_Hpj: "?z_hjx((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))))" (is "?z_hpk=>_")
          by (rule zenon_all_0 [of "?z_hjx" "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))", OF z_Hju])
          show FALSE
          proof (rule zenon_imply [OF z_Hpj])
           assume z_Hpl:"(~?z_hpk)"
           have z_Hpm: "(\\A zenon_Vola:((zenon_Vola \\in a_Mhash_primea)<=>(zenon_Vola \\in ?z_hee)))" (is "\\A x : ?z_hpr(x)")
           by (rule zenon_setequal_0 [of "a_Mhash_primea" "?z_hee", OF z_Hed])
           have z_Hps: "?z_hpr((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))))" (is "_<=>?z_hpt")
           by (rule zenon_all_0 [of "?z_hpr" "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))", OF z_Hpm])
           show FALSE
           proof (rule zenon_equiv [OF z_Hps])
            assume z_Hpu:"(~?z_hpg)"
            assume z_Hpv:"(~?z_hpt)"
            show FALSE
            by (rule notE [OF z_Hpu z_Hpg])
           next
            assume z_Hpg:"?z_hpg"
            assume z_Hpt:"?z_hpt"
            have z_Hpk: "?z_hpk"
            by (rule zenon_in_subsetof_0 [of "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))" "M" "(\<lambda>told. (((told[''ret''])[p])=FALSE))", OF z_Hpt])
            show FALSE
            by (rule notE [OF z_Hpl z_Hpk])
           qed
          next
           assume z_Hph:"?z_hph"
           show FALSE
           by (rule notE [OF z_Hpi z_Hph])
          qed
         next
          assume z_Hmw:"((a_uhash_primea[p])~=(a_whash_primea[p]))" (is "?z_hdv~=?z_hdw")
          assume z_Hel:"((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S1''))&(a_Mhash_primea=subsetOf(M, (\<lambda>told. (((told[''ret''])[p])=BOT))))))" (is "?z_hdo&?z_hem")
          have z_Hem: "?z_hem" (is "?z_hen&?z_hep")
          by (rule zenon_and_1 [OF z_Hel])
          have z_Hep: "?z_hep" (is "_=?z_heq")
          by (rule zenon_and_1 [OF z_Hem])
          have z_Hpj: "?z_hjx((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))))" (is "?z_hpk=>_")
          by (rule zenon_all_0 [of "?z_hjx" "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))", OF z_Hju])
          show FALSE
          proof (rule zenon_imply [OF z_Hpj])
           assume z_Hpl:"(~?z_hpk)"
           have z_Hpw: "(\\A zenon_Vryc:((zenon_Vryc \\in a_Mhash_primea)<=>(zenon_Vryc \\in ?z_heq)))" (is "\\A x : ?z_hqb(x)")
           by (rule zenon_setequal_0 [of "a_Mhash_primea" "?z_heq", OF z_Hep])
           have z_Hqc: "?z_hqb((CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs)))))" (is "_<=>?z_hqd")
           by (rule zenon_all_0 [of "?z_hqb" "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))", OF z_Hpw])
           show FALSE
           proof (rule zenon_equiv [OF z_Hqc])
            assume z_Hpu:"(~?z_hpg)"
            assume z_Hqe:"(~?z_hqd)"
            show FALSE
            by (rule notE [OF z_Hpu z_Hpg])
           next
            assume z_Hpg:"?z_hpg"
            assume z_Hqd:"?z_hqd"
            have z_Hpk: "?z_hpk"
            by (rule zenon_in_subsetof_0 [of "(CHOOSE x:(~((x \\in a_Mhash_primea)=>(x \\in Configs))))" "M" "(\<lambda>told. (((told[''ret''])[p])=BOT))", OF z_Hqd])
            show FALSE
            by (rule notE [OF z_Hpl z_Hpk])
           qed
          next
           assume z_Hph:"?z_hph"
           show FALSE
           by (rule notE [OF z_Hpi z_Hph])
          qed
         qed
        next
         assume z_Hix:"(~?z_hiy)"
         have z_Hfe: "(DOMAIN(pc)=PROCESSES)" (is "?z_hff=_")
         by (rule zenon_in_funcset_1 [of "pc" "PROCESSES" "{''0'', ''F1'', ''FR'', ''U1'', ''UR'', ''S1'', ''S2'', ''S3'', ''SR''}", OF z_Hm])
         have z_Hqf: "(DOMAIN(ret)=PROCESSES)" (is "?z_hhb=_")
         by (rule zenon_in_funcset_1 [of "ret" "PROCESSES" "({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))", OF z_Hcl])
         show FALSE
         proof (rule zenon_ifthenelse [of "(\<lambda>zenon_Vf. zenon_Vf)" "((a_uhash_primea[p])=(a_whash_primea[p]))" "((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf(M, (\<lambda>told. (((told[''ret''])[p])=FALSE))))))" "((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S1''))&(a_Mhash_primea=subsetOf(M, (\<lambda>told. (((told[''ret''])[p])=BOT))))))", OF z_Hc])
          assume z_Hdu:"((a_uhash_primea[p])=(a_whash_primea[p]))" (is "?z_hdv=?z_hdw")
          assume z_Hdx:"((a_rethash_primea=except(ret, p, FALSE))&((a_pchash_primea=except(pc, p, ''SR''))&(a_Mhash_primea=subsetOf(M, (\<lambda>told. (((told[''ret''])[p])=FALSE))))))" (is "?z_hdy&?z_hea")
          have z_Hdy: "?z_hdy" (is "_=?z_hdz")
          by (rule zenon_and_0 [OF z_Hdx])
          have z_Hea: "?z_hea" (is "?z_heb&?z_hed")
          by (rule zenon_and_1 [OF z_Hdx])
          have z_Heb: "?z_heb" (is "_=?z_hec")
          by (rule zenon_and_0 [OF z_Hea])
          have z_Hqf: "(?z_hhb=PROCESSES)"
          by (rule zenon_in_funcset_1 [of "ret" "PROCESSES" "({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))", OF z_Hcl])
          have z_Hqg: "(\\A zenon_Vo:((zenon_Vo \\in PROCESSES)=>((ret[zenon_Vo]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))" (is "\\A x : ?z_hqm(x)")
          by (rule zenon_in_funcset_2 [of "ret" "PROCESSES" "({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))", OF z_Hcl])
          show FALSE
          proof (rule zenon_notin_funcset [of "a_rethash_primea" "PROCESSES" "({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))", OF z_Hix])
           assume z_Hqn:"(~isAFcn(a_rethash_primea))" (is "~?z_hia")
           have z_Hqo: "(~isAFcn(?z_hdz))" (is "~?z_hib")
           by (rule subst [where P="(\<lambda>zenon_Vdla. (~isAFcn(zenon_Vdla)))", OF z_Hdy z_Hqn])
           show FALSE
           by (rule zenon_notisafcn_except [of "ret" "p" "FALSE", OF z_Hqo])
          next
           assume z_Hqp:"(DOMAIN(a_rethash_primea)~=PROCESSES)" (is "?z_hid~=_")
           have z_Hqq: "(DOMAIN(?z_hdz)~=PROCESSES)" (is "?z_hie~=_")
           by (rule subst [where P="(\<lambda>zenon_Vhla. (DOMAIN(zenon_Vhla)~=PROCESSES))", OF z_Hdy z_Hqp])
           have z_Hqr: "(?z_hhb~=PROCESSES)"
           by (rule zenon_domain_except_0 [of "(\<lambda>zenon_Vgla. (zenon_Vgla~=PROCESSES))" "ret" "p" "FALSE", OF z_Hqq])
           show FALSE
           by (rule notE [OF z_Hqr z_Hqf])
          next
           assume z_Hqs:"(~(\\A zenon_Vhb:((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))" (is "~(\\A x : ?z_hqu(x))")
           have z_Hqv: "(\\E zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))" (is "\\E x : ?z_hqw(x)")
           by (rule zenon_notallex_0 [of "?z_hqu", OF z_Hqs])
           have z_Hqx: "?z_hqw((CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N)))))))" (is "~(?z_hqy=>?z_hqz)")
           by (rule zenon_ex_choose_0 [of "?z_hqw", OF z_Hqv])
           have z_Hqy: "?z_hqy"
           by (rule zenon_notimply_0 [OF z_Hqx])
           have z_Hra: "(~?z_hqz)"
           by (rule zenon_notimply_1 [OF z_Hqx])
           have z_Hrb: "(~((a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))]) \\in {ACK, TRUE, FALSE}))" (is "~?z_hrc")
           by (rule zenon_notin_cup_0 [of "(a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))])" "{ACK, TRUE, FALSE}" "isa'dotdot(1, N)", OF z_Hra])
           have z_Hrd: "(~((a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))]) \\in isa'dotdot(1, N)))" (is "~?z_hre")
           by (rule zenon_notin_cup_1 [of "(a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))])" "{ACK, TRUE, FALSE}" "isa'dotdot(1, N)", OF z_Hra])
           have z_Hrf: "(~((a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))]) \\in {TRUE, FALSE}))" (is "~?z_hrg")
           by (rule zenon_notin_addElt_1 [of "(a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))])" "ACK" "{TRUE, FALSE}", OF z_Hrb])
           have z_Hri: "(~((a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))]) \\in {FALSE}))" (is "~?z_hrj")
           by (rule zenon_notin_addElt_1 [of "(a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))])" "TRUE" "{FALSE}", OF z_Hrf])
           have z_Hgr: "((a_rethash_primea[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, FALSE} \\cup isa'dotdot(1, N))))))])~=FALSE)" (is "?z_hgs~=?z_hcs")
           by (rule zenon_notin_addElt_0 [of "?z_hgs" "?z_hcs" "{}", OF z_Hri])
           have z_Hhe: "((CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, ?z_hcs} \\cup isa'dotdot(1, N)))))) \\in ?z_hff)" (is "?z_hhe")
           by (rule ssubst [where P="(\<lambda>zenon_Vwva. ((CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, ?z_hcs} \\cup isa'dotdot(1, N)))))) \\in zenon_Vwva))", OF z_Hfe z_Hqy])
           have z_Hha: "((CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, ?z_hcs} \\cup isa'dotdot(1, N)))))) \\in ?z_hhb)" (is "?z_hha")
           by (rule ssubst [where P="(\<lambda>zenon_Vwva. ((CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, ?z_hcs} \\cup isa'dotdot(1, N)))))) \\in zenon_Vwva))", OF z_Hqf z_Hqy])
           have z_Hro: "?z_hqm((CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, ?z_hcs} \\cup isa'dotdot(1, N)))))))" (is "_=>?z_hrp")
           by (rule zenon_all_0 [of "?z_hqm" "(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, ?z_hcs} \\cup isa'dotdot(1, N))))))", OF z_Hqg])
           show FALSE
           proof (rule zenon_imply [OF z_Hro])
            assume z_Hrq:"(~?z_hqy)"
            show FALSE
            by (rule notE [OF z_Hrq z_Hqy])
           next
            assume z_Hrp:"?z_hrp"
            show FALSE
            proof (rule zenon_in_cup [of "(ret[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, ?z_hcs} \\cup isa'dotdot(1, N))))))])" "{ACK, TRUE, ?z_hcs}" "isa'dotdot(1, N)", OF z_Hrp])
             assume z_Hrr:"((ret[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, ?z_hcs} \\cup isa'dotdot(1, N))))))]) \\in {ACK, TRUE, ?z_hcs})" (is "?z_hrr")
             show FALSE
             proof (rule notE [OF z_Hrb])
              have z_Hrs: "((ret[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, ?z_hcs} \\cup isa'dotdot(1, N))))))])=?z_hgs)" (is "?z_hhd=_")
              proof (rule zenon_nnpp [of "(?z_hhd=?z_hgs)"])
               assume z_Hhc:"(?z_hhd~=?z_hgs)"
               show FALSE
               by (rule zenon_L10_ [OF z_Heb z_Hdy z_Hgr z_Hha z_Hhc z_Hhe])
              qed
              have z_Hrc: "?z_hrc"
              by (rule subst [where P="(\<lambda>zenon_Voej. (zenon_Voej \\in {ACK, TRUE, ?z_hcs}))", OF z_Hrs], fact z_Hrr)
              thus "?z_hrc" .
             qed
            next
             assume z_Hrw:"((ret[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, ?z_hcs} \\cup isa'dotdot(1, N))))))]) \\in isa'dotdot(1, N))" (is "?z_hrw")
             show FALSE
             proof (rule notE [OF z_Hrd])
              have z_Hrs: "((ret[(CHOOSE zenon_Vhb:(~((zenon_Vhb \\in PROCESSES)=>((a_rethash_primea[zenon_Vhb]) \\in ({ACK, TRUE, ?z_hcs} \\cup isa'dotdot(1, N))))))])=?z_hgs)" (is "?z_hhd=_")
              proof (rule zenon_nnpp [of "(?z_hhd=?z_hgs)"])
               assume z_Hhc:"(?z_hhd~=?z_hgs)"
               show FALSE
               by (rule zenon_L10_ [OF z_Heb z_Hdy z_Hgr z_Hha z_Hhc z_Hhe])
              qed
              have z_Hre: "?z_hre"
              by (rule subst [where P="(\<lambda>zenon_Vpej. (zenon_Vpej \\in isa'dotdot(1, N)))", OF z_Hrs], fact z_Hrw)
              thus "?z_hre" .
             qed
            qed
           qed
          qed
         next
          assume z_Hmw:"((a_uhash_primea[p])~=(a_whash_primea[p]))" (is "?z_hdv~=?z_hdw")
          assume z_Hel:"((a_rethash_primea=ret)&((a_pchash_primea=except(pc, p, ''S1''))&(a_Mhash_primea=subsetOf(M, (\<lambda>told. (((told[''ret''])[p])=BOT))))))" (is "?z_hdo&?z_hem")
          have z_Hdo: "?z_hdo"
          by (rule zenon_and_0 [OF z_Hel])
          show FALSE
          by (rule zenon_L11_ [OF z_Hix z_Hcl z_Hdo])
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
ML_command {* writeln "*** TLAPS EXIT 72"; *} qed
lemma ob'34:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes F F'
fixes u u'
fixes v v'
fixes w w'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition StateSet suppressed *)
(* usable definition Configs suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition Init suppressed *)
(* usable definition UFUniteShared suppressed *)
(* usable definition UFSUnite suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Next suppressed *)
(* usable definition SameSetSpec suppressed *)
assumes v'44: "((((((pc) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & (((F) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & (((u) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((w) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & (((M) \<in> ((SUBSET (Configs))))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))])))) \<and> (((Next) \<or> (((((a_pchash_primea :: c)) = (pc))) & ((((a_Fhash_primea :: c)) = (F))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_whash_primea :: c)) = (w))) & ((((a_chash_primea :: c)) = (a_ca))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_Mhash_primea :: c)) = (M))) & ((((a_rethash_primea :: c)) = (ret))))))))"
fixes p
assumes p_in : "(p \<in> (PROCESSES))"
assumes v'51: "((((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''F1'')]))) & (\<exists> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((a_chash_primea :: c)) = ([(a_ca) EXCEPT ![(p)] = (i)]))) & ((((a_Mhash_primea :: c)) = (subsetOf((Configs), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((fapply ((told), (''op''))), (p))) = (BOT))) & (((fapply ((fapply ((told), (''arg''))), (p))) = (BOT))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''op''))) = ([(fapply ((told), (''op''))) EXCEPT ![(p)] = (''F'')]))) & (((fapply ((t), (''arg''))) = ([(fapply ((told), (''arg''))) EXCEPT ![(p)] = (fapply (((a_chash_primea :: c)), (p)))]))) & (((fapply ((t), (''ret''))) = (fapply ((told), (''ret''))))))))))))) & (((((a_Fhash_primea :: c)) = (F))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_whash_primea :: c)) = (w))) & ((((a_chash_primea :: c)) = (a_ca))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_rethash_primea :: c)) = (ret))))) | (((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''U1'')]))) & (\<exists> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (\<exists> j \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((a_chash_primea :: c)) = ([(a_ca) EXCEPT ![(p)] = (i)]))) & ((((a_dhash_primea :: c)) = ([(d) EXCEPT ![(p)] = (j)]))) & ((((a_Mhash_primea :: c)) = (subsetOf((Configs), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((fapply ((told), (''op''))), (p))) = (BOT))) & (((fapply ((fapply ((told), (''arg''))), (p))) = (BOT))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''op''))) = ([(fapply ((told), (''op''))) EXCEPT ![(p)] = (''U'')]))) & (((fapply ((t), (''arg''))) = ([(fapply ((told), (''arg''))) EXCEPT ![(p)] = (<<(fapply (((a_chash_primea :: c)), (p))), (fapply (((a_dhash_primea :: c)), (p)))>>)]))) & (((fapply ((t), (''ret''))) = (fapply ((told), (''ret'')))))))))))))) & (((((a_Fhash_primea :: c)) = (F))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_whash_primea :: c)) = (w))) & ((((a_chash_primea :: c)) = (a_ca))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_rethash_primea :: c)) = (ret))))) | (((((a_pchash_primea :: c)) = ([(pc) EXCEPT ![(p)] = (''S1'')]))) & (\<exists> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (\<exists> j \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((((a_chash_primea :: c)) = ([(a_ca) EXCEPT ![(p)] = (i)]))) & ((((a_dhash_primea :: c)) = ([(d) EXCEPT ![(p)] = (j)]))) & ((((a_Mhash_primea :: c)) = (subsetOf((Configs), %t. (\<exists> told \<in> (M) : ((((fapply ((fapply ((told), (''ret''))), (p))) = (BOT))) & (((fapply ((fapply ((told), (''op''))), (p))) = (BOT))) & (((fapply ((fapply ((told), (''arg''))), (p))) = (BOT))) & (((fapply ((t), (''sigma''))) = (fapply ((told), (''sigma''))))) & (((fapply ((t), (''op''))) = ([(fapply ((told), (''op''))) EXCEPT ![(p)] = (''S'')]))) & (((fapply ((t), (''arg''))) = ([(fapply ((told), (''arg''))) EXCEPT ![(p)] = (<<(fapply (((a_chash_primea :: c)), (p))), (fapply (((a_dhash_primea :: c)), (p)))>>)]))) & (((fapply ((t), (''ret''))) = (fapply ((told), (''ret'')))))))))))))) & (((((a_Fhash_primea :: c)) = (F))) & ((((a_uhash_primea :: c)) = (u))) & ((((a_vhash_primea :: c)) = (v))) & ((((a_whash_primea :: c)) = (w))) & ((((a_chash_primea :: c)) = (a_ca))) & ((((a_dhash_primea :: c)) = (d))) & ((((a_rethash_primea :: c)) = (ret))))))"
assumes v'52: "(((fapply ((pc), (p))) = (''0'')))"
shows "(((((a_pchash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ({(''0''), (''F1''), (''FR''), (''U1''), (''UR''), (''S1''), (''S2''), (''S3''), (''SR'')})]))) & ((((a_Fhash_primea :: c)) \<in> (subsetOf(([((isa_peri_peri_a (((Succ[0])), (N)))) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]), %A. (\<forall> i \<in> ((isa_peri_peri_a (((Succ[0])), (N)))) : (((fapply ((A), (fapply ((A), (i))))) = (fapply ((A), (i)))))))))) & ((((a_uhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_vhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_whash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_chash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_dhash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((isa_peri_peri_a (((Succ[0])), (N))))]))) & ((((a_Mhash_primea :: c)) \<in> ((SUBSET (Configs))))) & ((((a_rethash_primea :: c)) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> ((isa_peri_peri_a (((Succ[0])), (N))))))]))))"(is "PROP ?ob'34")
proof -
ML_command {* writeln "*** TLAPS ENTER 34"; *}
show "PROP ?ob'34"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 34"; *} qed
end
