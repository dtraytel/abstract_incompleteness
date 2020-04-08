(* This is the simplified and "corrected" version of Jeroslow's 
Second Incompleteness Theorem reported in the CADE 2019 paper: *)
theory Jeroslow_Corrected imports
Abstract_Representability Diagonalization
begin 

(* The Jeroslow assumptions: *)
(*****************************)

locale Jeroslow_Diagonalization = 
Deduct2_with_False 
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  num
  prv prv
+
Encode
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv prv
  enc 
+
TermEncode
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv prv
  Ops tenc  
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and eql cnj imp all exi 
and fls 
and num
and prv 
and enc ("\<langle>_\<rangle>") 
and Ops and tenc  
+  
fixes F :: "('trm \<Rightarrow> 'trm) set"
  and encF :: "('trm \<Rightarrow> 'trm) \<Rightarrow> ('trm \<Rightarrow> 'trm)" 
  and N :: "'trm \<Rightarrow> 'trm"
  and ssap :: "'fmla \<Rightarrow> 'trm \<Rightarrow> 'trm"  
(*  *)
assumes 
F[simp,intro!]: "\<And> f n. f \<in> F \<Longrightarrow> n \<in> num \<Longrightarrow> f n \<in> num"
and
encF[simp,intro!]: "\<And> f. f \<in> F \<Longrightarrow> encF f \<in> Ops"
and 
N[simp,intro!]: "N \<in> F" 
and 
ssap[simp]: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {xx} \<Longrightarrow> ssap \<phi> \<in> F"
(*  *)
and 
ReprF: "\<And>f n. f \<in> F \<Longrightarrow> n \<in> num \<Longrightarrow> prv (eql (encF f n) (f n))"
and
CapN: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> N \<langle>\<phi>\<rangle> = \<langle>neg \<phi>\<rangle>"
and  
CapSS: 
"\<And> \<psi> f. \<psi> \<in> fmla \<Longrightarrow> Fvars \<psi> = {xx} \<Longrightarrow> f \<in> F \<Longrightarrow> 
    ssap \<psi> (tenc (encF f)) = \<langle>inst \<psi> (encF f (tenc (encF f)))\<rangle>"
begin 

definition tJ :: "'fmla \<Rightarrow> 'trm" where 
"tJ \<psi> \<equiv> encF (ssap \<psi>) (tenc (encF (ssap \<psi>)))"

definition \<phi>J :: "'fmla \<Rightarrow> 'fmla" where 
"\<phi>J \<psi> \<equiv> subst \<psi> (tJ \<psi>) xx" 

lemma tJ[simp]: 
assumes "\<psi> \<in> fmla" and "Fvars \<psi> = {xx}"
shows "tJ \<psi> \<in> trm"
using assms tJ_def by auto

lemma FvarsT_tJ[simp]: 
assumes "\<psi> \<in> fmla" and "Fvars \<psi> = {xx}"
shows "FvarsT (tJ \<psi>) = {}"
using assms tJ_def by auto

lemma \<phi>J[simp]: 
assumes "\<psi> \<in> fmla" and "Fvars \<psi> = {xx}"
shows "\<phi>J \<psi> \<in> fmla"
using assms \<phi>J_def by auto

lemma Fvars_\<phi>J[simp]: 
assumes "\<psi> \<in> fmla" and "Fvars \<psi> = {xx}"
shows "Fvars (\<phi>J \<psi>) = {}"
using assms \<phi>J_def by (auto simp: Fvars_subst)

lemma diagonalization: 
assumes "\<psi> \<in> fmla" and "Fvars \<psi> = {xx}"
shows "prv (eql (tJ \<psi>) \<langle>inst \<psi> (tJ \<psi>)\<rangle>) \<and> 
       prv (eqv (\<phi>J \<psi>) (inst \<psi> \<langle>\<phi>J \<psi>\<rangle>))"
proof 
  define fJ where "fJ \<equiv> ssap \<psi>" 
  have fJ[simp]: "fJ \<in> F" unfolding fJ_def using assms by auto
  have "fJ (tenc (encF fJ)) = \<langle>inst \<psi> (tJ \<psi>)\<rangle>"
   by (simp add: CapSS assms fJ_def tJ_def)
  thus **: "prv (eql (tJ \<psi>) \<langle>inst \<psi> (tJ \<psi>)\<rangle>)"   
   using ReprF fJ fJ_def tJ_def by fastforce
  show "prv (eqv (\<phi>J \<psi>) (inst \<psi> \<langle>\<phi>J \<psi>\<rangle>))"
   using assms prv_eql_subst_trm_eqv[OF xx _  _ _ **, of "\<psi>"] 
   by (auto simp: \<phi>J_def inst_def) 
qed 


end \<comment> \<open>context Jeroslow_Diagonalization\<close>


locale Jeroslow_Godel_Second =  
Jeroslow_Diagonalization 
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  num
  prv 
  enc    
  Ops tenc 
  F encF N ssap
+
WRepr_Provability
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv prv
  enc
  P
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and eql cnj imp all exi 
and fls 
and num
and prv 
and enc ("\<langle>_\<rangle>") 
and Ops and tenc 
and P
and F encF N ssap
+ 
assumes 
HBL1: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv \<phi> \<Longrightarrow> prv (PP \<langle>\<phi>\<rangle>)" 
and 
SHBL3: "\<And>t. t \<in> trm \<Longrightarrow> FvarsT t = {} \<Longrightarrow> prv (imp (PP t) (PP \<langle>PP t\<rangle>))"
begin

  
(* Consistency formula a la Jeroslow: *)
definition jcons :: "'fmla" where 
"jcons \<equiv> all xx (neg (cnj (PP (Var xx)) (PP (encF N (Var (xx))))))" 

lemma prv_eql_subst_trm3:
"x \<in> var \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> 
prv (eql t1 t2) \<Longrightarrow> prv (subst \<phi> t1 x) \<Longrightarrow> prv (subst \<phi> t2 x)"
using prv_eql_subst_trm2  
  by (meson subst prv_imp_mp) 

lemma prv_eql_neg_encF_N: 
assumes "\<phi> \<in> fmla" and "Fvars \<phi> = {}"
shows "prv (eql \<langle>neg \<phi>\<rangle> (encF N \<langle>\<phi>\<rangle>))" 
  unfolding CapN[symmetric, OF assms]
  by (rule prv_prv_eql_sym) (auto simp: assms intro: ReprF)  
  
lemma prv_imp_neg_encF_N_aux: 
assumes "\<phi> \<in> fmla" and "Fvars \<phi> = {}"
shows "prv (imp (PP \<langle>neg \<phi>\<rangle>) (PP (encF N \<langle>\<phi>\<rangle>)))" 
using assms prv_eql_subst_trm2[OF _ _ _ _ prv_eql_neg_encF_N[OF assms], 
  of xx "PP (Var xx)"]  
  unfolding PP_def by auto

lemma prv_cnj_neg_encF_N_aux: 
assumes "\<phi> \<in> fmla" and "Fvars \<phi> = {}" "\<chi> \<in> fmla" "Fvars \<chi> = {}"
and "prv (neg (cnj \<chi> (PP \<langle>neg \<phi>\<rangle>)))"
shows"prv (neg (cnj \<chi> (PP (encF N \<langle>\<phi>\<rangle>))))"
using assms prv_eql_subst_trm3[OF _ _ _ _ prv_eql_neg_encF_N, 
  of xx "neg (cnj \<chi> (PP (Var xx)))"] 
  unfolding PP_def by auto
 
theorem jeroslow_godel_second: 
assumes consistent
shows "\<not> prv jcons"
proof
  assume *: "prv jcons"
  define \<psi> where "\<psi> \<equiv> PP (encF N (Var xx))"
  define t where "t \<equiv> tJ \<psi>"
  have \<psi>[simp,intro]: "\<psi> \<in> fmla" "Fvars \<psi> = {xx}" 
  and t[simp,intro]: "t \<in> trm" "FvarsT t = {}" 
    unfolding \<psi>_def t_def by auto

  have sPP[simp]: "subst (PP (encF N (Var xx))) \<langle>PP (encF N t)\<rangle> xx = 
             PP (encF N \<langle>PP (encF N t)\<rangle>)"
    unfolding PP_def by (subst subst_compose_eq_or) auto
  have sPP2[simp]: "subst (PP (encF N (Var xx))) t xx = PP (encF N t)"
    unfolding PP_def by (subst subst_compose_eq_or) auto
  have 00: "PP (encF N t) = inst \<psi> t" unfolding \<psi>_def inst_def PP_def
    by (subst subst_compose_eq_or) auto
  
  define \<phi> where "\<phi> \<equiv> \<phi>J \<psi>"
  have [simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}" unfolding \<phi>_def by auto
  have **: "prv (eql t \<langle>\<phi>\<rangle>)" 
    unfolding 00 \<phi>_def 
    using \<phi>J_def diagonalization inst_def t_def by auto
  have \<phi>: "\<phi> = PP (encF N t)" unfolding \<phi>_def \<phi>J_def t_def \<psi>_def 
    using sPP2 \<psi>_def t_def by blast
  have 1: "prv (imp \<phi> (PP \<langle>\<phi>\<rangle>))" using SHBL3[of "encF N t"] 
    using 00 \<phi>J_def \<phi>_def \<psi>_def inst_def t_def by auto
  have eqv_\<phi>: "prv (eqv \<phi> (PP (encF N \<langle>\<phi>\<rangle>)))"  using diagonalization
    by (metis "00" sPP \<phi>J_def \<phi>_def \<psi> \<psi>_def diagonalization inst_def t_def)
  have 2: "prv (imp \<phi> (PP (encF N \<langle>\<phi>\<rangle>)))" 
   using prv_cnjEL[OF _ _ eqv_\<phi>[unfolded eqv_def]] by auto 
  have "prv (imp (PP (encF N \<langle>\<phi>\<rangle>)) \<phi>)"
   using prv_cnjER[OF _ _ eqv_\<phi>[unfolded eqv_def]] by auto 
  from  prv_prv_imp_trans[OF _ _ _ prv_imp_neg_encF_N_aux this]
  have 22: "prv (imp (PP \<langle>neg \<phi>\<rangle>) \<phi>)" by auto
  have 3: "prv (imp \<phi> (cnj (PP \<langle>\<phi>\<rangle>) (PP (encF N \<langle>\<phi>\<rangle>))))" 
    by (rule prv_imp_cnj[OF _ _ _ 1 2]) (auto simp: \<phi>_def)
  have 4: "prv (neg (cnj (PP \<langle>\<phi>\<rangle>) (PP (encF N \<langle>\<phi>\<rangle>))))" 
     using prv_allE[OF _ _ _ *[unfolded jcons_def], of "\<langle>\<phi>\<rangle>"] 
  by (simp add: \<phi> \<psi>_def)
  have 5: "prv (neg \<phi>)" 
    unfolding neg_def 
    by (rule prv_prv_imp_trans[OF _ _ _ 3 4[unfolded neg_def]]) auto
  hence "prv (PP \<langle>neg \<phi>\<rangle>)" using  
      HBL1[OF _ _ 5] by auto
  hence "prv \<phi>" using prv_imp_mp[OF _ _ 22] by auto
  with 5 assms show False unfolding consistent_def3 by auto
qed
 
theorem jeroslow_godel_second_standardCon: 
assumes consistent 
and HBL4_prv: "\<And>\<phi>1 \<phi>2. {\<phi>1,\<phi>2} \<subseteq> fmla \<Longrightarrow> Fvars \<phi>1 = {} \<Longrightarrow> Fvars \<phi>2 = {} \<Longrightarrow> 
   prv (imp (cnj (PP \<langle>\<phi>1\<rangle>) (PP \<langle>\<phi>2\<rangle>)) (PP \<langle>cnj \<phi>1 \<phi>2\<rangle>))"
and WHBL2: "\<And>\<phi>1 \<phi>2. {\<phi>1,\<phi>2} \<subseteq> fmla \<Longrightarrow> Fvars \<phi>1 = {} \<Longrightarrow> Fvars \<phi>2 = {} \<Longrightarrow> 
   prv (imp \<phi>1 \<phi>2) \<Longrightarrow> prv (imp (PP \<langle>\<phi>1\<rangle>) (PP \<langle>\<phi>2\<rangle>))"
shows "\<not> prv (neg (PP \<langle>fls\<rangle>))"
proof
  assume *: (* jeroslow_godel_second's "prv jcons" is upgraded to: *) 
    "prv (neg (PP \<langle>fls\<rangle>))"
  define \<psi> where "\<psi> \<equiv> PP (encF N (Var xx))"
  define t where "t \<equiv> tJ \<psi>"
  have \<psi>[simp,intro]: "\<psi> \<in> fmla" "Fvars \<psi> = {xx}" 
  and t[simp,intro]: "t \<in> trm" "FvarsT t = {}" 
    unfolding \<psi>_def t_def by auto

  have [simp]: "subst (PP (encF N (Var xx))) \<langle>PP (encF N t)\<rangle> xx = 
             PP (encF N \<langle>PP (encF N t)\<rangle>)"
    unfolding PP_def by (subst subst_compose_eq_or) auto
  have [simp]: "subst (PP (encF N (Var xx))) t xx = PP (encF N t)"
    unfolding PP_def by (subst subst_compose_eq_or) auto
  have 00: "PP (encF N t) = inst \<psi> t" unfolding \<psi>_def inst_def PP_def
    by (subst subst_compose_eq_or) auto
  
  define \<phi> where "\<phi> = PP (encF N t)"
  have [simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}" unfolding \<phi>_def by auto
  have **: "prv (eql t \<langle>PP (encF N t)\<rangle>)" 
    unfolding 00 by (simp add: diagonalization t_def)
  have 1: "prv (imp \<phi> (PP \<langle>\<phi>\<rangle>))" using SHBL3[of "encF N t"] 
    by (auto simp: \<phi>_def)
  have 2: "prv (imp \<phi> (PP (encF N \<langle>\<phi>\<rangle>)))"
   using prv_eql_subst_trm2[OF xx _  _ _ **, of "PP (encF N (Var xx))"] 
   by (auto simp: \<phi>_def)
  have "prv (imp (PP (encF N \<langle>\<phi>\<rangle>)) \<phi>)"
   using prv_eql_subst_trm_rev2[OF xx _  _ _ **, of "PP (encF N (Var xx))"] 
   by (auto simp: \<phi>_def)
  from prv_prv_imp_trans[OF _ _ _ prv_imp_neg_encF_N_aux this]
  have 22: "prv (imp (PP \<langle>neg \<phi>\<rangle>) \<phi>)" by auto
  have 3: "prv (imp \<phi> (cnj (PP \<langle>\<phi>\<rangle>) (PP (encF N \<langle>\<phi>\<rangle>))))" 
    by (rule prv_imp_cnj[OF _ _ _ 1 2]) (auto simp: \<phi>_def)

  (*  This is the modification from the proof of jeroslow_godel_second: *)
  have 41: "prv (imp (cnj (PP \<langle>\<phi>\<rangle>) (PP \<langle>neg \<phi>\<rangle>)) (PP \<langle>cnj \<phi> (neg \<phi>)\<rangle>))"
  using HBL4_prv[of \<phi> "neg \<phi>"] by auto
  have "prv (imp (cnj \<phi> (neg \<phi>)) (fls))"  
    by (simp add: prv_cnj_imp_monoR2 prv_imp_neg_fls)
  from WHBL2[OF _ _ _ this] 
  have 42: "prv (imp (PP \<langle>cnj \<phi> (neg \<phi>)\<rangle>) (PP \<langle>fls\<rangle>))" by auto
  from prv_prv_imp_trans[OF _ _ _ 41 42]
  have "prv (imp (cnj (PP \<langle>\<phi>\<rangle>) (PP \<langle>neg \<phi>\<rangle>)) (PP \<langle>fls\<rangle>))" by auto
  from prv_prv_imp_trans[OF _ _ _ this *[unfolded neg_def]]
  have "prv (neg (cnj (PP \<langle>\<phi>\<rangle>) (PP \<langle>neg \<phi>\<rangle>)))"
  unfolding neg_def by auto
  from prv_cnj_neg_encF_N_aux[OF _ _ _ _ this]
  have 4: "prv (neg (cnj (PP \<langle>\<phi>\<rangle>) (PP (encF N \<langle>\<phi>\<rangle>))))" by auto
  (*  End modification *)

  have 5: "prv (neg \<phi>)" 
    unfolding neg_def 
    by (rule prv_prv_imp_trans[OF _ _ _ 3 4[unfolded neg_def]]) auto
  hence "prv (PP \<langle>neg \<phi>\<rangle>)" using HBL1[OF _ _ 5] by auto
  hence "prv \<phi>" using prv_imp_mp[OF _ _ 22] by auto
  with 5 assms show False unfolding consistent_def3 by auto
qed

(*****) 
definition noContr :: bool where 
"noContr \<equiv> \<forall> \<phi> \<in> fmla. Fvars \<phi> = {} \<longrightarrow> prv (neg (cnj (PP \<langle>\<phi>\<rangle>) (PP \<langle>neg \<phi>\<rangle>)))"

lemma jcons_noContr: 
assumes j: "prv jcons"
shows "noContr" 
unfolding noContr_def proof safe
  fix \<phi> assume \<phi>[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}"
  have [simp]: "subst (PP (encF N (Var xx))) \<langle>\<phi>\<rangle> xx =
               PP (encF N \<langle>\<phi>\<rangle>)" 
  unfolding PP_def by (simp add: subst_compose_same)
  note j = allE_id[OF _ _ j[unfolded jcons_def], simplified]
  have 0: "prv (neg (cnj (PP \<langle>\<phi>\<rangle>) 
                         (PP (encF N \<langle>\<phi>\<rangle>))))"
  (is "prv (neg (cnj (PP \<langle>\<phi>\<rangle>) ?j))")  
    using prv_subst[OF _ _ _ j, of xx "\<langle>\<phi>\<rangle>"] by simp
  have 1: "prv (imp (PP \<langle>neg \<phi>\<rangle>) ?j)" 
  using prv_eql_neg_encF_N[of \<phi>, simplified]  
  using prv_imp_neg_encF_N_aux by auto 
  have 2: "prv (imp (cnj (PP \<langle>\<phi>\<rangle>) (PP \<langle>neg \<phi>\<rangle>)) 
                    (cnj (PP \<langle>\<phi>\<rangle>) ?j))"
  using 0 1 by (simp add:  prv_cnj_mono prv_imp_refl) 

  have "prv (imp (cnj (PP \<langle>\<phi>\<rangle>) (PP \<langle>neg \<phi>\<rangle>)) 
                 (cnj (PP \<langle>\<phi>\<rangle>) ?j))"  
    by (simp add: 2 prv_cnj_mono prv_imp_refl) 
  thus "prv (neg (cnj (PP \<langle>\<phi>\<rangle>) (PP \<langle>neg \<phi>\<rangle>)))" using 0  
    using num Var Variable PP cnj exi fls neg_def prv_prv_imp_trans  
    \<phi> neg   
    by (smt Encode.enc N encF Jeroslow_Diagonalization_axioms Jeroslow_Diagonalization_def 
          Ops in_num)
qed 

(* noContr is still stronger than the standard notion of proving consistency: *)

lemma noContr_implies_neg_PP_fls:
 assumes "noContr"
 shows "prv (neg (PP \<langle>fls\<rangle>))" 
proof-
  have "prv (neg (cnj (PP \<langle>fls\<rangle>) (PP \<langle>neg fls\<rangle>)))"
    using assms unfolding noContr_def by auto
  thus ?thesis  
  using Fvars_tru enc in_num tru_def PP PP_def fls imp HBL1 neg_def 
       prv_cnj_imp prv_fls prv_imp_com prv_imp_mp
  by (metis Encode.enc WRepr_Provability_axioms WRepr_Provability_def)
qed
 
corollary jcons_implies_neg_PP_fls:
assumes "prv jcons"
shows "prv (neg (PP \<langle>fls\<rangle>))"
by (simp add: assms noContr_implies_neg_PP_fls jcons_noContr)

(* However, unlike jcons, which seems to be quite a bit stronger, 
noContr is equivalent to the standard notion under a slightly 
stronger assumption than our WWHBL2, namely, a binary version of that: *)

lemma neg_PP_fls_implies_noContr:
 assumes WWHBL22: 
"\<And>\<phi> \<chi> \<psi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
   Fvars \<phi> = {} \<Longrightarrow> Fvars \<chi> = {} \<Longrightarrow> Fvars \<psi> = {} \<Longrightarrow>
   prv (imp \<phi> (imp \<chi> \<psi>)) \<Longrightarrow> prv (imp (PP \<langle>\<phi>\<rangle>) (imp (PP \<langle>\<chi>\<rangle>) (PP \<langle>\<psi>\<rangle>)))"
 assumes p: "prv (neg (PP \<langle>fls\<rangle>))" 
 shows "noContr"
unfolding noContr_def proof safe
  fix \<phi> assume \<phi>[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}"
  have 0: "prv (imp \<phi> (imp (neg \<phi>) fls))"  
    by (simp add: prv_imp_neg_fls)
  have 1: "prv (imp (PP \<langle>\<phi>\<rangle>) (imp (PP \<langle>neg \<phi>\<rangle>) (PP \<langle>fls\<rangle>)))"  
    using WWHBL22[OF _ _ _ _ _ _ 0] by auto
  show "prv (neg (cnj (PP \<langle>\<phi>\<rangle>) (PP \<langle>neg \<phi>\<rangle>)))" using 1 p 
    using num PP cnj fls neg_def prv_cnj_imp_monoR2 prv_prv_imp_trans
    using \<phi> enc neg subsetCE  
    by (smt Encode.enc WRepr_Provability_axioms WRepr_Provability_def in_num)
qed 

end \<comment> \<open>context Jeroslow_Godel_Second\<close>

 
 
end 

