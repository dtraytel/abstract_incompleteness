(* An abstract formulation and proof of the second incompleteness theorem, 
which assumes the provability predicate "prf" and its weak representation P, 
subject to Hilbert-Bernays-Loeb (HBL) conditions. 
(It does not assumes any notion of "proof of" predicate and its representation.)
Its proof is essentially performed in provability logic  *)

theory Derivability_Conditions imports Abstract_Representability
begin 

term WRepr_Provability

(* We assume all three derivability conditions: *)
locale Deriv_Cond = 
WRepr_Provability 
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv bprv
  enc 
  P
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and num 
and eql cnj imp all exi 
and prv bprv 
and enc ("\<langle>_\<rangle>")
and P 
+
assumes 
(* The second and third Hilbert-Bernays-Loeb (HBL) derivability conditions: *)
HBL2: "\<And>\<phi> \<chi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> Fvars \<chi> = {} \<Longrightarrow> 
  bprv (imp (cnj (PP \<langle>\<phi>\<rangle>) (PP \<langle>imp \<phi> \<chi>\<rangle>)) 
           (PP \<langle>\<chi>\<rangle>))"
and 
HBL3: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> bprv (imp (PP \<langle>\<phi>\<rangle>) (PP \<langle>PP \<langle>\<phi>\<rangle>\<rangle>))"
begin

(* Recall what the HBL1 condition says: *)
lemma HBL1_PP: "\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv \<phi> \<Longrightarrow> bprv (PP \<langle>\<phi>\<rangle>)" 
  unfolding PP_def using HBL1 .

(* The implicational form of HBL2 *)
lemma HBL2_imp: 
 "\<And>\<phi> \<chi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> Fvars \<chi> = {} \<Longrightarrow> 
  bprv (imp (PP \<langle>imp \<phi> \<chi>\<rangle>) (imp (PP \<langle>\<phi>\<rangle>) (PP \<langle>\<chi>\<rangle>)))"
using HBL2 by (simp add: B.prv_cnj_imp B.prv_imp_com)

(* ... and its weaker, detached version: *)
lemma HBL2_imp2: 
assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla" "Fvars \<phi> = {}" "Fvars \<chi> = {}"
assumes "bprv (PP \<langle>imp \<phi> \<chi>\<rangle>)"
shows "bprv (imp (PP \<langle>\<phi>\<rangle>) (PP \<langle>\<chi>\<rangle>))"
using assms by (meson HBL2_imp PP enc imp num B.prv_imp_mp subsetCE) 


end \<comment> \<open>Deriv_Cond\<close>

(*<*)
end
(*>*)


