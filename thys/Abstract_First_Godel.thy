theory Abstract_First_Godel imports Godel_Formula Standard_Model
begin 

(* Here we prove half of (the abstract version of) Godel's first theorem, 
which only needs the fixpoint property of the Godel formula *)

context Godel_Form 
begin

(* First the "direct", positive formulation: *)
lemma godel_first_theEasyHalf_pos: 
assumes "prv \<phi>G"   shows "prv fls"
proof-   
  have "prv (neg (PP \<langle>\<phi>G\<rangle>))" using prv_eqv_prv[OF _ _ assms prv_\<phi>G_eqv] by auto
  moreover 
  {have "bprv (PP \<langle>\<phi>G\<rangle>)" using HBL1[OF \<phi>G Fvars_\<phi>G assms] unfolding PP_def .
   from bprv_prv[OF _ _ this, simplified] have "prv (PP \<langle>\<phi>G\<rangle>)" . 
  }
  ultimately show ?thesis using PP prv_neg_fls by (meson \<phi>G enc in_num)
qed

(* Then the more standard counterpositive formulation: *)
corollary godel_first_theEasyHalf: 
"consistent \<Longrightarrow> \<not> prv \<phi>G"
using godel_first_theEasyHalf_pos unfolding consistent_def by auto
 
end \<comment> \<open>context Godel_Form\<close>

(* The other half needs explicit proofs: *)
context Godel_Form_Proofs begin
  
lemma godel_first_theHardHalf: 
assumes oc: "\<omega>consistent"
shows "\<not> prv (neg \<phi>G)"
proof
  assume pn: "prv (neg \<phi>G)"
  hence pnn: "prv (neg (neg (wrepr.PP \<langle>\<phi>G\<rangle>)))"  
    using prv_eqv_imp_transi num wrepr.PP \<phi>G fls neg neg_def prv_\<phi>G_eqv prv_eqv_sym
    by (metis (full_types) enc in_num)
  note c = \<omega>consistent_implies_consistent[OF oc] 
  have np: "\<not> prv \<phi>G" using pn c unfolding consistent_def3 by blast
  have "\<forall>p \<in> num. bprv (neg (PPf p \<langle>\<phi>G\<rangle>))" using not_prv_prv_neg_PPf[OF _ _ np] by auto
  hence 0: "\<forall>p \<in> num. prv (neg (PPf p \<langle>\<phi>G\<rangle>))" using not_prv_prv_neg_PPf[OF _ _ np]
    by (fastforce intro: bprv_prv)
  have "\<not> prv (neg (neg (exi yy (PPf (Var yy) \<langle>\<phi>G\<rangle>))))" using 0 oc unfolding \<omega>consistent_def by auto
  hence "\<not> prv (neg (neg (wrepr.PP \<langle>\<phi>G\<rangle>)))"
    unfolding wrepr.PP_def by (subst P_def) (simp add:  PPf_def2)
  thus False using pnn by auto
qed

theorem godel_first: 
assumes "\<omega>consistent"
shows "\<not> prv \<phi>G \<and> \<not> prv (neg \<phi>G)"
  using assms godel_first_theEasyHalf godel_first_theHardHalf \<omega>consistent_implies_consistent by blast

theorem godel_first_ex: 
assumes "\<omega>consistent"
shows "\<exists> \<phi>. \<phi> \<in> fmla \<and> \<not> prv \<phi> \<and> \<not> prv (neg \<phi>)" 
  using assms godel_first by (intro exI[of _ \<phi>G]) blast


end \<comment> \<open>context Godel_Form_Proofs\<close>


(* THE MODEL-THEORETIC VERSION *)


(********************************)
(* The truth of the Godel sentence \<phi>G in the standard model *)

locale Godel_Form_Proofs_Minimal_Truth = 
Godel_Form_Proofs 
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  fls 
  prv bprv 
  enc
  S 
  dsj 
  "proof" prfOf encPf 
  Pf
+
Minimal_Truth_Soundness
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  bprv
  isTrue
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and eql cnj imp all exi 
and fls
and dsj
and num
and prv bprv   
and enc ("\<langle>_\<rangle>")
and S 
and "proof" :: "'proof set" and prfOf encPf 
and Pf
and isTrue
begin   

(* Recall that consistent and \<omega>consistent refer to prv. *)

theorem isTrue_\<phi>G:
  assumes "consistent"
  shows "isTrue \<phi>G" 
proof-
  have "\<forall> n \<in> num. bprv (neg (PPf n \<langle>\<phi>G\<rangle>))" 
  using not_prv_prv_neg_PPf[OF _ _ godel_first_theEasyHalf[OF assms]] by auto
  hence "\<forall> n \<in> num. isTrue (neg (PPf n \<langle>\<phi>G\<rangle>))" by (auto intro: bprv_sound_isTrue)
  hence "isTrue (all yy (neg (PPf (Var yy) \<langle>\<phi>G\<rangle>)))" by (auto intro: isTrue_all)
  moreover have "isTrue (imp (all yy (neg (PPf (Var yy) \<langle>\<phi>G\<rangle>))) \<phi>G)"
  using bprv_eqv_all_not_PPf_imp_\<phi>G by (auto intro!: bprv_sound_isTrue) 
  ultimately show ?thesis by (rule isTrue_imp[rotated -2]) auto
qed



(* Now we have (for sound theories) the strong form of Godel's first, which 
concludes the truth of the Godel sentence \<phi>G: *)

theorem godel_first_strong: 
"\<omega>consistent \<Longrightarrow> \<not> prv \<phi>G \<and> \<not> prv (neg \<phi>G) \<and> isTrue \<phi>G"
  using godel_first isTrue_\<phi>G \<omega>consistent_implies_consistent by blast

theorem godel_first_strong_ex: 
"\<omega>consistent \<Longrightarrow> \<exists> \<phi>. \<phi> \<in> fmla \<and> \<not> prv \<phi> \<and> \<not> prv (neg \<phi>) \<and> isTrue \<phi>" 
  using godel_first_strong by (intro exI[of _ \<phi>G]) blast


end \<comment> \<open>context Godel_Form_Proofs_Minimal_Truth\<close>



(************************)
locale Godel_Form_Minimal_Truth_Soundness_HBL1iff_Compl_Pf = 
Godel_Form 
  var trm fmla Var num 
  FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  prv bprv 
  enc
  S 
  P 
+  
Minimal_Truth_Soundness_HBL1iff_Compl_Pf
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  enc
  prv bprv
  P
  isTrue
  Pf   
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and eql cnj imp all exi 
and fls
and dsj
and num
and prv bprv 
and enc ("\<langle>_\<rangle>")
and S 
and isTrue
and P
and Pf



locale Godel_Form_Minimal_Truth_Soundness_HBL1iff_Compl_Pf_Compl_NegPf = 
Godel_Form_Minimal_Truth_Soundness_HBL1iff_Compl_Pf 
  var trm fmla Var FvarsT substT Fvars subst  
  eql cnj imp all exi 
  fls
  dsj
  num
  prv bprv
  enc 
  S 
  isTrue
  P
  Pf
+
Minimal_Truth_Soundness_HBL1iff_Compl_Pf_Compl_NegPf
  var trm fmla Var FvarsT substT Fvars subst  
  eql cnj imp all exi 
  fls
  dsj
  num
  enc  
  prv bprv
  P
  isTrue
  Pf
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and eql cnj imp all exi 
and fls
and dsj
and num
and prv bprv  
and enc ("\<langle>_\<rangle>")
and S 
and isTrue
and P
and Pf 
+
assumes prv_\<omega>consistent: "\<omega>consistent"

(* Semantic Godel's first, Godel-style, second variant 
... established as a sublocale statement *)
sublocale 
  Godel_Form_Minimal_Truth_Soundness_HBL1iff_Compl_Pf_Compl_NegPf < 
  recover_proofs: Godel_Form_Proofs_Minimal_Truth 
  where prfOf = prfOf and "proof" = "proof" and encPf = encPf 
  and prv = prv and bprv = bprv
  by standard  

(* ... and here is the explicit statement, inside the locale that 
provides all the assumptions *)
context Godel_Form_Minimal_Truth_Soundness_HBL1iff_Compl_Pf_Compl_NegPf begin
thm recover_proofs.godel_first_strong 

end


(* *)


(* THE CLASSICAL VERSION: *)
(**************************************)
(* To further obtain that the Godel formula is true, Classic takes advantage of Minimal_Truth_Soundness 
(w.r.t. a standard model) 
together with the fact that the truth of P \<langle>\<phi>\<rangle> implies the provability of \<phi>: 
*)

locale Godel_Form_Classical_HBL1_rev_prv =  
Godel_Form
  var trm fmla Var num FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  prv bprv 
  enc 
  S 
  P
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var num FvarsT substT Fvars subst
and eql cnj imp all exi
and fls
and prv bprv 
and enc ("\<langle>_\<rangle>")
and S
and P
+
assumes 
(*NB: we don't really need to assume classical reasoning 
(double negation) all throughout, 
but only for the provability predicate: *)
classical_P_prv: "\<And> \<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> let PP = (\<lambda>t. subst P t xx) in 
  prv (neg (neg (PP \<langle>\<phi>\<rangle>))) \<Longrightarrow> prv (PP \<langle>\<phi>\<rangle>)"
and 
HBL1_rev_prv: "\<And> \<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv (PP \<langle>\<phi>\<rangle>) \<Longrightarrow> prv \<phi>"
begin

lemma HBL1_rev: 
  assumes f: "\<phi> \<in> fmla" and fv: "Fvars \<phi> = {}" and bp: "bprv (PP \<langle>\<phi>\<rangle>)"
  shows "prv \<phi>"
  using assms by (auto intro!: HBL1_rev_prv bprv_prv[OF _ _ bp]) 

lemma classical_PP_prv: "\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv (neg (neg (PP \<langle>\<phi>\<rangle>))) \<Longrightarrow> prv (PP \<langle>\<phi>\<rangle>)"
  using classical_P_prv unfolding PP_def by auto

lemma HBL1_iff: "\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> bprv (PP \<langle>\<phi>\<rangle>) \<longleftrightarrow> prv \<phi>"
  using HBL1 HBL1_rev unfolding PP_def by auto

lemma HBL1_iff_prv: "\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv (PP \<langle>\<phi>\<rangle>) \<longleftrightarrow> prv \<phi>"
  by (meson HBL1_PP HBL1_rev_prv PP d_dwf.bprv_prv' enc in_num)
  
lemma godel_first_theHardHalf_pos: 
assumes "prv (neg \<phi>G)"   shows "prv fls"
proof-
  have "prv (neg (neg (PP \<langle>\<phi>G\<rangle>)))"  
    using assms neg_def prv_\<phi>G_eqv prv_eqv_imp_transi_rev by fastforce
  hence "prv (PP \<langle>\<phi>G\<rangle>)" using classical_PP_prv by auto 
  hence "prv \<phi>G" using Fvars_\<phi>G HBL1_rev_prv by blast
  thus ?thesis using assms prv_neg_fls by blast  
qed

(* Then the more standard counterpositive formulation: *)
corollary godel_first_theHardHalf: 
"consistent \<Longrightarrow> \<not> prv (neg \<phi>G)"
  using godel_first_theHardHalf_pos unfolding consistent_def by auto

theorem godel_first_classic: 
assumes "consistent"
shows "\<not> prv \<phi>G \<and> \<not> prv (neg \<phi>G)"
  using assms godel_first_theEasyHalf godel_first_theHardHalf by blast

theorem godel_first_classic_ex: 
assumes "consistent"
shows "\<exists> \<phi>. \<phi> \<in> fmla \<and> \<not> prv \<phi> \<and> \<not> prv (neg \<phi>)" 
  using assms godel_first_classic by (intro exI[of _ \<phi>G]) blast

end \<comment> \<open>Godel_Form_Classical_HBL1_rev_prv\<close>

locale Godel_Form_Classical_HBL1_rev_prv_Minimal_Truth_Soundness_TIP =  
Godel_Form_Classical_HBL1_rev_prv 
  var trm fmla Var num FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  prv bprv 
  enc 
  S 
  P
+
Minimal_Truth_Soundness 
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  bprv 
  isTrue
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var num FvarsT substT Fvars subst
and eql cnj dsj imp all exi
and fls
and prv bprv
and enc ("\<langle>_\<rangle>")
and S
and P
and isTrue
+
assumes 
(* Truth of \<phi> implies provability of (the internal representation of) \<phi> *)
TIP: "\<And> \<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> 
  let PP = (\<lambda>t. subst P t xx) in 
  isTrue (PP \<langle>\<phi>\<rangle>) \<Longrightarrow> prv \<phi>"
begin 

lemma TIP_PP: "\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> isTrue (PP \<langle>\<phi>\<rangle>) \<Longrightarrow> prv \<phi>"
  using TIP unfolding PP_def by auto

theorem isTrue_\<phi>G: 
  assumes consistent 
  shows "isTrue \<phi>G" 
proof-
  {assume "\<not> isTrue \<phi>G"
   hence 1: "isTrue (neg \<phi>G)" using isTrue_neg by fastforce
   have "bprv (imp (neg \<phi>G) (neg (neg (PP \<langle>\<phi>G\<rangle>))))"
   by (auto simp add: bprv_\<phi>G_eqv B.prv_imp_eqvER B.prv_imp_neg_rev)   
   from prv_imp_implies_isTrue[OF _ _ _ _ this 1, simplified]
   have "isTrue (neg (neg (PP \<langle>\<phi>G\<rangle>)))" .
   from isTrue_neg_neg[OF _ _ this, simplified] have "isTrue (PP \<langle>\<phi>G\<rangle>)" .
   hence "prv \<phi>G" using assms TIP_PP by auto 
   hence False using godel_first_classic assms by auto
  }
  thus ?thesis by auto
qed

theorem godel_first_classic_strong: "consistent \<Longrightarrow> \<not> prv \<phi>G \<and> \<not> prv (neg \<phi>G) \<and> isTrue \<phi>G"
  using godel_first_classic isTrue_\<phi>G by simp

theorem godel_first_classic_strong_ex: 
"consistent \<Longrightarrow> \<exists> \<phi>. \<phi> \<in> fmla \<and> \<not> prv \<phi> \<and> \<not> prv (neg \<phi>) \<and> isTrue \<phi>" 
  using godel_first_classic_strong by (intro exI[of _ \<phi>G]) blast 

end \<comment> \<open>locale Godel_Form_Classical_HBL1_rev_prv_Minimal_Truth_Soundness_TIP\<close>

context Godel_Form
begin
print_context

end

locale Godel_Form_Minimal_Truth_Soundness_HBL1iff_prv_Compl_Pf_Classical = 
Godel_Form 
  var trm fmla Var num FvarsT substT Fvars subst  
  eql cnj imp all exi 
  fls 
  prv bprv 
  enc 
  S  
  P 
+
Minimal_Truth_Soundness_HBL1iff_prv_Compl_Pf_Classical
  var trm fmla Var FvarsT substT Fvars subst  
  eql cnj imp all exi 
  fls
  dsj
  num
  enc  
  prv bprv
  P
  isTrue
  Pf
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and eql cnj imp all exi 
and fls
and dsj
and num
and prv bprv  
and enc ("\<langle>_\<rangle>")
and S 
and isTrue
and P
and Pf 


sublocale Godel_Form_Minimal_Truth_Soundness_HBL1iff_prv_Compl_Pf_Classical < 
  recover_proofs: Godel_Form_Classical_HBL1_rev_prv_Minimal_Truth_Soundness_TIP where prv = prv and bprv = bprv
proof (standard, goal_cases classical rev_rpv TIPf)
  case (classical \<phi>)
  then show ?case using HBL1_iff classical_P by (simp add: mts_prv_mts.PP_deff)
next
  case (rev_rpv \<phi>)
  then show ?case using HBL1_iff_prv PP_def by simp
next
  case (TIPf \<phi>)
  then show ?case using classical_P by (simp add: SS_def PP_def mts_prv_mts.TIP)
qed

context Godel_Form_Minimal_Truth_Soundness_HBL1iff_prv_Compl_Pf_Classical begin
thm recover_proofs.godel_first_classic_strong
end (* context Godel_Form_Minimal_Truth_Soundness_HBL1iff_Compl_Pf_Classical *)

end
