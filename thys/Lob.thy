(* We have set up the formalization of Godel's first (easy half) and Godel's second 
so that the following generalization, leading to Lob's theorem, are essnetially 
verbatim modifications of Godel's proofs, replacing negation with "implies \<phi>". 
*)

theory Lob imports Lob_Formula Derivability_Conditions
begin 

(* We assume all three derivability conditions: *)
locale Lob_Assumptions = 
Deriv_Cond
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv bprv
  enc
  P
+
Lob_Form
  var trm fmla Var num FvarsT substT Fvars subst
  eql cnj imp all exi 
  prv bprv
  enc
  S
  P
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var num FvarsT substT Fvars subst  
and eql cnj imp all exi 
and prv bprv
and enc ("\<langle>_\<rangle>")
and S
and P 
begin

(* Generalization of godel_first_theEasyHalf_pos, replacing fls with a sentence \<phi>: *)
lemma lob_aux_prv: 
assumes \<phi>[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}" and p: "prv (\<phi>L \<phi>)"   
shows "prv \<phi>"
proof-  
  have "prv (imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>)" using assms prv_eqv_prv[OF _ _ p prv_\<phi>L_eqv] by auto
  moreover have "bprv (PP \<langle>\<phi>L \<phi>\<rangle>)" using HBL1[OF \<phi>L[OF \<phi>] _ p] unfolding PP_def by simp
  from bprv_prv[OF _ _ this, simplified] have "prv (PP \<langle>\<phi>L \<phi>\<rangle>)" .
  ultimately show ?thesis using PP \<phi>L by (meson assms enc in_num prv_imp_mp)
qed

lemma lob_aux_bprv: 
assumes \<phi>[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}" and p: "bprv (\<phi>L \<phi>)"   
shows "bprv \<phi>"
proof- 
  note pp = bprv_prv[OF _ _ p, simplified] 
  have "bprv (imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>)" using assms B.prv_eqv_prv[OF _ _ p bprv_\<phi>L_eqv] by auto
  moreover have "bprv (PP \<langle>\<phi>L \<phi>\<rangle>)" using HBL1[OF \<phi>L[OF \<phi>] _ pp] unfolding PP_def by simp
  ultimately show ?thesis using PP \<phi>L by (meson assms enc in_num B.prv_imp_mp)
qed

(* Generalization of P_G, the main lemma used for Godel's second: *)
lemma P_L:
assumes \<phi>[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}"
shows "bprv (imp (PP \<langle>\<phi>L \<phi>\<rangle>) (PP \<langle>\<phi>\<rangle>))"
proof-
  have 0: "prv (imp (\<phi>L \<phi>) (imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>))" 
    using prv_\<phi>L_eqv by (intro prv_imp_eqvEL) auto
  have 1: "bprv (PP \<langle>imp (\<phi>L \<phi>) (imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>)\<rangle>)"
    using HBL1_PP[OF _ _ 0] by simp   
  have 2: "bprv (imp (PP \<langle>\<phi>L \<phi>\<rangle>) (PP \<langle>imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>\<rangle>))" 
  using HBL2_imp2[OF _ _ _ _ 1] by simp
  have 3: "bprv (imp (PP \<langle>\<phi>L \<phi>\<rangle>) (PP \<langle>PP \<langle>\<phi>L \<phi>\<rangle>\<rangle>))" 
    using HBL3[OF \<phi>L[OF \<phi>] _] by simp
  have 23: "bprv (imp (PP \<langle>\<phi>L \<phi>\<rangle>)
                      (cnj (PP \<langle>PP \<langle>\<phi>L \<phi>\<rangle>\<rangle>) 
                           (PP \<langle>imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>\<rangle>)))"
  using B.prv_imp_cnj[OF _ _ _ 3 2] by simp
  have 4: "bprv (imp (cnj (PP \<langle>PP \<langle>\<phi>L \<phi>\<rangle>\<rangle>) 
                          (PP \<langle>imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>\<rangle>)) 
                    (PP \<langle>\<phi>\<rangle>))" 
    using HBL2[of "PP \<langle>\<phi>L \<phi>\<rangle>" \<phi>] by simp
  show ?thesis using B.prv_prv_imp_trans[OF _ _ _ 23 4] by simp
qed  

(* Finally, Lob's theorem, which generalizes the positive formulation Godel's second theorem 
(godel_second): *)

(* In our two-relation framework, we get two variants of Lob's theorem.
A stronger variant, assuming prv and proving bprv, seems impossible. 
*)
theorem lob_bprv:
assumes \<phi>[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}" and p: "bprv (imp (PP \<langle>\<phi>\<rangle>) \<phi>)"
shows "bprv \<phi>"
proof- 
  have "bprv (imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>)"
    by (rule B.prv_prv_imp_trans[OF _ _ _ P_L p]) auto
  hence "bprv (\<phi>L \<phi>)"
    by (rule B.prv_eqv_prv_rev[OF _ _ _ bprv_\<phi>L_eqv, rotated 2]) auto
  thus ?thesis using lob_aux_bprv[OF \<phi>] by simp
qed 

theorem lob_prv:
assumes \<phi>[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}" and p: "prv (imp (PP \<langle>\<phi>\<rangle>) \<phi>)"
shows "prv \<phi>"
proof- 
  note PL = bprv_prv[OF _ _ P_L, simplified]
  have "prv (imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>)" 
    by (rule prv_prv_imp_trans[OF _ _ _ PL p]) auto 
  hence "prv (\<phi>L \<phi>)"
    by (rule prv_eqv_prv_rev[OF _ _ _ prv_\<phi>L_eqv, rotated 2]) auto
  thus ?thesis using lob_aux_prv[OF \<phi>] by simp
qed 

(* We could have of course infered Godel's first-easyHalf and Godel's second from 
these more general versions, but we leave the original arguments as they are more 
instructive. 
*)

end \<comment> \<open>Lob_Assumptions\<close>
 
end 



