(* Natural deduction system built from the Hilbert-style system: *)

theory Natural_Deduction
imports Abstract.Deduction
begin

context Deduct_with_False_Disj
begin

(* Natural deduction style proving: *)
definition nprv :: "'fmla set \<Rightarrow> 'fmla \<Rightarrow> bool" where
"nprv F \<phi> \<equiv> prv (imp (scnj F) \<phi>)"

lemma nprv_hyp:
"\<phi> \<in> F \<Longrightarrow> F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> nprv F \<phi>"
unfolding nprv_def
by (simp add: prv_scnj_imp_in subset_iff)

(* Structural rules for nprv: *)
lemma prv_nprv0I: "prv \<phi> \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> nprv {} \<phi>"
unfolding nprv_def by (simp add: prv_imp_triv)

lemma prv_nprv_emp: "\<phi> \<in> fmla \<Longrightarrow> prv \<phi> \<longleftrightarrow> nprv {} \<phi>"
using prv_nprv0I unfolding nprv_def
by auto (meson bot.extremum equals0D exists_no_Fvars finite.simps prv_imp_mp prv_imp_scnj scnj)

lemma nprv_mono:
assumes "nprv G \<phi>"
and "F \<subseteq> fmla" "finite F" "G \<subseteq> F" "\<phi> \<in> fmla"
shows "nprv F \<phi>"
using assms unfolding nprv_def
by (meson order_trans prv_prv_imp_trans prv_scnj_mono rev_finite_subset scnj)

lemma nprv_cut:
assumes "nprv F \<phi>" and "nprv (insert \<phi> F) \<psi>"
and "F \<subseteq> fmla" "finite F"  "\<phi> \<in> fmla"  "\<psi> \<in> fmla"
shows "nprv F \<psi>"
using assms unfolding nprv_def
by (metis (full_types) cnj finite.insertI
  insert_subset prv_imp_cnj prv_imp_cnj_scnj prv_imp_refl prv_prv_imp_trans scnj)

lemma nprv_strong_cut2:
"nprv F \<phi>1 \<Longrightarrow> nprv (insert \<phi>1 F) \<phi>2 \<Longrightarrow> nprv (insert \<phi>2 (insert \<phi>1 F)) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F \<psi>"
by (meson finite.insertI insert_subsetI nprv_cut)

lemma nprv_cut2:
"nprv F \<phi>1 \<Longrightarrow> nprv F \<phi>2 \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv (insert \<phi>2 (insert \<phi>1 F)) \<psi> \<Longrightarrow> nprv F \<psi>"
by (meson finite.insertI insert_subsetI nprv_mono nprv_strong_cut2 subset_insertI)


(* Useful for fine control of the eigenformula: *)
lemma nprv_insertShiftI:
"nprv (insert \<phi>1 (insert \<phi>2 F)) \<psi> \<Longrightarrow> nprv (insert \<phi>2 (insert \<phi>1 F)) \<psi>"
by (simp add: insert_commute)

lemma nprv_insertShift2I:
"nprv (insert \<phi>3 (insert \<phi>1 (insert \<phi>2 F))) \<psi> \<Longrightarrow> nprv (insert \<phi>1 (insert \<phi>2 (insert \<phi>3 F))) \<psi>"
by (simp add: insert_commute)

(* Going back from nrpv to prv for simple goals
(to be done by the brute-force of the huge amount of facts available about prv):  *)
lemma prv_nprvI: "prv \<phi> \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> nprv F \<phi>"
using prv_nprv0I
by (simp add: nprv_def prv_imp_triv)

thm prv_nprv0I

lemma prv_nprv1I:
assumes "\<phi> \<in> fmla" "\<psi> \<in> fmla" and "prv (imp \<phi> \<psi>)"
shows "nprv {\<phi>} \<psi>"
using assms unfolding nprv_def by (simp add: prv_scnj_imp)

lemma prv_nprv2I:
assumes "prv (imp \<phi>1 (imp \<phi>2 \<psi>))" "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla" "\<psi> \<in> fmla"
shows "nprv {\<phi>1,\<phi>2} \<psi>"
using assms unfolding nprv_def
by (meson cnj empty_subsetI finite.simps insert_subsetI prv_cnj_imp_monoR2 prv_prv_imp_trans prv_scnj2_imp_cnj scnj)

lemma nprv_prvI: "nprv {} \<phi> \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> prv \<phi>"
using prv_nprv_emp by auto

lemma nprv_clear: "nprv {} \<phi> \<Longrightarrow> F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> nprv F \<phi>"
by (rule nprv_mono) auto

lemma nprv_cut_set:
assumes F:  "finite F" "F \<subseteq> fmla" and G: "finite G" "G \<subseteq> fmla" "\<chi> \<in> fmla"
and n1: "\<And> \<psi>. \<psi> \<in> G \<Longrightarrow> nprv F \<psi>" and n2: "nprv (G \<union> F) \<chi>"
shows "nprv F \<chi>"
using G F n1 n2 proof(induction arbitrary: F \<chi>)
  case (insert \<psi> G F \<chi>)
  hence 0: "nprv F \<psi>" by auto
  have 1: "nprv (insert \<psi> F) \<chi>"  apply(rule insert.IH) using insert.prems
  by auto (meson finite.insertI insert_subset nprv_mono subset_eq)
  show ?case apply(rule nprv_cut[OF 0 1]) using insert.prems by auto
qed(insert nprv_clear, auto)

lemma nprv_clear2_1:
"nprv {\<phi>2} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear2_2:
"nprv {\<phi>1} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear3_1:
"nprv {\<phi>2,\<phi>3} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear3_2:
"nprv {\<phi>1,\<phi>3} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear3_3:
"nprv {\<phi>1,\<phi>2} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear4_1:
"nprv {\<phi>2,\<phi>3,\<phi>4} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<phi>4 \<in> fmla \<Longrightarrow>\<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear4_2:
"nprv {\<phi>1,\<phi>3,\<phi>4} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<phi>4 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear4_3:
"nprv {\<phi>1,\<phi>2,\<phi>4} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<phi>4 \<in> fmla \<Longrightarrow>\<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear4_4:
"nprv {\<phi>1,\<phi>2,\<phi>3} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<phi>4 \<in> fmla \<Longrightarrow>\<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear5_1:
"nprv {\<phi>2,\<phi>3,\<phi>4,\<phi>5} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<phi>4 \<in> fmla \<Longrightarrow> \<phi>5 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4,\<phi>5} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear5_2:
"nprv {\<phi>1,\<phi>3,\<phi>4,\<phi>5} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<phi>4 \<in> fmla \<Longrightarrow> \<phi>5 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4,\<phi>5} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear5_3:
"nprv {\<phi>1,\<phi>2,\<phi>4,\<phi>5} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<phi>4 \<in> fmla \<Longrightarrow> \<phi>5 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4,\<phi>5} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear5_4:
"nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>5} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<phi>4 \<in> fmla \<Longrightarrow> \<phi>5 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4,\<phi>5} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear5_5:
"nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<phi>4 \<in> fmla \<Longrightarrow> \<phi>5 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4,\<phi>5} \<psi>"
by (rule nprv_mono) auto

(* Substitutivity of nprv: *)
lemma nprv_subst:
assumes "x \<in> var" "t \<in> trm" "\<psi> \<in> fmla" "finite F" "F \<subseteq> fmla"
and 1: "nprv F \<psi>"
shows "nprv ((\<lambda>\<phi>. subst \<phi> t x) ` F) (subst \<psi> t x)"
using assms unfolding nprv_def
apply(intro prv_prv_imp_trans[OF _ _ _ prv_subst_scnj_imp])
using prv_subst[OF _ _ _ 1[unfolded nprv_def]] by auto

lemma nprv_subst_fresh:
assumes 0: "x \<in> var" "t \<in> trm" "\<psi> \<in> fmla" "finite F" "F \<subseteq> fmla"
"nprv F \<psi>" and 1: "x \<notin> \<Union> (Fvars ` F)"
shows "nprv F (subst \<psi> t x)"
proof-
  have 2: "(\<lambda>\<phi>. subst \<phi> t x) ` F = F" unfolding image_def using assms by force
  show ?thesis using nprv_subst[OF 0] unfolding 2 .
qed

lemma nprv_subst_rev:
assumes 0: "x \<in> var" "y \<in> var" "\<psi> \<in> fmla" "finite F" "F \<subseteq> fmla"
and f: "y = x \<or> (y \<notin> Fvars \<psi> \<and> y \<notin> \<Union> (Fvars ` F))"
and 1: "nprv ((\<lambda>\<phi>. subst \<phi> (Var y) x) ` F) (subst \<psi> (Var y) x)"
shows "nprv F \<psi>"
proof-
  have 0: "subst (subst \<psi> (Var y) x) (Var x) y = \<psi>"
  using assms by (auto simp: subst_compose_eq_or)
  have "nprv ((\<lambda>\<phi>. subst \<phi> (Var x) y) ` (\<lambda>\<phi>. subst \<phi> (Var y) x) ` F) \<psi>"
  apply(subst 0[symmetric]) apply(rule nprv_subst) using assms by auto
  moreover
  have "prv (imp (scnj F)
                 (scnj ((\<lambda>\<phi>. subst \<phi> (Var x) y) ` (\<lambda>\<phi>. subst \<phi> (Var y) x) ` F)))"
  apply(rule prv_scnj_mono_imp) using assms apply (fastforce,fastforce,fastforce,fastforce)
  apply safe subgoal for _ _ \<phi> apply(rule bexI[of _ \<phi>]) apply(rule prv_imp_refl2)
  using assms by (auto simp: subst_compose_eq_or) .
  ultimately show ?thesis unfolding nprv_def apply- apply(rule prv_prv_imp_trans) using assms by auto
qed

lemma nprv_psubst:
assumes 0: "snd ` set txs \<subseteq> var" "fst ` set txs \<subseteq> trm" "\<psi> \<in> fmla" "finite F" "F \<subseteq> fmla"
"distinct (map snd txs)"
and 1: "nprv F \<psi>"
shows "nprv ((\<lambda>\<phi>. psubst \<phi> txs) ` F) (psubst \<psi> txs)"
using assms unfolding nprv_def
apply(intro prv_prv_imp_trans[OF _ _ _ prv_psubst_scnj_imp])
using 0 prv_psubst[OF _ _ _ 1[unfolded nprv_def]]
apply(auto intro!: psubst) by (metis psubst_imp scnj)


(* Introduction and elimination rules for nprv: *)
(* We systematically leave the side-conditions at the end, to simplify reasoning *)
lemma nprv_impI:
"nprv (insert \<phi> F) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F (imp \<phi> \<psi>)"
unfolding nprv_def
by (metis cnj finite.insertI insert_subset prv_cnj_imp prv_imp_cnj_scnj prv_imp_com prv_prv_imp_trans scnj)

lemma nprv_impI_rev:
assumes "nprv F (imp \<phi> \<psi>)"
and "F \<subseteq> fmla" and "finite F" and "\<phi> \<in> fmla" and "\<psi> \<in> fmla"
shows "nprv (insert \<phi> F) \<psi>"
using assms unfolding nprv_def
by (metis cnj finite.insertI insert_subset prv_cnj_imp_monoR2 prv_eqv_imp_transi
    prv_eqv_scnj_insert prv_imp_com scnj)

lemma nprv_impI_rev2:
assumes "nprv F (imp \<phi> \<psi>)" and G: "insert \<phi> F \<subseteq> G"
and "G \<subseteq> fmla" and "finite G" and "\<phi> \<in> fmla" and "\<psi> \<in> fmla"
shows "nprv G \<psi>"
apply(rule nprv_mono[of "insert \<phi> F"])
using assms nprv_impI_rev apply simp_all
by (meson order_trans rev_finite_subset)

lemma nprv_mp:
"nprv F (imp \<phi> \<psi>) \<Longrightarrow> nprv F \<phi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F \<psi>"
unfolding nprv_def
by (metis (full_types) cnj prv_cnj_imp_monoR2 prv_imp_cnj prv_imp_refl prv_prv_imp_trans scnj)

lemma nprv_impE:
"nprv F (imp \<phi> \<psi>) \<Longrightarrow> nprv F \<phi> \<Longrightarrow>  nprv (insert \<psi> F) \<chi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow>
 nprv F \<chi>"
using nprv_cut nprv_mp by blast

lemmas nprv_impE0 = nprv_impE[OF nprv_hyp _ _, simped]
lemmas nprv_impE1 = nprv_impE[OF _ nprv_hyp _, simped]
lemmas nprv_impE2 = nprv_impE[OF _ _ nprv_hyp, simped]
lemmas nprv_impE01 = nprv_impE[OF nprv_hyp nprv_hyp _, simped]
lemmas nprv_impE02 = nprv_impE[OF nprv_hyp _ nprv_hyp, simped]
lemmas nprv_impE12 = nprv_impE[OF _ nprv_hyp nprv_hyp, simped]
lemmas nprv_impE012 = nprv_impE[OF nprv_hyp nprv_hyp nprv_hyp, simped]


lemma nprv_cnjI:
"nprv F \<phi> \<Longrightarrow> nprv F \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F (cnj \<phi> \<psi>)"
unfolding nprv_def by (simp add: prv_imp_cnj)

lemma nprv_cnjE:
"nprv F (cnj \<phi>1 \<phi>2) \<Longrightarrow> nprv (insert \<phi>1 (insert \<phi>2 F)) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F \<psi>"
unfolding nprv_def
by (metis cnj nprv_cut2 nprv_def prv_imp_cnjL prv_imp_cnjR prv_prv_imp_trans scnj)

lemmas nprv_cnjE0 = nprv_cnjE[OF nprv_hyp _, simped]
lemmas nprv_cnjE1 = nprv_cnjE[OF _ nprv_hyp, simped]
lemmas nprv_cnjE01 = nprv_cnjE[OF nprv_hyp nprv_hyp, simped]

lemma nprv_dsjIL:
"nprv F \<phi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F (dsj \<phi> \<psi>)"
unfolding nprv_def by (meson dsj prv_dsj_impL prv_prv_imp_trans scnj)

lemma nprv_dsjIR:
"nprv F \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F (dsj \<phi> \<psi>)"
unfolding nprv_def by (meson dsj prv_dsj_impR prv_prv_imp_trans scnj)

lemma nprv_dsjE:
assumes "nprv F (dsj \<phi> \<psi>)"
and "nprv (insert \<phi> F) \<chi>" "nprv (insert \<psi> F) \<chi>"
and "F \<subseteq> fmla" "finite F" "\<phi> \<in> fmla" "\<psi> \<in> fmla" "\<chi> \<in> fmla"
shows "nprv F \<chi>"
proof-
  have "nprv F (imp (dsj \<phi> \<psi>) \<chi>)"
    by (meson assms dsj imp nprv_def nprv_impI prv_imp_com prv_imp_dsjEE scnj)
  hence "nprv (insert (dsj \<phi> \<psi>) F) \<chi>" using assms
    by (simp add: nprv_impI_rev)
  thus ?thesis using assms by (meson dsj nprv_cut)
qed

lemmas nprv_dsjE0 = nprv_dsjE[OF nprv_hyp _ _, simped]
lemmas nprv_dsjE1 = nprv_dsjE[OF _ nprv_hyp _, simped]
lemmas nprv_dsjE2 = nprv_dsjE[OF _ _ nprv_hyp, simped]
lemmas nprv_dsjE01 = nprv_dsjE[OF nprv_hyp nprv_hyp _, simped]
lemmas nprv_dsjE02 = nprv_dsjE[OF nprv_hyp _ nprv_hyp, simped]
lemmas nprv_dsjE12 = nprv_dsjE[OF _ nprv_hyp nprv_hyp, simped]
lemmas nprv_dsjE012 = nprv_dsjE[OF nprv_hyp nprv_hyp nprv_hyp, simped]

lemma nprv_flsE: "nprv F fls \<Longrightarrow> F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow>  nprv F \<phi>"
unfolding nprv_def using prv_prv_imp_trans scnj by blast

lemmas nprv_flsE0 = nprv_flsE[OF nprv_hyp, simped]

lemma nprv_truI: "F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> nprv F tru"
unfolding nprv_def by (simp add: prv_imp_tru)

lemma nprv_negI:
"nprv (insert \<phi> F) fls \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow>
 nprv F (neg \<phi>)"
unfolding neg_def by (auto intro: nprv_impI)

lemma nprv_neg_fls:
"nprv F (neg \<phi>) \<Longrightarrow> nprv F \<phi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F fls"
unfolding neg_def using nprv_mp by blast

lemma nprv_negE:
"nprv F (neg \<phi>) \<Longrightarrow> nprv F \<phi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F \<psi>"
using nprv_flsE nprv_neg_fls by blast

lemmas nprv_negE0 = nprv_negE[OF nprv_hyp _, simped]
lemmas nprv_negE1 = nprv_negE[OF _ nprv_hyp, simped]
lemmas nprv_negE01 = nprv_negE[OF nprv_hyp nprv_hyp, simped]

lemma nprv_scnjI:
"(\<And> \<psi>. \<psi> \<in> G \<Longrightarrow> nprv F \<psi>) \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> G \<subseteq> fmla \<Longrightarrow> finite G \<Longrightarrow>
 nprv F (scnj G)"
unfolding nprv_def by (simp add: prv_imp_scnj)

lemma nprv_scnjE:
"nprv F (scnj G) \<Longrightarrow> nprv (G \<union> F) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> G \<subseteq> fmla \<Longrightarrow> finite G \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F \<psi>"
apply(rule nprv_cut_set)
by auto (meson nprv_def prv_prv_imp_trans prv_scnj_imp_in scnj subset_eq)

lemmas nprv_scnjE0 = nprv_scnjE[OF nprv_hyp _, simped]
lemmas nprv_scnjE1 = nprv_scnjE[OF _ nprv_hyp, simped]
lemmas nprv_scnjE01 = nprv_scnjE[OF nprv_hyp nprv_hyp, simped]

lemma nprv_lcnjI:
"(\<And> \<psi>. \<psi> \<in> set \<psi>s \<Longrightarrow> nprv F \<psi>) \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> set \<psi>s \<subseteq> fmla \<Longrightarrow>
 nprv F (lcnj \<psi>s)"
unfolding nprv_def by (simp add: prv_imp_lcnj)

lemma nprv_lcnjE:
"nprv F (lcnj \<phi>s) \<Longrightarrow> nprv (set \<phi>s \<union> F) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> set \<phi>s \<subseteq> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F \<psi>"
apply(rule nprv_cut_set)
by auto (meson lcnj nprv_def prv_lcnj_imp_in prv_prv_imp_trans scnj subsetCE)

lemmas nprv_lcnjE0 = nprv_lcnjE[OF nprv_hyp _, simped]
lemmas nprv_lcnjE1 = nprv_lcnjE[OF _ nprv_hyp, simped]
lemmas nprv_lcnjE01 = nprv_lcnjE[OF nprv_hyp nprv_hyp, simped]

lemma nprv_sdsjI:
"nprv F \<phi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> G \<subseteq> fmla \<Longrightarrow> finite G \<Longrightarrow> \<phi> \<in> G \<Longrightarrow>
 nprv F (sdsj G)"
unfolding nprv_def by (simp add: prv_imp_sdsj)

lemma nprv_sdsjE:
assumes "nprv F (sdsj G)"
and "\<And> \<psi>. \<psi> \<in> G \<Longrightarrow> nprv (insert \<psi> F) \<chi>"
and "F \<subseteq> fmla" "finite F" "G \<subseteq> fmla" "finite G" "\<chi> \<in> fmla"
shows "nprv F \<chi>"
proof-
  have 0: "prv (imp (sdsj G) (imp (scnj F) \<chi>))"
    apply(rule prv_sdsj_imp) using assms
    by auto (meson nprv_def nprv_impI prv_imp_com scnj set_rev_mp)
  hence "nprv F (imp (sdsj G) \<chi>)"
    by (simp add: 0 assms nprv_def prv_imp_com)
  thus ?thesis using assms nprv_mp by blast
qed

lemmas nprv_sdsjE0 = nprv_sdsjE[OF nprv_hyp _, simped]
lemmas nprv_sdsjE1 = nprv_sdsjE[OF _ nprv_hyp, simped]
lemmas nprv_sdsjE01 = nprv_sdsjE[OF nprv_hyp nprv_hyp, simped]

lemma nprv_ldsjI:
"nprv F \<phi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> set \<phi>s \<subseteq> fmla \<Longrightarrow>  \<phi> \<in> set \<phi>s \<Longrightarrow>
 nprv F (ldsj \<phi>s)"
unfolding nprv_def by(simp add: prv_imp_ldsj)

lemma nprv_ldsjE:
assumes "nprv F (ldsj \<psi>s)"
and "\<And> \<psi>. \<psi> \<in> set \<psi>s \<Longrightarrow> nprv (insert \<psi> F) \<chi>"
and "F \<subseteq> fmla" "finite F" "set \<psi>s \<subseteq> fmla"  "\<chi> \<in> fmla"
shows "nprv F \<chi>"
proof-
  have 0: "prv (imp (ldsj \<psi>s) (imp (scnj F) \<chi>))"
    apply(rule prv_ldsj_imp) using assms
    by auto (meson nprv_def nprv_impI prv_imp_com scnj set_rev_mp)
  hence "nprv F (imp (ldsj \<psi>s) \<chi>)"
    by (simp add: 0 assms nprv_def prv_imp_com)
  thus ?thesis using assms nprv_mp by blast
qed

lemmas nprv_ldsjE0 = nprv_ldsjE[OF nprv_hyp _, simped]
lemmas nprv_ldsjE1 = nprv_ldsjE[OF _ nprv_hyp, simped]
lemmas nprv_ldsjE01 = nprv_ldsjE[OF nprv_hyp nprv_hyp, simped]

lemma nprv_allI:
"nprv F \<phi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> x \<in> var \<Longrightarrow> x \<notin> \<Union> (Fvars ` F) \<Longrightarrow>
 nprv F (all x \<phi>)"
unfolding nprv_def by (rule prv_all_imp_gen) auto

lemma nprv_allE:
assumes "nprv F (all x \<phi>)" "nprv (insert (subst \<phi> t x) F) \<psi>"
"F \<subseteq> fmla" "finite F" "\<phi> \<in> fmla" "t \<in> trm" "x \<in> var" "\<psi> \<in> fmla"
shows "nprv F \<psi>"
proof-
  have "nprv F (subst \<phi> t x)"
  using assms unfolding nprv_def by (meson all subst prv_all_inst prv_prv_imp_trans scnj)
  thus ?thesis by (meson assms local.subst nprv_cut)
qed

lemmas nprv_allE0 = nprv_allE[OF nprv_hyp _, simped]
lemmas nprv_allE1 = nprv_allE[OF _ nprv_hyp, simped]
lemmas nprv_allE01 = nprv_allE[OF nprv_hyp nprv_hyp, simped]

lemma nprv_exiI:
"nprv F (subst \<phi> t x) \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow>
 nprv F (exi x \<phi>)"
unfolding nprv_def by (meson exi local.subst prv_exi_inst prv_prv_imp_trans scnj)

lemma nprv_exiE:
assumes n: "nprv F (exi x \<phi>)"
and nn: "nprv (insert \<phi> F) \<psi>"
and 0[simp]: "F \<subseteq> fmla" "finite F" "\<phi> \<in> fmla" "x \<in> var" "\<psi> \<in> fmla"
and x: "x \<notin> \<Union> (Fvars ` F)" "x \<notin> Fvars \<psi>"
shows "nprv F \<psi>"
proof-
  have "nprv F (imp (exi x \<phi>) \<psi>)" unfolding nprv_def apply(rule prv_imp_com)
  apply simp_all apply(rule prv_exi_imp_gen) using x apply simp_all
  apply(rule prv_imp_com) apply simp_all unfolding nprv_def[symmetric]
  apply(rule nprv_impI) using nn by auto
  thus ?thesis using n assms nprv_mp by blast
qed

lemmas nprv_exiE0 = nprv_exiE[OF nprv_hyp _, simped]
lemmas nprv_exiE1 = nprv_exiE[OF _ nprv_hyp, simped]
lemmas nprv_exiE01 = nprv_exiE[OF nprv_hyp nprv_hyp, simped]

(* Adding lemmas of various shapes into the proof context *)
lemma nprv_addLemmaE:
assumes "prv \<phi>" "nprv (insert \<phi> F) \<psi>"
and "\<phi> \<in> fmla" "\<psi> \<in> fmla" and "F \<subseteq> fmla" and "finite F"
shows "nprv F \<psi>"
using assms nprv_cut prv_nprvI by blast

lemmas nprv_addLemmaE1 = nprv_addLemmaE[OF _ nprv_hyp, simped]

lemma nprv_addImpLemmaI:
assumes "prv (imp \<phi>1 \<phi>2)"
and "F \<subseteq> fmla" "finite F" "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla"
and "nprv F \<phi>1"
shows "nprv F \<phi>2"
by (meson assms nprv_def prv_prv_imp_trans scnj)

lemma nprv_addImpLemmaE:
assumes "prv (imp \<phi>1 \<phi>2)" and "nprv F \<phi>1" and "nprv ((insert \<phi>2) F) \<psi>"
and "F \<subseteq> fmla" "finite F" "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla" "\<psi> \<in> fmla"
shows "nprv F \<psi>"
using assms nprv_addImpLemmaI nprv_cut by blast

lemmas nprv_addImpLemmaE1 = nprv_addImpLemmaE[OF _ nprv_hyp _, simped]
lemmas nprv_addImpLemmaE2 = nprv_addImpLemmaE[OF _ _ nprv_hyp, simped]
lemmas nprv_addImpLemmaE12 = nprv_addImpLemmaE[OF _ nprv_hyp nprv_hyp, simped]

lemma nprv_addImp2LemmaI:
assumes "prv (imp \<phi>1 (imp \<phi>2 \<phi>3))"
and "F \<subseteq> fmla" "finite F" "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla" "\<phi>3 \<in> fmla"
and "nprv F \<phi>1" "nprv F \<phi>2"
shows "nprv F \<phi>3"
by (meson assms imp nprv_addImpLemmaI nprv_mp)

lemma nprv_addImp2LemmaE:
assumes "prv (imp \<phi>1 (imp \<phi>2 \<phi>3))" and "nprv F \<phi>1" and "nprv F \<phi>2" and "nprv ((insert \<phi>3) F) \<psi>"
and "F \<subseteq> fmla" "finite F" "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla"  "\<phi>3 \<in> fmla" "\<psi> \<in> fmla"
shows "nprv F \<psi>"
by (meson assms nprv_addImp2LemmaI nprv_cut)

lemmas nprv_addImp2LemmaE1 = nprv_addImp2LemmaE[OF _ nprv_hyp _ _, simped]
lemmas nprv_addImp2LemmaE2 = nprv_addImp2LemmaE[OF _ _ nprv_hyp _, simped]
lemmas nprv_addImp2LemmaE3 = nprv_addImp2LemmaE[OF _ _ _ nprv_hyp, simped]
lemmas nprv_addImp2LemmaE12 = nprv_addImp2LemmaE[OF _ nprv_hyp nprv_hyp _, simped]
lemmas nprv_addImp2LemmaE13 = nprv_addImp2LemmaE[OF _ nprv_hyp _ nprv_hyp, simped]
lemmas nprv_addImp2LemmaE23 = nprv_addImp2LemmaE[OF _ _ nprv_hyp nprv_hyp, simped]
lemmas nprv_addImp2LemmaE123 = nprv_addImp2LemmaE[OF _ nprv_hyp nprv_hyp nprv_hyp, simped]

lemma nprv_addImp3LemmaI:
assumes "prv (imp \<phi>1 (imp \<phi>2 (imp \<phi>3 \<phi>4)))"
and "F \<subseteq> fmla" "finite F" "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla" "\<phi>3 \<in> fmla" "\<phi>4 \<in> fmla"
and "nprv F \<phi>1" "nprv F \<phi>2" "nprv F \<phi>3"
shows "nprv F \<phi>4"
by (meson assms imp nprv_addImpLemmaI nprv_mp)

lemma nprv_addImp3LemmaE:
assumes "prv (imp \<phi>1 (imp \<phi>2 (imp \<phi>3 \<phi>4)))"  and "nprv F \<phi>1" and "nprv F \<phi>2" and "nprv F \<phi>3"
and "nprv ((insert \<phi>4) F) \<psi>"
and "F \<subseteq> fmla" "finite F" "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla" "\<phi>3 \<in> fmla" "\<phi>4 \<in> fmla" "\<psi> \<in> fmla"
shows "nprv F \<psi>"
by (meson assms nprv_addImp3LemmaI nprv_cut)

lemmas nprv_addImp3LemmaE1 = nprv_addImp3LemmaE[OF _ nprv_hyp _ _ _, simped]
lemmas nprv_addImp3LemmaE2 = nprv_addImp3LemmaE[OF _ _ nprv_hyp _ _, simped]
lemmas nprv_addImp3LemmaE3 = nprv_addImp3LemmaE[OF _ _ _ nprv_hyp _, simped]
lemmas nprv_addImp3LemmaE4 = nprv_addImp3LemmaE[OF _ _ _ _ nprv_hyp, simped]
lemmas nprv_addImp3LemmaE12 = nprv_addImp3LemmaE[OF _ nprv_hyp nprv_hyp _ _, simped]
lemmas nprv_addImp3LemmaE13 = nprv_addImp3LemmaE[OF _ nprv_hyp _ nprv_hyp _, simped]
lemmas nprv_addImp3LemmaE14 = nprv_addImp3LemmaE[OF _ nprv_hyp _ _ nprv_hyp, simped]
lemmas nprv_addImp3LemmaE23 = nprv_addImp3LemmaE[OF _ _ nprv_hyp nprv_hyp _, simped]
lemmas nprv_addImp3LemmaE24 = nprv_addImp3LemmaE[OF _ _ nprv_hyp _ nprv_hyp, simped]
lemmas nprv_addImp3LemmaE34 = nprv_addImp3LemmaE[OF _ _ _ nprv_hyp nprv_hyp, simped]
lemmas nprv_addImp3LemmaE123 = nprv_addImp3LemmaE[OF _ nprv_hyp nprv_hyp nprv_hyp _, simped]
lemmas nprv_addImp3LemmaE124 = nprv_addImp3LemmaE[OF _ nprv_hyp nprv_hyp _ nprv_hyp, simped]
lemmas nprv_addImp3LemmaE134 = nprv_addImp3LemmaE[OF _ nprv_hyp _ nprv_hyp nprv_hyp, simped]
lemmas nprv_addImp3LemmaE234 = nprv_addImp3LemmaE[OF _ _ nprv_hyp nprv_hyp nprv_hyp, simped]
lemmas nprv_addImp3LemmaE1234 = nprv_addImp3LemmaE[OF _ nprv_hyp nprv_hyp nprv_hyp nprv_hyp, simped]

lemma nprv_addDsjLemmaE:
assumes "prv (dsj \<phi>1 \<phi>2)" and "nprv (insert \<phi>1 F) \<psi>" and "nprv ((insert \<phi>2) F) \<psi>"
and "F \<subseteq> fmla" "finite F" "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla" "\<psi> \<in> fmla"
shows "nprv F \<psi>"
by (meson assms dsj nprv_clear nprv_dsjE prv_nprv0I)

lemmas nprv_addDsjLemmaE1 = nprv_addDsjLemmaE[OF _ nprv_hyp _, simped]
lemmas nprv_addDsjLemmaE2 = nprv_addDsjLemmaE[OF _ _ nprv_hyp, simped]
lemmas nprv_addDsjLemmaE12 = nprv_addDsjLemmaE[OF _ nprv_hyp nprv_hyp, simped]


(* Intro/elim/etc. rules for equality  *)

(* Reflexivity: *)
lemma nprv_eql_reflI: "F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> t \<in> trm \<Longrightarrow> nprv F (eql t t)"
by (simp add: prv_eql_reflT prv_nprvI)

lemma nprv_eq_eqlI: "t1 = t2 \<Longrightarrow> F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> t1 \<in> trm \<Longrightarrow> nprv F (eql t1 t2)"
by (simp add: prv_eql_reflT prv_nprvI)

(* Symmetry: *)
lemmas nprv_eql_symI =  nprv_addImpLemmaI[OF prv_eql_sym, simped, rotated 4]
lemmas nprv_eql_symE =  nprv_addImpLemmaE[OF prv_eql_sym, simped, rotated 2]

lemmas nprv_eql_symE0 =  nprv_eql_symE[OF nprv_hyp _, simped]
lemmas nprv_eql_symE1 =  nprv_eql_symE[OF _ nprv_hyp, simped]
lemmas nprv_eql_symE01 =  nprv_eql_symE[OF nprv_hyp nprv_hyp, simped]

(* Transitivity: *)
lemmas nprv_eql_transI = nprv_addImp2LemmaI[OF prv_eql_imp_trans, simped, rotated 5]
lemmas nprv_eql_transE = nprv_addImp2LemmaE[OF prv_eql_imp_trans, simped, rotated 3]

lemmas nprv_eql_transE0 = nprv_eql_transE[OF nprv_hyp _ _, simped]
lemmas nprv_eql_transE1 = nprv_eql_transE[OF _ nprv_hyp _, simped]
lemmas nprv_eql_transE2 = nprv_eql_transE[OF _ _ nprv_hyp, simped]
lemmas nprv_eql_transE01 = nprv_eql_transE[OF nprv_hyp nprv_hyp _, simped]
lemmas nprv_eql_transE02 = nprv_eql_transE[OF nprv_hyp _ nprv_hyp, simped]
lemmas nprv_eql_transE12 = nprv_eql_transE[OF _ nprv_hyp nprv_hyp, simped]
lemmas nprv_eql_transE012 = nprv_eql_transE[OF nprv_hyp nprv_hyp nprv_hyp, simped]

(* Substitutivity: *)
lemmas nprv_eql_substI = nprv_addImp2LemmaI[OF prv_eql_subst_trm_rev, simped, rotated 6]
lemmas nprv_eql_substE = nprv_addImp2LemmaE[OF prv_eql_subst_trm_rev, simped, rotated 4]

lemmas nprv_eql_substE0 = nprv_eql_substE[OF nprv_hyp _ _, simped]
lemmas nprv_eql_substE1 = nprv_eql_substE[OF _ nprv_hyp _, simped]
lemmas nprv_eql_substE2 = nprv_eql_substE[OF _ _ nprv_hyp, simped]
lemmas nprv_eql_substE01 = nprv_eql_substE[OF nprv_hyp nprv_hyp _, simped]
lemmas nprv_eql_substE02 = nprv_eql_substE[OF nprv_hyp _ nprv_hyp, simped]
lemmas nprv_eql_substE12 = nprv_eql_substE[OF _ nprv_hyp nprv_hyp, simped]
lemmas nprv_eql_substE012 = nprv_eql_substE[OF nprv_hyp nprv_hyp nprv_hyp, simped]

(* Other seemingly useful variations of the intro/elim rules: *)

lemma nprv_cnjH:
"nprv (insert \<phi>1 (insert \<phi>2 F)) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv (insert (cnj \<phi>1 \<phi>2) F) \<psi>"
apply(rule nprv_cut2[of _ \<phi>1 \<phi>2])
apply (auto simp: nprv_impI_rev prv_imp_cnjL prv_imp_cnjR prv_nprvI)
by (meson cnj finite.insertI insert_iff insert_subset nprv_mono subset_insertI)

end \<comment> \<open>context Deduct_with_False_Disj\<close>

end
