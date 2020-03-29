(* Axioms about the deduction in a logical system that (shallowly) embeds
intuitionistic mininimal logic over a signature containing the numerals.  *)
theory Deduction imports Syntax
begin

locale Deduct = 
Syntax_with_Numerals_and_Connectives 
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi              
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst 
and num
and eql cnj imp all exi  
+  
fixes 
(* Provability of numeric formulas: *)
prv :: "'fmla \<Rightarrow> bool"
(* Hilbert-style system for intuitionistic logic over \<longrightarrow>,\<and>,\<forall>,\<exists> (no need for \<bottom>, \<not> or \<or>).
(This style is preferred since it requires the least amount of infrastructure) *)
assumes 
(* Propositional rules and axioms: *)
(* One single rule, modus ponens: *)
prv_imp_mp: 
"\<And> \<phi> \<chi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> 
   prv (imp \<phi> \<chi>) \<Longrightarrow> prv \<phi> \<Longrightarrow> prv \<chi>"
and 
prv_imp_imp_triv: 
"\<And>\<phi> \<chi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> 
   prv (imp \<phi> (imp \<chi> \<phi>))"
and 
prv_imp_trans: 
"\<And> \<phi> \<chi> \<psi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> 
  prv (imp (imp \<phi> (imp \<chi> \<psi>))
           (imp (imp \<phi> \<chi>) (imp \<phi> \<psi>)))"
and 
prv_imp_cnjL: 
"\<And> \<phi> \<chi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> 
  prv (imp (cnj \<phi> \<chi>) \<phi>)"
and 
prv_imp_cnjR: 
"\<And> \<phi> \<chi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> 
  prv (imp (cnj \<phi> \<chi>) \<chi>)"
and 
prv_imp_cnjI: 
"\<And> \<phi> \<chi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> 
  prv (imp \<phi> (imp \<chi> (cnj \<phi> \<chi>)))"
and 
(*   *)
(* Predicate calculus (quantifier) rules and axioms : *)
(* Two rules, universal and existential generalization: *)
prv_all_imp_gen: 
"\<And> x \<phi> \<chi>. x \<notin> Fvars \<phi> \<Longrightarrow> prv (imp \<phi> \<chi>) \<Longrightarrow> prv (imp \<phi> (all x \<chi>))"
and 
prv_exi_imp_gen: 
"\<And> x \<phi> \<chi>. x \<in> var \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> 
  x \<notin> Fvars \<chi> \<Longrightarrow> prv (imp \<phi> \<chi>) \<Longrightarrow> prv (imp (exi x \<phi>) \<chi>)"   
(* Two quantifier instantiation axioms: *) and 
prv_all_inst: 
"\<And> x \<phi> t. 
  x \<in> var \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> 
  prv (imp (all x \<phi>) (subst \<phi> t x))"
and 
prv_exi_inst: 
"\<And> x \<phi> t. 
  x \<in> var \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> 
  prv (imp (subst \<phi> t x) (exi x \<phi>))"
and 
(* The equality rules:   *)
(*  *)
prv_eql_refl: 
"\<And> x. x \<in> var \<Longrightarrow> 
  prv (eql (Var x) (Var x))"
and 
prv_eql_subst: 
"\<And> \<phi> x y.
   x \<in> var \<Longrightarrow> y \<in> var \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> 
   prv ((imp (eql (Var x) (Var y))
             (imp \<phi> (subst \<phi> (Var y) x))))"
begin

(****)
(* Properties of the propositional fragment: *) 
lemma prv_imp_triv:
assumes phi: "\<phi> \<in> fmla" and psi: "\<psi> \<in> fmla" 
shows "prv \<psi> \<Longrightarrow> prv (imp \<phi> \<psi>)" 
  by (meson prv_imp_imp_triv prv_imp_mp imp phi psi)

lemma prv_imp_refl: 
assumes phi: "\<phi> \<in> fmla" 
shows "prv (imp \<phi> \<phi>)" 
  by (metis prv_imp_imp_triv prv_imp_mp prv_imp_trans imp phi)

lemma prv_imp_refl2: "\<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> \<phi> = \<psi> \<Longrightarrow> prv (imp \<phi> \<psi>)"
using prv_imp_refl by auto  

lemma prv_cnjI: 
assumes phi: "\<phi> \<in> fmla" and chi: "\<chi> \<in> fmla"
shows "prv \<phi> \<Longrightarrow> prv \<chi> \<Longrightarrow> prv (cnj \<phi> \<chi>)"
  by (meson cnj prv_imp_cnjI prv_imp_mp imp phi chi)

lemma prv_cnjEL: 
assumes phi: "\<phi> \<in> fmla" and chi: "\<chi> \<in> fmla"
shows "prv (cnj \<phi> \<chi>) \<Longrightarrow> prv \<phi>"
  using chi phi prv_imp_cnjL prv_imp_mp by blast 

lemma prv_cnjER: 
assumes phi: "\<phi> \<in> fmla" and chi: "\<chi> \<in> fmla"
shows "prv (cnj \<phi> \<chi>) \<Longrightarrow> prv \<chi>"
  using chi phi prv_imp_cnjR prv_imp_mp by blast 

lemma prv_prv_imp_trans: 
assumes phi: "\<phi> \<in> fmla" and chi: "\<chi> \<in> fmla" and psi: "\<psi> \<in> fmla"
assumes 1: "prv (imp \<phi> \<chi>)" and 2: "prv (imp \<chi> \<psi>)" 
shows "prv (imp \<phi> \<psi>)"
proof-
  have "prv (imp \<phi> (imp \<chi> \<psi>))" by (simp add: 2 chi prv_imp_triv phi psi)
  thus ?thesis by (metis 1 chi prv_imp_mp prv_imp_trans imp phi psi)
qed

lemma prv_imp_trans1: 
assumes phi: "\<phi> \<in> fmla" and chi: "\<chi> \<in> fmla" and psi: "\<psi> \<in> fmla"
shows "prv (imp (imp \<chi> \<psi>) (imp (imp \<phi> \<chi>) (imp \<phi> \<psi>)))"
  by (meson chi prv_prv_imp_trans prv_imp_imp_triv prv_imp_trans imp phi psi)

lemma prv_imp_com: 
assumes phi: "\<phi> \<in> fmla" and chi: "\<chi> \<in> fmla" and psi: "\<psi> \<in> fmla"
assumes "prv (imp \<phi> (imp \<chi> \<psi>))"
shows "prv (imp \<chi> (imp \<phi> \<psi>))"
  by (metis (no_types) assms prv_prv_imp_trans prv_imp_imp_triv prv_imp_mp prv_imp_trans imp)
 
lemma prv_imp_trans2: 
assumes phi: "\<phi> \<in> fmla" and chi: "\<chi> \<in> fmla" and psi: "\<psi> \<in> fmla"
shows "prv (imp (imp \<phi> \<chi>) (imp (imp \<chi> \<psi>) (imp \<phi> \<psi>)))"
using prv_imp_mp prv_imp_trans prv_imp_trans1 prv_imp_imp_triv 
  by (meson chi prv_imp_com imp phi psi) 

lemma prv_imp_cnj:
assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla" and "\<psi> \<in> fmla"
shows "prv (imp \<phi> \<psi>) \<Longrightarrow> prv (imp \<phi> \<chi>) \<Longrightarrow> prv (imp \<phi> (cnj \<psi> \<chi>))" 
  by (smt assms cnj prv_prv_imp_trans prv_imp_cnjI prv_imp_com 
          prv_imp_mp prv_imp_refl prv_imp_trans imp)

lemma prv_imp_imp_com: 
assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla" and "\<psi> \<in> fmla"
shows 
"prv (imp (imp \<phi> (imp \<chi> \<psi>)) 
          (imp \<chi> (imp \<phi> \<psi>)))"
  by (metis (no_types) assms  
   prv_prv_imp_trans prv_imp_com prv_imp_imp_triv prv_imp_trans imp) 

lemma prv_cnj_imp_monoR2:
assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla" and "\<psi> \<in> fmla"
assumes "prv (imp \<phi> (imp \<chi> \<psi>))"
shows "prv (imp (cnj \<phi> \<chi>) \<psi>)"
  by (smt assms cnj prv_prv_imp_trans prv_imp_cnjL prv_imp_cnjR 
      prv_imp_com prv_imp_mp prv_imp_refl prv_imp_trans imp) 

lemma prv_imp_imp_imp_cnj:
assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla" and "\<psi> \<in> fmla"
shows 
"prv (imp (imp \<phi> (imp \<chi> \<psi>))
          (imp (cnj \<phi> \<chi>) \<psi>))"
proof-
  have "prv (imp \<phi> (imp (imp \<phi> (imp \<chi> \<psi>)) (imp \<chi> \<psi>)))" 
    by (simp add: assms prv_imp_com prv_imp_refl)
  hence "prv (imp \<phi> (imp \<chi> (imp (imp \<phi> (imp \<chi> \<psi>)) \<psi>)))" 
    by (metis (no_types, lifting) assms prv_prv_imp_trans prv_imp_imp_com imp)
  hence "prv (imp (cnj \<phi> \<chi>) 
                    (imp (imp \<phi> (imp \<chi> \<psi>)) \<psi>))"  
    by (simp add: assms prv_cnj_imp_monoR2)
  thus ?thesis using assms prv_imp_com prv_imp_mp by (meson cnj imp)
qed

lemma prv_imp_cnj_imp:
assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla" and "\<psi> \<in> fmla"
shows 
"prv (imp (imp (cnj \<phi> \<chi>) \<psi>)
          (imp \<phi> (imp \<chi> \<psi>)))"
  by (metis (no_types) assms cnj prv_prv_imp_trans prv_imp_cnjI prv_imp_com prv_imp_trans2 imp)

lemma prv_cnj_imp:
assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla" and "\<psi> \<in> fmla"
assumes "prv (imp (cnj \<phi> \<chi>) \<psi>)"
shows "prv (imp \<phi> (imp \<chi> \<psi>))"
  using assms prv_imp_cnj_imp prv_imp_mp by (meson cnj imp)

(* Monotonicy of conjunction w.r.t. implication: *)
lemma prv_cnj_imp_monoR: 
assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla" and "\<psi> \<in> fmla"
shows "prv (imp (imp \<phi> \<chi>) (imp (imp \<phi> \<psi>) (imp \<phi> (cnj \<chi> \<psi>))))"
  using assms prv_imp_cnjI prv_imp_mp prv_imp_trans prv_imp_trans1  
  by (smt cnj prv_cnj_imp prv_imp_cnj prv_imp_cnjL prv_imp_cnjR prv_cnj_imp_monoR2 imp)
   
lemma prv_imp_cnj3L: 
assumes "\<phi>1 \<in> fmla" and "\<phi>2 \<in> fmla" and "\<chi> \<in> fmla"
shows "prv (imp (imp \<phi>1 \<chi>) (imp (cnj \<phi>1 \<phi>2) \<chi>))"
  using assms prv_imp_cnjL prv_imp_mp prv_imp_trans2 
  by (metis cnj imp)

lemma prv_imp_cnj3R: 
assumes "\<phi>1 \<in> fmla" and "\<phi>2 \<in> fmla" and "\<chi> \<in> fmla"
shows "prv (imp (imp \<phi>2 \<chi>) (imp (cnj \<phi>1 \<phi>2) \<chi>))"
  using prv_imp_cnjR prv_imp_mp prv_imp_trans2 
  by (metis assms cnj imp)

lemma prv_cnj_imp_mono: 
assumes "\<phi>1 \<in> fmla" and "\<phi>2 \<in> fmla" and "\<chi>1 \<in> fmla" and "\<chi>2 \<in> fmla"
shows "prv (imp (imp \<phi>1 \<chi>1) (imp (imp \<phi>2 \<chi>2) (imp (cnj \<phi>1 \<phi>2) (cnj \<chi>1 \<chi>2))))"
proof-
  have "prv (imp (imp (cnj \<phi>1 \<phi>2) \<chi>1) (imp (imp (cnj \<phi>1 \<phi>2) \<chi>2) (imp (cnj \<phi>1 \<phi>2) (cnj \<chi>1 \<chi>2))))"
  using prv_cnj_imp_monoR[of "cnj \<phi>1 \<phi>2" \<chi>1 \<chi>2] assms by auto 
  hence "prv (imp (imp \<phi>1 \<chi>1) (imp (imp (cnj \<phi>1 \<phi>2) \<chi>2) (imp (cnj \<phi>1 \<phi>2) (cnj \<chi>1 \<chi>2))))"
    using assms prv_cnj_imp prv_imp_cnj prv_imp_cnj3L prv_imp_cnjR prv_imp_imp_imp_cnj prv_imp_mp
    by (smt cnj prv_prv_imp_trans imp)
  hence "prv (imp (imp (cnj \<phi>1 \<phi>2) \<chi>2) (imp (imp \<phi>1 \<chi>1) (imp (cnj \<phi>1 \<phi>2) (cnj \<chi>1 \<chi>2))))"
    using prv_imp_com assms by (meson cnj imp)
  hence "prv (imp (imp \<phi>2 \<chi>2) (imp (imp \<phi>1 \<chi>1) (imp (cnj \<phi>1 \<phi>2) (cnj \<chi>1 \<chi>2))))"
    using prv_imp_cnj3R prv_imp_mp prv_imp_trans1 
    by (metis (no_types) assms cnj prv_prv_imp_trans imp) 
  thus ?thesis using prv_imp_com assms  
    by (meson cnj imp)
qed

lemma prv_cnj_mono: 
assumes "\<phi>1 \<in> fmla" and "\<phi>2 \<in> fmla" and "\<chi>1 \<in> fmla" and "\<chi>2 \<in> fmla"
assumes "prv (imp \<phi>1 \<chi>1)" and "prv (imp \<phi>2 \<chi>2)"
shows "prv (imp (cnj \<phi>1 \<phi>2) (cnj \<chi>1 \<chi>2))"
  using assms prv_cnj_imp_mono prv_imp_mp 
  by (metis (mono_tags) cnj prv_prv_imp_trans prv_imp_cnj prv_imp_cnjL prv_imp_cnjR)

lemma prv_cnj_imp_monoR4:
assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla" and "\<psi>1 \<in> fmla" and "\<psi>2 \<in> fmla"
shows 
"prv (imp (imp \<phi> (imp \<chi> \<psi>1)) 
          (imp (imp \<phi> (imp \<chi> \<psi>2)) (imp \<phi> (imp \<chi> (cnj \<psi>1 \<psi>2)))))"
  by (simp add: assms prv_cnj_imp prv_imp_cnj prv_imp_cnjL prv_imp_cnjR prv_cnj_imp_monoR2)
 
lemma prv_imp_cnj4:
assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla" and "\<psi>1 \<in> fmla" and "\<psi>2 \<in> fmla"
shows "prv (imp \<phi> (imp \<chi> \<psi>1)) \<Longrightarrow> prv (imp \<phi> (imp \<chi> \<psi>2)) \<Longrightarrow> prv (imp \<phi> (imp \<chi> (cnj \<psi>1 \<psi>2)))"
  by (simp add: assms prv_cnj_imp prv_imp_cnj prv_cnj_imp_monoR2)

lemma prv_cnj_imp_monoR5: 
assumes "\<phi>1 \<in> fmla" and "\<phi>2 \<in> fmla" and "\<chi>1 \<in> fmla" and "\<chi>2 \<in> fmla"
shows "prv (imp (imp \<phi>1 \<chi>1) (imp (imp \<phi>2 \<chi>2) (imp \<phi>1 (imp \<phi>2 (cnj \<chi>1 \<chi>2)))))"
proof-
  have "prv (imp (imp \<phi>1 \<chi>1) (imp (imp \<phi>2 \<chi>2) (imp (cnj \<phi>1 \<phi>2) (cnj \<chi>1 \<chi>2))))"
    using prv_cnj_imp_mono[of \<phi>1 \<phi>2  \<chi>1 \<chi>2] assms by auto
  hence "prv (imp (imp \<phi>1 \<chi>1) (imp (cnj \<phi>1 \<phi>2) (imp (imp \<phi>2 \<chi>2) (cnj \<chi>1 \<chi>2))))"
    using assms prv_cnj_imp prv_imp_cnj3L prv_imp_cnj4 prv_imp_com prv_imp_imp_imp_cnj prv_imp_mp
    by (smt cnj prv_prv_imp_trans imp)
  hence "prv (imp (imp \<phi>1 \<chi>1) (imp \<phi>1 (imp \<phi>2 (imp (imp \<phi>2 \<chi>2) (cnj \<chi>1 \<chi>2)))))" 
    using prv_imp_cnj_imp prv_imp_mp prv_imp_trans2  
    by (metis (mono_tags) assms cnj prv_prv_imp_trans imp)
  hence 1: "prv (imp (imp \<phi>1 \<chi>1) (imp \<phi>1 (imp (imp \<phi>2 \<chi>2) (imp \<phi>2  (cnj \<chi>1 \<chi>2)))))" 
    using prv_cnj_imp prv_imp_cnjR prv_imp_mp prv_imp_trans1 
    by (metis (no_types) assms cnj prv_cnj_imp_monoR prv_prv_imp_trans prv_imp_imp_triv imp)
  thus ?thesis using prv_imp_imp_com prv_imp_mp prv_imp_trans2  
    using assms cnj prv_prv_imp_trans prv_imp_cnjI imp  
    by (smt \<open>prv (imp (imp \<phi>1 \<chi>1) (imp (imp \<phi>2 \<chi>2) (imp (cnj \<phi>1 \<phi>2) (cnj \<chi>1 \<chi>2))))\<close> 
         prv_cnj_imp_monoR2 prv_imp_cnj_imp)
qed

lemma prv_imp_cnj5: 
assumes "\<phi>1 \<in> fmla" and "\<phi>2 \<in> fmla" and "\<chi>1 \<in> fmla" and "\<chi>2 \<in> fmla"
assumes "prv (imp \<phi>1 \<chi>1)" and "prv (imp \<phi>2 \<chi>2)"
shows "prv (imp \<phi>1 (imp \<phi>2 (cnj \<chi>1 \<chi>2)))"
  by (simp add: assms prv_cnj_imp prv_cnj_mono)

(* Properties of formula equivalence: *)
lemma prv_eqv_imp: 
assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla" 
shows "prv (imp (eqv \<phi> \<chi>) (eqv \<chi> \<phi>))"
  by (simp add: assms prv_imp_cnj prv_imp_cnjL prv_imp_cnjR eqv_def)

lemma prv_eqv_eqv: 
assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla" 
shows "prv (eqv (eqv \<phi> \<chi>) (eqv \<chi> \<phi>))"
  using assms prv_cnjI prv_eqv_imp eqv_def by auto

lemma prv_imp_eqvEL: 
"\<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> prv (eqv \<phi>1 \<phi>2) \<Longrightarrow> prv (imp \<phi>1 \<phi>2)"
  unfolding eqv_def by (meson cnj imp prv_imp_cnjL prv_imp_mp)

lemma prv_imp_eqvER: 
"\<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> prv (eqv \<phi>1 \<phi>2) \<Longrightarrow> prv (imp \<phi>2 \<phi>1)"
unfolding eqv_def by (meson cnj imp prv_imp_cnjR prv_imp_mp)

lemma prv_eqv_imp_trans: 
assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla" and "\<psi> \<in> fmla"
shows "prv (imp (eqv \<phi> \<chi>) (imp (eqv \<chi> \<psi>) (eqv \<phi> \<psi>)))"
proof-
  have "prv (imp (eqv \<phi> \<chi>) (imp (imp \<chi> \<psi>) (imp \<phi> \<psi>)))"
  using assms prv_imp_cnjL prv_imp_mp prv_imp_trans2 eqv_def  
  by (metis prv_imp_cnj3L eqv imp)
  hence "prv (imp (eqv \<phi> \<chi>) (imp (eqv \<chi> \<psi>) (imp \<phi> \<psi>)))" 
    using prv_imp_cnjL prv_imp_mp prv_imp_trans2 eqv_def  
    by (metis (no_types) assms prv_imp_cnj3L prv_imp_com eqv imp)
  hence 1: "prv (imp (cnj (eqv \<phi> \<chi>) (eqv \<chi> \<psi>)) (imp \<phi> \<psi>))"  
    using prv_cnj_imp_monoR2  
    by (simp add: assms(1) assms(2) assms(3))
  have "prv (imp (eqv \<phi> \<chi>) (imp (imp \<psi> \<chi>) (imp \<psi> \<phi>)))"
    using prv_imp_cnjR prv_imp_mp prv_imp_trans1 eqv_def  
    by (metis assms prv_cnj_imp_monoR2 prv_imp_triv imp)
  hence "prv (imp (eqv \<phi> \<chi>) (imp (eqv \<chi> \<psi>) (imp \<psi> \<phi>)))" 
    using prv_imp_cnjR prv_imp_mp prv_imp_trans2 eqv_def   
    by (smt assms prv_prv_imp_trans prv_imp_com eqv imp)   
  hence 2: "prv (imp (cnj (eqv \<phi> \<chi>) (eqv \<chi> \<psi>)) (imp \<psi> \<phi>))"  
    using prv_cnj_imp_monoR2 
    by (metis (no_types, lifting) assms eqv imp)
  have "prv (imp (cnj (eqv \<phi> \<chi>) (eqv \<chi> \<psi>)) (eqv \<phi> \<psi>))"
   using 1 2 apply(subst eqv_def[of \<phi> \<psi>]) using assms prv_imp_cnj by auto
  thus ?thesis 
    by (simp add: assms prv_cnj_imp)
qed  

lemma prv_eqv_cnj_trans: 
assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla" and "\<psi> \<in> fmla"
shows "prv (imp (cnj (eqv \<phi> \<chi>) (eqv \<chi> \<psi>)) (eqv \<phi> \<psi>))"
  by (simp add: assms prv_eqv_imp_trans prv_cnj_imp_monoR2)

lemma prv_eqvI:
  assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla"
  assumes "prv (imp \<phi> \<chi>)" and "prv (imp \<chi> \<phi>)"
  shows "prv (eqv \<phi> \<chi>)"
  by (simp add: assms eqv_def prv_cnjI)

(* Formula equivalence is a congruence *)
lemma prv_eqv_refl: "\<phi> \<in> fmla \<Longrightarrow> prv (eqv \<phi> \<phi>)"
  by (simp add: prv_cnjI prv_imp_refl eqv_def)

lemma prv_eqv_sym: 
assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla" 
shows "prv (eqv \<phi> \<chi>) \<Longrightarrow> prv (eqv \<chi> \<phi>)"
  using assms prv_cnjI prv_imp_cnjL prv_imp_cnjR prv_imp_mp eqv_def 
  by (meson prv_eqv_imp eqv)

lemma prv_eqv_trans: 
assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla" and "\<psi> \<in> fmla"
shows "prv (eqv \<phi> \<chi>) \<Longrightarrow> prv (eqv \<chi> \<psi>) \<Longrightarrow> prv (eqv \<phi> \<psi>)"
  using assms prv_cnjI prv_cnj_imp_monoR2 prv_imp_mp prv_imp_trans1 prv_imp_imp_triv eqv_def 
  by (metis prv_prv_imp_trans prv_imp_cnjL prv_imp_cnjR eqv imp)

lemma imp_imp_compat_eqvL: 
assumes "\<phi>1 \<in> fmla" and "\<phi>2 \<in> fmla" and "\<chi> \<in> fmla" 
shows "prv (imp (eqv \<phi>1 \<phi>2) (eqv (imp \<phi>1 \<chi>) (imp \<phi>2 \<chi>)))"
  using eqv_def assms prv_imp_cnj prv_cnj_imp_monoR2 prv_imp_mp prv_imp_trans2 prv_imp_imp_triv
  by (smt cnj prv_prv_imp_trans prv_imp_cnjL prv_imp_cnjR imp)

lemma imp_imp_compat_eqvR: 
assumes "\<phi> \<in> fmla" and "\<chi>1 \<in> fmla" and "\<chi>2 \<in> fmla" 
shows "prv (imp (eqv \<chi>1 \<chi>2) (eqv (imp \<phi> \<chi>1) (imp \<phi> \<chi>2)))"
  by (simp add: assms prv_cnj_mono prv_imp_trans1 eqv_def)
 

lemma imp_imp_compat_eqv: 
assumes "\<phi>1 \<in> fmla" and "\<phi>2 \<in> fmla" and "\<chi>1 \<in> fmla" and "\<chi>2 \<in> fmla" 
shows "prv (imp (eqv \<phi>1 \<phi>2) (imp (eqv \<chi>1 \<chi>2) (eqv (imp \<phi>1 \<chi>1) (imp \<phi>2 \<chi>2))))"
proof-
  have "prv (imp (eqv \<phi>1 \<phi>2) (imp (eqv \<chi>1 \<chi>2) (cnj (eqv (imp \<phi>1 \<chi>1) (imp \<phi>2 \<chi>1))
                                                    (eqv (imp \<phi>2 \<chi>1) (imp \<phi>2 \<chi>2)))))"
    using prv_imp_cnj5
    [OF _ _ _ _ imp_imp_compat_eqvL[of \<phi>1 \<phi>2 \<chi>1] imp_imp_compat_eqvR[of \<phi>2 \<chi>1 \<chi>2]] assms by auto
  hence "prv (imp (cnj (eqv \<phi>1 \<phi>2) (eqv \<chi>1 \<chi>2)) (cnj (eqv (imp \<phi>1 \<chi>1) (imp \<phi>2 \<chi>1))
                                                      (eqv (imp \<phi>2 \<chi>1) (imp \<phi>2 \<chi>2))))"
    by(simp add: assms prv_cnj_imp_monoR2)
  hence "prv (imp (cnj (eqv \<phi>1 \<phi>2) (eqv \<chi>1 \<chi>2)) (eqv (imp \<phi>1 \<chi>1) (imp \<phi>2 \<chi>2)))" 
    using assms prv_eqv_cnj_trans[of "imp \<phi>1 \<chi>1" "imp \<phi>2 \<chi>1" "imp \<phi>2 \<chi>2"]  
   using prv_imp_mp prv_imp_trans2  
   by (metis (no_types) cnj prv_prv_imp_trans eqv imp)
  thus ?thesis using assms prv_cnj_imp by auto
qed 

lemma imp_compat_eqvL:
assumes "\<phi>1 \<in> fmla" and "\<phi>2 \<in> fmla" and "\<chi> \<in> fmla"  
assumes "prv (eqv \<phi>1 \<phi>2)" 
shows "prv (eqv (imp \<phi>1 \<chi>) (imp \<phi>2 \<chi>))"
  using assms prv_imp_mp imp_imp_compat_eqvL by (meson eqv imp)

lemma imp_compat_eqvR: 
assumes "\<phi> \<in> fmla" and "\<chi>1 \<in> fmla" and "\<chi>2 \<in> fmla" 
assumes "prv (eqv \<chi>1 \<chi>2)"  
shows "prv (eqv (imp \<phi> \<chi>1) (imp \<phi> \<chi>2))" 
using assms prv_imp_mp imp_imp_compat_eqvR by (meson eqv imp)

lemma imp_compat_eqv: 
assumes "\<phi>1 \<in> fmla" and "\<phi>2 \<in> fmla" and "\<chi>1 \<in> fmla" and "\<chi>2 \<in> fmla" 
assumes "prv (eqv \<phi>1 \<phi>2)" and "prv (eqv \<chi>1 \<chi>2)" 
shows "prv (eqv (imp \<phi>1 \<chi>1) (imp \<phi>2 \<chi>2))"
  using assms prv_imp_mp imp_imp_compat_eqv by (metis eqv imp)

(*  *)
lemma imp_cnj_compat_eqvL: 
assumes "\<phi>1 \<in> fmla" and "\<phi>2 \<in> fmla" and "\<chi> \<in> fmla" 
shows "prv (imp (eqv \<phi>1 \<phi>2) (eqv (cnj \<phi>1 \<chi>) (cnj \<phi>2 \<chi>)))"
  using eqv_def assms prv_cnj_imp_mono prv_imp_com prv_imp_mp prv_imp_refl
  by (smt cnj imp)

lemma imp_cnj_compat_eqvR: 
assumes "\<phi> \<in> fmla" and "\<chi>1 \<in> fmla" and "\<chi>2 \<in> fmla" 
shows "prv (imp (eqv \<chi>1 \<chi>2) (eqv (cnj \<phi> \<chi>1) (cnj \<phi> \<chi>2)))"
  by (simp add: assms prv_cnj_mono prv_imp_cnj3R prv_imp_cnj4 prv_imp_cnjL prv_imp_triv eqv_def)

lemma imp_cnj_compat_eqv: 
assumes "\<phi>1 \<in> fmla" and "\<phi>2 \<in> fmla" and "\<chi>1 \<in> fmla" and "\<chi>2 \<in> fmla" 
shows "prv (imp (eqv \<phi>1 \<phi>2) (imp (eqv \<chi>1 \<chi>2) (eqv (cnj \<phi>1 \<chi>1) (cnj \<phi>2 \<chi>2))))"
proof-
  have "prv (imp (eqv \<phi>1 \<phi>2) (imp (eqv \<chi>1 \<chi>2) (cnj (eqv (cnj \<phi>1 \<chi>1) (cnj \<phi>2 \<chi>1))
                                                    (eqv (cnj \<phi>2 \<chi>1) (cnj \<phi>2 \<chi>2)))))"
    using prv_imp_cnj5
    [OF _ _ _ _ imp_cnj_compat_eqvL[of \<phi>1 \<phi>2 \<chi>1] imp_cnj_compat_eqvR[of \<phi>2 \<chi>1 \<chi>2]] assms by auto
  hence "prv (imp (cnj (eqv \<phi>1 \<phi>2) (eqv \<chi>1 \<chi>2)) (cnj (eqv (cnj \<phi>1 \<chi>1) (cnj \<phi>2 \<chi>1))
                                                      (eqv (cnj \<phi>2 \<chi>1) (cnj \<phi>2 \<chi>2))))"
    by(simp add: assms prv_cnj_imp_monoR2)
  hence "prv (imp (cnj (eqv \<phi>1 \<phi>2) (eqv \<chi>1 \<chi>2)) (eqv (cnj \<phi>1 \<chi>1) (cnj \<phi>2 \<chi>2)))" 
    using assms prv_eqv_cnj_trans[of "cnj \<phi>1 \<chi>1" "cnj \<phi>2 \<chi>1" "cnj \<phi>2 \<chi>2"]  
   using prv_imp_mp prv_imp_trans2  
   by (metis (no_types) cnj prv_prv_imp_trans eqv)
  thus ?thesis using assms prv_cnj_imp by auto
qed 

lemma cnj_compat_eqvL:
assumes "\<phi>1 \<in> fmla" and "\<phi>2 \<in> fmla" and "\<chi> \<in> fmla"  
assumes "prv (eqv \<phi>1 \<phi>2)" 
shows "prv (eqv (cnj \<phi>1 \<chi>) (cnj \<phi>2 \<chi>))"
  using assms prv_imp_mp imp_cnj_compat_eqvL by (meson eqv cnj)

lemma cnj_compat_eqvR: 
assumes "\<phi> \<in> fmla" and "\<chi>1 \<in> fmla" and "\<chi>2 \<in> fmla" 
assumes "prv (eqv \<chi>1 \<chi>2)"  
shows "prv (eqv (cnj \<phi> \<chi>1) (cnj \<phi> \<chi>2))" 
using assms prv_imp_mp imp_cnj_compat_eqvR by (meson eqv cnj)

lemma cnj_compat_eqv: 
assumes "\<phi>1 \<in> fmla" and "\<phi>2 \<in> fmla" and "\<chi>1 \<in> fmla" and "\<chi>2 \<in> fmla" 
assumes "prv (eqv \<phi>1 \<phi>2)" and "prv (eqv \<chi>1 \<chi>2)" 
shows "prv (eqv (cnj \<phi>1 \<chi>1) (cnj \<phi>2 \<chi>2))"
  using assms prv_imp_mp imp_cnj_compat_eqv by (metis eqv imp cnj)

lemma prv_eqv_prv:
  assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla"
  assumes "prv \<phi>" and "prv (eqv \<phi> \<chi>)"
  shows "prv \<chi>" 
  by (metis assms prv_imp_cnjL prv_imp_mp eqv eqv_def imp)

lemma prv_eqv_prv_rev:
  assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla"
  assumes "prv \<phi>" and "prv (eqv \<chi> \<phi>)"
  shows "prv \<chi>" 
  using assms prv_eqv_prv prv_eqv_sym by blast

lemma prv_imp_eqv_transi: 
assumes "\<phi> \<in> fmla" and "\<chi>1 \<in> fmla" and "\<chi>2 \<in> fmla" 
assumes "prv (imp \<phi> \<chi>1)" and "prv (eqv \<chi>1 \<chi>2)"
shows "prv (imp \<phi> \<chi>2)"
  by (meson assms imp imp_compat_eqvR prv_eqv_prv)

lemma prv_imp_eqv_transi_rev: 
assumes "\<phi> \<in> fmla" and "\<chi>1 \<in> fmla" and "\<chi>2 \<in> fmla" 
assumes "prv (imp \<phi> \<chi>2)" and "prv (eqv \<chi>1 \<chi>2)"
shows "prv (imp \<phi> \<chi>1)"
  by (meson assms prv_eqv_sym prv_imp_eqv_transi)

lemma prv_eqv_imp_transi: 
assumes "\<phi>1 \<in> fmla" and "\<phi>2 \<in> fmla" and "\<chi> \<in> fmla"
assumes "prv (eqv \<phi>1 \<phi>2)" and "prv (imp \<phi>2 \<chi>)"
shows "prv (imp \<phi>1 \<chi>)"  
  by (meson assms prv_imp_eqv_transi prv_imp_refl prv_prv_imp_trans)

lemma prv_eqv_imp_transi_rev: 
assumes "\<phi>1 \<in> fmla" and "\<phi>2 \<in> fmla" and "\<chi> \<in> fmla"
assumes "prv (eqv \<phi>1 \<phi>2)" and "prv (imp \<phi>1 \<chi>)"
shows "prv (imp \<phi>2 \<chi>)"
  by (meson assms prv_eqv_imp_transi prv_eqv_sym)

lemma prv_imp_monoL: "\<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> 
prv (imp \<chi> \<psi>) \<Longrightarrow> prv (imp (imp \<phi> \<chi>) (imp \<phi> \<psi>))"
  by (meson imp prv_imp_mp prv_imp_trans1)

lemma prv_imp_monoR: "\<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> 
prv (imp \<psi> \<chi>) \<Longrightarrow> prv (imp (imp \<chi> \<phi>) (imp \<psi> \<phi>))"
  by (meson imp prv_imp_mp prv_imp_trans2)


(* Properties concerning the quantifiers: *)

(* Fundamental properties: *)
lemma prv_allE: 
assumes "x \<in> var" and "\<phi> \<in> fmla" and "t \<in> trm"
shows "prv (all x \<phi>) \<Longrightarrow> prv (subst \<phi> t x)"
  using assms prv_all_inst prv_imp_mp by (meson subst all)

lemma prv_exiI: 
assumes "x \<in> var" and "\<phi> \<in> fmla" and "t \<in> trm"
shows "prv (subst \<phi> t x) \<Longrightarrow> prv (exi x \<phi>)"
  using assms prv_exi_inst prv_imp_mp by (meson subst exi)

lemma prv_imp_imp_exi: 
assumes "x \<in> var" and "\<phi> \<in> fmla" and "\<chi> \<in> fmla"
assumes "x \<notin> Fvars \<phi>"
shows "prv (imp (exi x (imp \<phi> \<chi>)) (imp \<phi> (exi x \<chi>)))" 
using assms imp exi Fvars_exi Fvars_imp Un_iff assms prv_exi_imp_gen prv_exi_inst prv_imp_mp 
      prv_imp_trans1 member_remove remove_def subst_same_Var by (metis (full_types) Var)

lemma prv_imp_exi: 
assumes "x \<in> var" and "\<phi> \<in> fmla" and "\<chi> \<in> fmla"
shows "x \<notin> Fvars \<phi> \<Longrightarrow> prv (exi x (imp \<phi> \<chi>)) \<Longrightarrow> prv (imp \<phi> (exi x \<chi>))"
  using assms prv_imp_imp_exi prv_imp_mp by (meson exi imp)
 
lemma prv_exi_imp:
assumes x: "x \<in> var" and "\<phi> \<in> fmla" and "\<chi> \<in> fmla"
assumes "x \<notin> Fvars \<chi>" and d: "prv (all x (imp \<phi> \<chi>))"
shows "prv (imp (exi x \<phi>) \<chi>)" 
proof-
  have "prv (imp \<phi> \<chi>)" using prv_allE[of x _ "Var x", of "imp \<phi> \<chi>"] assms by simp
  thus ?thesis using assms prv_exi_imp_gen by blast
qed

lemma prv_all_imp: 
assumes x: "x \<in> var" and "\<phi> \<in> fmla" and "\<chi> \<in> fmla"
assumes "x \<notin> Fvars \<phi>" and "prv (all x (imp \<phi> \<chi>))"
shows "prv (imp \<phi> (all x \<chi>))"    
proof-
  have "prv (imp \<phi> \<chi>)" using prv_allE[of x _ "Var x", of "imp \<phi> \<chi>"] assms by simp
  thus ?thesis using assms prv_all_imp_gen by blast
qed

lemma prv_exi_inst_same: 
assumes "\<phi> \<in> fmla" "\<chi> \<in> fmla" "x \<in> var" 
shows "prv (imp \<phi> (exi x \<phi>))"
proof-
  have 0: "\<phi> = subst \<phi> (Var x) x" using assms by simp
  show ?thesis apply(subst 0) apply(rule prv_exi_inst) using assms by auto
qed

lemma prv_exi_cong: 
assumes "\<phi> \<in> fmla" "\<chi> \<in> fmla" "x \<in> var" 
and "prv (imp \<phi> \<chi>)"
shows "prv (imp (exi x \<phi>) (exi x \<chi>))"
proof-
  have 0: "prv (imp \<chi> (exi x \<chi>))" using assms prv_exi_inst_same by auto
  show ?thesis apply(rule prv_exi_imp_gen) using assms apply auto 
    using "0" exi prv_prv_imp_trans by blast
qed

lemma prv_exi_congW: 
assumes "\<phi> \<in> fmla" "\<chi> \<in> fmla" "x \<in> var" 
and "prv (imp \<phi> \<chi>)" "prv (exi x \<phi>)"
shows "prv (exi x \<chi>)"
  by (meson exi assms prv_exi_cong prv_imp_mp)

lemma prv_all_cong: 
assumes "\<phi> \<in> fmla" "\<chi> \<in> fmla" "x \<in> var" 
and "prv (imp \<phi> \<chi>)"
shows "prv (imp (all x \<phi>) (all x \<chi>))"
proof-
  have 0: "prv (imp (all x \<phi>) \<chi>)" using assms  
    by (metis Var all prv_all_inst prv_prv_imp_trans subst_same_Var)
  show ?thesis by (simp add: "0" assms prv_all_imp_gen)
qed

lemma prv_all_congW: 
assumes "\<phi> \<in> fmla" "\<chi> \<in> fmla" "x \<in> var" 
and "prv (imp \<phi> \<chi>)" "prv (all x \<phi>)"
shows "prv (all x \<chi>)"
  by (meson all assms prv_all_cong prv_imp_mp)


(*********)

lemma exists_no_Fvars: "\<exists> \<phi>. \<phi> \<in> fmla \<and> prv \<phi> \<and> Fvars \<phi> = {}"
proof-
  obtain n where [simp]: "n \<in> num" using numNE by blast
  show ?thesis apply(rule exI[of _ "imp (eql n n) 
                           (eql n n)"])
    by (simp add: prv_imp_refl)
qed

lemma prv_all_gen:
assumes "x \<in> var" and "\<phi> \<in> fmla"
assumes "prv \<phi>" shows "prv (all x \<phi>)"  
  using assms prv_all_imp_gen prv_imp_mp prv_imp_triv exists_no_Fvars by blast

lemma prv_subst: 
assumes "x \<in> var" and "\<phi> \<in> fmla" and "t \<in> trm"  
shows "prv \<phi> \<Longrightarrow> prv (subst \<phi> t x)" 
  by (simp add: assms prv_allE prv_all_gen)

lemma prv_rawpsubst: 
assumes "\<phi> \<in> fmla" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm" 
and "prv \<phi>"
shows "prv (rawpsubst \<phi> txs)" 
using assms apply (induct txs arbitrary: \<phi>)
apply auto[] subgoal for tx txs \<phi> by (cases tx) (auto intro: prv_subst) .

lemma prv_psubst: 
assumes "\<phi> \<in> fmla" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm" 
and "prv \<phi>"
shows "prv (psubst \<phi> txs)" 
proof-
  define us where us: "us \<equiv> getFrN (map snd txs) (map fst txs) [\<phi>] (length txs)"
  have us_facts: "set us \<subseteq> var" 
  "set us \<inter> Fvars \<phi> = {}" 
  "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}" 
  "set us \<inter> snd ` (set txs) = {}"
  "length us = length txs"
  "distinct us"
  using assms unfolding us  
  using getFrN_FvarsT[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
        getFrN_Fvars[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
        getFrN_var[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
        getFrN_length[of "map snd txs" "map fst txs" "[\<phi>]" "length txs"]
        getFrN_length[of "map snd txs" "map fst txs" "[\<phi>]" "length txs"]
  apply auto by (metis (no_types, hide_lams) IntI empty_iff image_iff old.prod.inject surjective_pairing)
  show ?thesis using assms us_facts unfolding psubst_def 
  by (auto simp: Let_def us[symmetric] intro!: prv_rawpsubst rawpsubst dest!: set_zip_D)
qed

lemma prv_eqv_rawpsubst:
"\<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> snd ` set txs \<subseteq> var \<Longrightarrow> fst ` set txs \<subseteq> trm \<Longrightarrow> prv (eqv \<phi> \<psi>) \<Longrightarrow> 
 prv (eqv (rawpsubst \<phi> txs) (rawpsubst \<psi> txs))"
by (metis eqv prv_rawpsubst rawpsubst_eqv) 

lemma prv_eqv_psubst:
"\<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> snd ` set txs \<subseteq> var \<Longrightarrow> fst ` set txs \<subseteq> trm \<Longrightarrow> prv (eqv \<phi> \<psi>) \<Longrightarrow> 
 distinct (map snd txs) \<Longrightarrow> 
 prv (eqv (psubst \<phi> txs) (psubst \<psi> txs))" 
by (metis eqv prv_psubst psubst_eqv)

lemma prv_all_imp_trans:
assumes "x \<in> var" and "\<phi> \<in> fmla" and "\<chi> \<in> fmla" and "\<psi> \<in> fmla"
shows "prv (all x (imp \<phi> \<chi>)) \<Longrightarrow> prv (all x (imp \<chi> \<psi>)) \<Longrightarrow> prv (all x (imp \<phi> \<psi>))"
  by (metis Var assms prv_allE prv_all_gen prv_prv_imp_trans imp subst_same_Var)

lemma prv_all_imp_cnj:
assumes "x \<in> var" and "\<phi> \<in> fmla" and "\<chi> \<in> fmla" and "\<psi> \<in> fmla"
shows "prv (all x (imp \<phi> (imp \<psi> \<chi>))) \<Longrightarrow> prv (all x (imp (cnj \<psi> \<phi>) \<chi>))"
  by (metis Var assms cnj prv_allE prv_all_gen prv_imp_com prv_cnj_imp_monoR2 imp subst_same_Var)

lemma prv_all_imp_cnj_rev:
assumes "x \<in> var" and "\<phi> \<in> fmla" and "\<chi> \<in> fmla" and "\<psi> \<in> fmla"
shows "prv (all x (imp (cnj \<phi> \<psi>) \<chi>)) \<Longrightarrow> prv (all x (imp \<phi> (imp \<psi> \<chi>)))" 
  by (metis (full_types) Var assms cnj prv_allE prv_all_gen prv_cnj_imp imp subst_same_Var)

(* Conjunction vs conjunction (todo: move above) *)

lemma prv_cnj_com_imp:
 assumes \<phi>[simp]: "\<phi> \<in> fmla" and \<chi>[simp]: "\<chi> \<in> fmla"
 shows "prv (imp (cnj \<phi> \<chi>) (cnj \<chi> \<phi>))" 
  by (simp add: prv_imp_cnj prv_imp_cnjL prv_imp_cnjR)  

lemma prv_cnj_com:
 assumes \<phi>[simp]: "\<phi> \<in> fmla" and \<chi>[simp]: "\<chi> \<in> fmla"
 shows "prv (eqv (cnj \<phi> \<chi>) (cnj \<chi> \<phi>))"
  by (simp add: prv_cnj_com_imp prv_eqvI)

lemma prv_cnj_assoc_imp1:
 assumes \<phi>[simp]: "\<phi> \<in> fmla" and \<chi>[simp]: "\<chi> \<in> fmla" and \<psi>[simp]: "\<psi> \<in> fmla"
 shows "prv (imp (cnj \<phi> (cnj \<chi> \<psi>)) (cnj (cnj \<phi> \<chi>) \<psi>))" 
  by (simp add: prv_cnj_imp_monoR2 prv_imp_cnj prv_imp_cnjL prv_imp_cnjR prv_imp_triv)

lemma prv_cnj_assoc_imp2:
 assumes \<phi>[simp]: "\<phi> \<in> fmla" and \<chi>[simp]: "\<chi> \<in> fmla" and \<psi>[simp]: "\<psi> \<in> fmla"
 shows "prv (imp (cnj (cnj \<phi> \<chi>) \<psi>) (cnj \<phi> (cnj \<chi> \<psi>)))"
  by (smt \<chi> \<phi> \<psi> cnj prv_imp_cnj prv_imp_cnjL prv_imp_cnjR prv_prv_imp_trans)

lemma prv_cnj_assoc:
 assumes \<phi>[simp]: "\<phi> \<in> fmla" and \<chi>[simp]: "\<chi> \<in> fmla" and \<psi>[simp]: "\<psi> \<in> fmla"
 shows "prv (eqv (cnj \<phi> (cnj \<chi> \<psi>)) (cnj (cnj \<phi> \<chi>) \<psi>))" 
  by (simp add: prv_cnj_assoc_imp1 prv_cnj_assoc_imp2 prv_eqvI)

lemma prv_cnj_com_imp3: 
assumes "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla" "\<phi>3 \<in> fmla"
shows "prv (imp (cnj \<phi>1 (cnj \<phi>2 \<phi>3))
                (cnj \<phi>2 (cnj \<phi>1 \<phi>3)))"
  by (simp add: assms prv_cnj_imp_monoR2 prv_imp_cnj prv_imp_cnjL prv_imp_refl prv_imp_triv)

(*****)
(* Properties concerning equality: *)
lemma var_NE: "var \<noteq> {}"
  using infinite_var by auto
 
lemma prv_eql_reflT: 
assumes t: "t \<in> trm"
shows "prv (eql t t)"
proof-
  obtain x where x: "x \<in> var" using var_NE by auto
  show ?thesis using prv_subst[OF x _ t prv_eql_refl[OF x]] x t by simp
qed

lemma prv_eql_subst_trm: 
assumes xx: "x \<in> var" and \<phi>: "\<phi> \<in> fmla" and "t1 \<in> trm" and "t2 \<in> trm"
shows "prv ((imp (eql t1 t2)
                 (imp (subst \<phi> t1 x) (subst \<phi> t2 x))))"
proof-
  have "finite ({x} \<union> FvarsT t1 \<union> FvarsT t2 \<union> Fvars \<phi>)" (is "finite ?A")  
    by (simp add: assms finite_FvarsT finite_Fvars)
  then obtain y where y: "y \<in> var" and "y \<notin> ?A" 
    by (meson finite_subset infinite_var subset_iff)
  hence xy: "x \<noteq> y" and yt1: "y \<notin> FvarsT t1" and yt2: "y \<notin> FvarsT t2" and y\<phi>: "y \<notin> Fvars \<phi>" by auto
  have x: "x \<notin> Fvars (subst \<phi> (Var y) x)" using xy y assms by (simp add: Fvars_subst)
  hence 1: "prv (imp (eql t1 (Var y)) (imp (subst \<phi> t1 x) (subst \<phi> (Var y) x)))" 
    using xy y assms prv_subst[OF xx _ _ prv_eql_subst[OF xx y \<phi>]] by simp
  have yy: "y \<notin> Fvars (subst \<phi> t1 x)" using yt1 y\<phi> assms by (simp add: Fvars_subst)
  from prv_subst[OF y _ _ 1, of t2] 
  show ?thesis using xy yt1 yt2 y\<phi> x xx y yy assms by auto  
qed

lemma prv_eql_subst_trm2: 
assumes "x \<in> var" and "\<phi> \<in> fmla" and "t1 \<in> trm" and "t2 \<in> trm"
assumes "prv (eql t1 t2)"
shows "prv (imp (subst \<phi> t1 x) (subst \<phi> t2 x))"
  by (meson assms eql imp local.subst prv_eql_subst_trm prv_imp_mp)  

lemma prv_eql_sym: 
assumes "t1 \<in> trm" and "t2 \<in> trm"
shows "prv (imp (eql t1 t2) (eql t2 t1))"
proof-
  obtain x where x: "x \<in> var" and "x \<notin> FvarsT t1" 
    by (meson assms finite_FvarsT finite_subset infinite_var subsetI)
  thus ?thesis using prv_eql_subst_trm[of x "eql (Var x) t1" t1 t2] apply simp
  using assms prv_eql_reflT prv_imp_com prv_imp_mp x imp  
  by (meson eql)
qed 

lemma prv_prv_eql_sym: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> prv (eql t1 t2) \<Longrightarrow> prv (eql t2 t1)"
  by (meson eql prv_eql_sym prv_imp_mp)

lemma prv_all_eql: 
assumes "x \<in> var" and "y \<in> var" and "\<phi> \<in> fmla" and "t1 \<in> trm" and "t2 \<in> trm"
shows "prv (all x ((imp (eql t1 t2)
                   (imp (subst \<phi> t2 y) (subst \<phi> t1 y)))))"
  by (meson subst assms prv_all_gen prv_prv_imp_trans prv_eql_subst_trm prv_eql_sym eql imp)

lemma prv_eql_subst_trm_rev: 
assumes "t1 \<in> trm" and "t2 \<in> trm" and "\<phi> \<in> fmla" and "y \<in> var"
shows 
"prv ((imp (eql t1 t2)
           (imp (subst \<phi> t2 y) (subst \<phi> t1 y))))"
  using assms prv_all_eql prv_all_inst prv_imp_mp subst_same_Var 
  by (meson subst prv_prv_imp_trans prv_eql_subst_trm prv_eql_sym eql imp)

lemma prv_eql_subst_trm_rev2: 
assumes "x \<in> var" and "\<phi> \<in> fmla" and "t1 \<in> trm" and "t2 \<in> trm"
assumes "prv (eql t1 t2)"
shows "prv (imp (subst \<phi> t2 x) (subst \<phi> t1 x))"
  by (meson assms eql imp local.subst prv_eql_subst_trm_rev prv_imp_mp)

lemma prv_eql_subst_trm_eqv: 
assumes "x \<in> var" and "\<phi> \<in> fmla" and "t1 \<in> trm" and "t2 \<in> trm"
assumes "prv (eql t1 t2)"
shows "prv (eqv (subst \<phi> t1 x) (subst \<phi> t2 x))"
using assms prv_eql_subst_trm2[OF assms] prv_eql_subst_trm_rev2[OF assms] 
  prv_eqvI by auto

lemma all_subst_rename_prv:  
"\<phi> \<in> fmla \<Longrightarrow> x \<in> var \<Longrightarrow> y \<in> var \<Longrightarrow> 
   y \<notin> Fvars \<phi> \<Longrightarrow> prv (all x \<phi>) \<Longrightarrow> prv (all y (subst \<phi> (Var y) x))"
  by (simp add: prv_allE prv_all_gen)

lemma allE_id: 
assumes "y \<in> var" and "\<phi> \<in> fmla" 
assumes "prv (all y \<phi>)"
shows "prv \<phi>"
  using assms prv_allE  
  by (metis Var subst_same_Var) 

lemma prv_eql_subst_trm_id:
assumes "y \<in> var" "\<phi> \<in> fmla" and "n \<in> num"
shows "prv (imp (eql (Var y) n) (imp \<phi> (subst \<phi> n y)))"
  using assms prv_eql_subst_trm 
  by (metis Var in_num subst_same_Var)  

lemma prv_eql_subst_trm_id_back:
assumes "y \<in> var" "\<phi> \<in> fmla" and "n \<in> num"
shows "prv (imp (eql (Var y) n) (imp (subst \<phi> n y) \<phi>))"
  by (metis Var assms in_num prv_eql_subst_trm_rev subst_same_Var)

lemma prv_eql_subst_trm_id_rev:
assumes "y \<in> var" "\<phi> \<in> fmla" and "n \<in> num"
shows "prv (imp (eql n (Var y)) (imp \<phi> (subst \<phi> n y)))"
  using assms prv_eql_subst_trm_rev  
  by (metis Var in_num subst_same_Var)  

lemma prv_eql_subst_trm_id_back_rev:
assumes "y \<in> var" "\<phi> \<in> fmla" and "n \<in> num"
shows "prv (imp (eql n (Var y)) (imp (subst \<phi> n y) \<phi>))"
  by (metis (full_types) Var assms(1) assms(2) assms(3) in_num prv_eql_subst_trm subst_same_Var)

lemma prv_eql_imp_trans_rev:
assumes t1[simp]: "t1 \<in> trm" and t2[simp]: "t2 \<in> trm" and t3[simp]: "t3 \<in> trm"
shows "prv (imp (eql t1 t2) (imp (eql t1 t3) (eql t2 t3)))"
proof-
  obtain y1 where y1[simp]: "y1 \<in> var" and "y1 \<notin> FvarsT t1 \<union> FvarsT t2 \<union> FvarsT t3" 
    using finite_FvarsT finite_subset infinite_var subsetI t1 t2 t3
    by (metis (full_types) infinite_Un)
  hence [simp]: "y1 \<notin> FvarsT t1" "y1 \<notin> FvarsT t2" "y1 \<notin>  FvarsT t3" by auto
  obtain y2 where y2[simp]: "y2 \<in> var" and "y2 \<notin> FvarsT t1 \<union> FvarsT t2 \<union> FvarsT t3 \<union> {y1}" 
    using finite_FvarsT finite_subset infinite_var subsetI t1 t2 t3
    by (metis (full_types) finite_insert infinite_Un insert_is_Un)
  hence [simp]: "y2 \<notin> FvarsT t1" "y2 \<notin> FvarsT t2" "y2 \<notin>  FvarsT t3" "y1 \<noteq> y2" by auto
  have 0: "prv (imp (eql (Var y1) (Var y2)) 
                    (imp (eql (Var y1) t3) (eql (Var y2) t3)))" 
    using prv_eql_subst[OF y1 y2, of "eql (Var y1) t3"] by simp
  note 1 = prv_subst[OF y1 _ t1 0, simplified]
  show ?thesis using prv_subst[OF y2 _ t2 1, simplified] .
qed

lemma prv_eql_imp_trans:
assumes t1[simp]: "t1 \<in> trm" and t2[simp]: "t2 \<in> trm" and t3[simp]: "t3 \<in> trm"
shows "prv (imp (eql t1 t2) (imp (eql t2 t3) (eql t1 t3)))"
  by (meson eql imp prv_eql_sym prv_eql_imp_trans_rev prv_prv_imp_trans t1 t2 t3)

lemma prv_eql_trans:
assumes t1[simp]: "t1 \<in> trm" and t2[simp]: "t2 \<in> trm" and t3[simp]: "t3 \<in> trm"
and "prv (eql t1 t2)" and "prv (eql t2 t3)"
shows "prv (eql t1 t3)"
  by (meson assms cnj eql prv_cnjI prv_cnj_imp_monoR2 prv_eql_imp_trans prv_imp_mp)


(* Soft substitution is equivalent to substitution *)

lemma prv_subst_imp_softSubst: 
assumes [simp,intro!]: "x \<in> var" "t \<in> trm" "\<phi> \<in> fmla" "x \<notin> FvarsT t" 
shows "prv (imp (subst \<phi> t x) (softSubst \<phi> t x))" 
unfolding softSubst_def by (rule prv_imp_exi) 
(auto simp: prv_eql_reflT prv_imp_cnj prv_imp_refl prv_imp_triv subst_compose_same Fvars_subst 
      intro: prv_exiI[of _ _ t]) 

lemma prv_subst_implies_softSubst: 
assumes "x \<in> var" "t \<in> trm" "\<phi> \<in> fmla"
and "x \<notin> FvarsT t"
and "prv (subst \<phi> t x)"
shows "prv (softSubst \<phi> t x)"  
using assms prv_subst_imp_softSubst 
  by (metis Var cnj eql exi subst prv_imp_mp softSubst_def) 

lemma prv_softSubst_imp_subst: 
assumes [simp,intro!]: "x \<in> var" "t \<in> trm" "\<phi> \<in> fmla" "x \<notin> FvarsT t" 
shows "prv (imp (softSubst \<phi> t x) (subst \<phi> t x))" 
  unfolding softSubst_def apply(rule prv_exi_imp_gen) apply (auto simp: Fvars_subst)
  by (metis Var assms eql subst prv_cnj_imp_monoR2 prv_eql_subst_trm subst_same_Var)

lemma prv_softSubst_implies_subst: 
assumes "x \<in> var" "t \<in> trm" "\<phi> \<in> fmla"
and "x \<notin> FvarsT t"
and "prv (softSubst \<phi> t x)"
shows "prv (subst \<phi> t x)" 
  by (metis Var assms cnj eql exi local.subst prv_imp_mp prv_softSubst_imp_subst softSubst_def)

lemma prv_softSubst_eqv_subst: 
assumes [simp,intro!]: "x \<in> var" "t \<in> trm" "\<phi> \<in> fmla" "x \<notin> FvarsT t" 
shows "prv (eqv (softSubst \<phi> t x) (subst \<phi> t x))" 
by (metis Var assms cnj eql exi local.subst prv_eqvI prv_softSubst_imp_subst prv_subst_imp_softSubst softSubst_def)



end(* context Deduct_with_Numerals_and_Connectives *)


(* Deduction that incorporates false: *)
locale Deduct_with_False = 
Syntax_with_Connectives_False
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls  
+
Deduct 
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and eql cnj imp all exi 
and fls
and num  
and prv
+
assumes
prv_fls[simp,intro]: "\<And>\<phi>. prv (imp fls \<phi>)"
begin

(* Basic properties of fls (False): *)
lemma prv_expl: 
assumes "\<phi> \<in> fmla"
assumes "prv fls"
shows "prv \<phi>"   
  using assms prv_imp_mp by blast

lemma prv_cnjR_fls: "\<phi> \<in> fmla \<Longrightarrow> prv (eqv (cnj fls \<phi>) fls)" 
  by (simp add: prv_eqvI prv_imp_cnjL)

lemma prv_cnjL_fls: "\<phi> \<in> fmla \<Longrightarrow> prv (eqv (cnj \<phi> fls) fls)" 
  by (simp add: prv_eqvI prv_imp_cnjR)


(* Properties involving negation: *)

lemma prv_imp_neg_fls:
assumes "\<phi> \<in> fmla"
shows "prv (imp \<phi> (imp (neg \<phi>) fls))"
using assms prv_imp_com prv_imp_refl neg_def by auto

lemma prv_neg_fls:
assumes "\<phi> \<in> fmla"   
assumes "prv \<phi>" and "prv (neg \<phi>)"
shows "prv fls" 
  by (metis assms prv_imp_mp fls neg_def)

lemma prv_imp_neg_neg:
assumes "\<phi> \<in> fmla"
shows "prv (imp \<phi> (neg (neg \<phi>)))"
  using assms prv_imp_neg_fls neg_def by auto

lemma prv_neg_neg:
assumes "\<phi> \<in> fmla"
assumes "prv \<phi>" 
shows "prv (neg (neg \<phi>))"
  by (metis assms prv_imp_mp prv_imp_neg_fls neg neg_def)

lemma prv_imp_imp_neg_rev: 
assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla" 
shows "prv (imp (imp \<phi> \<chi>)
                (imp (neg \<chi>) (neg \<phi>)))"
  unfolding neg_def using prv_imp_trans2[OF assms fls] .

lemma prv_imp_neg_rev: 
assumes "\<phi> \<in> fmla" and "\<chi> \<in> fmla" 
assumes "prv (imp \<phi> \<chi>)"
shows "prv (imp (neg \<chi>) (neg \<phi>))"
  by (meson assms imp neg prv_imp_imp_neg_rev prv_imp_mp)

lemma prv_eqv_neg_prv_fls:
"\<phi> \<in> fmla \<Longrightarrow>  
prv (eqv \<phi> (neg \<phi>)) \<Longrightarrow> prv fls"
by (metis cnj fls neg neg_def prv_cnj_imp_monoR2 prv_eqv_imp_transi prv_imp_cnj prv_imp_eqvER prv_imp_mp prv_imp_neg_rev)

lemma prv_eqv_eqv_neg_prv_fls:
"\<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> 
prv (eqv \<phi> \<chi>) \<Longrightarrow> prv (eqv \<phi> (neg \<chi>))\<Longrightarrow> prv fls"
  by (meson neg prv_eqv_neg_prv_fls prv_eqv_sym prv_eqv_trans)

lemma prv_eqv_eqv_neg_prv_fls2:
"\<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> 
prv (eqv \<phi> \<chi>) \<Longrightarrow> prv (eqv \<chi> (neg \<phi>))\<Longrightarrow> prv fls"  
  by (simp add: prv_eqv_eqv_neg_prv_fls prv_eqv_sym)

lemma prv_neg_imp_imp_trans: 
assumes "\<phi> \<in> fmla" "\<chi> \<in> fmla"  "\<psi> \<in> fmla" 
and "prv (neg \<phi>)"
and "prv (imp \<chi> (imp \<psi> \<phi>))"
shows "prv (imp \<chi> (neg \<psi>))"
unfolding neg_def   
  by (metis assms cnj fls neg_def prv_cnj_imp prv_cnj_imp_monoR2 prv_prv_imp_trans)

lemma prv_imp_neg_imp_neg_imp:
assumes "\<phi> \<in> fmla" "\<chi> \<in> fmla"  
and "prv (neg \<phi>)" 
shows "prv ((imp \<chi> (neg (imp \<chi> \<phi>))))" 
  by (metis assms fls imp neg_def prv_imp_com prv_imp_monoL)

lemma prv_prv_neg_imp_neg: 
assumes "\<phi> \<in> fmla" "\<chi> \<in> fmla" 
and "prv \<phi>" and "prv \<chi>"
shows "prv (neg (imp \<phi> (neg \<chi>)))"
  by (meson assms imp neg prv_imp_mp prv_imp_neg_imp_neg_imp prv_neg_neg)

lemma prv_imp_neg_imp_cnjL: 
assumes "\<phi> \<in> fmla" "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla" 
and "prv (imp \<phi> (neg \<phi>1))" 
shows "prv (imp \<phi> (neg (cnj \<phi>1 \<phi>2)))"
  unfolding neg_def by (metis assms cnj fls neg neg_def prv_imp_cnj3L prv_prv_imp_trans)

lemma prv_imp_neg_imp_cnjR: 
assumes "\<phi> \<in> fmla" "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla" 
and "prv (imp \<phi> (neg \<phi>2))" 
shows "prv (imp \<phi> (neg (cnj \<phi>1 \<phi>2)))"
  unfolding neg_def by (metis assms cnj fls neg neg_def prv_imp_cnj3R prv_prv_imp_trans)

(* Negation versus quantifiers: *)
lemma prv_all_neg_imp_neg_exi: 
assumes x: "x \<in> var" and \<phi>: "\<phi> \<in> fmla"
shows "prv (imp (all x (neg \<phi>)) (neg (exi x \<phi>)))"
proof-
  have 0: "prv (imp (all x (neg \<phi>)) (imp \<phi> fls))" 
    using prv_all_inst[OF x, of "neg \<phi>" "Var x",simplified] assms by (auto simp: neg_def)
  have 1: "prv (imp \<phi> (imp (all x (neg \<phi>)) fls))" 
    using 0 by (simp add: assms  prv_imp_com)
  have 2: "prv (imp (exi x \<phi>) (imp (all x (neg \<phi>)) fls))"
    apply(rule prv_exi_imp_gen) using 1 assms by auto
  thus ?thesis by (simp add: assms  neg_def prv_imp_com)
qed

lemma prv_neg_exi_imp_all_neg: 
assumes x: "x \<in> var" and \<phi>: "\<phi> \<in> fmla"
shows "prv (imp (neg (exi x \<phi>)) (all x (neg \<phi>)))"
apply(rule prv_all_imp_gen[of x "neg (exi x \<phi>)"])
  using assms by (auto simp: prv_exi_inst_same prv_imp_neg_rev)

lemma prv_neg_exi_eqv_all_neg: 
assumes x: "x \<in> var" and \<phi>: "\<phi> \<in> fmla"
shows "prv (eqv (neg (exi x \<phi>)) (all x (neg \<phi>)))"
  by (simp add: \<phi> prv_all_neg_imp_neg_exi prv_eqvI prv_neg_exi_imp_all_neg x)

lemma prv_neg_exi_implies_all_neg: 
assumes x: "x \<in> var" and \<phi>: "\<phi> \<in> fmla" and "prv (neg (exi x \<phi>))"
shows "prv (all x (neg \<phi>))"
  by (meson \<phi> all assms(3) exi neg prv_imp_mp prv_neg_exi_imp_all_neg x)

lemma prv_neg_neg_exi: 
assumes "x \<in> var" "\<phi> \<in> fmla"
and "prv (neg \<phi>)"
shows "prv (neg (exi x \<phi>))" 
using assms neg_def prv_exi_imp_gen by auto

lemma prv_exi_imp_exiI: 
assumes [simp]: "x \<in> var" "y \<in> var" "\<phi> \<in> fmla" and yx: "y = x \<or> y \<notin> Fvars \<phi>"
shows "prv (imp (exi x \<phi>) (exi y (subst \<phi> (Var y) x)))" 
proof(cases "y = x")
  case [simp]: False 
  show ?thesis apply(rule prv_exi_imp_gen) apply (simp_all add: Fvars_subst)
  apply(rule prv_imp_exi) using yx apply simp_all
  apply(rule prv_exiI[of _ _ "Var x"]) apply simp_all  
  by (metis Var assms prv_imp_refl2 subst_same_Var subst_subst)
qed(simp add: yx prv_imp_refl)

lemma prv_imp_neg_allI: 
assumes "\<phi> \<in> fmla" "\<chi> \<in> fmla" "t \<in> trm" "x \<in> var"
and "prv (imp \<phi> (neg (subst \<chi> t x)))"
shows "prv (imp \<phi> (neg (all x \<chi>)))"
  by (meson all assms subst neg prv_all_inst prv_imp_neg_rev prv_prv_imp_trans)

lemma prv_imp_neg_allWI: 
assumes "\<chi> \<in> fmla" "t \<in> trm" "x \<in> var"
and "prv (neg (subst \<chi> t x))"
shows "prv (neg (all x \<chi>))"
  by (metis all assms fls subst neg_def prv_all_inst prv_prv_imp_trans)

(* Properties pertaining to the tru (True) constant: *)
lemma prv_imp_tru: "\<phi> \<in> fmla \<Longrightarrow> prv (imp \<phi> tru)" 
  by (simp add: neg_def prv_imp_triv tru_def)

lemma prv_tru_imp: "\<phi> \<in> fmla \<Longrightarrow> prv (eqv (imp tru \<phi>) \<phi>)" 
  by (metis imp neg_def prv_eqvI prv_fls prv_imp_com prv_imp_imp_triv prv_imp_mp prv_imp_refl tru tru_def)

lemma prv_fls_neg_tru: "\<phi> \<in> fmla \<Longrightarrow> prv (eqv fls (neg tru))" 
  using neg_def prv_eqvI prv_neg_neg tru_def by auto

lemma prv_tru_neg_fls: "\<phi> \<in> fmla \<Longrightarrow> prv (eqv tru (neg fls))" 
  by (simp add: prv_eqv_refl tru_def)

lemma prv_cnjR_tru: "\<phi> \<in> fmla \<Longrightarrow> prv (eqv (cnj tru \<phi>) \<phi>)" 
  by (simp add: prv_eqvI prv_imp_cnj prv_imp_cnjR prv_imp_refl prv_imp_tru)

lemma prv_cnjL_tru: "\<phi> \<in> fmla \<Longrightarrow> prv (eqv (cnj \<phi> tru) \<phi>)" 
  by (simp add: prv_eqvI prv_imp_cnj prv_imp_cnjL prv_imp_refl prv_imp_tru)

(**)
(* Properties of set conjunctions. 
These are based on properties of then auxiliary list conjunctions. *)

lemma prv_lcnj_imp_in: 
  assumes "set \<phi>s \<subseteq> fmla"
  and "\<phi> \<in> set \<phi>s"
  shows "prv (imp (lcnj \<phi>s) \<phi>)"
proof-
  have "\<phi> \<in> fmla" using assms by auto
  thus ?thesis using assms apply(induct \<phi>s arbitrary: \<phi>)   
  by (auto simp : prv_imp_cnjL prv_cnj_imp_monoR2 prv_imp_triv)
qed

lemma prv_lcnj_imp: 
assumes "\<chi> \<in> fmla" and "set \<phi>s \<subseteq> fmla"
and "\<phi> \<in> set \<phi>s" and "prv (imp \<phi> \<chi>)"  
shows "prv (imp (lcnj \<phi>s) \<chi>)"
  using assms lcnj prv_lcnj_imp_in prv_prv_imp_trans by blast

lemma prv_imp_lcnj: 
  assumes "\<chi> \<in> fmla" and "set \<phi>s \<subseteq> fmla"
  and "\<And>\<phi>. \<phi> \<in> set \<phi>s \<Longrightarrow> prv (imp \<chi> \<phi>)"
  shows "prv (imp \<chi> (lcnj \<phi>s))"
  using assms apply(induct \<phi>s arbitrary: \<chi>)    
  by (auto simp add: prv_imp_tru prv_imp_com prv_imp_cnj)  

lemma prv_lcnj_imp_inner:
assumes "\<phi> \<in> fmla" "set \<phi>1s \<subseteq> fmla" "set \<phi>2s \<subseteq> fmla" 
shows "prv (imp (cnj \<phi> (lcnj (\<phi>1s @ \<phi>2s))) (lcnj (\<phi>1s @ \<phi> # \<phi>2s)))"
using assms proof(induction \<phi>1s)
  case (Cons \<phi>1 \<phi>1s)
  have [intro!]: "set (\<phi>1s @ \<phi>2s) \<subseteq> fmla" "set (\<phi>1s @ \<phi> # \<phi>2s) \<subseteq> fmla"  using Cons by auto
  have 0: "prv (imp (cnj \<phi> (cnj \<phi>1 (lcnj (\<phi>1s @ \<phi>2s)))) 
                 (cnj \<phi>1 (cnj \<phi> (lcnj (\<phi>1s @ \<phi>2s)))))" 
    apply(rule prv_cnj_com_imp3) using Cons by fastforce+
  have 1: "prv (imp (cnj \<phi>1 (cnj \<phi> (lcnj (\<phi>1s @ \<phi>2s)))) 
                 (cnj \<phi>1 (lcnj (\<phi>1s @ \<phi> # \<phi>2s))))"
  using Cons by (intro prv_cnj_mono) (auto simp add: prv_imp_refl)  
  show ?case using prv_prv_imp_trans[OF _ _ _ 0 1] Cons by auto
qed(simp add: prv_imp_refl)

lemma prv_lcnj_imp_remdups:
assumes "set \<phi>s \<subseteq> fmla"  
shows "prv (imp (lcnj (remdups \<phi>s)) (lcnj \<phi>s))" 
  using assms apply(induct \<phi>s)  
  by (auto simp: prv_imp_cnj prv_lcnj_imp_in prv_cnj_mono prv_imp_refl)
    
lemma prv_lcnj_mono:
assumes \<phi>1s: "set \<phi>1s \<subseteq> fmla" and "set \<phi>2s \<subseteq> set \<phi>1s"  
shows "prv (imp (lcnj \<phi>1s) (lcnj \<phi>2s))"
proof-
  define \<phi>2s' where \<phi>2s': "\<phi>2s' = remdups \<phi>2s"
  have A: "set \<phi>2s' \<subseteq> set \<phi>1s" "distinct \<phi>2s'" unfolding  \<phi>2s' using assms by auto
  have B: "prv (imp (lcnj \<phi>1s) (lcnj \<phi>2s'))"
  using \<phi>1s A proof(induction \<phi>1s arbitrary: \<phi>2s')
    case (Cons \<phi>1 \<phi>1s \<phi>2ss)  
    show ?case proof(cases "\<phi>1 \<in> set \<phi>2ss")
      case True
      then obtain \<phi>2ss1 \<phi>2ss2 where \<phi>2ss: "\<phi>2ss = \<phi>2ss1 @ \<phi>1 # \<phi>2ss2"       
      by (meson split_list)
      define \<phi>2s where \<phi>2s: "\<phi>2s \<equiv> \<phi>2ss1 @ \<phi>2ss2" 
      have nin: "\<phi>1 \<notin> set \<phi>2s" using \<phi>2ss `distinct \<phi>2ss` unfolding \<phi>2s by auto
      have [intro!]: "set \<phi>2s \<subseteq> fmla" unfolding \<phi>2s using \<phi>2ss Cons by auto
      have 0: "prv (imp (cnj \<phi>1 (lcnj \<phi>2s)) (lcnj \<phi>2ss))"
      unfolding \<phi>2s \<phi>2ss apply(rule prv_lcnj_imp_inner) using Cons \<phi>2ss by auto
      have 1: "prv (imp (lcnj \<phi>1s) (lcnj \<phi>2s))" apply(rule Cons.IH) using nin Cons.prems True  
      using \<phi>2s \<phi>2ss by  auto
      have 2: "prv (imp (cnj \<phi>1 (lcnj \<phi>1s)) (cnj \<phi>1 (lcnj \<phi>2s)))"
      using Cons \<phi>2ss \<phi>2s 1 by (intro prv_cnj_mono) (fastforce simp add: prv_imp_refl)+ 
      show ?thesis apply simp apply(rule prv_prv_imp_trans[OF _ _ _ 2 0]) using Cons by auto
    next
      case False
      then show ?thesis using Cons apply simp
      by (meson cnj lcnj prv_imp_cnjR prv_prv_imp_trans subset_insert subset_trans)
    qed  
  qed(simp add: prv_imp_refl)
  have C: "prv (imp (lcnj \<phi>2s') (lcnj \<phi>2s))"
    unfolding \<phi>2s' apply(rule prv_lcnj_imp_remdups) using assms by auto
  show ?thesis apply(rule prv_prv_imp_trans[OF _ _ _ B C]) using A assms by auto
qed

lemma prv_lcnj_eqv:
assumes "set \<phi>1s \<subseteq> fmla" and "set \<phi>2s = set \<phi>1s"
shows "prv (eqv (lcnj \<phi>1s) (lcnj \<phi>2s))"
  apply(rule prv_eqvI) using assms prv_lcnj_mono by auto

lemma prv_lcnj_mono_imp:
  assumes "set \<phi>1s \<subseteq> fmla" "set \<phi>2s \<subseteq> fmla" and "\<forall> \<phi>2 \<in> set \<phi>2s. \<exists> \<phi>1 \<in> set \<phi>1s. prv (imp \<phi>1 \<phi>2)"  
  shows "prv (imp (lcnj \<phi>1s) (lcnj \<phi>2s))"
  apply(rule prv_imp_lcnj) using assms apply auto 
  using prv_lcnj_imp by blast


(* Commutation of scnj with substitution  works only up to equivalence, not for equality 
(this is why it's here, not in Syntax): *)
lemma prv_subst_scnj: 
assumes "F \<subseteq> fmla" "finite F" "t \<in> trm" "x \<in> var"
shows "prv (eqv (subst (scnj F) t x) (scnj ((\<lambda>\<phi>. subst \<phi> t x) ` F)))" 
using assms unfolding scnj_def by (fastforce intro!: prv_lcnj_eqv)

lemma prv_imp_subst_scnj: 
assumes "F \<subseteq> fmla" "finite F" "t \<in> trm" "x \<in> var"
shows "prv (imp (subst (scnj F) t x) (scnj ((\<lambda>\<phi>. subst \<phi> t x) ` F)))"
using prv_subst_scnj[OF assms] assms apply(intro prv_imp_eqvEL) by auto

lemma prv_subst_scnj_imp: 
assumes "F \<subseteq> fmla" "finite F" "t \<in> trm" "x \<in> var"
shows "prv (imp (scnj ((\<lambda>\<phi>. subst \<phi> t x) ` F)) (subst (scnj F) t x))"
using prv_subst_scnj[OF assms] assms apply(intro prv_imp_eqvER) by auto

lemma prv_scnj_imp_in: 
  assumes "F \<subseteq> fmla" "finite F"
  and "\<phi> \<in> F"
  shows "prv (imp (scnj F) \<phi>)"
  unfolding scnj_def apply(rule prv_lcnj_imp_in) using assms by auto

lemma prv_scnj_imp: 
assumes "\<chi> \<in> fmla" and "F \<subseteq> fmla" "finite F"
and "\<phi> \<in> F" and "prv (imp \<phi> \<chi>)"  
shows "prv (imp (scnj F) \<chi>)"
  unfolding scnj_def apply(rule prv_lcnj_imp) using assms by auto

lemma prv_imp_scnj: 
  assumes "\<chi> \<in> fmla" and "F \<subseteq> fmla" "finite F"
  and "\<And>\<phi>. \<phi> \<in> F \<Longrightarrow> prv (imp \<chi> \<phi>)"  
  shows "prv (imp \<chi> (scnj F))"
  unfolding scnj_def apply(rule prv_imp_lcnj) using assms by auto  
 
lemma prv_scnj_mono:
assumes "F1 \<subseteq> fmla" and "F2 \<subseteq> F1" and "finite F1"  
shows "prv (imp (scnj F1) (scnj F2))"
  unfolding scnj_def apply(rule prv_lcnj_mono) using assms  
  by auto (metis asList contra_subsetD infinite_super) 

lemma prv_scnj_mono_imp:
  assumes "F1 \<subseteq> fmla" "F2 \<subseteq> fmla" "finite F1" "finite F2"  
  and "\<forall> \<phi>2 \<in> F2. \<exists> \<phi>1 \<in> F1. prv (imp \<phi>1 \<phi>2)"  
  shows "prv (imp (scnj F1) (scnj F2))"
  unfolding scnj_def apply(rule prv_lcnj_mono_imp) using assms by auto 


(**)
lemma prv_imp_scnj_insert: 
assumes "F \<subseteq> fmla" and "finite F" and "\<phi> \<in> fmla"
shows "prv (imp (scnj (insert \<phi> F)) (cnj \<phi> (scnj F)))"
using assms apply (intro prv_imp_cnj) apply auto
apply(intro prv_scnj_imp) apply (auto intro: prv_imp_refl)
apply(intro prv_scnj_mono) apply auto .

lemma prv_implies_scnj_insert: 
assumes "F \<subseteq> fmla" and "finite F" and "\<phi> \<in> fmla"
and "prv (scnj (insert \<phi> F))"
shows "prv (cnj \<phi> (scnj F))"
by (meson assms  cnj finite.insertI insert_subset prv_imp_mp prv_imp_scnj_insert scnj)

lemma prv_imp_cnj_scnj: 
assumes "F \<subseteq> fmla" and "finite F" and "\<phi> \<in> fmla"
shows "prv (imp (cnj \<phi> (scnj F)) (scnj (insert \<phi> F)))"
using assms apply (intro prv_imp_scnj) apply auto
apply(intro prv_imp_cnjL) 
by (auto simp: prv_cnj_imp_monoR2 prv_imp_triv prv_scnj_imp_in subset_iff)

lemma prv_implies_cnj_scnj: 
assumes "F \<subseteq> fmla" and "finite F" and "\<phi> \<in> fmla"
and "prv (cnj \<phi> (scnj F))"
shows "prv (scnj (insert \<phi> F))"
by (meson assms  cnj finite.insertI insert_subset prv_imp_cnj_scnj prv_imp_mp scnj)

lemma prv_eqv_scnj_insert: 
assumes "F \<subseteq> fmla" and "finite F" and "\<phi> \<in> fmla"
shows "prv (eqv (scnj (insert \<phi> F)) (cnj \<phi> (scnj F)))"
by (simp add: assms prv_eqvI prv_imp_cnj_scnj prv_imp_scnj_insert)

lemma prv_scnj1_imp: 
"\<phi> \<in> fmla \<Longrightarrow> prv (imp (scnj {\<phi>}) \<phi>)" 
using prv_scnj_imp_in by auto

lemma prv_imp_scnj1: 
"\<phi> \<in> fmla \<Longrightarrow> prv (imp \<phi> (scnj {\<phi>}))"  
using prv_imp_refl prv_imp_scnj by fastforce 

lemma prv_scnj2_imp_cnj: 
"\<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> prv (imp (scnj {\<phi>,\<psi>}) (cnj \<phi> \<psi>))"
using prv_imp_cnj prv_scnj_imp_in by auto

lemma prv_cnj_imp_scnj2: 
"\<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> prv (imp (cnj \<phi> \<psi>) (scnj {\<phi>,\<psi>}))"
  using prv_imp_cnjL prv_imp_cnjR prv_imp_scnj by fastforce

lemma prv_imp_imp_scnj2: 
"\<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> prv (imp \<phi> (imp \<psi> (scnj {\<phi>,\<psi>})))"
  using prv_cnj_imp_scnj2 prv_cnj_imp by auto

(* *)
lemma prv_rawpsubst_scnj: 
assumes "F \<subseteq> fmla" "finite F"
and "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
shows "prv (eqv (rawpsubst (scnj F) txs) (scnj ((\<lambda>\<phi>. rawpsubst \<phi> txs) ` F)))"
using assms proof(induction txs arbitrary: F)
  case (Cons tx txs)
  then obtain t x where tx[simp]: "tx = (t,x)" by (cases tx) auto
  hence [simp]: "t \<in> trm" "x \<in> var" using Cons.prems by auto
  have 0: "(\<lambda>\<phi>. rawpsubst (subst \<phi> t x) txs) ` F = 
           (\<lambda>\<phi>. rawpsubst \<phi> txs) ` ((\<lambda>\<phi>. subst \<phi> t x) ` F)"
  using Cons.prems by auto
  have "prv (eqv (subst (scnj F) t x) 
                 (scnj ((\<lambda>\<phi>. subst \<phi> t x) ` F)))" 
  apply(rule prv_subst_scnj) using Cons.prems by auto
  hence "prv (eqv (rawpsubst (subst (scnj F) t x) txs) 
                  (rawpsubst (scnj ((\<lambda>\<phi>. subst \<phi> t x) ` F)) txs))"
  (* AtoD: find_theorems intro found nothing, not even after apply- ! *)
  apply(intro prv_eqv_rawpsubst) using Cons.prems by auto
  moreover 
  have "prv (eqv (rawpsubst (scnj ((\<lambda>\<phi>. subst \<phi> t x) ` F)) txs) 
                 (scnj ((\<lambda>\<phi>. rawpsubst (subst \<phi> t x) txs) ` F)))"
  unfolding 0  apply(rule Cons.IH) using Cons.prems by auto
  ultimately show ?case apply- apply(rule prv_eqv_trans) using Cons.prems by (auto intro!: rawpsubst)
qed(auto simp: image_def prv_eqv_refl)[] 

lemma prv_psubst_scnj:  
assumes "F \<subseteq> fmla" "finite F"
and "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
and "distinct (map snd txs)" 
shows "prv (eqv (psubst (scnj F) txs) (scnj ((\<lambda>\<phi>. psubst \<phi> txs) ` F)))" 
proof-  
  define us where us: "us \<equiv> getFrN (map snd txs) (map fst txs) [scnj F] (length txs)"
  have us_facts: "set us \<subseteq> var" 
  "set us \<inter> \<Union> (Fvars ` F) = {}" 
  "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}" 
  "set us \<inter> snd ` (set txs) = {}"
  "length us = length txs"
  "distinct us" 
  using assms unfolding us      
  using getFrN_Fvars[of "map snd txs" "map fst txs" "[scnj F]" _ "length txs"]
        getFrN_FvarsT[of "map snd txs" "map fst txs" "[scnj F]" _ "length txs"]
        getFrN_var[of "map snd txs" "map fst txs" "[scnj F]" _ "length txs"]
        getFrN_length[of "map snd txs" "map fst txs" "[scnj F]" "length txs"]  
  apply auto apply fastforce  
  by (smt IntI empty_iff image_iff snd_conv)
  
  define vs where vs: "vs \<equiv> \<lambda> \<phi>. getFrN (map snd txs) (map fst txs) [\<phi>] (length txs)"
  hence vss: "\<And>\<phi>. vs \<phi> = getFrN (map snd txs) (map fst txs) [\<phi>] (length txs)" by auto
  {fix \<phi> assume "\<phi> \<in> F" hence "\<phi> \<in> fmla" using assms by auto
   hence "set (vs \<phi>)  \<subseteq> var \<and> 
    set (vs \<phi>) \<inter> Fvars \<phi> = {} \<and>   
    set (vs \<phi>) \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {} \<and> 
    set (vs \<phi>) \<inter> snd ` (set txs) = {} \<and> 
    length (vs \<phi>) = length txs \<and> 
    distinct (vs \<phi>)"   
   using assms unfolding vs      
   using getFrN_Fvars[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
         getFrN_FvarsT[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
         getFrN_var[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
         getFrN_length[of "map snd txs" "map fst txs" "[\<phi>]" "length txs"]  
   apply auto apply fastforce  
   by (smt IntI empty_iff image_iff snd_conv)
  } note vs_facts = this  
 
  let ?tus = "zip (map fst txs) us"
  let ?uxs = "zip (map Var us) (map snd txs)" 
  let ?tvs = "\<lambda> \<phi>. zip (map fst txs) (vs \<phi>)"
  let ?vxs = "\<lambda> \<phi>. zip (map Var (vs \<phi>)) (map snd txs)"

  let ?c = "rawpsubst (scnj F) ?uxs"
  have c: "prv (eqv ?c 
                   (scnj ((\<lambda>\<phi>. rawpsubst \<phi> ?uxs) ` F)))" 
    apply(rule prv_rawpsubst_scnj) using assms us_facts apply (auto intro!: rawpsubstT)
    apply(drule set_zip_rightD) apply simp apply blast  
    apply(drule set_zip_leftD) apply simp apply blast .
  hence "prv (eqv (rawpsubst ?c ?tus) 
                  (rawpsubst (scnj ((\<lambda>\<phi>. rawpsubst \<phi> ?uxs) ` F)) ?tus))" 
  apply(intro prv_eqv_rawpsubst) using assms us_facts by (auto intro!: rawpsubst dest!: set_zip_D)
  moreover 
  have "prv (eqv (rawpsubst (scnj ((\<lambda>\<phi>. rawpsubst \<phi> ?uxs) ` F)) ?tus)
                 (scnj ((\<lambda>\<phi>. rawpsubst \<phi> ?tus) ` ((\<lambda>\<phi>. rawpsubst \<phi> ?uxs) ` F))))"
  apply(rule prv_rawpsubst_scnj)  using assms us_facts by (auto intro!: rawpsubst dest!: set_zip_D) 
  ultimately 
  have 0: "prv (eqv (rawpsubst ?c ?tus) 
                    (scnj ((\<lambda>\<phi>. rawpsubst \<phi> ?tus) ` ((\<lambda>\<phi>. rawpsubst \<phi> ?uxs) ` F))))"  
  apply- apply(rule prv_eqv_trans) using assms us_facts by (auto intro!: rawpsubst dest!: set_zip_D)
  moreover 
  have "prv (eqv (scnj ((\<lambda>\<phi>. rawpsubst \<phi> ?tus) ` ((\<lambda>\<phi>. rawpsubst \<phi> ?uxs) ` F))) 
                 (scnj ((\<lambda>\<phi>. rawpsubst (rawpsubst \<phi> (?vxs \<phi>)) (?tvs \<phi>)) ` F)))"  
  apply(rule prv_eqvI) using assms us_facts  apply (auto intro!: rawpsubst dest!: set_zip_D)
  apply (meson contra_subsetD vs_facts)  apply (meson contra_subsetD vs_facts)
  subgoal  
    apply(rule prv_scnj_mono_imp) 
    apply (auto intro!: rawpsubst dest!: set_zip_D)
    apply (meson contra_subsetD vs_facts) apply (meson contra_subsetD vs_facts)
    subgoal for \<phi> apply(rule bexI[of _ \<phi>]) apply(rule prv_imp_refl2) 
    apply (auto intro!: rawpsubst dest!: set_zip_D)
    apply (meson contra_subsetD vs_facts) apply (meson contra_subsetD vs_facts)
    apply(rule rawpsubst_compose_freshVar2)
    apply (auto intro!: rawpsubst dest!: set_zip_D) 
    apply (meson contra_subsetD vs_facts) apply (meson contra_subsetD vs_facts) 
    using vs_facts apply fastforce 
    apply (smt IntI UN_I all_not_in_conv fst_conv image_iff vs_facts)
    by (metis (no_types, hide_lams) IntI empty_iff image_iff snd_conv vs_facts)+ . 
  subgoal  
    apply(rule prv_scnj_mono_imp) 
    apply (auto intro!: rawpsubst dest!: set_zip_D)
    apply (meson contra_subsetD vs_facts) apply (meson contra_subsetD vs_facts)
    subgoal for \<phi> apply(rule bexI[of _ \<phi>]) apply(rule prv_imp_refl2) 
    apply (auto intro!: rawpsubst dest!: set_zip_D)
    apply (meson contra_subsetD vs_facts) apply (meson contra_subsetD vs_facts)
    apply(rule rawpsubst_compose_freshVar2)
    apply (auto intro!: rawpsubst dest!: set_zip_D) 
    apply (meson contra_subsetD vs_facts) apply (meson contra_subsetD vs_facts) 
    using vs_facts apply fastforce 
    apply (smt IntI UN_I all_not_in_conv fst_conv image_iff vs_facts)
    by (metis (no_types, hide_lams) IntI empty_iff image_iff snd_conv vs_facts)+ . .
  ultimately 
  have "prv (eqv (rawpsubst (rawpsubst (scnj F) ?uxs) ?tus)
           (scnj ((\<lambda>\<phi>. rawpsubst (rawpsubst \<phi> (?vxs \<phi>)) (?tvs \<phi>)) ` F)))"
  apply- apply(rule prv_eqv_trans) using assms us_facts apply (auto intro!: rawpsubst dest!: set_zip_D)
  by (meson subsetCE vs_facts)+ 
  thus ?thesis unfolding psubst_def apply (simp add: Let_def us[symmetric])
  unfolding vss[symmetric] .
qed

lemma prv_imp_psubst_scnj: 
assumes "F \<subseteq> fmla" "finite F" "snd ` set txs \<subseteq> var" "fst ` set txs \<subseteq> trm"
and "distinct (map snd txs)"
shows "prv (imp (psubst (scnj F) txs) (scnj ((\<lambda>\<phi>. psubst \<phi> txs) ` F)))"
using prv_psubst_scnj[OF assms] assms apply(intro prv_imp_eqvEL) by auto

lemma prv_psubst_scnj_imp: 
assumes "F \<subseteq> fmla" "finite F" "snd ` set txs \<subseteq> var" "fst ` set txs \<subseteq> trm"
and "distinct (map snd txs)"
shows "prv (imp (scnj ((\<lambda>\<phi>. psubst \<phi> txs) ` F)) (psubst (scnj F) txs))"
using prv_psubst_scnj[OF assms] assms apply(intro prv_imp_eqvER) by auto

   
(***************)
(* Consistency, i.e., the notion of not proving false *)
definition consistent :: bool where 
"consistent \<equiv> \<not> prv fls"

lemma consistent_def2: "consistent \<longleftrightarrow> (\<exists>\<phi> \<in> fmla. \<not> prv \<phi>)"
  unfolding consistent_def using prv_expl by blast

lemma consistent_def3: "consistent \<longleftrightarrow> (\<forall>\<phi> \<in> fmla. \<not> (prv \<phi> \<and> prv (neg \<phi>)))"
  unfolding consistent_def using prv_neg_fls neg_def by auto


(* Omega-consistency: *)
definition \<omega>consistent :: bool where 
"\<omega>consistent \<equiv> 
 \<forall> \<phi> \<in> fmla. \<forall> x \<in> var. Fvars \<phi> = {x} \<longrightarrow> 
   (\<forall> n \<in> num. prv (neg (subst \<phi> n x))) 
   \<longrightarrow> 
   \<not> prv (neg (neg (exi x \<phi>)))"

(* The above particularly strong version of \<omega>consistent is used for the sake of working without 
assuming classical logic. It of course implies some more standard formulations for classical logic: *)

definition \<omega>consistentStd1 :: bool where 
"\<omega>consistentStd1 \<equiv> 
 \<forall> \<phi> \<in> fmla. \<forall> x \<in> var. Fvars \<phi> = {x} \<longrightarrow> 
    (\<forall> n \<in> num. prv (neg (subst \<phi> n x))) \<longrightarrow> \<not> prv (exi x \<phi>)"

definition \<omega>consistentStd2 :: bool where 
"\<omega>consistentStd2 \<equiv> 
 \<forall> \<phi> \<in> fmla. \<forall> x \<in> var. Fvars \<phi> = {x} \<longrightarrow> 
   (\<forall> n \<in> num. prv (subst \<phi> n x)) \<longrightarrow> \<not> prv (exi x (neg \<phi>))"
  
lemma \<omega>consistent_impliesStd1: 
"\<omega>consistent \<Longrightarrow> 
 \<omega>consistentStd1"
  unfolding \<omega>consistent_def \<omega>consistentStd1_def using prv_neg_neg by blast

lemma \<omega>consistent_impliesStd2: 
"\<omega>consistent \<Longrightarrow> 
 \<omega>consistentStd2"
  apply(drule \<omega>consistent_impliesStd1)
  unfolding  \<omega>consistentStd1_def \<omega>consistentStd2_def apply safe 
  subgoal for \<phi> x
  apply(drule bspec[of _ _ "neg \<phi>"]) apply auto
  using subst prv_neg_neg by auto .

(* Side note: in the presence of classical logic deduction, our condition is 
equivalent to the standard ones: *)
lemma \<omega>consistent_iffStd1: 
  assumes "\<And> \<phi>. \<phi> \<in> fmla \<Longrightarrow> prv (imp (neg (neg \<phi>)) \<phi>)"
  shows "\<omega>consistent \<longleftrightarrow> \<omega>consistentStd1"
  using \<omega>consistent_impliesStd1 apply auto[] 
  unfolding \<omega>consistentStd1_def \<omega>consistent_def by (meson assms exi neg prv_imp_mp)

lemma \<omega>consistent_iffStd2: 
  assumes "\<And> \<phi>. \<phi> \<in> fmla \<Longrightarrow> prv (imp (neg (neg \<phi>)) \<phi>)"
  shows "\<omega>consistent \<longleftrightarrow> \<omega>consistentStd2"
  unfolding \<omega>consistent_iffStd1[OF assms, simplified] 
    \<omega>consistentStd1_def \<omega>consistentStd2_def apply auto
  subgoal for \<phi> x
  apply(drule bspec[of _ _ "neg \<phi>"]) apply auto
    by (auto simp add: prv_neg_neg) 
  subgoal for \<phi> x
  apply(drule bspec[of _ _ "neg \<phi>"]) apply auto
    by (metis exi fls imp neg_def prv_exi_cong prv_imp_mp prv_imp_neg_fls) . 

(* All our three notions of \<omega>consistency (which are equivalent under classical logic)
imply consistency (within our intuitionsitic logic):
*)
lemma \<omega>consistentStd1_implies_consistent: 
assumes "\<omega>consistentStd1"
shows "consistent"
unfolding consistent_def
proof safe
  assume pf: "prv fls" 
  then obtain x where x: "x \<in> var" "x \<notin> Fvars fls" 
    using finite_Fvars getFresh by auto
  let ?fls = "cnj (fls) (eql (Var x) (Var x))"
  have 0: "\<forall> n \<in> num. prv (neg (subst ?fls n x))" and 1: "prv (exi x fls)"
  using x fls  by (auto simp: pf prv_expl)
  have 2: "\<not> prv (exi x ?fls)" using 0 fls x assms 
    unfolding \<omega>consistentStd1_def by simp
  show False using 1 2 consistent_def consistent_def2 pf x(1) by blast
qed

lemma \<omega>consistentStd2_implies_consistent: 
assumes "\<omega>consistentStd2"
shows "consistent"
unfolding consistent_def
proof safe
  assume pf: "prv fls" 
  then obtain x where x: "x \<in> var" "x \<notin> Fvars fls" 
    using finite_Fvars getFresh by auto
  let ?fls = "cnj (fls) (eql (Var x) (Var x))"
  have 0: "\<forall> n \<in> num. prv (subst ?fls n x)" and 1: "prv (exi x (neg ?fls))"
  using x fls  by (auto simp: pf prv_expl)
  have 2: "\<not> prv (exi x (neg ?fls))" using 0 fls x assms 
    unfolding \<omega>consistentStd2_def by auto  
  show False using 1 2 by simp
qed

corollary \<omega>consistent_implies_consistent: 
assumes "\<omega>consistent"
shows "consistent"
by (simp add: \<omega>consistentStd2_implies_consistent \<omega>consistent_impliesStd2 assms)



end \<comment> \<open>context Deduct_with_False\<close>



(* Further incorporate disjunction: *)
locale Deduct_with_False_Disj = 
Syntax_with_Connectives_False_Disj
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls 
  dsj
+   
Deduct_with_False  
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  num
  prv
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and eql cnj imp all exi 
and fls
and dsj
and num
and prv
+
assumes 
prv_dsj_impL: 
"\<And> \<phi> \<chi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> 
  prv (imp \<phi> (dsj \<phi> \<chi>))"
and 
prv_dsj_impR: 
"\<And> \<phi> \<chi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> 
  prv (imp \<chi> (dsj \<phi> \<chi>))"
and 
prv_imp_dsjE: 
"\<And> \<phi> \<chi> \<psi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> 
  prv (imp (imp \<phi> \<psi>) (imp (imp \<chi> \<psi>) (imp (dsj \<phi> \<chi>) \<psi>)))"
begin

lemma prv_imp_dsjEE:
assumes \<phi>[simp]: "\<phi> \<in> fmla" and \<chi>[simp]: "\<chi> \<in> fmla" and \<psi>[simp]: "\<psi> \<in> fmla"
assumes " prv (imp \<phi> \<psi>)" and "prv (imp \<chi> \<psi>)"
shows "prv (imp (dsj \<phi> \<chi>) \<psi>)"  
  by (metis assms dsj imp prv_imp_dsjE prv_imp_mp) 

lemma prv_dsj_cases: 
assumes "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla" "\<chi> \<in> fmla" 
and "prv (dsj \<phi>1 \<phi>2)" and "prv (imp \<phi>1 \<chi>)" and "prv (imp \<phi>2 \<chi>)"
shows "prv \<chi>" 
  by (meson assms  dsj prv_imp_dsjEE prv_imp_mp)

(* Disjunction vs disjunction   *)
  
lemma prv_dsj_com_imp:
 assumes \<phi>[simp]: "\<phi> \<in> fmla" and \<chi>[simp]: "\<chi> \<in> fmla"
 shows "prv (imp (dsj \<phi> \<chi>) (dsj \<chi> \<phi>))" 
  by (metis \<chi> \<phi> dsj imp prv_dsj_impL prv_dsj_impR prv_imp_dsjE prv_imp_mp)

lemma prv_dsj_com:
 assumes \<phi>[simp]: "\<phi> \<in> fmla" and \<chi>[simp]: "\<chi> \<in> fmla"
 shows "prv (eqv (dsj \<phi> \<chi>) (dsj \<chi> \<phi>))"
  by (simp add: prv_dsj_com_imp prv_eqvI)

lemma prv_dsj_assoc_imp1:
 assumes \<phi>[simp]: "\<phi> \<in> fmla" and \<chi>[simp]: "\<chi> \<in> fmla" and \<psi>[simp]: "\<psi> \<in> fmla"
 shows "prv (imp (dsj \<phi> (dsj \<chi> \<psi>)) (dsj (dsj \<phi> \<chi>) \<psi>))" 
  using prv_imp_mp prv_prv_imp_trans 
           \<chi> \<phi> \<psi> dsj imp prv_dsj_impL prv_dsj_impR prv_imp_dsjE 
  by (smt Deduct_axioms)

lemma prv_dsj_assoc_imp2:
 assumes \<phi>[simp]: "\<phi> \<in> fmla" and \<chi>[simp]: "\<chi> \<in> fmla" and \<psi>[simp]: "\<psi> \<in> fmla"
 shows "prv (imp (dsj (dsj \<phi> \<chi>) \<psi>) (dsj \<phi> (dsj \<chi> \<psi>)))" 
  by (smt prv_imp_mp Deduct.prv_prv_imp_trans Deduct_axioms 
    \<chi> \<phi> \<psi> dsj imp prv_dsj_impL prv_dsj_impR prv_imp_dsjE)

lemma prv_dsj_assoc:
 assumes \<phi>[simp]: "\<phi> \<in> fmla" and \<chi>[simp]: "\<chi> \<in> fmla" and \<psi>[simp]: "\<psi> \<in> fmla"
 shows "prv (eqv (dsj \<phi> (dsj \<chi> \<psi>)) (dsj (dsj \<phi> \<chi>) \<psi>))"
  by (simp add: prv_dsj_assoc_imp1 prv_dsj_assoc_imp2 prv_eqvI)

lemma prv_dsj_com_imp3: 
assumes "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla" "\<phi>3 \<in> fmla"
shows "prv (imp (dsj \<phi>1 (dsj \<phi>2 \<phi>3))
                (dsj \<phi>2 (dsj \<phi>1 \<phi>3)))"
  by (smt assms  dsj prv_dsj_impL prv_dsj_impR prv_imp_dsjEE prv_prv_imp_trans) 

lemma prv_dsj_mono: 
"\<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<chi>1 \<in> fmla \<Longrightarrow> \<chi>2 \<in> fmla \<Longrightarrow> 
prv (imp \<phi>1 \<chi>1) \<Longrightarrow> prv (imp \<phi>2 \<chi>2) \<Longrightarrow> prv (imp (dsj \<phi>1 \<phi>2) (dsj \<chi>1 \<chi>2))"
  by (meson dsj prv_dsj_impL prv_dsj_impR prv_imp_dsjEE prv_prv_imp_trans)

(* Disjunction vs conjunction   *) 

lemma prv_cnj_dsj_distrib1:
 assumes \<phi>[simp]: "\<phi> \<in> fmla" and \<chi>1[simp]: "\<chi>1 \<in> fmla" and \<chi>2[simp]: "\<chi>2 \<in> fmla"
 shows "prv (imp (cnj \<phi> (dsj \<chi>1 \<chi>2)) (dsj (cnj \<phi> \<chi>1) (cnj \<phi> \<chi>2)))"
  by (simp add: prv_cnj_imp prv_cnj_imp_monoR2 prv_dsj_impL prv_dsj_impR prv_imp_com prv_imp_dsjEE)

lemma prv_cnj_dsj_distrib2:
 assumes \<phi>[simp]: "\<phi> \<in> fmla" and \<chi>1[simp]: "\<chi>1 \<in> fmla" and \<chi>2[simp]: "\<chi>2 \<in> fmla"
 shows "prv (imp (dsj (cnj \<phi> \<chi>1) (cnj \<phi> \<chi>2)) (cnj \<phi> (dsj \<chi>1 \<chi>2)))"  
  by (simp add: prv_cnj_mono prv_dsj_impL prv_dsj_impR prv_imp_dsjEE prv_imp_refl)

lemma prv_cnj_dsj_distrib:
 assumes \<phi>[simp]: "\<phi> \<in> fmla" and \<chi>1[simp]: "\<chi>1 \<in> fmla" and \<chi>2[simp]: "\<chi>2 \<in> fmla"
 shows "prv (eqv (cnj \<phi> (dsj \<chi>1 \<chi>2)) (dsj (cnj \<phi> \<chi>1) (cnj \<phi> \<chi>2)))"
  by (simp add: prv_cnj_dsj_distrib1 prv_cnj_dsj_distrib2 prv_eqvI)

(**)

lemma prv_dsj_cnj_distrib1:
 assumes \<phi>[simp]: "\<phi> \<in> fmla" and \<chi>1[simp]: "\<chi>1 \<in> fmla" and \<chi>2[simp]: "\<chi>2 \<in> fmla"
 shows "prv (imp (dsj \<phi> (cnj \<chi>1 \<chi>2)) (cnj (dsj \<phi> \<chi>1) (dsj \<phi> \<chi>2)))"
  by (simp add: prv_cnj_mono prv_dsj_impL prv_dsj_impR prv_imp_cnj prv_imp_dsjEE)

lemma prv_dsj_cnj_distrib2:
 assumes \<phi>[simp]: "\<phi> \<in> fmla" and \<chi>1[simp]: "\<chi>1 \<in> fmla" and \<chi>2[simp]: "\<chi>2 \<in> fmla"
 shows "prv (imp (cnj (dsj \<phi> \<chi>1) (dsj \<phi> \<chi>2)) (dsj \<phi> (cnj \<chi>1 \<chi>2)))"
proof -
  have "\<forall>f fa fb. (((prv (imp f (imp fb fa)) \<or> \<not> prv (imp f fa)) \<or> fa \<notin> fmla) \<or> f \<notin> fmla) \<or> fb \<notin> fmla"
    by (meson imp prv_imp_imp_triv prv_prv_imp_trans)
  then show ?thesis
    by (metis \<chi>1 \<chi>2 \<phi> cnj dsj imp prv_cnj_imp prv_cnj_imp_monoR2 prv_dsj_impL prv_dsj_impR 
        prv_imp_com prv_imp_dsjEE)
qed 

lemma prv_dsj_cnj_distrib:
 assumes \<phi>[simp]: "\<phi> \<in> fmla" and \<chi>1[simp]: "\<chi>1 \<in> fmla" and \<chi>2[simp]: "\<chi>2 \<in> fmla"
 shows "prv (eqv (dsj \<phi> (cnj \<chi>1 \<chi>2)) (cnj (dsj \<phi> \<chi>1) (dsj \<phi> \<chi>2)))"
  by (simp add: prv_dsj_cnj_distrib1 prv_dsj_cnj_distrib2 prv_eqvI)


(* Disjunction vs. True and False: *)
lemma prv_dsjR_fls: "\<phi> \<in> fmla \<Longrightarrow> prv (eqv (dsj fls \<phi>) \<phi>)" 
  by (simp add: prv_dsj_impR prv_eqvI prv_imp_dsjEE prv_imp_refl)

lemma prv_dsjL_fls: "\<phi> \<in> fmla \<Longrightarrow> prv (eqv (dsj \<phi> fls) \<phi>)" 
  by (simp add: prv_dsj_impL prv_eqvI prv_imp_dsjEE prv_imp_refl)

lemma prv_dsjR_tru: "\<phi> \<in> fmla \<Longrightarrow> prv (eqv (dsj tru \<phi>) tru)" 
  by (simp add: prv_dsj_impL prv_eqvI prv_imp_tru)

lemma prv_dsjL_tru: "\<phi> \<in> fmla \<Longrightarrow> prv (eqv (dsj \<phi> tru) tru)" 
  by (simp add: prv_dsj_impR prv_eqvI prv_imp_tru)


(**)
(* Properties of set disjunctions. 
These are based on properties of then auxiliary list disunctions. *)


lemma prv_imp_ldsj_in: 
  assumes "set \<phi>s \<subseteq> fmla"
  and "\<phi> \<in> set \<phi>s"
  shows "prv (imp \<phi> (ldsj \<phi>s))"
proof-
  have "\<phi> \<in> fmla" using assms by auto
  thus ?thesis 
  using assms apply(induct \<phi>s arbitrary: \<phi>)   
  apply (auto simp add: prv_dsj_impL) 
  by (meson dsj ldsj prv_dsj_impR prv_prv_imp_trans) 
qed

lemma prv_imp_ldsj: 
assumes "\<chi> \<in> fmla" and "set \<phi>s \<subseteq> fmla"
and "\<phi> \<in> set \<phi>s" and "prv (imp \<chi> \<phi>)"  
shows "prv (imp \<chi> (ldsj \<phi>s))" 
  using assms ldsj prv_imp_ldsj_in prv_prv_imp_trans by blast

lemma prv_ldsj_imp: 
  assumes "\<chi> \<in> fmla" and "set \<phi>s \<subseteq> fmla"
  and "\<And>\<phi>. \<phi> \<in> set \<phi>s \<Longrightarrow> prv (imp \<phi> \<chi>)"
  shows "prv (imp (ldsj \<phi>s) \<chi>)"
  using assms apply(induct \<phi>s arbitrary: \<chi>)    
  by (auto simp add: prv_imp_tru prv_imp_com prv_imp_dsjEE) 

lemma prv_ldsj_imp_inner:
assumes "\<phi> \<in> fmla" "set \<phi>1s \<subseteq> fmla" "set \<phi>2s \<subseteq> fmla" 
shows "prv (imp (ldsj (\<phi>1s @ \<phi> # \<phi>2s)) (dsj \<phi> (ldsj (\<phi>1s @ \<phi>2s))))"
using assms proof(induction \<phi>1s)
  case (Cons \<phi>1 \<phi>1s)
  have [intro!]: "set (\<phi>1s @ \<phi>2s) \<subseteq> fmla" "set (\<phi>1s @ \<phi> # \<phi>2s) \<subseteq> fmla"  using Cons by auto
  have 0: "prv (imp (dsj \<phi>1 (dsj \<phi> (ldsj (\<phi>1s @ \<phi>2s)))) 
                 (dsj \<phi> (dsj \<phi>1 (ldsj (\<phi>1s @ \<phi>2s)))))" 
    apply(rule prv_dsj_com_imp3) using Cons by fastforce+
  have 1: "prv (imp (dsj \<phi>1 (ldsj (\<phi>1s @ \<phi> # \<phi>2s))) 
                (dsj \<phi>1 (dsj \<phi> (ldsj (\<phi>1s @ \<phi>2s)))))"
  using Cons by (intro prv_dsj_mono) (auto simp add: prv_imp_refl)   
  show ?case apply simp using prv_prv_imp_trans[OF _ _ _ 1 0] Cons by auto
qed(simp add: prv_imp_refl)

lemma prv_ldsj_imp_remdups:
assumes "set \<phi>s \<subseteq> fmla"  
shows "prv (imp  (ldsj \<phi>s) (ldsj (remdups \<phi>s)))" 
  using assms apply(induct \<phi>s) apply auto 
  apply (simp add: prv_imp_dsjEE prv_imp_ldsj_in)    
  by (smt dsj ldsj prv_dsj_impL prv_dsj_impR prv_imp_dsjEE prv_prv_imp_trans set_remdups)
    
lemma prv_ldsj_mono:
assumes \<phi>2s: "set \<phi>2s \<subseteq> fmla" and "set \<phi>1s \<subseteq> set \<phi>2s"  
shows "prv (imp (ldsj \<phi>1s) (ldsj \<phi>2s))"
proof-
  define \<phi>1s' where \<phi>1s': "\<phi>1s' = remdups \<phi>1s"
  have A: "set \<phi>1s' \<subseteq> set \<phi>2s" "distinct \<phi>1s'" unfolding \<phi>1s' using assms by auto
  have B: "prv (imp (ldsj \<phi>1s') (ldsj \<phi>2s))"
  using \<phi>2s A proof(induction \<phi>2s arbitrary: \<phi>1s')
    case (Cons \<phi>2 \<phi>2s \<phi>1ss)  
    show ?case proof(cases "\<phi>2 \<in> set \<phi>1ss")
      case True
      then obtain \<phi>1ss1 \<phi>1ss2 where \<phi>1ss: "\<phi>1ss = \<phi>1ss1 @ \<phi>2 # \<phi>1ss2"       
      by (meson split_list)
      define \<phi>1s where \<phi>1s: "\<phi>1s \<equiv> \<phi>1ss1 @ \<phi>1ss2" 
      have nin: "\<phi>2 \<notin> set \<phi>1s" using \<phi>1ss `distinct \<phi>1ss` unfolding \<phi>1s by auto
      have [intro!,simp]: "set \<phi>1s \<subseteq> fmla" unfolding \<phi>1s using \<phi>1ss Cons by auto
      have 0: "prv (imp (ldsj \<phi>1ss) (dsj \<phi>2 (ldsj \<phi>1s)))"
        unfolding \<phi>1s \<phi>1ss
        apply(rule prv_ldsj_imp_inner) using Cons \<phi>1ss by auto
      have 1: "prv (imp (ldsj \<phi>1s) (ldsj \<phi>2s))" apply(rule Cons.IH) using nin Cons.prems True  
      using \<phi>1s \<phi>1ss by  auto
      have 2: "prv (imp (dsj \<phi>2 (ldsj \<phi>1s)) (dsj \<phi>2 (ldsj \<phi>2s)))" find_theorems imp cnj name: mono
      using Cons \<phi>1ss \<phi>1s 1  apply(intro prv_dsj_mono) 
      using prv_imp_refl by auto blast+  
      show ?thesis apply simp apply(rule prv_prv_imp_trans[OF _ _ _ 0 2]) using Cons by auto
    next
      case False
      then show ?thesis   using Cons  
        by auto (smt dsj ldsj prv_dsj_impR prv_prv_imp_trans subset_insert subset_trans)  
    qed  
  qed(simp add: prv_imp_refl)
  have C: "prv (imp (ldsj \<phi>1s) (ldsj \<phi>1s'))"
    unfolding \<phi>1s' apply(rule prv_ldsj_imp_remdups) using assms by auto
  show ?thesis apply(rule prv_prv_imp_trans[OF _ _ _ C B]) using A assms by auto
qed

lemma prv_ldsj_eqv:
assumes "set \<phi>1s \<subseteq> fmla" and "set \<phi>2s = set \<phi>1s"
shows "prv (eqv (ldsj \<phi>1s) (ldsj \<phi>2s))"
  apply(rule prv_eqvI) using assms prv_ldsj_mono by auto

lemma prv_ldsj_mono_imp:
  assumes "set \<phi>1s \<subseteq> fmla" "set \<phi>2s \<subseteq> fmla" and "\<forall> \<phi>1 \<in> set \<phi>1s. \<exists> \<phi>2 \<in> set \<phi>2s. prv (imp \<phi>1 \<phi>2)"  
  shows "prv (imp (ldsj \<phi>1s) (ldsj \<phi>2s))"
  apply(rule prv_ldsj_imp) using assms apply auto 
  using prv_imp_ldsj by blast

(* *)
lemma prv_subst_sdsj:
"F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow> 
 prv (eqv (subst (sdsj F) t x) (sdsj ((\<lambda>\<phi>. subst \<phi> t x) ` F)))"
unfolding sdsj_def by (fastforce intro!: prv_ldsj_eqv)

lemma prv_imp_sdsj_in: 
  assumes "\<phi> \<in> fmla" and "F \<subseteq> fmla" "finite F"
  and "\<phi> \<in> F"
  shows "prv (imp \<phi> (sdsj F))"
  unfolding sdsj_def apply(rule prv_imp_ldsj_in) using assms by auto

lemma prv_imp_sdsj: 
assumes "\<chi> \<in> fmla" and "F \<subseteq> fmla" "finite F"
and "\<phi> \<in> F" and "prv (imp \<chi> \<phi>)"  
shows "prv (imp \<chi> (sdsj F))"
  unfolding sdsj_def apply(rule prv_imp_ldsj) using assms by auto

lemma prv_sdsj_imp: 
  assumes "\<chi> \<in> fmla" and "F \<subseteq> fmla" "finite F"
  and "\<And>\<phi>. \<phi> \<in> F \<Longrightarrow> prv (imp \<phi> \<chi>)"  
  shows "prv (imp (sdsj F) \<chi>)"
  unfolding sdsj_def apply(rule prv_ldsj_imp) using assms by auto  
 
lemma prv_sdsj_mono:
assumes "F2 \<subseteq> fmla" and "F1 \<subseteq> F2" and "finite F2"  
shows "prv (imp (sdsj F1) (sdsj F2))"
  unfolding sdsj_def apply(rule prv_ldsj_mono) using assms 
  by auto (metis asList contra_subsetD infinite_super) 

lemma prv_sdsj_mono_imp:
  assumes "F1 \<subseteq> fmla" "F2 \<subseteq> fmla" "finite F1" "finite F2"  
  and "\<forall> \<phi>1 \<in> F1. \<exists> \<phi>2 \<in> F2. prv (imp \<phi>1 \<phi>2)"  
  shows "prv (imp (sdsj F1) (sdsj F2))"
  unfolding sdsj_def apply(rule prv_ldsj_mono_imp) using assms by auto 

lemma prv_sdsj_cases:  
assumes "F \<subseteq> fmla" "finite F" "\<psi> \<in> fmla" 
and "prv (sdsj F)" and "\<And> \<phi>. \<phi> \<in> F \<Longrightarrow> prv (imp \<phi> \<psi>)" 
shows "prv \<psi>" 
  by (meson assms prv_imp_mp prv_sdsj_imp sdsj)

lemma prv_sdsj1_imp: 
"\<phi> \<in> fmla \<Longrightarrow> prv (imp (sdsj {\<phi>}) \<phi>)" 
  using prv_imp_refl prv_sdsj_imp by fastforce

lemma prv_imp_sdsj1: 
"\<phi> \<in> fmla \<Longrightarrow> prv (imp \<phi> (sdsj {\<phi>}))"  
using prv_imp_refl prv_imp_sdsj by fastforce 

lemma prv_sdsj2_imp_dsj: 
"\<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> prv (imp (sdsj {\<phi>,\<psi>}) (dsj \<phi> \<psi>))"
  using prv_dsj_impL prv_dsj_impR prv_sdsj_imp by fastforce

lemma prv_dsj_imp_sdsj2: 
"\<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> prv (imp (dsj \<phi> \<psi>) (sdsj {\<phi>,\<psi>}))"
  by (simp add: prv_imp_dsjEE prv_imp_sdsj_in) 


(**)
lemma prv_rawpsubst_sdsj: 
assumes "F \<subseteq> fmla" "finite F"
and "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
shows "prv (eqv (rawpsubst (sdsj F) txs) (sdsj ((\<lambda>\<phi>. rawpsubst \<phi> txs) ` F)))"
using assms proof(induction txs arbitrary: F)
  case (Cons tx txs)
  then obtain t x where tx[simp]: "tx = (t,x)" by (cases tx) auto
  hence [simp]: "t \<in> trm" "x \<in> var" using Cons.prems by auto
  have 0: "(\<lambda>\<phi>. rawpsubst (subst \<phi> t x) txs) ` F = 
           (\<lambda>\<phi>. rawpsubst \<phi> txs) ` ((\<lambda>\<phi>. subst \<phi> t x) ` F)"
  using Cons.prems by auto
  have "prv (eqv (subst (sdsj F) t x) 
                 (sdsj ((\<lambda>\<phi>. subst \<phi> t x) ` F)))" 
  apply(rule prv_subst_sdsj) using Cons.prems by auto
  hence "prv (eqv (rawpsubst (subst (sdsj F) t x) txs) 
                  (rawpsubst (sdsj ((\<lambda>\<phi>. subst \<phi> t x) ` F)) txs))"
  apply(intro prv_eqv_rawpsubst) using Cons.prems by auto
  moreover 
  have "prv (eqv (rawpsubst (sdsj ((\<lambda>\<phi>. subst \<phi> t x) ` F)) txs) 
                 (sdsj ((\<lambda>\<phi>. rawpsubst (subst \<phi> t x) txs) ` F)))"
  unfolding 0  apply(rule Cons.IH) using Cons.prems by auto
  ultimately show ?case apply- apply(rule prv_eqv_trans) using Cons.prems by (auto intro!: rawpsubst)
qed(auto simp: image_def prv_eqv_refl)[] 


lemma prv_psubst_sdsj:  
assumes "F \<subseteq> fmla" "finite F"
and "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
and "distinct (map snd txs)" 
shows "prv (eqv (psubst (sdsj F) txs) (sdsj ((\<lambda>\<phi>. psubst \<phi> txs) ` F)))" 
proof-  
  define us where us: "us \<equiv> getFrN (map snd txs) (map fst txs) [sdsj F] (length txs)"
  have us_facts: "set us \<subseteq> var" 
  "set us \<inter> \<Union> (Fvars ` F) = {}" 
  "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}" 
  "set us \<inter> snd ` (set txs) = {}"
  "length us = length txs"
  "distinct us" 
  using assms unfolding us      
  using getFrN_Fvars[of "map snd txs" "map fst txs" "[sdsj F]" _ "length txs"]
        getFrN_FvarsT[of "map snd txs" "map fst txs" "[sdsj F]" _ "length txs"]
        getFrN_var[of "map snd txs" "map fst txs" "[sdsj F]" _ "length txs"]
        getFrN_length[of "map snd txs" "map fst txs" "[sdsj F]" "length txs"]  
  apply auto apply fastforce  
  by (smt IntI empty_iff image_iff snd_conv)
  
  define vs where vs: "vs \<equiv> \<lambda> \<phi>. getFrN (map snd txs) (map fst txs) [\<phi>] (length txs)"
  hence vss: "\<And>\<phi>. vs \<phi> = getFrN (map snd txs) (map fst txs) [\<phi>] (length txs)" by auto
  {fix \<phi> assume "\<phi> \<in> F" hence "\<phi> \<in> fmla" using assms by auto
   hence "set (vs \<phi>)  \<subseteq> var \<and> 
    set (vs \<phi>) \<inter> Fvars \<phi> = {} \<and>   
    set (vs \<phi>) \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {} \<and> 
    set (vs \<phi>) \<inter> snd ` (set txs) = {} \<and> 
    length (vs \<phi>) = length txs \<and> 
    distinct (vs \<phi>)"   
   using assms unfolding vs      
   using getFrN_Fvars[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
         getFrN_FvarsT[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
         getFrN_var[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
         getFrN_length[of "map snd txs" "map fst txs" "[\<phi>]" "length txs"]  
   apply auto apply fastforce  
   by (smt IntI empty_iff image_iff snd_conv)
  } note vs_facts = this  
 
  let ?tus = "zip (map fst txs) us"
  let ?uxs = "zip (map Var us) (map snd txs)" 
  let ?tvs = "\<lambda> \<phi>. zip (map fst txs) (vs \<phi>)"
  let ?vxs = "\<lambda> \<phi>. zip (map Var (vs \<phi>)) (map snd txs)"

  let ?c = "rawpsubst (sdsj F) ?uxs"
  have c: "prv (eqv ?c 
                   (sdsj ((\<lambda>\<phi>. rawpsubst \<phi> ?uxs) ` F)))" 
    apply(rule prv_rawpsubst_sdsj) using assms us_facts apply (auto intro!: rawpsubstT)
    apply(drule set_zip_rightD) apply simp apply blast  
    apply(drule set_zip_leftD) apply simp apply blast .
  hence "prv (eqv (rawpsubst ?c ?tus) 
                  (rawpsubst (sdsj ((\<lambda>\<phi>. rawpsubst \<phi> ?uxs) ` F)) ?tus))" 
  apply(intro prv_eqv_rawpsubst) using assms us_facts by (auto intro!: rawpsubst dest!: set_zip_D)
  moreover 
  have "prv (eqv (rawpsubst (sdsj ((\<lambda>\<phi>. rawpsubst \<phi> ?uxs) ` F)) ?tus)
                 (sdsj ((\<lambda>\<phi>. rawpsubst \<phi> ?tus) ` ((\<lambda>\<phi>. rawpsubst \<phi> ?uxs) ` F))))"
  apply(rule prv_rawpsubst_sdsj)  using assms us_facts by (auto intro!: rawpsubst dest!: set_zip_D) 
  ultimately 
  have 0: "prv (eqv (rawpsubst ?c ?tus) 
                    (sdsj ((\<lambda>\<phi>. rawpsubst \<phi> ?tus) ` ((\<lambda>\<phi>. rawpsubst \<phi> ?uxs) ` F))))"  
  apply- apply(rule prv_eqv_trans) using assms us_facts by (auto intro!: rawpsubst dest!: set_zip_D)
  moreover 
  have "prv (eqv (sdsj ((\<lambda>\<phi>. rawpsubst \<phi> ?tus) ` ((\<lambda>\<phi>. rawpsubst \<phi> ?uxs) ` F))) 
                 (sdsj ((\<lambda>\<phi>. rawpsubst (rawpsubst \<phi> (?vxs \<phi>)) (?tvs \<phi>)) ` F)))"  
  apply(rule prv_eqvI) using assms us_facts  apply (auto intro!: rawpsubst dest!: set_zip_D)
  apply (meson contra_subsetD vs_facts)  apply (meson contra_subsetD vs_facts)
  subgoal  
    apply(rule prv_sdsj_mono_imp) 
    apply (auto intro!: rawpsubst dest!: set_zip_D)
    apply (meson contra_subsetD vs_facts) apply (meson contra_subsetD vs_facts)
    subgoal for \<phi> apply(rule bexI[of _ \<phi>]) apply(rule prv_imp_refl2) 
    apply (auto intro!: rawpsubst dest!: set_zip_D)
    apply (meson contra_subsetD vs_facts) apply (meson contra_subsetD vs_facts)
    apply(rule rawpsubst_compose_freshVar2)
    apply (auto intro!: rawpsubst dest!: set_zip_D) 
    apply (meson contra_subsetD vs_facts) apply (meson contra_subsetD vs_facts) 
    using vs_facts apply fastforce 
    apply (smt IntI UN_I all_not_in_conv fst_conv image_iff vs_facts)
    by (metis (no_types, hide_lams) IntI empty_iff image_iff snd_conv vs_facts)+ . 
  subgoal  
    apply(rule prv_sdsj_mono_imp) 
    apply (auto intro!: rawpsubst dest!: set_zip_D)
    apply (meson contra_subsetD vs_facts) apply (meson contra_subsetD vs_facts)
    subgoal for \<phi> apply(rule bexI[of _ \<phi>]) apply(rule prv_imp_refl2) 
    apply (auto intro!: rawpsubst dest!: set_zip_D)
    apply (meson contra_subsetD vs_facts) apply (meson contra_subsetD vs_facts)
    apply(rule rawpsubst_compose_freshVar2)
    apply (auto intro!: rawpsubst dest!: set_zip_D) 
    apply (meson contra_subsetD vs_facts) apply (meson contra_subsetD vs_facts) 
    using vs_facts apply fastforce 
    apply (smt IntI UN_I all_not_in_conv fst_conv image_iff vs_facts)
    by (metis (no_types, hide_lams) IntI empty_iff image_iff snd_conv vs_facts)+ . .
  ultimately 
  have "prv (eqv (rawpsubst (rawpsubst (sdsj F) ?uxs) ?tus)
           (sdsj ((\<lambda>\<phi>. rawpsubst (rawpsubst \<phi> (?vxs \<phi>)) (?tvs \<phi>)) ` F)))"
  apply- apply(rule prv_eqv_trans) using assms us_facts apply (auto intro!: rawpsubst dest!: set_zip_D)
  by (meson subsetCE vs_facts)+ 
  thus ?thesis unfolding psubst_def apply (simp add: Let_def us[symmetric])
  unfolding vss[symmetric] .
qed

end \<comment> \<open>context Deduction_with_False_Disj\<close>


(* Factoring in explicit proofs: *)
locale Deduct_with_Proofs = 
Deduct_with_False_Disj  
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  prv
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and eql cnj imp all exi 
and fls
and dsj
and num
and prv
+
fixes  
"proof" :: "'proof set"
and
prfOf :: "'proof \<Rightarrow> 'fmla \<Rightarrow> bool"
assumes 
(* Provability means there exists a proof (only needed for sentences) *)
prv_prfOf: "\<And> \<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv \<phi> \<longleftrightarrow> (\<exists> prf \<in> proof. prfOf prf \<phi>)"


(* Working with two provability relations:
provability prv and basic provability bprv  *)

locale Deduct2 = 
Deduct
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  prv
+
B: Deduct
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  bprv
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst 
and num
and eql cnj imp all exi 
and prv bprv
+
assumes bprv_prv: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> bprv \<phi> \<Longrightarrow> prv \<phi>" 
begin

(* Removing the sentence (empty Fvars) hypothesis from bprv_prv *)
lemma bprv_prv': 
  assumes \<phi>: "\<phi> \<in> fmla" and b: "bprv \<phi>"
  shows "prv \<phi>"  
proof-
  obtain V where V: "Fvars \<phi> = V" by blast
  have VV: "V \<subseteq> var" using Fvars V \<phi> by blast
  have f: "finite V" using V finite_Fvars[OF \<phi>] by auto
  thus ?thesis using \<phi> b V VV
  proof(induction V arbitrary: \<phi> rule: finite.induct)
    case (emptyI \<phi>)
    then show ?case by (simp add: bprv_prv)
  next
    case (insertI W v \<phi>)
    show ?case proof(cases "v \<in> W")
      case True 
      thus ?thesis 
      using insertI.IH[OF `\<phi> \<in> fmla`] insertI.prems 
      by (simp add: insert_absorb)
    next
      case False
      hence 1: "Fvars (all v \<phi>) = W"       
        using insertI.prems by auto
      moreover have "bprv (all v \<phi>)"  
        using B.prv_all_gen insertI.prems by auto
      ultimately have "prv (all v \<phi>)" using insertI by auto
      thus ?thesis using allE_id insertI.prems by blast
    qed 
  qed
qed

end (* context Deduct2 *)


locale Deduct2_with_False = 
Deduct_with_False  
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  num
  prv
+
B: Deduct_with_False
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  num
  bprv
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and eql cnj imp all exi 
and fls 
and num
and prv bprv
+
assumes bprv_prv: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> bprv \<phi> \<Longrightarrow> prv \<phi>" 

sublocale Deduct2_with_False < d_dwf: Deduct2 
  apply standard using bprv_prv .

context Deduct2_with_False begin

lemma consistent_B_consistent: "consistent \<Longrightarrow> B.consistent"
  using B.consistent_def bprv_prv consistent_def by blast

end (* context Deduct2_with_False *)

locale Deduct2_with_False_Disj = 
Deduct_with_False_Disj  
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  prv
+ 
B: Deduct_with_False_Disj  
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  bprv
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and eql cnj imp all exi 
and fls
and dsj
and num
and prv bprv
+
assumes bprv_prv: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> bprv \<phi> \<Longrightarrow> prv \<phi>" 

sublocale Deduct2_with_False_Disj < dwf_dwfd: Deduct2_with_False
  apply standard using bprv_prv .


(* We consider proof structure only for prv, not for bprv *)
locale Deduct2_with_Proofs = 
Deduct2_with_False_Disj
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  prv bprv 
+
Deduct_with_Proofs  
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  prv
  "proof" prfOf
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and eql cnj imp all exi 
and fls
and dsj
and num
and prv bprv
and "proof" :: "'proof set" and prfOf  

(* Factoring in a strict-order-like relation (not actually required to be an order): *)
locale Deduct2_with_PseudoOrder = 
Deduct2_with_False_Disj  
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  prv bprv
+
Syntax_PseudoOrder 
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  Lq
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and eql cnj imp all exi 
and fls
and dsj
and num   
and prv bprv 
and Lq
+
assumes 
(* We do not assume any ordering properties, but only these two axioms, Lq_num and Lq_num2, 
which (interestingly) would be satisfied by both \<le> and < within a sufficiently strong 
arithmetic such as Robinson's Q *)
(* For each formula \<phi>(z) and numeral q, if \<phi>(p) is provable for all p
then \<forall> z \<le> q. \<phi>(z) is provable.  
(Note that a more natural property would assume \<phi>(p) is provable for all p\<le>q, 
but we can get away with the stronger assumption (on the left of the implication). )
*)
Lq_num: 
"let LLq = (\<lambda> t1 t2. psubst Lq [(t1,zz), (t2,yy)]) in  
 \<forall> \<phi> \<in> fmla. \<forall> q \<in> num. Fvars \<phi> = {zz} \<and> (\<forall> p \<in> num. bprv (subst \<phi> p zz))
    \<longrightarrow> prv (all zz (imp (LLq (Var zz) q) \<phi>))"
and 
(* For each numeral p, there exists a finite set P such that it is provable that 
\<forall> y. (\<Or>p\<in>P. x = p) \<or> y \<le> p
(where we write \<le> instead of Lq, but could also think of <): 
*)
Lq_num2: 
"let LLq = (\<lambda> t1 t2. psubst Lq [(t1,zz), (t2,yy)]) in   
 \<forall> p \<in> num. \<exists> P \<subseteq> num. finite P \<and> prv (dsj (sdsj {eql (Var yy) r | r. r \<in> P}) (LLq p (Var yy)))"
begin 

lemma LLq_num: 
assumes "\<phi> \<in> fmla" "q \<in> num" "Fvars \<phi> = {zz}" "\<forall> p \<in> num. bprv (subst \<phi> p zz)"
shows "prv (all zz (imp (LLq (Var zz) q) \<phi>))"
using assms Lq_num unfolding LLq_def by auto 

lemma LLq_num2: 
assumes "p \<in> num" 
shows "\<exists> P \<subseteq> num. finite P \<and> prv (dsj (sdsj {eql (Var yy) r | r. r \<in> P}) (LLq p (Var yy)))"
using assms Lq_num2 unfolding LLq_def by auto 

end \<comment> \<open>context Deduct_with_PseudoOrder\<close>

locale Deduct2_with_Proofs_PseudoOrder = 
Deduct2_with_Proofs  
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  prv bprv
  "proof" prfOf
+
Deduct2_with_PseudoOrder
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  prv bprv
  Lq
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and eql cnj imp all exi 
and fls
and dsj
and num
and prv bprv
and "proof" :: "'proof set" and prfOf 
and Lq


(*<*)
end
(*>*)