theory PseudoTerms
  imports Natural_Deduction 
begin

context Generic_Syntax
begin 

(* For our pseudo-terms, Variable 0 will be the output variable: *)
abbreviation "out \<equiv> Variable 0"
(* The concrete cases we consider will have only one output variable, 
 namely V 1: *)
abbreviation "inp \<equiv> Variable (Suc 0)"

(* These can speed up simplification: *)
lemma out: "out \<in> var"
  and inp: "inp \<in> var" 
  by auto
lemma out_inp_distinct[simp]: 
"out \<noteq> inp" "out \<noteq> inp"
"out \<noteq> xx" "out \<noteq> yy" "yy \<noteq> out" "out \<noteq> zz" "zz \<noteq> out" "out \<noteq> xx'" "xx' \<noteq> out" 
   "out \<noteq> yy'" "yy' \<noteq> out" "out \<noteq> zz'" "zz' \<noteq> out"
"inp \<noteq> xx" "inp \<noteq> yy" "yy \<noteq> inp" "inp \<noteq> zz" "zz \<noteq> inp" "inp \<noteq> xx'" "xx' \<noteq> inp" 
   "inp \<noteq> yy'" "yy' \<noteq> inp" "inp \<noteq> zz'" "zz' \<noteq> inp"
  by auto

(* Instantiation of a formula (in particular, a pseudo-term) 
with a term on the input variable: *)
definition instInp :: "'fmla \<Rightarrow> 'trm \<Rightarrow> 'fmla" where 
"instInp \<phi> t \<equiv> subst \<phi> t inp"

lemma instInp_fmla[simp,intro]: 
assumes "\<phi> \<in> fmla" and "t \<in> trm"
shows "instInp \<phi> t \<in> fmla"
using assms instInp_def by auto

lemma Fvars_instInp[simp,intro]: 
assumes "\<phi> \<in> fmla" and "t \<in> trm" "Fvars \<phi> = {inp}"
shows "Fvars (instInp \<phi> t) = FvarsT t"
using assms instInp_def by (auto simp: Fvars_subst)


end (* context Generic_Syntax *)


context Deduct_with_False_Disj_Rename 
begin 

(* TODO: move where they belong: *)

lemma nprv_exi_commute: 
assumes [simp]: "x \<in> var" "y \<in> var" "\<phi> \<in> fmla"
shows "nprv {exi x (exi y \<phi>)} (exi y (exi x \<phi>))"
apply(rule nprv_exiE0[of x "exi y \<phi>"], auto)
apply(rule nprv_clear2_2, auto)
apply(rule nprv_exiE0[of y \<phi>], auto)
apply(rule nprv_clear2_2, auto)
apply(rule nprv_exiI[of _ _ "Var y"], auto)
by (rule nprv_exiI[of _ _ "Var x"], auto intro: nprv_hyp)

lemma prv_exi_commute: 
assumes [simp]: "x \<in> var" "y \<in> var" "\<phi> \<in> fmla"
shows "prv (imp (exi x (exi y \<phi>)) (exi y (exi x \<phi>)))"
apply(rule nprv_prvI, auto)
apply(rule nprv_impI, auto)
by (rule nprv_exi_commute, auto)

lemma subst_all_idle[simp]: 
assumes [simp]: "x \<in> var" "\<phi> \<in> fmla" "t \<in> trm"
shows "subst (all x \<phi>) t x = all x \<phi>"
apply(rule subst_notIn) by auto

lemma subst_exi_idle[simp]: 
assumes [simp]: "x \<in> var" "\<phi> \<in> fmla" "t \<in> trm"
shows "subst (exi x \<phi>) t x = exi x \<phi>"
apply(rule subst_notIn) by auto

lemma subst_exu_idle[simp]: 
assumes [simp]: "x \<in> var" "\<phi> \<in> fmla" "t \<in> trm"
shows "subst (exu x \<phi>) t x = exu x \<phi>"
apply(rule subst_notIn) by auto

lemma prv_exu_exi:
  assumes "x \<in> var" "\<phi> \<in> fmla" "prv (exu x \<phi>)"
  shows "prv (exi x \<phi>)"
  by (meson assms exi exu prv_exu_imp_exi prv_imp_mp)

(* end TODO *)




(* Pseudo-terms over the first n+1 variables (i.e., having free n-variables) *)
definition ptrm :: "nat \<Rightarrow> 'fmla set" where 
"ptrm n \<equiv> {\<sigma> \<in> fmla . Fvars \<sigma> = Variable ` {0..n} \<and> prv (exu out \<sigma>)}"

lemma ptrm[intro,simp]: "\<sigma> \<in> ptrm n \<Longrightarrow> \<sigma> \<in> fmla"
  unfolding ptrm_def by auto

lemma ptrm_1_Fvars[simp]: "\<sigma> \<in> ptrm (Suc 0) \<Longrightarrow> Fvars \<sigma> = {out,inp}"
	unfolding ptrm_def by auto

lemma ptrm_prv_exu: "\<sigma> \<in> ptrm n \<Longrightarrow> prv (exu out \<sigma>)"
  unfolding ptrm_def by auto

lemma ptrm_prv_exi: "\<sigma> \<in> ptrm n \<Longrightarrow> prv (exi out \<sigma>)"
  by (simp add: ptrm_prv_exu prv_exu_exi)

lemma nprv_ptrmE_exi: 
"\<sigma> \<in> ptrm n \<Longrightarrow> nprv (insert \<sigma> F) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> 
 \<psi> \<in> fmla \<Longrightarrow> out \<notin> Fvars \<psi> \<Longrightarrow> out \<notin> \<Union> (Fvars ` F) \<Longrightarrow> nprv F \<psi>"
  apply (frule ptrm_prv_exu, drule ptrm)
  apply(rule nprv_exuE_exi[of _ out \<sigma>]) 
  by (auto intro!: prv_nprvI)

lemma nprv_ptrmE_uni: 
"\<sigma> \<in> ptrm n \<Longrightarrow> nprv F (subst \<sigma> t1 out) \<Longrightarrow> nprv F (subst \<sigma> t2 out) \<Longrightarrow> 
 nprv (insert (eql t1 t2) F) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> t1 \<in> trm \<Longrightarrow> t2 \<in> trm 
 \<Longrightarrow> nprv F \<psi>"
  apply (frule ptrm_prv_exu, drule ptrm)
  apply(rule nprv_exuE_uni[of _ out \<sigma> t1 t2]) 
  by (auto intro!: prv_nprvI)

lemma nprv_ptrmE_uni0: 
"\<sigma> \<in> ptrm n \<Longrightarrow> nprv F \<sigma> \<Longrightarrow> nprv F (subst \<sigma> t out) \<Longrightarrow> 
 nprv (insert (eql (Var out) t) F) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> t \<in> trm 
 \<Longrightarrow> nprv F \<psi>"
  apply(rule nprv_ptrmE_uni[of \<sigma> _ _ "Var out" t]) by auto

lemma nprv_ptrmE0_uni0: 
"\<sigma> \<in> ptrm n \<Longrightarrow> \<sigma> \<in> F \<Longrightarrow> nprv F (subst \<sigma> t out) \<Longrightarrow> 
 nprv (insert (eql (Var out) t) F) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> t \<in> trm 
 \<Longrightarrow> nprv F \<psi>"
apply(rule nprv_ptrmE_uni0[of \<sigma> n _ t]) by (auto intro: nprv_hyp)


(* The forall versus exists equivalence for pseudo-terms *)

lemma ptrm_nprv_exi: 
assumes \<sigma>: "\<sigma> \<in> ptrm n" and [simp]: "\<phi> \<in> fmla"
shows "nprv {\<sigma>, exi out (cnj \<sigma> \<phi>)} \<phi>"
proof-
  have [simp]: "\<sigma> \<in> fmla" using \<sigma> by simp
  define z where "z \<equiv> getFr [out] [] [\<sigma>,\<phi>]"
  have z_facts[simp]: "z \<in> var" "z \<noteq> out" "z \<notin> Fvars \<sigma>" "z \<notin> Fvars \<phi>" 
  using getFr_FvarsT_Fvars[of "[out]" "[]" "[\<sigma>,\<phi>]"] unfolding z_def[symmetric] by auto 
  have 0: "exi out (cnj \<sigma> \<phi>) = exi z (subst (cnj \<sigma> \<phi>) (Var z) out)"
    by(rule exi_rename, auto)
  show ?thesis 
    unfolding 0 
    apply(rule nprv_exiE0[of z "subst (cnj \<sigma> \<phi>) (Var z) out"], auto)
    apply(rule nprv_ptrmE0_uni0[OF \<sigma>, of _ "Var z"], auto)
      subgoal by (rule nprv_cnjE0, auto intro: nprv_hyp)
      subgoal 
        apply(rule nprv_clear4_4, auto)
        apply(rule nprv_clear3_3, auto)      
        apply (rule nprv_cnjE0, auto)
        apply(rule nprv_clear4_4, auto)
        apply(rule nprv_clear3_1, auto)
        by (rule nprv_eql_substE012[of "Var out" "Var z" _ \<phi> out \<phi>], auto) .
qed

lemma ptrm_nprv_exi_all: 
  assumes \<sigma>: "\<sigma> \<in> ptrm n" and [simp]: "\<phi> \<in> fmla"
  shows "nprv {exi out (cnj \<sigma> \<phi>)} (all out (imp \<sigma> \<phi>))" 
proof-  
  have [simp]: "\<sigma> \<in> fmla" using \<sigma> by simp 
  show ?thesis   
  apply(rule nprv_allI, auto)
  apply(rule nprv_impI, auto)
  by (rule ptrm_nprv_exi[OF \<sigma>], auto)
qed

lemma ptrm_prv_exi_imp_all: 
  assumes \<sigma>: "\<sigma> \<in> ptrm n" and [simp]: "\<phi> \<in> fmla"
  shows "prv (imp (exi out (cnj \<sigma> \<phi>)) (all out (imp \<sigma> \<phi>)))" 
proof-  
  have [simp]: "\<sigma> \<in> fmla" using \<sigma> by simp 
  show ?thesis 
  apply(rule nprv_prvI, auto)
  apply(rule nprv_impI, auto)
    by (rule ptrm_nprv_exi_all[OF \<sigma>], auto)
qed

lemma ptrm_nprv_all_imp_exi: 
  assumes \<sigma>: "\<sigma> \<in> ptrm n" and [simp]: "\<phi> \<in> fmla"
  shows "nprv {all out (imp \<sigma> \<phi>)} (exi out (cnj \<sigma> \<phi>))" 
proof-  
  have [simp]: "\<sigma> \<in> fmla" using \<sigma> by simp
  define z where "z \<equiv> getFr [out] [] [\<sigma>,\<phi>]"
  have z_facts[simp]: "z \<in> var" "z \<noteq> out" "z \<notin> Fvars \<sigma>" "z \<notin> Fvars \<phi>" 
  using getFr_FvarsT_Fvars[of "[out]" "[]" "[\<sigma>,\<phi>]"] unfolding z_def[symmetric] by auto   
  show ?thesis  
    apply(rule nprv_ptrmE_exi[OF \<sigma>], auto) 
    apply(rule nprv_exiI[of _ "cnj \<sigma> \<phi>" "Var out" out], auto)
    apply(rule nprv_allE0[of out "imp \<sigma> \<phi>" _ "Var out"], auto)
    apply(rule nprv_clear3_3, auto)
    apply(rule nprv_cnjI, auto intro: nprv_hyp)
    by (rule nprv_impE01, auto intro: nprv_hyp)
qed

lemma ptrm_prv_all_imp_exi: 
  assumes \<sigma>: "\<sigma> \<in> ptrm n" and [simp]: "\<phi> \<in> fmla"
  shows "prv (imp (all out (imp \<sigma> \<phi>)) (exi out (cnj \<sigma> \<phi>)))" 
proof-  
  have [simp]: "\<sigma> \<in> fmla" using \<sigma> by simp
  define z where "z \<equiv> getFr [out] [] [\<sigma>,\<phi>]"
  have z_facts[simp]: "z \<in> var" "z \<noteq> out" "z \<notin> Fvars \<sigma>" "z \<notin> Fvars \<phi>" 
  using getFr_FvarsT_Fvars[of "[out]" "[]" "[\<sigma>,\<phi>]"] unfolding z_def[symmetric] by auto   
  show ?thesis 
  apply(rule nprv_prvI, auto)
  apply(rule nprv_impI, auto)
  by (rule ptrm_nprv_all_imp_exi[OF \<sigma>], auto) 
qed


(* Some "notations" to facilitate reasoning for pterms: *)

(* Composition of a formula with a pseudo-term by plugging/substituting the 
 pseudo-term for its "inp" variable : *)
definition cmpP :: "'fmla \<Rightarrow> nat \<Rightarrow> 'fmla \<Rightarrow> 'fmla" where 
"cmpP \<phi> n \<tau> \<equiv> let zz = Variable (Suc (Suc n)) in 
   exi zz (cnj (subst \<tau> (Var zz) out) (subst \<phi> (Var zz) inp))" 

lemma cmpP_fmla[simp, intro]: 
	assumes "\<phi> \<in> fmla" and "\<tau> \<in> fmla"
	shows "cmpP \<phi> n \<tau> \<in> fmla"
	using assms unfolding cmpP_def by (auto simp: Let_def)

lemma Fvars_cmpP: 
assumes "\<phi> \<in> fmla" and \<tau>: "\<tau> \<in> ptrm n"  "Variable (Suc (Suc n)) \<notin> Fvars \<phi>"
shows "Fvars (cmpP \<phi> n \<tau>) = Fvars \<phi> - {inp} \<union> Variable ` {(Suc 0)..n}"
using assms unfolding cmpP_def Let_def ptrm_def by (auto simp: Fvars_subst)

lemma Fvars_cmpP2: 
assumes "\<phi> \<in> fmla" and \<tau>: "\<tau> \<in> ptrm n" and "Fvars \<phi> \<subseteq> {inp}"
shows "Fvars (cmpP \<phi> n \<tau>) = Fvars \<phi> - {inp} \<union> Variable ` {(Suc 0)..n}"
apply(subst Fvars_cmpP) using assms by auto 

lemma cmpP1: 
assumes \<sigma>: "\<sigma> \<in> ptrm (Suc 0)" and \<tau>: "\<tau> \<in> ptrm n"
shows "cmpP \<sigma> n \<tau> \<in> ptrm n"
proof-
  note Let_def[simp]
  have [simp]: "\<sigma> \<in> fmla" "\<tau> \<in> fmla" "Fvars \<sigma> = {out,inp}" 
   "Fvars \<tau> = Variable ` {0..n}"
    using assms unfolding ptrm_def by auto
  define zz where "zz \<equiv> Variable (Suc (Suc n))"
  have zz_facts[simp]: "zz \<in> var" "\<And>i. i \<le> n \<Longrightarrow> Variable i \<noteq> zz \<and> zz \<noteq> Variable i"
    "out \<noteq> zz \<and> zz \<noteq> out" "inp \<noteq> zz \<and> zz \<noteq> inp" 
   unfolding zz_def by auto

  define x where "x \<equiv> getFr [out,inp,zz] [] [\<sigma>,\<tau>]"
  have x_facts[simp]: "x \<in> var" "x \<noteq> out" "x \<noteq> inp" 
  "x \<noteq> zz" "zz \<noteq> x" "x \<notin> Fvars \<sigma>" "x \<notin> Fvars \<tau>" 
  using getFr_FvarsT_Fvars[of "[out,inp,zz]" "[]" "[\<sigma>,\<tau>]"] unfolding x_def[symmetric] by auto
  have [simp]: "x \<noteq> Variable (Suc (Suc n))"  
  	using x_facts(4) zz_def by auto
  define z where "z \<equiv> getFr [out,inp,zz,x] [] [\<sigma>,\<tau>]"
  have z_facts[simp]: "z \<in> var" "z \<noteq> out" "z \<noteq> inp" "z \<noteq> x" "z \<noteq> zz" "z \<notin> Fvars \<sigma>" "z \<notin> Fvars \<tau>" 
  using getFr_FvarsT_Fvars[of "[out,inp,zz,x]" "[]" "[\<sigma>,\<tau>]"] unfolding z_def[symmetric] by auto

  (* AtoD: Do you happen to see why sis I have to prove these? *)
  have [simp]: "\<And>i. z = Variable i \<Longrightarrow> \<not> i \<le> n" 
   and [simp]: "\<And>i. x = Variable i \<Longrightarrow> \<not> i \<le> n" 
   using \<open>Fvars \<tau> = Variable ` {0..n}\<close> atLeastAtMost_iff z_facts(7) apply blast
   using \<open>Fvars \<tau> = Variable ` {0..n}\<close> atLeastAtMost_iff x_facts(7) by blast

  have [simp]: "Fvars (cmpP \<sigma> n \<tau>) = Variable ` {0..n}"
    unfolding cmpP_def by (auto simp: Fvars_subst)
  have tt: "exi out \<tau> = exi zz (subst \<tau> (Var zz) out)" apply(rule exi_rename) by auto

  have exi_\<sigma>: "prv (exi out \<sigma>)" and exi_\<tau>: "prv (exi zz (subst \<tau> (Var zz) out))"
  	using \<sigma> \<tau> ptrm_prv_exi tt by fastforce+ 	
  have exi_\<sigma>: "prv (exi out (subst \<sigma> (Var zz) inp))"
    using prv_subst[OF _ _ _ exi_\<sigma>, of inp "Var zz"] by auto

  have exu_\<sigma>: "prv (exu out \<sigma>)"  
  	using \<sigma> ptrm_prv_exu by blast  
  have exu_\<sigma>: "prv (exu out (subst \<sigma> (Var zz) inp))"
    using prv_subst[OF _ _ _ exu_\<sigma>, of inp "Var zz"] by auto

  have zz_z: "exi zz (cnj (subst \<tau> (Var zz) out) (subst \<sigma> (Var zz) inp)) = 
              exi z (cnj (subst \<tau> (Var z) out) (subst \<sigma> (Var z) inp))"
   apply(subst exi_rename[of _ zz z]) apply auto
   apply (auto simp: Fvars_subst)  
   apply(subst subst_subst) by auto 
   (* AtoD: Do you happen to see why I have to subst with subst_subst, 
     which is a simplification rule *)
  have 0: "prv (exu out (cmpP \<sigma> n \<tau>))" 
  apply(rule nprv_prvI, auto)
  apply(rule nprv_exuI_exi[of _ _ _ x], auto)  
  subgoal unfolding cmpP_def Let_def 
    apply(rule nprv_addImpLemmaI[OF prv_exi_commute], auto)
    apply(rule nprv_addLemmaE[OF exi_\<tau>], auto)
    apply(rule nprv_exiE[of _ zz "subst \<tau> (Var zz) out"], auto simp: nprv_hyp) 
    apply(rule nprv_clear2_2, auto)
    apply(rule nprv_exiI[of _ _ "Var zz"], auto)
    apply(rule nprv_addLemmaE[OF exi_\<sigma>], auto)
    apply(rule nprv_exiE[of _ out "subst \<sigma> (Var zz) inp"], auto simp: nprv_hyp Fvars_subst) 
    apply(rule nprv_clear3_2, auto)
    apply(rule nprv_exiI[of _ _ "Var out"], auto)
    apply(subst subst_subst, auto) (* same here *)
    by (rule nprv_cnjI, auto intro: nprv_hyp)
  subgoal
    unfolding cmpP_def Let_def zz_def[symmetric] apply(subst subst_exi, auto)  
    apply(subst subst_compose_same, auto)
    apply(rule nprv_exiE0[of zz], auto simp: Fvars_subst  z_def[symmetric])
    apply(rule nprv_clear3_2, auto)
    apply(rule nprv_cnjE0, auto)
    apply(rule nprv_clear4_3, auto)
    unfolding zz_z 
    apply(rule nprv_exiE0[of z], auto simp: Fvars_subst)
    apply(rule nprv_clear4_4, auto)
    apply(rule nprv_cnjE0, auto)
    apply(rule nprv_clear5_3, auto)
    apply(rule nprv_cut[of _ "eql (Var z) (Var zz)"], auto)
    subgoal
      apply(rule nprv_clear4_2, auto)
      apply(rule nprv_clear3_3, auto)
      by (rule nprv_ptrmE_uni[OF \<tau>, of _ "Var z" "Var zz"], auto simp: nprv_hyp)
    subgoal
      apply(rule nprv_clear5_2, auto)
      apply(rule nprv_clear4_3, auto)  
      apply(rule nprv_eql_substE[of _ "Var zz" "Var z" \<sigma> inp], auto simp: nprv_hyp)
      subgoal
        by (rule nprv_eql_symE01, auto)
      subgoal
        apply(rule nprv_clear4_2, auto)
        apply(rule nprv_clear3_2, auto)
        apply(rule nprv_addLemmaE[OF exu_\<sigma>], auto)
        apply(rule nprv_exuE_uni[of _ out "subst \<sigma> (Var zz) inp" "Var out" "Var x"], auto simp: nprv_hyp) 
        by (rule nprv_eql_symE01, auto) . . .
	show ?thesis using 0 unfolding ptrm_def cmpP_def Let_def by (auto simp: Fvars_subst)
qed		


(* Properties of pseudo-term instances: *)

lemma Fvars_instInp_ptrm_1[simp,intro]: 
assumes \<tau>: "\<tau> \<in> ptrm (Suc 0)" and "t \<in> trm"
shows "Fvars (instInp \<tau> t) = insert out (FvarsT t)"
using assms instInp_def by (auto simp: Fvars_subst)

lemma instInp: 
assumes \<tau>: "\<tau> \<in> ptrm (Suc 0)" and [simp]: "t \<in> trm" 
and [simp]: "FvarsT t = Variable ` {(Suc 0)..n}"
shows "instInp \<tau> t \<in> ptrm n"
proof- 
  note Let_def[simp]
  have [simp]: "\<tau> \<in> fmla" "Fvars \<tau> = {out,inp}" 
    using assms unfolding ptrm_def by auto
  have [simp]: "Fvars (instInp \<tau> t) = insert out (FvarsT t)" 
   apply(subst Fvars_instInp_ptrm_1) using \<tau> by auto 
  have 0: "exu out (instInp \<tau> t) = subst (exu out \<tau>) t inp" 
    unfolding instInp_def by (subst subst_exu) auto
  have 1: "prv (exu out \<tau>)" using \<tau> unfolding ptrm_def by auto   
  have "prv (exu out (instInp \<tau> t))" 
  unfolding 0 by (rule prv_subst[OF _ _ _ 1], auto) 
  thus ?thesis using assms unfolding ptrm_def[of n] by auto
qed

lemma instInp_0: 
assumes \<tau>: "\<tau> \<in> ptrm (Suc 0)" and "t \<in> trm" and "FvarsT t = {}"
shows "instInp \<tau> t \<in> ptrm 0"
using assms by (intro instInp, auto)

lemma instInp_1: 
assumes \<tau>: "\<tau> \<in> ptrm (Suc 0)" and "t \<in> trm" and "FvarsT t = {inp}"
shows "instInp \<tau> t \<in> ptrm (Suc 0)"
using assms by (intro instInp, auto)

lemma instInp_cmpP: 
assumes \<phi>: "\<phi> \<in> fmla" "Fvars \<phi> \<subseteq> {inp}" and \<tau>: "\<tau> \<in> ptrm (Suc 0)" 
and "t \<in> trm" and "FvarsT t = {}"
shows "instInp (cmpP \<phi> (Suc 0) \<tau>) t = cmpP \<phi> 0 (instInp \<tau> t)"
proof-
  define x1 and x2 where 
   x12: "x1 \<equiv> Variable (Suc (Suc 0))" 
        "x2 \<equiv> Variable (Suc (Suc (Suc 0)))"
  have x_facts[simp]: "x1 \<in> var" "x2 \<in> var" "x1 \<noteq> inp" "x2 \<noteq> inp"
   "x1 \<noteq> out" "out \<noteq> x1" "x2 \<noteq> out" "out \<noteq> x2" "x1 \<noteq> x2" "x2 \<noteq> x1"
   unfolding x12 by auto
  show ?thesis 
  using assms unfolding instInp_def cmpP_def Let_def x12[symmetric] 
  apply(subst subst_exi) apply auto
  apply(subst subst_compose_same, auto)
  apply(subst subst_compose_diff, auto)
  apply(subst exi_rename[of _ x1 x2], auto simp: Fvars_subst)
  apply(subst subst_comp, auto)  
  apply(subst subst_notIn[of \<phi> _ x1], auto) .
qed 


(* Provable equality between a pseudo-term and a term: *)
definition prveqlPT :: "'fmla \<Rightarrow> 'trm \<Rightarrow> bool" where 
"prveqlPT \<tau> t \<equiv> prv (subst \<tau> t out)"

lemma prveqlPT_nprv_instInp_cmpP: 
assumes[simp]: "\<phi> \<in> fmla" and f: "Fvars \<phi> \<subseteq> {inp}" and \<tau>: "\<tau> \<in> ptrm 0" 
and [simp]: "t \<in> trm" "FvarsT t = {}"
and \<tau>t: "prveqlPT \<tau> t"  
shows "nprv {cmpP \<phi> 0 \<tau>} (instInp \<phi> t)"
proof-
  have [simp]: "\<tau> \<in> fmla" "Fvars \<tau> = {out}" using \<tau> unfolding ptrm_def by auto
  define zz where "zz \<equiv> Variable (Suc (Suc 0))"
  have zz_facts[simp]: "zz \<in> var"  
    "out \<noteq> zz \<and> zz \<noteq> out" "inp \<noteq> zz \<and> zz \<noteq> inp" "zz \<notin> Fvars \<tau>" "zz \<notin> Fvars \<phi>"
   unfolding zz_def using f by auto

  note lemma1 = nprv_addLemmaE[OF \<tau>t[unfolded prveqlPT_def]] 

  show ?thesis unfolding cmpP_def Let_def zz_def[symmetric] instInp_def
  apply(rule lemma1, auto) 
  apply(rule nprv_exiE0[of zz], auto simp: Fvars_subst)
  apply(rule nprv_clear3_3, auto)
  apply(rule nprv_cnjE0, auto)
  apply(rule nprv_clear4_3, auto)
  apply(rule nprv_ptrmE_uni[OF \<tau>, of _ t "Var zz"], auto intro: nprv_hyp)
  apply(rule nprv_clear4_2, auto)
  apply(rule nprv_clear3_3, auto)
  apply(rule nprv_eql_substE012[of t "Var zz" _ \<phi> inp], auto) .
qed

lemma prveqlPT_prv_instInp_cmpP: 
assumes"\<phi> \<in> fmla" and f: "Fvars \<phi> \<subseteq> {inp}" and \<tau>: "\<tau> \<in> ptrm 0" 
and "t \<in> trm" "FvarsT t = {}"
and \<tau>t: "prveqlPT \<tau> t"  
shows "prv (imp (cmpP \<phi> 0 \<tau>) (instInp \<phi> t))"
apply(intro nprv_prvI nprv_impI prveqlPT_nprv_instInp_cmpP)
using assms by auto 

lemma prveqlPT_nprv_cmpP_instInp: 
assumes[simp]: "\<phi> \<in> fmla" and f: "Fvars \<phi> \<subseteq> {inp}" and \<tau>: "\<tau> \<in> ptrm 0" 
and [simp]: "t \<in> trm" "FvarsT t = {}"
and \<tau>t: "prveqlPT \<tau> t"  
shows "nprv {instInp \<phi> t} (cmpP \<phi> 0 \<tau>)"
proof-
  have [simp]: "\<tau> \<in> fmla" "Fvars \<tau> = {out}" using \<tau> unfolding ptrm_def by auto
  define zz where "zz \<equiv> Variable (Suc (Suc 0))"
  have zz_facts[simp]: "zz \<in> var"  
    "out \<noteq> zz \<and> zz \<noteq> out" "inp \<noteq> zz \<and> zz \<noteq> inp" "zz \<notin> Fvars \<tau>" "zz \<notin> Fvars \<phi>"
   unfolding zz_def using f by auto 

  note lemma1 = nprv_addLemmaE[OF \<tau>t[unfolded prveqlPT_def]] 

  show ?thesis unfolding cmpP_def Let_def zz_def[symmetric] instInp_def
  apply(rule lemma1, auto) 
  apply(rule nprv_exiI[of _ _ t], auto) 
  apply(rule nprv_cnjI, auto simp: nprv_hyp) . 
qed

lemma prveqlPT_prv_cmpP_instInp: 
assumes"\<phi> \<in> fmla" and f: "Fvars \<phi> \<subseteq> {inp}" and \<tau>: "\<tau> \<in> ptrm 0" 
and "t \<in> trm" "FvarsT t = {}"
and \<tau>t: "prveqlPT \<tau> t"  
shows "prv (imp (instInp \<phi> t) (cmpP \<phi> 0 \<tau>))"
apply(intro nprv_prvI nprv_impI prveqlPT_nprv_cmpP_instInp)
using assms by auto 

lemma prveqlPT_prv_instInp_eqv_cmpP: 
assumes"\<phi> \<in> fmla" and f: "Fvars \<phi> \<subseteq> {inp}" and \<tau>: "\<tau> \<in> ptrm 0" 
and "t \<in> trm" "FvarsT t = {}"
and \<tau>t: "prveqlPT \<tau> t"  
shows "prv (eqv (cmpP \<phi> 0 \<tau>) (instInp \<phi> t))"  
apply(rule prv_eqvI)
using assms prveqlPT_prv_instInp_cmpP prveqlPT_prv_cmpP_instInp by auto

(* Compositionality of cmpP: *)
lemma nprv_cmpP_compose: 
assumes [simp]: "\<chi> \<in> fmla" "Fvars \<chi> = {inp}"
and \<sigma>[simp]: "\<sigma> \<in> ptrm (Suc 0)" and \<tau>[simp]: "\<tau> \<in> ptrm 0"
shows "nprv {cmpP (cmpP \<chi> (Suc 0) \<sigma>) 0 \<tau>} 
            (cmpP \<chi> 0 (cmpP \<sigma> 0 \<tau>))" (is ?A)
(* *)
      "nprv {cmpP \<chi> 0 (cmpP \<sigma> 0 \<tau>)} 
            (cmpP (cmpP \<chi> (Suc 0) \<sigma>) 0 \<tau>)" (is ?B)
proof-
  define \<chi>\<sigma> and \<sigma>\<tau> where \<chi>\<sigma>_def: "\<chi>\<sigma> \<equiv> cmpP \<chi> (Suc 0) \<sigma>" and \<sigma>\<tau>_def: "\<sigma>\<tau> \<equiv> cmpP \<sigma> 0 \<tau>"

  have [simp]: "\<sigma> \<in> fmla" "Fvars \<sigma> = {out,inp}" "\<tau> \<in> fmla" "Fvars \<tau> = {out}"
    using \<sigma> \<tau> unfolding ptrm_def by auto
  have \<chi>\<sigma>[simp]: "\<chi>\<sigma> \<in> fmla" "Fvars \<chi>\<sigma> = {inp}" unfolding \<chi>\<sigma>_def by (auto simp: Fvars_cmpP2)
  have \<sigma>\<tau>[simp]:  "\<sigma>\<tau> \<in> ptrm 0" "\<sigma>\<tau> \<in> fmla" "Fvars \<sigma>\<tau> = {out}" unfolding \<sigma>\<tau>_def 
    by (auto simp: Fvars_cmpP cmpP1)
  define z where "z \<equiv> Variable (Suc (Suc 0))"
  have z_facts[simp]: "z \<in> var"  
    "out \<noteq> z \<and> z \<noteq> out" "inp \<noteq> z \<and> z \<noteq> inp" "z \<notin> Fvars \<chi>" "z \<notin> Fvars \<sigma>" "z \<notin> Fvars \<tau>"
   unfolding z_def by auto
  define zz where "zz \<equiv> Variable (Suc (Suc (Suc 0)))"
  have zz_facts[simp]: "zz \<in> var"  
    "out \<noteq> zz \<and> zz \<noteq> out" "inp \<noteq> zz \<and> zz \<noteq> inp" "z \<noteq> zz \<and> zz \<noteq> z"
    "zz \<notin> Fvars \<chi>" "zz \<notin> Fvars \<sigma>" "zz \<notin> Fvars \<tau>"
   unfolding zz_def z_def by auto
  define z' where "z' \<equiv> getFr [out,inp,z,zz] [] [\<chi>,\<sigma>,\<tau>]"
  have z'_facts[simp]: "z' \<in> var" "z' \<noteq> out" "z' \<noteq> inp" "z' \<noteq> z" "z \<noteq> z'" "z' \<noteq> zz" "zz \<noteq> z'"
   "z' \<notin> Fvars \<chi>""z' \<notin> Fvars \<sigma>" "z' \<notin> Fvars \<tau>" 
  using getFr_FvarsT_Fvars[of "[out,inp,z,zz]" "[]" "[\<chi>,\<sigma>,\<tau>]"] unfolding z'_def[symmetric] by auto

  have \<chi>\<sigma>': "cmpP \<chi>\<sigma> 0 \<tau> = exi z' (cnj (subst \<tau> (Var z') out) (subst \<chi>\<sigma> (Var z') inp))" 
    unfolding cmpP_def Let_def z_def[symmetric]
    by (auto simp: Fvars_subst exi_rename[of _ z z']) 
  have \<chi>\<sigma>z': "subst \<chi>\<sigma> (Var z') inp = 
    exi zz (cnj (subst (subst \<sigma> (Var zz) out) (Var z') inp) (subst \<chi> (Var zz) inp))"
  unfolding \<chi>\<sigma>_def cmpP_def Let_def zz_def[symmetric] 
  by (auto simp: subst_compose_same) 
  have \<sigma>\<tau>zz: "subst \<sigma>\<tau> (Var zz) out = 
     exi z (cnj (subst \<tau> (Var z) out) (subst (subst \<sigma> (Var zz) out) (Var z) inp))"
  unfolding \<sigma>\<tau>_def cmpP_def Let_def z_def[symmetric]  
  apply (auto simp: subst_compose_same) by (subst subst_compose_diff, auto)
  
  have "nprv {cmpP \<chi>\<sigma> 0 \<tau>} (cmpP \<chi> 0 \<sigma>\<tau>)" 
  unfolding \<chi>\<sigma>' 
  apply(rule nprv_exiE0, auto simp: Fvars_cmpP)
  apply(rule nprv_clear2_2, auto)
  apply(rule nprv_cnjE0, auto)
  apply(rule nprv_clear3_3, auto)
  unfolding \<chi>\<sigma>z'
  apply(rule nprv_exiE0, auto simp: Fvars_subst Fvars_cmpP)
  apply(rule nprv_clear3_3, auto)
  apply(rule nprv_cnjE0, auto)
  apply(rule nprv_clear4_3, auto)
  unfolding cmpP_def Let_def z_def[symmetric]
  apply(rule nprv_exiI[of _ _ "Var zz"], auto)
  apply(rule nprv_cnjI, auto)
  subgoal
    apply(rule nprv_clear3_2, auto)
    unfolding \<sigma>\<tau>zz
    apply(rule nprv_exiI[of _ _ "Var z'"], auto simp: Fvars_subst)
    apply(rule nprv_cnjI, auto intro: nprv_hyp) .
  subgoal
    apply(rule nprv_hyp, auto) . .   
  thus ?A unfolding \<chi>\<sigma>_def \<sigma>\<tau>_def .

  have \<chi>\<sigma>\<tau>: "cmpP \<chi> 0 \<sigma>\<tau> = exi z' (cnj (subst \<sigma>\<tau> (Var z') out) (subst \<chi> (Var z') inp))"
  unfolding cmpP_def Let_def z_def[symmetric]
  by (auto simp: Fvars_subst exi_rename[of _ z z']) 

  have \<sigma>\<tau>z': "subst \<sigma>\<tau> (Var z') out = 
   exi z (cnj (subst \<tau> (Var z) out) (subst (subst \<sigma> (Var z) inp) (Var z') out))"
  unfolding \<sigma>\<tau>_def cmpP_def Let_def z_def[symmetric] 
  by (auto simp: subst_compose_same)

  have \<chi>\<sigma>z: "subst \<chi>\<sigma> (Var z) inp = 
    exi zz (cnj (subst (subst \<sigma> (Var z) inp) (Var zz) out) (subst \<chi> (Var zz) inp))"
  unfolding \<chi>\<sigma>_def cmpP_def Let_def zz_def[symmetric] 
  apply (auto simp: subst_compose_same) by (subst subst_compose_diff, auto)

  have "nprv {cmpP \<chi> 0 \<sigma>\<tau>} (cmpP \<chi>\<sigma> 0 \<tau>)"   
  unfolding \<chi>\<sigma>\<tau>
  apply(rule nprv_exiE0, auto simp: Fvars_cmpP)
  apply(rule nprv_clear2_2, auto)
  apply(rule nprv_cnjE0, auto)
  apply(rule nprv_clear3_3, auto)
  unfolding \<sigma>\<tau>z'
  apply(rule nprv_exiE0, auto simp: Fvars_cmpP Fvars_subst)
  apply(rule nprv_clear3_2, auto)
  apply(rule nprv_cnjE0, auto)
  apply(rule nprv_clear4_3, auto)
  unfolding cmpP_def Let_def z_def[symmetric]
  apply(rule nprv_exiI[of _ _ "Var z"], auto)
  apply(rule nprv_cnjI, auto)
  subgoal
    apply(rule nprv_hyp, auto) .
  subgoal
    unfolding \<chi>\<sigma>z
    apply(rule nprv_exiI[of _ _ "Var z'"], auto simp: Fvars_subst)
    apply(rule nprv_cnjI, auto intro: nprv_hyp) . .
  thus ?B unfolding \<chi>\<sigma>_def \<sigma>\<tau>_def .
qed

lemma prv_cmpP_compose: 
assumes [simp]: "\<chi> \<in> fmla" "Fvars \<chi> = {inp}"
and \<sigma>[simp]: "\<sigma> \<in> ptrm (Suc 0)" and \<tau>[simp]: "\<tau> \<in> ptrm 0"
shows "prv (imp (cmpP (cmpP \<chi> (Suc 0) \<sigma>) 0 \<tau>)
                (cmpP \<chi> 0 (cmpP \<sigma> 0 \<tau>)))" (is ?A)
and 
      "prv (imp (cmpP \<chi> 0 (cmpP \<sigma> 0 \<tau>))
                (cmpP (cmpP \<chi> (Suc 0) \<sigma>) 0 \<tau>))" (is ?B)
and 
      "prv (eqv (cmpP (cmpP \<chi> (Suc 0) \<sigma>) 0 \<tau>)
                (cmpP \<chi> 0 (cmpP \<sigma> 0 \<tau>)))" (is ?C)
proof-
  have [simp]: "\<sigma> \<in> fmla" "Fvars \<sigma> = {out,inp}" "\<tau> \<in> fmla" "Fvars \<tau> = {out}"
  using \<sigma> \<tau> unfolding ptrm_def by auto
  show ?A ?B by (intro nprv_prvI nprv_impI nprv_cmpP_compose, auto)+
  thus ?C by (intro prv_eqvI, auto)
qed

end (* context Deduct_with_False_Disj_Rename *)
  

end 