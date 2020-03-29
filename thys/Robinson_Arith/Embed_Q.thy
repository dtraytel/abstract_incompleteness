(* Embedding (intuitionistic) Robinson Arithmetic (Q) *)
theory Embed_Q imports Embed_Syntax_Arith Natural_Deduction
begin  

(* Factoring in a strict-order-like relation (not actually required to be an order): *)
locale Deduct_with_PseudoOrder = 
Deduct_with_False_Disj  
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  prv 
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
and prv
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
 \<forall> \<phi> \<in> fmla. \<forall> q \<in> num. Fvars \<phi> = {zz} \<and> (\<forall> p \<in> num. prv (subst \<phi> p zz))
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
assumes "\<phi> \<in> fmla" "q \<in> num" "Fvars \<phi> = {zz}" "\<forall> p \<in> num. prv (subst \<phi> p zz)"
shows "prv (all zz (imp (LLq (Var zz) q) \<phi>))"
using assms Lq_num unfolding LLq_def by auto 

lemma LLq_num2: 
assumes "p \<in> num" 
shows "\<exists> P \<subseteq> num. finite P \<and> prv (dsj (sdsj {eql (Var yy) r | r. r \<in> P}) (LLq p (Var yy)))"
using assms Lq_num2 unfolding LLq_def by auto 

end \<comment> \<open>context Deduct_with_PseudoOrder\<close>

(*****************************************************)
(* Deduction in (intuitionistic) Robinson arithmetic, a.k.a. (intuitionistic) system Q *)
locale Deduct_Q = 
Syntax_Arith 
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  zer suc pls tms
+
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
and zer suc pls tms 
and prv
+
assumes 
(* The Q axioms: Their names are suffixed by "var" because they employ some fixed variables; 
we will prove more general versions, for arbitrary trms.  
*)
prv_neg_zer_suc_var: 
"prv (neg (eql zer (suc (Var xx))))"
and 
prv_inj_suc_var: 
"prv (imp (eql (suc (Var xx)) (suc (Var yy))) 
          (eql (Var xx) (Var yy)))"
and 
prv_zer_dsj_suc_var: 
"prv (dsj (eql (Var yy) zer)
          (exi xx (eql (Var yy) (suc (Var xx)))))"
and 
prv_pls_zer_var:
"prv (eql (pls (Var xx) zer) (Var xx))"
and 
prv_pls_suc_var:
"prv (eql (pls (Var xx) (suc (Var yy))) 
          (suc (pls (Var xx) (Var yy))))"
and 
prv_tms_zer_var:
"prv (eql (tms (Var xx) zer) zer)"
and 
prv_tms_suc_var:
"prv (eql (tms (Var xx) (suc (Var yy))) 
          (pls (tms (Var xx) (Var yy)) (Var xx)))"
begin

(* Rules for quantifiers that allow changing, on the fly, the bound variable with 
one that is fresh for the proof context: *)
lemma nprv_allI_var: 
assumes n1: "nprv F (subst \<phi> (Var y) x)" 
and i[simp]: "F \<subseteq> fmla" "finite F" "\<phi> \<in> fmla"  "x \<in> var"  "y \<in> var"  
and u: "y \<notin> \<Union> (Fvars ` F)" and yx: "y = x \<or> y \<notin> Fvars \<phi>"
shows "nprv F (all x \<phi>)" 
apply(subst all_rename2[of _ _ y]) using yx apply auto 
apply(rule nprv_allI) using assms apply auto
apply(rule nprv_allI) by auto   

lemma nprv_exiE_var: 
assumes n: "nprv F (exi x \<phi>)"
and nn: "nprv (insert (subst \<phi> (Var y) x) F) \<psi>"
and 0: "F \<subseteq> fmla" "finite F" "\<phi> \<in> fmla" "x \<in> var" "y \<in> var" "\<psi> \<in> fmla"
and yx: "y = x \<or> y \<notin> Fvars \<phi>" "y \<notin> \<Union> (Fvars ` F)" "y \<notin> Fvars \<psi>"
shows "nprv F \<psi>" 
proof-
  have e: "exi x \<phi> = exi y (subst \<phi> (Var y) x)"   
  apply(subst exi_rename2[of _ _ y]) using 0 yx n nn by (auto simp: 0)
  show ?thesis apply(rule nprv_exiE[of _ y "subst \<phi> (Var y) x"]) 
  using assms unfolding e by auto
qed

(******)
(* Natural deduction with the bounded quantifiers *)

lemma nprv_exuI: 
assumes n1: "nprv F (subst \<phi> t x)" and n2: "nprv (insert \<phi> F) (eql (Var x) t)"
and i[simp]: "F \<subseteq> fmla" "finite F" "\<phi> \<in> fmla" "t \<in> trm" "x \<in> var"   "x \<notin> FvarsT t" 
and u: "x \<notin> \<Union> (Fvars ` F)"
shows "nprv F (exu x \<phi>)" 
proof- 
  define z where "z \<equiv> getFr [x] [t] [\<phi>]"
  have z_facts[simp]: "z \<in> var" "z \<noteq> x" "x \<noteq> z"   "z \<notin> FvarsT t" "z \<notin> Fvars \<phi>"   
  using getFr_FvarsT_Fvars[of "[x]" "[t]" "[\<phi>]"] unfolding z_def[symmetric] by auto
  show ?thesis 
  apply(simp add: exu_def_var[of _ z])
  apply(rule nprv_cnjI) apply simp_all
    apply(rule nprv_exiI[of _ _ t]) apply simp_all
    apply(rule n1)
    (**) 
    apply(rule nprv_exiI[of _ _ t]) apply simp_all
    apply(rule nprv_allI) using u apply simp_all
    apply(rule nprv_impI) using n2 apply simp_all
  done
qed

lemma nprv_exuI_var: 
assumes n1: "nprv F (subst \<phi> t x)" and n2: "nprv (insert (subst \<phi> (Var y) x) F) (eql (Var y) t)"
and i[simp]: "F \<subseteq> fmla" "finite F" "\<phi> \<in> fmla" "t \<in> trm" "x \<in> var"   
"y \<in> var" "y \<notin> FvarsT t" and u: "y \<notin> \<Union> (Fvars ` F)" and yx: "y = x \<or> y \<notin> Fvars \<phi>"
shows "nprv F (exu x \<phi>)" 
apply(subst exu_rename2[of _ _ y]) using yx apply auto 
apply(rule nprv_exuI) using assms apply auto
apply(rule nprv_exuI) apply auto  
by (metis i(3-6) i(4) i(5) i(6) subst_same_Var subst_subst)

(* The most useful inro rule for arithmetic: *)
lemma nprv_exuI_exi: 
assumes n1: "nprv F (exi x \<phi>)" and n2: "nprv (insert (subst \<phi> (Var y) x) (insert \<phi> F)) (eql (Var y) (Var x))"
and i[simp]: "F \<subseteq> fmla" "finite F" "\<phi> \<in> fmla" "x \<in> var" "y \<in> var" "y \<noteq> x" "y \<notin> Fvars \<phi>"
and u: "x \<notin> \<Union> (Fvars ` F)" "y \<notin> \<Union> (Fvars ` F)"
shows "nprv F (exu x \<phi>)"
proof-
  have e: "nprv (insert \<phi> F) (exu x \<phi>)"  
  apply(rule nprv_exuI_var[of _ _ "Var x" _ y]) apply simp_all
  apply(rule nprv_hyp) apply simp_all
  using n2 u by auto
  show ?thesis
  apply(rule nprv_cut[OF n1]) apply simp_all
  apply(rule nprv_exiE0) using u apply auto 
  apply(rule nprv_mono[OF e]) by auto
qed

lemma prv_exu_imp_exi:
assumes [simp]: "\<phi> \<in> fmla" "x \<in> var"
shows "prv (imp (exu x \<phi>) (exi x \<phi>))"  
proof-
  define z where z: "z \<equiv> getFr [x] [] [\<phi>]"
  have z_facts[simp]: "z \<in> var" "z \<noteq> x" "x \<noteq> z" "z \<notin> Fvars \<phi>"   
  using getFr_FvarsT_Fvars[of "[x]" "[]" "[\<phi>]"] unfolding z by auto
  show ?thesis unfolding exu_def apply(simp add: Let_def z[symmetric]) 
  by (simp add: prv_imp_cnjL)
qed
 
(* This is just exu behaving for elimination and forward like exi: *)
lemma nprv_exuE_exi: 
assumes n1: "nprv F (exu x \<phi>)" and n2: "nprv (insert \<phi> F) \<psi>"
and i[simp]: "F \<subseteq> fmla" "finite F" "\<phi> \<in> fmla" "x \<in> var" "\<psi> \<in> fmla" "x \<notin> Fvars \<psi>"
and u: "x \<notin> \<Union> (Fvars ` F)" 
shows "nprv F \<psi>" 
apply(rule nprv_exiE[of _ x \<phi>]) using assms apply auto 
by (rule nprv_addImpLemmaI[OF prv_exu_imp_exi[of \<phi> x]]) auto

lemma nprv_exuF_exi: 
assumes n1: "exu x \<phi> \<in> F" and n2: "nprv (insert \<phi> F) \<psi>"
and i[simp]: "F \<subseteq> fmla" "finite F" "\<phi> \<in> fmla" "x \<in> var" "\<psi> \<in> fmla" "x \<notin> Fvars \<psi>"
and u: "x \<notin> \<Union> (Fvars ` F)" 
shows "nprv F \<psi>" 
using assms  nprv_exuE_exi nprv_hyp by metis

lemma prv_exu_uni: 
assumes [simp]: "\<phi> \<in> fmla" "x \<in> var" "t1 \<in> trm" "t2 \<in> trm"
shows "prv (imp (exu x \<phi>) (imp (subst \<phi> t1 x) (imp (subst \<phi> t2 x) (eql t1 t2))))"
proof-
  define z where z: "z \<equiv> getFr [x] [t1,t2] [\<phi>]"
  have z_facts[simp]: "z \<in> var" "z \<noteq> x" "x \<noteq> z" "z \<notin> Fvars \<phi>"  "z \<notin> FvarsT t1" "z \<notin> FvarsT t2"  
  using getFr_FvarsT_Fvars[of "[x]" "[t1,t2]" "[\<phi>]"] unfolding z by auto
  show ?thesis
  apply(rule nprv_prvI) apply simp_all
  apply(rule nprv_impI) apply simp_all
  apply(simp add: exu_def_var[of _ z])   
  apply(rule nprv_cnjE0) apply auto
  apply(rule nprv_clear3_1) apply(rule nprv_clear2_2) apply simp_all
  apply(rule nprv_exiE0) apply (auto simp: Fvars_subst)
  apply(rule nprv_clear2_2) apply simp_all  
  apply(rule nprv_allE0[of _ _ _ t1]) apply auto
  apply(rule nprv_allE0[of _ _ _ t2]) apply auto
  apply(rule nprv_clear3_3) apply simp_all
  apply(rule nprv_impI) apply simp_all
  apply(rule nprv_impI) apply simp_all  
  apply(rule nprv_impE01) apply auto
  apply(rule nprv_clear5_2) apply simp_all apply(rule nprv_clear4_3) apply simp_all
  apply(rule nprv_impE01) apply auto 
  apply(rule nprv_clear4_3) apply simp_all apply(rule nprv_clear3_3) apply simp_all
  apply(rule nprv_eql_symE0[of t2 "Var z"]) apply auto 
  apply(rule nprv_eql_transE012) apply auto 
  done
qed

lemmas nprv_exuE_uni = nprv_addImp3LemmaE[OF prv_exu_uni,simped,rotated 4]
lemmas nprv_exuF_uni = nprv_exuE_uni[OF nprv_hyp,simped]


(**************************************)
(* Natural deduction with the bounded quantifiers *)

lemma nprv_ballI: 
"nprv (insert (LLq (Var x) t) F) \<phi> \<Longrightarrow> 
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow> 
 x \<notin> \<Union> (Fvars ` F) \<Longrightarrow> x \<notin> FvarsT t \<Longrightarrow> 
 nprv F (ball x t \<phi>)"
unfolding ball_def 
apply(rule nprv_allI) apply simp_all
apply(rule nprv_impI) apply simp_all
done

lemma nprv_ballE_aux: 
"nprv F (ball x t \<phi>) \<Longrightarrow> nprv F (LLq t1 t) \<Longrightarrow> 
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> t \<in> atrm \<Longrightarrow> t1 \<in> atrm \<Longrightarrow> x \<in> var \<Longrightarrow> x \<notin> FvarsT t \<Longrightarrow> 
 nprv F (subst \<phi> t1 x)"  
unfolding ball_def apply(rule nprv_allE[of _ x "imp (LLq (Var x) t) \<phi>" t1]) apply simp_all 
apply(rule nprv_impE0[of "LLq t1 t" "subst \<phi> t1 x"]) apply simp_all
  apply(rule nprv_mono[of F]) apply auto
  apply(rule nprv_hyp) apply simp_all
done

lemma nprv_ballE: 
"nprv F (ball x t \<phi>) \<Longrightarrow> nprv F (LLq t1 t) \<Longrightarrow> nprv (insert (subst \<phi> t1 x) F) \<psi> \<Longrightarrow> 
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> t \<in> atrm \<Longrightarrow> t1 \<in> atrm \<Longrightarrow> x \<in> var \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>  
 x \<notin> FvarsT t \<Longrightarrow> 
 nprv F \<psi>"  
by (meson atrm_trm local.subst nprv_ballE_aux nprv_cut rev_subsetD)

lemmas nprv_ballE0 = nprv_ballE[OF nprv_hyp _ _, simped]
lemmas nprv_ballE1 = nprv_ballE[OF _ nprv_hyp _, simped]
lemmas nprv_ballE2 = nprv_ballE[OF _ _ nprv_hyp, simped] 
lemmas nprv_ballE01 = nprv_ballE[OF nprv_hyp nprv_hyp _, simped]
lemmas nprv_ballE02 = nprv_ballE[OF nprv_hyp _ nprv_hyp, simped]
lemmas nprv_ballE12 = nprv_ballE[OF _ nprv_hyp nprv_hyp, simped]
lemmas nprv_ballE012 = nprv_ballE[OF nprv_hyp nprv_hyp nprv_hyp, simped]

lemma nprv_bexiI: 
"nprv F (subst \<phi> t1 x) \<Longrightarrow> nprv F (LLq t1 t) \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> t \<in> atrm \<Longrightarrow> t1 \<in> atrm \<Longrightarrow> x \<in> var \<Longrightarrow> 
 x \<notin> FvarsT t \<Longrightarrow> 
 nprv F (bexi x t \<phi>)"
unfolding bexi_def  
apply(rule nprv_exiI[of _ _ t1]) apply simp_all
apply(rule nprv_cnjI) apply simp_all 
done

lemma nprv_bexiE: 
"nprv F (bexi x t \<phi>) \<Longrightarrow> nprv (insert (LLq (Var x) t) (insert \<phi> F)) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> x \<in> var \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> t \<in> atrm \<Longrightarrow> 
 x \<notin> \<Union> (Fvars ` F) \<Longrightarrow> x \<notin> Fvars \<psi> \<Longrightarrow> x \<notin> FvarsT t \<Longrightarrow> 
 nprv F \<psi>" 
unfolding bexi_def 
apply(rule nprv_exiE[of _ x "cnj (LLq (Var x) t) \<phi>"]) apply simp_all 
apply(rule nprv_cnjH) apply simp_all
done  

lemmas nprv_bexiE0 = nprv_bexiE[OF nprv_hyp _, simped]
lemmas nprv_bexiE1 = nprv_bexiE[OF _ nprv_hyp, simped] 
lemmas nprv_bexiE01 = nprv_bexiE[OF nprv_hyp nprv_hyp, simped]

(**)

(* The substitution closures of the variable-based axioms 
(and the rulifications of the ones that are implications, negations or disjunctions).  *)

lemma prv_neg_zer_suc: 
assumes [simp]: "t \<in> atrm" shows "prv (neg (eql zer (suc t)))"
using prv_psubst[OF _ _ _ prv_neg_zer_suc_var, of "[(t,xx)]"]
by simp

lemma prv_neg_suc_zer: 
assumes "t \<in> atrm" shows "prv (neg (eql (suc t) zer))"
by (metis assms atrm.simps atrm_imp_trm eql fls neg_def prv_eql_sym 
  prv_neg_zer_suc prv_prv_imp_trans zer_atrm)


(* Rulification: *)    
lemmas nprv_zer_suc_contrE = 
 nprv_flsE[OF nprv_addImpLemmaE[OF prv_neg_zer_suc[unfolded neg_def]], OF _ _ nprv_hyp, simped, rotated]

lemmas nprv_zer_suc_contrE0 = nprv_zer_suc_contrE[OF nprv_hyp, simped]
 

(* A variation of the above, taking advantage of transitivity and symmetry: *)
lemma nprv_zer_suc_2contrE:
"nprv F (eql t zer) \<Longrightarrow> nprv F (eql t (suc t1)) \<Longrightarrow> 
 finite F \<Longrightarrow> F \<subseteq> fmla \<Longrightarrow> t \<in> atrm \<Longrightarrow> t1 \<in> atrm \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> 
 nprv F \<phi>" 
using nprv_eql_transI[OF nprv_eql_symI] nprv_zer_suc_contrE  
by (meson atrm_imp_trm suc zer_atrm)

lemmas nprv_zer_suc_2contrE0 = nprv_zer_suc_2contrE[OF nprv_hyp _, simped]
lemmas nprv_zer_suc_2contrE1 = nprv_zer_suc_2contrE[OF _ nprv_hyp, simped]
lemmas nprv_zer_suc_2contrE01 = nprv_zer_suc_2contrE[OF nprv_hyp nprv_hyp, simped]
(* *)
 
lemma prv_inj_suc: 
"t \<in> atrm \<Longrightarrow> t' \<in> atrm \<Longrightarrow> 
 prv (imp (eql (suc t) (suc t')) 
          (eql t t'))"
using prv_psubst[OF _ _ _ prv_inj_suc_var, of "[(t,xx),(t',yy)]"]
by simp

(* Rulification: *) 
lemmas nprv_eql_sucI = nprv_addImpLemmaI[OF prv_inj_suc, simped, rotated 4]
lemmas nprv_eql_sucE = nprv_addImpLemmaE[OF prv_inj_suc, simped, rotated 2]

lemmas nprv_eql_sucE0 = nprv_eql_sucE[OF nprv_hyp _, simped]
lemmas nprv_eql_sucE1 = nprv_eql_sucE[OF _ nprv_hyp, simped]
lemmas nprv_eql_sucE01 = nprv_eql_sucE[OF nprv_hyp nprv_hyp, simped]

(* NB: Provable substitution closures of sentences in the presence of quantifiers do not go 
very smoothly -- the main reason being that bound variable renaming is not assumed 
to hold up to equality, but it (only follows that it) holds up to provability: *)
lemma prv_zer_dsj_suc: 
assumes t[simp]: "t \<in> atrm" and x[simp]: "x \<in> var" "x \<notin> FvarsT t"
shows "prv (dsj (eql t zer)
           (exi x (eql t (suc (Var x)))))" 
proof-
  define x' where x': "x' \<equiv> getFr [x,yy] [t] []"
  have x'_facts[simp]: "x' \<in> var" "x' \<noteq> x"  "x' \<noteq> yy" "x' \<notin> FvarsT t" unfolding x' 
  using getFr_FvarsT_Fvars[of "[x,yy]" "[t]" "[]"] by auto

  have "prv (imp (exi xx (eql (Var yy) (suc (Var xx)))) (exi x' (eql (Var yy) (suc (Var x')))))" 
  by (auto intro!: prv_exi_imp prv_all_gen 
           simp: prv_exi_inst[of x' "eql (Var yy) (suc (Var x'))" "Var xx", simplified])      
  with prv_zer_dsj_suc_var 
  have 0: "prv (dsj (eql (Var yy) zer) (exi x' (eql (Var yy) (suc (Var x')))))"  
  by (smt Var atrm_imp_trm dsj eql exi prv_dsj_cases 
         prv_dsj_impL prv_dsj_impR prv_prv_imp_trans suc x'_facts(1) xx yy zer_atrm)

  note 1 = prv_psubst[OF _ _ _ 0, of "[(t,yy)]", simplified] 
  moreover have "prv (imp (exi x' (eql t (suc (Var x')))) (exi x (eql t (suc (Var x)))))" 
  by (auto intro!: prv_exi_imp prv_all_gen simp: prv_exi_inst[of x "eql t (suc (Var x))" "Var x'", simplified])     
  ultimately show ?thesis  
  by (smt Var atrm_imp_trm dsj eql exi in_num prv_dsj_mono prv_imp_mp prv_imp_refl suc t x'_facts(1) x(1) zer)
qed

(* The rulification of the above disjunction amounts to reasoning by zero-suc cases: *)
lemma nprv_zer_suc_casesE: 
"nprv (insert (eql t zer) F) \<phi> \<Longrightarrow> nprv (insert (eql t (suc (Var x))) F) \<phi> \<Longrightarrow> 
 finite F \<Longrightarrow> F \<subseteq> fmla \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> x \<in> var \<Longrightarrow> t \<in> atrm \<Longrightarrow> 
 x \<notin> Fvars \<phi> \<Longrightarrow> x \<notin> FvarsT t \<Longrightarrow> x \<notin> \<Union> (Fvars ` F) \<Longrightarrow> 
 nprv F \<phi>"
apply(rule nprv_addDsjLemmaE[OF prv_zer_dsj_suc]) apply auto 
apply(rule nprv_exiE0[of x "eql t (suc (Var x))"]) apply simp_all
apply(rule nprv_mono[of "insert (eql _ (suc _)) _"]) by auto

lemmas nprv_zer_suc_casesE0 = nprv_zer_suc_casesE[OF nprv_hyp _, simped]
lemmas nprv_zer_suc_casesE1 = nprv_zer_suc_casesE[OF _ nprv_hyp, simped]
lemmas nprv_zer_suc_casesE01 = nprv_zer_suc_casesE[OF nprv_hyp nprv_hyp, simped]
(* *)

lemma prv_pls_zer:
assumes [simp]: "t \<in> atrm" shows "prv (eql (pls t zer) t)"
using prv_psubst[OF _ _ _ prv_pls_zer_var, of "[(t,xx)]"]
by simp  

lemma prv_pls_suc:
"t \<in> atrm \<Longrightarrow> t' \<in> atrm \<Longrightarrow>  
 prv (eql (pls t (suc t')) 
          (suc (pls t t')))"
using prv_psubst[OF _ _ _ prv_pls_suc_var, of "[(t,xx),(t',yy)]"]
by simp 

lemma prv_tms_zer:
assumes [simp]: "t \<in> atrm" shows "prv (eql (tms t zer) zer)"
using prv_psubst[OF _ _ _ prv_tms_zer_var, of "[(t,xx)]"]
by simp 

lemma prv_tms_suc:
"t \<in> atrm \<Longrightarrow> t' \<in> atrm \<Longrightarrow> 
 prv (eql (tms t (suc t')) 
          (pls (tms t t') t))"
using prv_psubst[OF _ _ _ prv_tms_suc_var, of "[(t,xx),(t',yy)]"]
by simp 


(* Congruence rules for the operators (follow from substitutivity of equality): *)

lemma prv_suc_imp_cong:  
assumes t1[simp]: "t1 \<in> atrm" and t2[simp]: "t2 \<in> atrm"
shows "prv (imp (eql t1 t2)
                (eql (suc t1) (suc t2)))"
proof-
  define z where "z \<equiv> getFr [xx,yy,zz] [t1,t2] []"
  have z_facts[simp]: "z \<in> var" "z \<noteq> xx" "z \<noteq> yy" "z \<noteq> zz" "zz \<noteq> z" "z \<notin> FvarsT t1"  "z \<notin> FvarsT t2"  
  using getFr_FvarsT_Fvars[of "[xx,yy,zz]" "[t1,t2]" "[]"] unfolding z_def[symmetric] by auto 
  show ?thesis 
  apply(rule nprv_prvI) apply simp_all
  apply(rule nprv_impI) apply simp_all
  apply(rule nprv_eql_substE02[of t1 t2  _ "eql (suc (Var z)) (suc t2)" z]) apply simp_all
  apply(rule nprv_eq_eqlI) apply simp_all .
qed

(* Rulification: *)    
lemmas nprv_suc_congI = nprv_addImpLemmaI[OF prv_suc_imp_cong, simped, rotated 4]
lemmas nprv_suc_congE = nprv_addImpLemmaE[OF prv_suc_imp_cong, simped, rotated 2]

lemmas nprv_suc_congE0 = nprv_suc_congE[OF nprv_hyp _, simped]
lemmas nprv_suc_congE1 = nprv_suc_congE[OF _ nprv_hyp, simped]
lemmas nprv_suc_congE01 = nprv_suc_congE[OF nprv_hyp nprv_hyp, simped]

lemma prv_suc_cong:  
assumes t1[simp]: "t1 \<in> atrm" and t2[simp]: "t2 \<in> atrm"
assumes "prv (eql t1 t2)"
shows "prv (eql (suc t1) (suc t2))"  
by (meson assms atrm_suc atrm_imp_trm eql prv_imp_mp prv_suc_imp_cong t1 t2) 

lemma prv_pls_imp_cong:  
assumes t1[simp]: "t1 \<in> atrm" and t1'[simp]: "t1' \<in> atrm" 
and t2[simp]: "t2 \<in> atrm" and t2'[simp]: "t2' \<in> atrm"
shows "prv (imp (eql t1 t1')
                (imp (eql t2 t2') (eql (pls t1 t2) (pls t1' t2'))))"
proof-
  define z where "z \<equiv> getFr [xx,yy,zz] [t1,t1',t2,t2'] []"
  have z_facts[simp]: "z \<in> var" "z \<noteq> xx" "z \<noteq> yy" "z \<noteq> zz" "zz \<noteq> z" 
  "z \<notin> FvarsT t1" "z \<notin> FvarsT t1'" "z \<notin> FvarsT t2" "z \<notin> FvarsT t2'"       
  using getFr_FvarsT_Fvars[of "[xx,yy,zz]" "[t1,t1',t2,t2']" "[]"] unfolding z_def[symmetric] by auto
  show ?thesis 
  apply(rule nprv_prvI) apply simp_all
  apply(rule nprv_impI) apply simp_all
  apply(rule nprv_impI) apply simp_all
  apply(rule nprv_eql_substE02[of t1 t1'  _ "eql (pls (Var z) t2) (pls t1' t2')" z]) apply simp_all
  apply(rule nprv_eql_substE02[of t2 t2'  _ "eql (pls t1' (Var z)) (pls t1' t2')" z]) apply simp_all
  apply(rule nprv_eq_eqlI) apply simp_all .
qed

(* Rulification: *)    
lemmas nprv_pls_congI = nprv_addImp2LemmaI[OF prv_pls_imp_cong, simped, rotated 6]
lemmas nprv_pls_congE = nprv_addImp2LemmaE[OF prv_pls_imp_cong, simped, rotated 4]

lemmas nprv_pls_congE0 = nprv_pls_congE[OF nprv_hyp _ _, simped]
lemmas nprv_pls_congE1 = nprv_pls_congE[OF _ nprv_hyp _, simped]
lemmas nprv_pls_congE2 = nprv_pls_congE[OF _ _ nprv_hyp, simped] 
lemmas nprv_pls_congE01 = nprv_pls_congE[OF nprv_hyp nprv_hyp _, simped]
lemmas nprv_pls_congE02 = nprv_pls_congE[OF nprv_hyp _ nprv_hyp, simped]
lemmas nprv_pls_congE12 = nprv_pls_congE[OF _ nprv_hyp nprv_hyp, simped]
lemmas nprv_pls_congE012 = nprv_pls_congE[OF nprv_hyp nprv_hyp nprv_hyp, simped]

lemma prv_pls_cong:  
assumes "t1 \<in> atrm" "t1' \<in> atrm" "t2 \<in> atrm" "t2' \<in> atrm"
and "prv (eql t1 t1')" and "prv (eql t2 t2')"
shows "prv (eql (pls t1 t2) (pls t1' t2'))"
by (metis assms atrm_imp_trm cnj eql pls prv_cnjI prv_cnj_imp_monoR2 prv_imp_mp prv_pls_imp_cong)

lemma prv_pls_congL: 
"t1 \<in> atrm \<Longrightarrow> t1' \<in> atrm \<Longrightarrow> t2 \<in> atrm \<Longrightarrow> 
 prv (eql t1 t1') \<Longrightarrow> prv (eql (pls t1 t2) (pls t1' t2))"
by (rule prv_pls_cong[OF _ _ _ _ _ prv_eql_reflT]) auto

lemma prv_pls_congR: 
"t1 \<in> atrm \<Longrightarrow> t2 \<in> atrm \<Longrightarrow> t2' \<in> atrm \<Longrightarrow> 
 prv (eql t2 t2') \<Longrightarrow> prv (eql (pls t1 t2) (pls t1 t2'))"
by (rule prv_pls_cong[OF _ _ _ _ prv_eql_reflT]) auto

lemma nprv_pls_cong:  
assumes [simp]: "t1 \<in> atrm" "t1' \<in> atrm" "t2 \<in> atrm" "t2' \<in> atrm"
shows "nprv {eql t1 t1', eql t2 t2'} (eql (pls t1 t2) (pls t1' t2'))"
apply (simp add: nprv_def)  
by (smt assms atrm_imp_trm cnj empty_subsetI eql finite.emptyI finite.insertI insert_subset 
    pls prv_cnj_imp_monoR2 prv_pls_imp_cong prv_prv_imp_trans prv_scnj2_imp_cnj scnj) 

lemma prv_tms_imp_cong:  
assumes t1[simp]: "t1 \<in> atrm" and t1'[simp]: "t1' \<in> atrm" 
and t2[simp]: "t2 \<in> atrm" and t2'[simp]: "t2' \<in> atrm"
shows "prv (imp (eql t1 t1')
                (imp (eql t2 t2') (eql (tms t1 t2) (tms t1' t2'))))"
proof-
  define z where "z \<equiv> getFr [xx,yy,zz] [t1,t1',t2,t2'] []"
  have z_facts[simp]: "z \<in> var" "z \<noteq> xx" "z \<noteq> yy" "z \<noteq> zz" "zz \<noteq> z" 
  "z \<notin> FvarsT t1" "z \<notin> FvarsT t1'" "z \<notin> FvarsT t2" "z \<notin> FvarsT t2'"       
  using getFr_FvarsT_Fvars[of "[xx,yy,zz]" "[t1,t1',t2,t2']" "[]"] unfolding z_def[symmetric] by auto
  show ?thesis 
  apply(rule nprv_prvI) apply simp_all
  apply(rule nprv_impI) apply simp_all
  apply(rule nprv_impI) apply simp_all
  apply(rule nprv_eql_substE02[of t1 t1'  _ "eql (tms (Var z) t2) (tms t1' t2')" z]) apply simp_all
  apply(rule nprv_eql_substE02[of t2 t2'  _ "eql (tms t1' (Var z)) (tms t1' t2')" z]) apply simp_all
  apply(rule nprv_eq_eqlI) apply simp_all .
qed

(* Rulification: *)    
lemmas nprv_tms_congI = nprv_addImp2LemmaI[OF prv_tms_imp_cong, simped, rotated 6]
lemmas nprv_tms_congE = nprv_addImp2LemmaE[OF prv_tms_imp_cong, simped, rotated 4]

lemmas nprv_tms_congE0 = nprv_tms_congE[OF nprv_hyp _ _, simped]
lemmas nprv_tms_congE1 = nprv_tms_congE[OF _ nprv_hyp _, simped]
lemmas nprv_tms_congE2 = nprv_tms_congE[OF _ _ nprv_hyp, simped] 
lemmas nprv_tms_congE01 = nprv_tms_congE[OF nprv_hyp nprv_hyp _, simped]
lemmas nprv_tms_congE02 = nprv_tms_congE[OF nprv_hyp _ nprv_hyp, simped]
lemmas nprv_tms_congE12 = nprv_tms_congE[OF _ nprv_hyp nprv_hyp, simped]
lemmas nprv_tms_congE012 = nprv_tms_congE[OF nprv_hyp nprv_hyp nprv_hyp, simped]

lemma prv_tms_cong:  
assumes "t1 \<in> atrm" "t1' \<in> atrm" "t2 \<in> atrm" "t2' \<in> atrm"
and "prv (eql t1 t1')" and "prv (eql t2 t2')"
shows "prv (eql (tms t1 t2) (tms t1' t2'))"
by (metis assms atrm_imp_trm cnj eql tms prv_cnjI prv_cnj_imp_monoR2 prv_imp_mp prv_tms_imp_cong) 

lemma nprv_tms_cong:  
assumes [simp]: "t1 \<in> atrm" "t1' \<in> atrm" "t2 \<in> atrm" "t2' \<in> atrm"
shows "nprv {eql t1 t1', eql t2 t2'} (eql (tms t1 t2) (tms t1' t2'))"
apply (simp add: nprv_def)  
by (smt assms atrm_imp_trm cnj empty_subsetI eql finite.emptyI finite.insertI insert_subset 
    tms prv_cnj_imp_monoR2 prv_tms_imp_cong prv_prv_imp_trans prv_scnj2_imp_cnj scnj)

lemma prv_tms_congL: 
"t1 \<in> atrm \<Longrightarrow> t1' \<in> atrm \<Longrightarrow> t2 \<in> atrm \<Longrightarrow> 
 prv (eql t1 t1') \<Longrightarrow> prv (eql (tms t1 t2) (tms t1' t2))"
by (rule prv_tms_cong[OF _ _ _ _ _ prv_eql_reflT]) auto

lemma prv_tms_congR: 
"t1 \<in> atrm \<Longrightarrow> t2 \<in> atrm \<Longrightarrow> t2' \<in> atrm \<Longrightarrow> 
 prv (eql t2 t2') \<Longrightarrow> prv (eql (tms t1 t2) (tms t1 t2'))"
by (rule prv_tms_cong[OF _ _ _ _ prv_eql_reflT]) auto

(* *)




(****************************)
(* Properties provable in Q: *)

(* General properties, unconstrained by numerals: *)

lemma prv_pls_suc_zer:
"t \<in> atrm \<Longrightarrow> prv (eql (pls t (suc zer)) (suc t))"  
by (metis (no_types, hide_lams) atrm.atrm_pls atrm_imp_trm 
 in_num pls prv_eql_trans prv_pls_suc prv_pls_zer prv_suc_cong suc suc_num zer zer_atrm)

lemma prv_LLq_suc_imp: 
assumes [simp]: "t1 \<in> atrm" "t2 \<in> atrm"
shows "prv (imp (LLq (suc t1) (suc t2)) (LLq t1 t2))"
proof- 
  define z where "z \<equiv> getFr [xx,yy,zz] [t1,t2] []"
  have z_facts[simp]: "z \<in> var" "z \<noteq> xx" "z \<noteq> yy" "z \<noteq> zz" "zz \<noteq> z" "z \<notin> FvarsT t1"  "z \<notin> FvarsT t2"  
  using getFr_FvarsT_Fvars[of "[xx,yy,zz]" "[t1,t2]" "[]"] unfolding z_def[symmetric] by auto 
  show ?thesis 
  apply(rule nprv_prvI) apply simp_all
  apply(rule nprv_impI) apply simp_all
  apply(simp add: LLq_pls[of _ _ z])
  apply(rule nprv_exiE0) apply auto
  apply(rule nprv_addLemmaE[OF prv_pls_suc[of "Var z" t1]]) apply auto 
  apply(rule nprv_clear3_3) apply simp_all
  apply(rule nprv_eql_transE01[of "suc t2" "pls (Var z) (suc t1)" _ "suc (pls (Var z) t1)"]) apply auto 
  apply(rule nprv_eql_sucE0[of t2 "pls (Var z) t1"]) apply auto  
  apply(rule nprv_exiI[of _ _ "Var z" z]) apply auto
  apply(rule nprv_hyp) apply auto .
qed

(* Rulification: *)
lemmas nprv_LLq_sucI = nprv_addImpLemmaI[OF prv_LLq_suc_imp, simped, rotated 4]
lemmas nprv_LLq_sucE = nprv_addImpLemmaE[OF prv_LLq_suc_imp, simped, rotated 2]

lemmas nprv_LLq_sucE0 = nprv_LLq_sucE[OF nprv_hyp _, simped]
lemmas nprv_LLq_sucE1 = nprv_LLq_sucE[OF _ nprv_hyp, simped]
lemmas nprv_LLq_sucE01 = nprv_LLq_sucE[OF nprv_hyp nprv_hyp, simped]


lemma prv_LLs_imp_LLq: 
assumes [simp]: "t1 \<in> atrm" "t2 \<in> atrm"  
shows "prv (imp (LLs t1 t2) (LLq t1 t2))"
apply(simp add: LLs_LLq) by (simp add: prv_imp_cnjL) 

lemma prv_LLq_refl: 
"prv (LLq zer zer)"
by (auto simp: LLq_pls_zz prv_pls_zer prv_prv_eql_sym intro!: prv_exiI[of zz _ zer]) 

(* NB: Monotonicity of pls and tms w.r.t. LLq cannot be proved in Q *)
lemma prv_suc_mono_LLq: 
assumes "t1 \<in> atrm" "t2 \<in> atrm"
shows "prv (imp (LLq t1 t2) (LLq (suc t1) (suc t2)))" 
proof-
  have assms1: "t1 \<in> trm" "t2 \<in> trm" using assms by auto
  define z where "z \<equiv> getFr [xx,yy,zz] [t1,t2] []"
  have z_facts[simp]: "z \<in> var" "z \<noteq> xx" "z \<noteq> yy" "z \<noteq> zz" "zz \<noteq> z" "z \<notin> FvarsT t1" "z \<notin> FvarsT t2" 
  using getFr_FvarsT_Fvars[of "[xx,yy,zz]" "[t1,t2]" "[]"] using assms1 unfolding z_def[symmetric] by auto 
  define x where "x \<equiv> getFr [xx,yy,zz,z] [t1,t2] []"
  have x_facts[simp]: "x \<in> var" "x \<noteq> xx" "x \<noteq> yy" "x \<noteq> zz" "zz \<noteq> x" "x \<noteq> z" "z \<noteq> x" "x \<notin> FvarsT t1""x \<notin> FvarsT t2"
  using getFr_FvarsT_Fvars[of "[xx,yy,zz,z]" "[t1,t2]" "[]"] using assms1 unfolding x_def[symmetric] by auto 
  note assms[simp]
  show ?thesis
  apply(simp add: LLq_pls[of _ _ z])
  apply(rule nprv_prvI) apply simp_all
  apply(rule nprv_impI) apply simp_all 
  apply(rule nprv_exiE0[of z "eql t2 (pls (Var z) t1)"]) apply auto
  apply(rule nprv_clear2_2) apply simp_all
  apply(rule nprv_exiI[of _ _ "Var z"]) apply simp_all
  apply(rule nprv_addLemmaE[OF prv_pls_suc[of "Var z" t1]]) apply simp_all
  apply(rule nprv_eql_substE[of _  "pls (Var z) (suc t1)" "suc (pls (Var z) t1)"
    "eql (suc t2) (Var x)" x]) apply auto 
    apply(rule nprv_hyp) apply simp_all
    (**)
    apply(rule nprv_clear2_1) apply simp_all  
    apply(rule nprv_suc_congI) apply simp_all
    apply(rule nprv_hyp) apply simp_all
    (* *)
    apply(rule nprv_hyp) apply simp_all
  done
qed
 
(* Rulification: *)
lemmas nprv_suc_mono_LLqI = nprv_addImpLemmaI[OF prv_suc_mono_LLq, simped, rotated 4]
lemmas nprv_suc_mono_LLqE = nprv_addImpLemmaE[OF prv_suc_mono_LLq, simped, rotated 2]

lemmas nprv_suc_mono_LLqE0 = nprv_suc_mono_LLqE[OF nprv_hyp _, simped]
lemmas nprv_suc_mono_LLqE1 = nprv_suc_mono_LLqE[OF _ nprv_hyp, simped]
lemmas nprv_suc_mono_LLqE01 = nprv_suc_mono_LLqE[OF nprv_hyp nprv_hyp, simped]


(* Representability properties: *)
(* ... of  number inequality *)
lemma prv_neg_eql_suc_Num_zer: 
"prv (neg (eql (suc (Num n)) zer))"
apply(induct n)  
  apply (metis Num Num.simps(1) Num_atrm eql fls in_num neg_def prv_eql_sym prv_neg_zer_suc prv_prv_imp_trans suc)
  by (metis Num_atrm atrm_imp_trm eql fls neg_def prv_eql_sym prv_neg_zer_suc prv_prv_imp_trans suc zer_atrm)

lemma diff_prv_eql_Num: 
assumes "m \<noteq> n"
shows "prv (neg (eql (Num m) (Num n)))"
using assms proof(induct m arbitrary: n)
  case 0
  then obtain n' where n: "n = Suc n'" by (cases n) auto
  thus ?case unfolding n by (simp add: prv_neg_zer_suc) 
next
  case (Suc m n) note s = Suc 
  show ?case 
  proof(cases n)
    case 0 
    thus ?thesis by (simp add: prv_neg_eql_suc_Num_zer)
  next
    case (Suc n') note n = Suc 
    thus ?thesis using s apply auto 
    by (meson Num Num_atrm eql in_num neg prv_imp_mp prv_imp_neg_rev prv_inj_suc suc) 
  qed
qed

lemma consistent_prv_eql_Num_equal: 
assumes consistent and "prv (eql (Num m) (Num n))"
shows "m = n" 
using assms consistent_def3 diff_prv_eql_Num in_num by blast

(* ,.. of plus *)
lemma prv_pls_zer_zer: 
"prv (eql (pls zer zer) zer)"
  by (simp add: prv_pls_zer)

lemma prv_eql_pls_plus:
"prv (eql (pls (Num m) (Num n))
          (Num (m+n)))"
proof(induct n) 
  case (Suc n)   
  note 0 = prv_pls_suc[of "Num m" "Num n", simplified]
  show ?case apply simp
  apply(rule prv_eql_trans[OF _ _ _ 0 prv_suc_cong[OF _ _ Suc]]) by auto
qed(simp add: prv_pls_zer)

lemma not_plus_prv_neg_eql_pls:
assumes "m + n \<noteq> k" 
shows "prv (neg (eql (pls (Num m) (Num n)) (Num k)))"
using assms proof(induction n arbitrary: k)
  case 0 hence m: "m \<noteq> k" by simp
  show ?case 
  apply(rule nprv_prvI) apply simp_all
  apply(rule nprv_addLemmaE[OF prv_pls_zer, of "Num m"]) apply simp_all
  apply(rule nprv_eql_substE[of _ "pls (Num m) zer" "Num m" "neg (eql (Var xx) (Num k))" xx]) apply auto
    apply(rule nprv_hyp) apply simp_all
    (* *)
    apply(rule prv_nprvI) apply (simp_all)
    apply(rule diff_prv_eql_Num[OF m])
    (* *) 
    apply(rule nprv_hyp) apply simp_all
  done
next
  case (Suc n)
  show ?case 
  apply(rule nprv_prvI) apply simp_all
  apply(rule nprv_addLemmaE[OF prv_pls_suc, of "Num m" "Num n"]) apply simp_all
  apply(rule nprv_eql_substE[of _ "pls (Num m) (suc (Num n))" "suc (pls (Num m) (Num n))"  
     "neg (eql (Var xx) (Num k))" xx]) apply auto
    apply(rule nprv_hyp) apply simp_all
    (* *)
    apply(rule nprv_clear) apply simp_all
    apply(cases k)
      apply(rule prv_nprvI) apply simp_all
      apply(rule prv_neg_suc_zer) apply(simp_all)
    subgoal for k' using Suc.IH[of k'] Suc.prems apply simp
      apply(drule nprv_addLemmaE) apply simp_all 
      apply(rule nprv_negI) apply simp_all
      apply(rule nprv_negE0) apply auto
      apply(rule nprv_eql_sucI) apply simp_all
      apply(rule nprv_hyp) apply simp_all
    done
    (**)
    apply(rule nprv_hyp) apply simp_all
  done
qed 

lemma consistent_prv_eql_pls_plus_rev:
assumes "consistent" "prv (eql (pls (Num m) (Num n)) (Num k))"
shows "k = m + n"
by (metis Num assms consistent_def eql not_plus_prv_neg_eql_pls num pls prv_neg_fls subsetCE)


(* ... of times: *)
lemma prv_tms_Num_zer: 
"prv (eql (tms (Num n) zer) zer)"
by(auto simp: prv_tms_zer)

lemma prv_eql_tms_times: 
"prv (eql (tms (Num m) (Num n)) (Num (m * n)))"
proof(induct n)
  case (Suc n)
  note 0 = prv_pls_congL[OF _ _ _ Suc, of "Num m", simplified]
  thm prv_pls_cong[no_vars]
  show ?case
  apply(rule nprv_prvI) apply simp_all
  apply(rule nprv_addLemmaE[OF 0]) apply simp_all
  apply(rule nprv_addLemmaE[OF prv_tms_suc[of "Num m" "Num n", simplified]]) apply simp_all
  apply(rule nprv_eql_transE01[of
      "tms (Num m) (suc (Num n))" 
      "pls (tms (Num m) (Num n)) (Num m)" _ 
      "pls (Num (m * n)) (Num m)"]) apply simp_all
  apply(rule nprv_clear3_2) apply simp_all  apply(rule nprv_clear2_2) apply simp_all
  apply(rule nprv_addLemmaE[OF prv_eql_pls_plus[of "m * n" m]]) apply simp_all
  apply(rule nprv_eql_transE01[of
      "tms (Num m) (suc (Num n))"
      "pls (Num (m * n)) (Num m)" _
      "Num (m * n + m)"]) apply simp_all   
  apply(rule nprv_hyp) apply (auto simp: add.commute)
  done
qed(auto simp: prv_tms_zer)

lemma ge_prv_neg_eql_pls_Num_zer:
assumes [simp]: "t \<in> atrm" and m: "m > k"
shows "prv (neg (eql (pls t (Num m)) (Num k)))"
proof- 
  define z where "z \<equiv> getFr [xx,yy,zz] [t] []"
  have z_facts[simp]: "z \<in> var" "z \<noteq> xx" "z \<noteq> yy" "z \<noteq> zz" "zz \<noteq> z" "z \<notin> FvarsT t" 
  using getFr_FvarsT_Fvars[of "[xx,yy,zz]" "[t]" "[]"] using assms unfolding z_def[symmetric] by auto 
  show ?thesis using m proof(induction k arbitrary: m)
    case (0 m)
    show ?case
    apply(cases m) using 0 apply auto
    subgoal for n
    apply(rule nprv_prvI) apply simp_all
    apply(rule nprv_addLemmaE[OF prv_neg_suc_zer[of "pls t (Num n)"]]) apply auto 
    apply(rule nprv_negI) apply auto  
    apply(rule nprv_negE0) apply auto
    apply(rule nprv_clear2_2) apply simp_all
    apply(rule nprv_eql_symE0) apply auto
    apply(rule nprv_eql_substE[of _ zer "pls t (suc (Num n))" "eql (suc (pls t (Num n))) (Var z)" z]) apply auto
      apply(rule nprv_hyp) apply simp_all
      (**)
      apply(rule nprv_clear) apply simp_all
      apply(rule nprv_eql_symI) apply simp_all
      apply(rule prv_nprvI) apply simp_all 
      apply(rule prv_pls_suc) apply simp_all
      (**)
      apply(rule nprv_hyp) apply simp_all
    . .
  next
    case (Suc k mm)
    then obtain m where mm[simp]: "mm = Suc m" and k: "k < m" by (cases mm) auto
    show ?case apply simp
    apply(rule nprv_prvI) apply simp_all
    apply(rule nprv_addLemmaE[OF Suc.IH[OF k]]) apply auto 
    apply(rule nprv_negI) apply auto  
    apply(rule nprv_negE0) apply auto
    apply(rule nprv_clear2_2) apply simp_all 
    apply(rule nprv_impI_rev) apply simp_all
    apply(rule nprv_addLemmaE[OF prv_pls_suc[of t "Num m"]]) apply simp_all
    apply(rule nprv_eql_substE[of _ "pls t (suc (Num m))" "suc (pls t (Num m))" 
      "imp (eql (Var z) (suc (Num k))) (eql (pls t (Num m)) (Num k))" z]) apply auto
      apply(rule nprv_hyp) apply simp_all
      (**)
      apply(rule nprv_clear) apply simp_all
      apply(rule nprv_impI) apply simp_all
      apply(rule nprv_eql_sucI) apply simp_all
      apply(rule nprv_hyp) apply simp_all
      (**)
      apply(rule nprv_hyp) apply simp_all . 
   qed 
qed

lemma nprv_pls_Num_injectR:
assumes [simp]: "t1 \<in> atrm" "t2 \<in> atrm"
shows "prv (imp (eql (pls t1 (Num m)) (pls t2 (Num m)))
                (eql t1 t2))"
proof-
  define z where "z \<equiv> getFr [xx,yy] [t1,t2] []"
  have z_facts[simp]: "z \<in> var" "z \<noteq> xx" "z \<noteq> yy" "z \<notin> FvarsT t1" "z \<notin> FvarsT t2"
  using getFr_FvarsT_Fvars[of "[xx,yy]" "[t1,t2]" "[]"] unfolding z_def[symmetric] by auto
  show ?thesis proof(induction m)
    case 0
    show ?case apply simp
    apply(rule nprv_prvI) apply simp_all
    apply(rule nprv_addLemmaE[OF prv_pls_zer[of t1]]) apply simp_all
    apply(rule nprv_eql_substE[of _ "pls t1 zer" "t1" "imp (eql (Var z) (pls t2 zer)) (eql t1 t2)" z]) apply auto
      apply(rule nprv_hyp) apply simp_all
      (**)
      apply(rule nprv_clear) apply simp_all
      apply(rule nprv_addLemmaE[OF prv_pls_zer[of t2]]) apply simp_all
      apply(rule nprv_eql_substE[of _ "pls t2 zer" "t2" "imp (eql t1 (Var z)) (eql t1 t2)" z]) apply auto
        apply(rule nprv_hyp) apply simp_all
        (**)
        apply(rule nprv_impI) apply simp_all  
        apply(rule nprv_hyp) apply simp_all
        (**)
        apply(rule nprv_hyp) apply simp_all
      (**)
      apply(rule nprv_hyp) apply simp_all
    done  
  next
    case (Suc m)
    show ?case 
    apply(rule nprv_prvI) apply simp_all
    apply(rule nprv_addLemmaE[OF prv_pls_suc[of t1 "Num m"]]) apply simp_all
    apply(rule nprv_eql_substE[of _ "pls t1 (suc (Num m))" "suc (pls t1 (Num m))" 
     "imp (eql (Var z) (pls t2 (suc (Num m)))) (eql t1 t2)" z]) apply auto
      apply(rule nprv_hyp) apply simp_all
      (**)
      apply(rule nprv_clear) apply simp_all
      apply(rule nprv_addLemmaE[OF prv_pls_suc[of t2 "Num m"]]) apply simp_all
      apply(rule nprv_eql_substE[of _ "pls t2 (suc (Num m))" "suc (pls t2 (Num m))" 
       "imp (eql (suc (pls t1 (Num m))) (Var z)) (eql t1 t2)" z]) apply auto
        apply(rule nprv_hyp) apply simp_all
        (**)
        apply(rule nprv_clear) apply simp_all
        apply(rule nprv_impI) apply simp_all
        apply(rule nprv_eql_sucE0) apply auto
        apply(rule nprv_clear2_2) apply simp_all
        apply(rule prv_nprv1I) apply simp_all
        apply(rule Suc.IH)
        (**)
        apply(rule nprv_hyp) apply simp_all
     (**)
     apply(rule nprv_hyp) apply simp_all 
    done
  qed
qed

(* Rulification: *)
lemmas nprv_pls_Num_injectI = nprv_addImpLemmaI[OF nprv_pls_Num_injectR, simped, rotated 4]
lemmas nprv_pls_Num_injectE = nprv_addImpLemmaE[OF nprv_pls_Num_injectR, simped, rotated 2]

lemmas nprv_pls_Num_injectE0 = nprv_pls_Num_injectE[OF nprv_hyp _, simped]
lemmas nprv_pls_Num_injectE1 = nprv_pls_Num_injectE[OF _ nprv_hyp, simped]
lemmas nprv_pls_Num_injectE01 = nprv_pls_Num_injectE[OF nprv_hyp nprv_hyp, simped]


lemma not_times_prv_neg_eql_tms:
assumes "m * n \<noteq> k" 
shows "prv (neg (eql (tms (Num m) (Num n)) (Num k)))"
using assms proof(induction n arbitrary: k)
  case 0 hence m: "0 \<noteq> k" by simp have zer: "zer = Num 0" by simp
  show ?case 
  apply(rule nprv_prvI) apply simp_all
  apply(rule nprv_addLemmaE[OF prv_tms_zer, of "Num m"]) apply simp_all
  apply(rule nprv_eql_substE[of _ "tms (Num m) zer" zer "neg (eql (Var xx) (Num k))" xx]) apply auto
    apply(rule nprv_hyp) apply simp_all
    (* *)
    apply(rule prv_nprvI) apply (simp_all)
    apply(subst zer) apply(rule diff_prv_eql_Num[OF m])
    (* *) 
    apply(rule nprv_hyp) apply simp_all
  done
next
  case (Suc n)
  have 0: "nprv {} (neg (eql (pls (tms (Num m) (Num n)) (Num m)) (Num k)))"  
  proof(cases "k < m")
    case [simp]: True
    show ?thesis
    apply(rule prv_nprvI)  apply simp_all
    apply(rule ge_prv_neg_eql_pls_Num_zer) apply simp_all
    done
  next
    case False
    define k' where "k' \<equiv> k - m"
    with False have k: "k = k' + m" by auto
    hence mm: "m * n \<noteq> k'" using False Suc.prems by auto
    note IH = Suc.IH[OF mm]
    show ?thesis unfolding k
    apply(rule nprv_negI) apply auto 
    apply(rule nprv_addLemmaE[OF prv_prv_eql_sym[OF _ _ prv_eql_pls_plus[of k' m]]]) apply auto
    apply(rule nprv_eql_transE01[of _ "Num (k' + m)"]) apply auto
    apply(rule nprv_clear3_2) apply simp_all apply(rule nprv_clear2_2) apply simp_all
    apply(rule nprv_pls_Num_injectE0) apply auto
    apply(rule nprv_clear2_2) apply simp_all
    apply(rule nprv_addLemmaE[OF IH]) apply simp_all
    apply(rule nprv_negE0) apply auto
    apply(rule nprv_hyp) apply simp_all 
    done
  qed        
  show ?case 
  apply(rule nprv_prvI) apply simp_all
  apply(rule nprv_addLemmaE[OF prv_tms_suc, of "Num m" "Num n"]) apply simp_all
  apply(rule nprv_eql_substE[of _ "tms (Num m) (suc (Num n))" "pls (tms (Num m) (Num n)) (Num m)"
     "neg (eql (Var xx) (Num k))" xx]) apply auto
    apply(rule nprv_hyp) apply simp_all
    (* *)
    apply(rule nprv_clear) apply simp_all 
    apply(rule 0)
    (* *)
    apply(rule nprv_hyp) apply simp_all
  done
qed 

lemma consistent_prv_eql_tms_times_rev:
assumes "consistent" "prv (eql (tms (Num m) (Num n)) (Num k))"
shows "k = m * n"
by (metis Num assms consistent_def eql not_times_prv_neg_eql_tms num tms prv_neg_fls subsetCE)


(* .. of order:   *) 

lemma leq_prv_LLq_Num: 
assumes "m \<le> n"
shows "prv (LLq (Num m) (Num n))"
proof-  
  obtain i where n: "n = i + m" using assms add.commute le_Suc_ex by blast
  show ?thesis unfolding n apply(simp add: LLq_pls_zz)
  apply(rule prv_exiI[of _ _ "Num i"]) apply simp_all
  apply(rule prv_prv_eql_sym) apply simp_all
  using prv_eql_pls_plus . 
qed


(* .. The "order-adequacy" properties Q1--O9 from P.Smith, page 73  *) 

lemma prv_LLq_zer: (* O1 *)
assumes [simp]: "t \<in> atrm"
shows "prv (LLq zer t)"
proof-
  define z where "z \<equiv> getFr [xx,yy] [t] []"
  have z_facts[simp]: "z \<in> var" "z \<noteq> xx" "z \<noteq> yy" "z \<notin> FvarsT t"  
  using getFr_FvarsT_Fvars[of "[xx,yy]" "[t]" "[]"] unfolding z_def[symmetric] by auto 
  show ?thesis
  apply(simp add: LLq_pls[of _ _ z])
  apply(simp add: prv_nprv_emp)
  apply(rule nprv_exiI[of _ _ t]) apply simp_all
  apply(rule nprv_eql_symI) apply simp_all
  apply(rule prv_nprvI) apply simp_all
  apply(rule prv_pls_zer) apply simp_all .
qed 

lemmas Q1 = prv_LLq_zer

lemma prv_LLq_zer_imp_eql: 
assumes [simp]: "t \<in> atrm"
shows "prv (imp (LLq t zer) (eql t zer))"
proof-
  define y where "y \<equiv> getFr [] [t] []"
  have y_facts[simp]: "y \<in> var" "y \<notin> FvarsT t"  
  using getFr_FvarsT_Fvars[of "[]" "[t]" "[]"] unfolding y_def[symmetric] by auto 
  define z where "z \<equiv> getFr [y] [t] []"
  have z_facts[simp]: "z \<in> var" "z \<noteq> y" "z \<notin> FvarsT t"  
  using getFr_FvarsT_Fvars[of "[y]" "[t]" "[]"] unfolding z_def[symmetric] by auto 
  define x where "x \<equiv> getFr [y,z] [t] []"
  have x_facts[simp]: "x \<in> var" "x \<noteq> y" "x \<noteq> z" "x \<notin> FvarsT t"  
  using getFr_FvarsT_Fvars[of "[y,z]" "[t]" "[]"] unfolding x_def by auto 
  show ?thesis 
  apply(rule nprv_prvI) apply(simp_all)
  apply(rule nprv_impI) apply simp_all  
  apply(rule nprv_zer_suc_casesE[of t _ _ y]) apply simp_all
    apply(rule nprv_hyp) apply simp_all
    (* *)  
    apply(simp add: LLq_pls[of _ _ z])  
    apply(rule nprv_exiE0[of z "eql zer (pls (Var z) t)"]) apply simp_all 
    apply(rule nprv_clear3_3) apply simp_all
    apply(rule nprv_eql_symE0[of t]) apply auto 
    apply(rule nprv_eql_substE01[of "suc (Var y)" t _ "eql zer (pls (Var z) (Var x))" x]) apply simp_all
    apply(rule nprv_addLemmaE[OF prv_pls_suc[of "Var z" "Var y",simplified]]) apply simp_all
    apply(rule nprv_eql_transE01[of zer "pls (Var z) (suc (Var y))" _ "suc (pls (Var z) (Var y))"]) apply simp_all 
    apply(rule nprv_zer_suc_contrE0[of "pls (Var z) (Var y)"]) apply simp_all
  done
qed

(* Rulification: *)
lemmas nprv_LLq_zer_eqlI = nprv_addImpLemmaI[OF prv_LLq_zer_imp_eql, simped, rotated 3]
lemmas nprv_LLq_zer_eqlE = nprv_addImpLemmaE[OF prv_LLq_zer_imp_eql, simped, rotated 1]

lemmas nprv_LLq_zer_eqlE0 = nprv_LLq_zer_eqlE[OF nprv_hyp _, simped]
lemmas nprv_LLq_zer_eqlE1 = nprv_LLq_zer_eqlE[OF _ nprv_hyp, simped]
lemmas nprv_LLq_zer_eqlE01 = nprv_LLq_zer_eqlE[OF nprv_hyp nprv_hyp, simped] 


lemma prv_sdsj_eql_imp_LLq: (* O2 *)
assumes [simp]: "t \<in> atrm"
shows "prv (imp (ldsj (map (\<lambda>i. eql t (Num i)) (toN n))) (LLq t (Num n)))"
proof-
  define z where "z \<equiv> getFr [xx,yy] [t] []"
  have z_facts[simp]: "z \<in> var" "z \<noteq> xx" "z \<noteq> yy" "z \<notin> FvarsT t"  
  using getFr_FvarsT_Fvars[of "[xx,yy]" "[t]" "[]"] unfolding z_def[symmetric] by auto 
  note imp[intro!]  note dsj[intro!]
  show ?thesis
  apply(rule nprv_prvI) apply auto
  apply(rule nprv_impI) apply auto   
  apply(rule nprv_ldsjE0) apply auto
  subgoal for i  
  apply(rule nprv_eql_substE[of _ t "Num i" "LLq (Var z) (Num n)" z]) apply auto 
    apply(rule nprv_hyp) apply auto
    (* *)
    apply(rule prv_nprvI) apply auto  
    apply(rule leq_prv_LLq_Num) apply simp 
    (**)
    apply(rule nprv_hyp) apply auto . .
qed 

(* Rulification: *)
declare subset_eq[simp]
lemmas nprv_sdsj_eql_LLqI = nprv_addImpLemmaI[OF prv_sdsj_eql_imp_LLq, simped, rotated 3]
lemmas nprv_sdsj_eql_LLqE = nprv_addImpLemmaE[OF prv_sdsj_eql_imp_LLq, simped, rotated 1] 
declare subset_eq[simp del]

lemmas nprv_sdsj_eql_LLqE0 = nprv_sdsj_eql_LLqE[OF nprv_hyp _, simped]
lemmas nprv_sdsj_eql_LLqE1 = nprv_sdsj_eql_LLqE[OF _ nprv_hyp, simped]
lemmas nprv_sdsj_eql_LLqE01 = nprv_sdsj_eql_LLqE[OF nprv_hyp nprv_hyp, simped]

lemmas O2I = nprv_sdsj_eql_LLqI
lemmas O2E = nprv_sdsj_eql_LLqE
lemmas O2E0 = nprv_sdsj_eql_LLqE0
lemmas O2E1 = nprv_sdsj_eql_LLqE1
lemmas O2E01 = nprv_sdsj_eql_LLqE01
(* *)

lemma prv_LLq_imp_sdsj_eql: (* O3 *)
assumes [simp]: "t \<in> atrm"
shows "prv (imp (LLq t (Num n)) (ldsj (map (\<lambda>i. eql t (Num i)) (toN n))))"
using assms proof(induction n arbitrary: t)
  case (0 t) note 0[simp]
  show ?case  
  apply(rule nprv_prvI) apply simp_all
  apply(rule nprv_impI) apply simp_all
  apply(rule nprv_ldsjI) apply simp_all  
  apply(rule prv_nprv1I) apply simp_all 
  apply(rule prv_LLq_zer_imp_eql) by simp
next
  case (Suc n) note  t[simp] = `t \<in> atrm`
  define z where "z \<equiv> getFr [xx,yy,zz] [t] []"
  have z_facts[simp]: "z \<in> var" "z \<noteq> xx" "z \<noteq> yy" "z \<noteq> zz" "zz \<noteq> z" "z \<notin> FvarsT t"  
  using getFr_FvarsT_Fvars[of "[xx,yy,zz]" "[t]" "[]"] unfolding z_def[symmetric] by auto 
  note subset_eq[simp]  
  show ?case
  apply(rule nprv_prvI) apply auto  
  apply(rule nprv_zer_suc_casesE[of t _ _ z]) apply auto
    apply(rule nprv_impI) apply auto
    apply(rule nprv_ldsjI) apply auto
    apply(rule nprv_hyp) apply auto   
    (**)  
    apply(rule nprv_eql_substE[of _ t "suc (Var z)"  
         "imp (LLq (Var xx) (suc (Num n))) (ldsj (map (\<lambda>i. eql (Var xx) (Num i)) (toN (Suc n))))" xx]) apply auto 
    apply(rule nprv_hyp) apply auto
    
    (* *)
    apply(rule nprv_clear) apply auto
    apply(rule nprv_impI) apply auto 
    apply(rule nprv_LLq_sucE0) apply auto 
    apply(rule nprv_addImpLemmaE[OF Suc.IH[of "Var z", simplified]]) apply auto
      apply(rule nprv_hyp) apply auto
      (**)
      apply(rule nprv_ldsjE0) apply auto  
      subgoal for i  apply(rule nprv_ldsjI[of _ "eql (suc (Var z)) (suc (Num i))"])  apply auto
        apply(rule nprv_suc_congI) apply auto
        apply(rule nprv_hyp) apply auto
        apply(auto simp: image_def intro!: bexI[of _ "Suc i"]) . 
    (* *)
    apply(rule nprv_hyp) apply auto .
qed

(* Rulification: *)
declare subset_eq[simp]
lemmas prv_LLq_sdsj_eqlI = nprv_addImpLemmaI[OF prv_LLq_imp_sdsj_eql, simped, rotated 3]
lemmas prv_LLq_sdsj_eqlE = nprv_addImpLemmaE[OF prv_LLq_imp_sdsj_eql, simped, rotated 1] 
declare subset_eq[simp del]

lemmas prv_LLq_sdsj_eqlE0 = prv_LLq_sdsj_eqlE[OF nprv_hyp _, simped]
lemmas prv_LLq_sdsj_eqlE1 = prv_LLq_sdsj_eqlE[OF _ nprv_hyp, simped]
lemmas prv_LLq_sdsj_eqlE01 = prv_LLq_sdsj_eqlE[OF nprv_hyp nprv_hyp, simped]

lemmas O3I = prv_LLq_sdsj_eqlI
lemmas O3E = prv_LLq_sdsj_eqlE
lemmas O3E0 = prv_LLq_sdsj_eqlE0
lemmas O3E1 = prv_LLq_sdsj_eqlE1
lemmas O3E01 = prv_LLq_sdsj_eqlE01

(*  *)
lemma not_leq_prv_neg_LLq_Num: 
assumes "\<not> m \<le> n"  (* This is just m < n, of course. *)
shows "prv (neg (LLq (Num m) (Num n)))"
apply(rule nprv_prvI) apply simp_all
apply(rule nprv_negI) apply simp_all
apply(rule O3E0) apply auto 
apply(rule nprv_ldsjE0) apply auto
subgoal for i 
apply(rule nprv_clear3_2) apply auto
apply(rule nprv_clear2_2) apply auto
apply(rule prv_nprv1I) apply simp_all
unfolding neg_def[symmetric] 
apply(rule diff_prv_eql_Num) 
using assms apply simp
. .
 
lemma consistent_prv_LLq_Num_leq: 
assumes consistent  "prv (LLq (Num m) (Num n))" 
shows "m \<le> n"
by (metis Num assms consistent_def LLq not_leq_prv_neg_LLq_Num num prv_neg_fls subsetCE)
(* *)

lemma prv_ball_NumI: (* O4 *)
assumes [simp]: "x \<in> var" "\<phi> \<in> fmla"
and 1: "\<And> i. i \<le> n \<Longrightarrow> prv (subst \<phi> (Num i) x)"
shows "prv (ball x (Num n) \<phi>)"
apply(rule nprv_prvI) apply simp_all
apply(rule nprv_ballI) apply simp_all 
apply(rule O3E0) apply auto  
apply(rule nprv_clear2_2) apply auto
apply(rule nprv_ldsjE0) apply auto
apply(rule nprv_clear2_2) apply auto
subgoal for i   
apply(rule nprv_eql_substE[of _ "Var x" "Num i" \<phi> x]) apply auto
  apply(rule nprv_hyp, auto)
  (**)
  apply(rule prv_nprvI) apply(simp_all add: 1)
  (**)
  apply(rule nprv_hyp) apply simp_all
. .

lemmas O4 = prv_ball_NumI

lemma prv_bexi_NumI: (* O5 *)
assumes [simp]: "x \<in> var" "\<phi> \<in> fmla"
and i: "i \<le> n" and 1: "prv (subst \<phi> (Num i) x)"
shows "prv (bexi x (Num n) \<phi>)"
apply(rule nprv_prvI) apply simp_all
apply(rule nprv_bexiI[of _ _ "Num i"]) apply simp_all 
  apply(rule prv_nprvI) apply (simp_all add: 1)
  apply(rule prv_nprvI) apply (simp_all add: i leq_prv_LLq_Num)
done

lemmas O5 = prv_bexi_NumI

lemma prv_LLq_Num_imp_Suc: (* O6 *)
assumes [simp]: "t \<in> atrm"
shows "prv (imp (LLq t (Num n)) (LLq t (suc (Num n))))"
apply(rule nprv_prvI) apply simp_all
apply(rule nprv_impI) apply simp_all 
apply(rule O3E0) apply auto 
apply(rule nprv_clear2_2) apply auto
apply(rule nprv_ldsjE0) apply auto
apply(rule nprv_clear2_2) apply auto
subgoal for i    
apply(rule nprv_eql_substE[of _ t "Num i" "LLq (Var xx) (suc (Num n))" xx]) apply auto
  apply(rule nprv_hyp) apply simp_all
  (**)
  apply(rule prv_nprvI) apply simp_all  
  apply(subst Num.simps(2)[symmetric])
  apply(rule leq_prv_LLq_Num) apply simp
  (* *)
  apply(rule nprv_hyp) apply simp_all
. .

(* Rulification: *)
lemmas nprv_LLq_Num_SucI = nprv_addImpLemmaI[OF prv_LLq_Num_imp_Suc, simped, rotated 3]
lemmas nprv_LLq_Num_SucE = nprv_addImpLemmaE[OF prv_LLq_Num_imp_Suc, simped, rotated 1]

lemmas nprv_LLq_Num_SucE0 = nprv_LLq_Num_SucE[OF nprv_hyp _, simped]
lemmas nprv_LLq_Num_SucE1 = nprv_LLq_Num_SucE[OF _ nprv_hyp, simped]
lemmas nprv_LLq_Num_SucE01 = nprv_LLq_Num_SucE[OF nprv_hyp nprv_hyp, simped]

lemmas O6I = nprv_LLq_Num_SucI
lemmas O6E = nprv_LLq_Num_SucE
lemmas O6E0 = nprv_LLq_Num_SucE0
lemmas O6E1 = nprv_LLq_Num_SucE1
lemmas O6E01 = nprv_LLq_Num_SucE01

 
(* Crucial for proving O7: *)
lemma prv_LLq_suc_Num_pls_Num: 
assumes [simp]: "t \<in> atrm"
shows "prv (LLq (suc (Num n)) (pls (suc t) (Num n)))"
proof-
  define z where "z \<equiv> getFr [xx,yy,zz] [t] []"
  have z_facts[simp]: "z \<in> var" "z \<noteq> xx" "z \<noteq> yy" "z \<noteq> zz" "zz \<noteq> z" "z \<notin> FvarsT t"  
  using getFr_FvarsT_Fvars[of "[xx,yy,zz]" "[t]" "[]"] unfolding z_def[symmetric] by auto 
  show ?thesis 
  proof(induction n)
    case 0
    then show ?case apply(simp add: LLq_pls[of _ _ z])
    apply(rule nprv_prvI) apply simp_all
    apply(rule nprv_exiI[of _ _ t]) apply simp_all
    apply(rule nprv_addLemmaE[OF prv_pls_zer[of "suc t"]]) apply simp_all
    apply(rule nprv_eql_substE[of _ "pls (suc t) zer"  "suc t"  "eql (Var z) (pls t (suc zer))" z]) apply auto
      apply(rule nprv_hyp) apply simp_all
      (**)
      apply(rule nprv_clear)
      apply(rule nprv_eql_symI) apply simp_all 
      apply(rule prv_nprvI) apply simp_all
      apply(rule prv_pls_suc_zer) apply simp_all
      apply(rule nprv_hyp) apply simp_all
    done
  next
    case (Suc n)
    have nn: "suc (Num n) = suc (Num n)" by simp
    show ?case  
    apply(rule nprv_prvI) apply simp_all
    apply(rule nprv_addLemmaE[OF prv_pls_suc[of "suc t" "Num n"]]) apply simp_all
    apply(rule nprv_eql_substE[of _ "pls (suc t) (suc (Num n))" "suc (pls (suc t) (Num n))" 
      "LLq (suc (suc (Num n))) (Var z)" z]) apply auto
      apply(rule nprv_hyp) apply simp_all
      (* *)
      apply(rule nprv_clear) apply simp_all
      apply(rule nprv_suc_mono_LLqI) apply simp_all
      apply(rule prv_nprvI) apply (simp_all add: Suc.IH)
      (* *)
      apply(rule nprv_hyp) apply simp_all
     done
  qed
qed 

lemma prv_Num_LLq_imp_eql_suc: (* O7 *)
assumes [simp]: "t \<in> atrm"
shows "prv (imp (LLq (Num n) t) 
                (dsj (eql (Num n) t) 
                     (LLq (suc (Num n)) t)))"
proof-
  define z where "z \<equiv> getFr [xx,yy,zz] [t] []"
  have z_facts[simp]: "z \<in> var" "z \<noteq> xx" "z \<noteq> yy" "z \<noteq> zz" "zz \<noteq> z" "z \<notin> FvarsT t"  
  using getFr_FvarsT_Fvars[of "[xx,yy,zz]" "[t]" "[]"] unfolding z_def[symmetric] by auto 
  define x where "x \<equiv> getFr [xx,yy,zz,z] [t] []"
  have x_facts[simp]: "x \<in> var" "x \<noteq> xx" "x \<noteq> yy" "x \<noteq> zz" "zz \<noteq> x" "x \<noteq> z" "z \<noteq> x" "x \<notin> FvarsT t"  
  using getFr_FvarsT_Fvars[of "[xx,yy,zz,z]" "[t]" "[]"] unfolding x_def[symmetric] by auto 
  define y where "y \<equiv> getFr [x,z] [t] []" 
  have y_facts[simp]: "y \<in> var" "y \<notin> FvarsT t" "x \<noteq> y" "y \<noteq> x" "z \<noteq> y" "y \<noteq> z"
  using getFr_FvarsT_Fvars[of "[x,z]" "[t]" "[]"] unfolding y_def[symmetric] by auto 
  show ?thesis
  apply(rule nprv_prvI) apply simp_all
  apply(rule nprv_impI) apply simp_all  
  apply(subst LLq_pls[of _ _ z]) apply simp_all
  apply(rule nprv_exiE0) apply auto
  apply(rule nprv_clear2_2) apply simp_all
  apply(rule nprv_zer_suc_casesE[of "Var z" _ _ x]) apply auto
  subgoal
    apply(rule nprv_dsjIL)   
    apply(rule nprv_impI_rev2[of "{eql (Var z) zer}" "eql t (pls (Var z) (Num n))"]) apply auto
    apply(rule nprv_eql_substE
    [of _ "Var z" zer "imp (eql t (pls (Var y) (Num n))) (eql (Num n) t)" y]) apply auto
      apply(rule nprv_hyp) apply simp_all
      (**)
      apply(rule nprv_clear) apply simp_all
      apply(rule nprv_impI) apply simp_all
      subgoal 
        apply(rule nprv_eql_substE[of _ t "pls zer (Num n)" "eql (Num n) (Var y)" y]) apply auto
          apply(rule nprv_hyp) apply simp_all
          (**)
          apply(rule nprv_clear) apply simp_all
          apply(rule prv_nprvI) apply simp_all  
          apply(rule prv_prv_eql_sym) apply simp_all
          apply(subst Num.simps(1)[symmetric])  
          apply (metis plus_nat.add_0 prv_eql_pls_plus) 
          apply(rule nprv_hyp) apply simp_all
      done
      apply(rule nprv_hyp) apply simp_all
    done
    subgoal
    apply(rule nprv_dsjIR) apply simp_all 
    apply(rule nprv_impI_rev2[of "{eql (Var z) (suc (Var x))}" "eql t (pls (Var z) (Num n))"]) apply auto
    apply(rule nprv_eql_substE
    [of _  "Var z" "suc (Var x)" "imp (eql t (pls (Var y) (Num n)))  (LLq (suc (Num n)) t)" y]) 
    apply auto 
    apply(rule nprv_hyp) apply simp_all
    (* *)
    apply(rule nprv_clear) apply simp_all
    apply(rule nprv_impI) apply simp_all
    apply(rule nprv_eql_substE
    [of _  t "pls (suc (Var x)) (Num n)" "LLq (suc (Num n)) (Var y)" y]) 
    apply auto 
      apply(rule nprv_hyp) apply simp_all
      (**)
      apply(rule prv_nprvI) apply (simp_all add: prv_LLq_suc_Num_pls_Num)
      (**) 
      apply(rule nprv_hyp) apply simp_all
    (* *)
    apply(rule nprv_hyp) apply simp_all
    done
  done
qed

(* Rulification (this one is slightly more complex, as it puts together impE with dsjE): *)
lemma prv_Num_LLq_eql_sucE: 
"nprv F (LLq (Num n) t) \<Longrightarrow>
 nprv (insert (eql (Num n) t) F) \<psi> \<Longrightarrow> 
 nprv (insert (LLq (suc (Num n)) t) F) \<psi> \<Longrightarrow>
 t \<in> atrm \<Longrightarrow> F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow>  \<psi> \<in> fmla \<Longrightarrow> 
 nprv F \<psi>"
apply(rule nprv_addImpLemmaE[OF prv_Num_LLq_imp_eql_suc]) apply auto
apply(rule nprv_dsjE0[of "eql (Num n) t" "LLq (suc (Num n)) t"])  
apply auto
  apply(rule nprv_mono[of "insert (eql (Num n) t) F"]) apply auto
  apply(rule nprv_mono[of "insert (LLq (suc (Num n)) t) F"]) apply auto
done

lemmas prv_Num_LLq_eql_sucE0 = prv_Num_LLq_eql_sucE[OF nprv_hyp _ _, simped]
lemmas prv_Num_LLq_eql_sucE1 = prv_Num_LLq_eql_sucE[OF _ nprv_hyp _, simped]
lemmas prv_Num_LLq_eql_sucE2 = prv_Num_LLq_eql_sucE[OF _ _ nprv_hyp, simped] 
lemmas prv_Num_LLq_eql_sucE01 = prv_Num_LLq_eql_sucE[OF nprv_hyp nprv_hyp _, simped]
lemmas prv_Num_LLq_eql_sucE02 = prv_Num_LLq_eql_sucE[OF nprv_hyp _ nprv_hyp, simped]
lemmas prv_Num_LLq_eql_sucE12 = prv_Num_LLq_eql_sucE[OF _ nprv_hyp nprv_hyp, simped]
lemmas prv_Num_LLq_eql_sucE012 = prv_Num_LLq_eql_sucE[OF nprv_hyp nprv_hyp nprv_hyp, simped]
(* *)

lemmas O7E = prv_Num_LLq_eql_sucE
lemmas O7E0 = prv_Num_LLq_eql_sucE0
(**)

(* Although we work in intuitionistic logic, 
Q decides equality of arbitrary entities with numerals: *)
lemma prv_dsj_eql_Num_neg: 
assumes "t \<in> atrm"   
shows "prv (dsj (eql t (Num n)) (neg (eql t (Num n))))"
using assms proof(induction n arbitrary: t)
  case [simp]:(0 t)  
  define z where "z \<equiv> getFr [xx,yy,zz] [t] []"
  have z_facts[simp]: "z \<in> var" "z \<noteq> xx" "z \<noteq> yy" "z \<noteq> zz" "zz \<noteq> z" "z \<notin> FvarsT t"  
  using getFr_FvarsT_Fvars[of "[xx,yy,zz]" "[t]" "[]"] unfolding z_def[symmetric] by auto 
  show ?case apply simp
  apply(rule nprv_prvI) apply simp_all
  apply(rule nprv_zer_suc_casesE[of t _ _ z]) apply simp_all
    apply(rule nprv_dsjIL) apply simp_all
    apply(rule nprv_hyp) apply simp_all
    (**)
    apply(rule nprv_dsjIR) apply simp_all
    apply(rule nprv_negI) apply simp_all 
    apply(rule nprv_zer_suc_2contrE01) apply auto
  done   
next
  case (Suc n) note  `t \<in> atrm`[simp]
  define z where "z \<equiv> getFr [xx,yy,zz] [t] []"
  have z_facts[simp]: "z \<in> var" "z \<noteq> xx" "z \<noteq> yy" "z \<noteq> zz" "zz \<noteq> z" "z \<notin> FvarsT t"  
  using getFr_FvarsT_Fvars[of "[xx,yy,zz]" "[t]" "[]"] unfolding z_def[symmetric] by auto 
  show ?case 
  apply(rule nprv_prvI) apply simp_all
  apply(rule nprv_zer_suc_casesE[of t _ _ z]) apply simp_all
    apply(rule nprv_dsjIR) apply simp_all
    apply(rule nprv_negI) apply simp_all
    apply(rule nprv_zer_suc_2contrE01) apply auto
    (**) 
    apply(rule nprv_eql_substE [of _ t "suc (Var z)"
       "dsj (eql (Var z) (suc (Num n))) (neg (eql (Var z) (suc (Num n))))" z]) apply auto
      apply(rule nprv_hyp) apply simp_all
      (**)
      apply(rule nprv_clear) apply simp_all
      apply(rule nprv_addLemmaE[OF Suc.IH[of "Var z"]]) apply simp_all
      apply(rule nprv_dsjE0) apply auto
        apply(rule nprv_dsjIL) apply simp_all
        apply(rule nprv_suc_congI) apply simp_all
        apply(rule nprv_hyp) apply simp_all
        (**)
        apply(rule nprv_dsjIR) apply simp_all   
        apply(rule nprv_negI) apply simp_all
        apply(rule nprv_negE0) apply auto
        apply(rule nprv_eql_sucI) apply simp_all
        apply(rule nprv_hyp) apply simp_all
    (**)
    apply(rule nprv_hyp) apply simp_all 
  done 
qed 

(* Rulification: *) 
lemmas nprv_eql_Num_casesE = nprv_addDsjLemmaE[OF prv_dsj_eql_Num_neg, simped, rotated]

lemmas nprv_eql_Num_casesE0 = nprv_eql_Num_casesE[OF nprv_hyp _, simped]
lemmas nprv_eql_Num_casesE1 = nprv_eql_Num_casesE[OF _ nprv_hyp, simped]
lemmas nprv_eql_Num_casesE01 = nprv_eql_Num_casesE[OF nprv_hyp nprv_hyp, simped] 
(* *)

lemma prv_LLq_Num_dsj: (* O8 *)
assumes [simp]: "t \<in> atrm"
shows "prv (dsj (LLq t (Num n)) (LLq (Num n) t))"
proof(induction n)
  case 0
  show ?case
  apply(rule nprv_prvI) apply simp_all 
  apply(rule nprv_dsjIR) apply simp_all
  apply(rule prv_nprvI) apply (simp_all add: prv_LLq_zer)
  done
next
  case (Suc n)
  have nn: "suc (Num n) = Num (Suc n)" by simp
  show ?case
  apply(rule nprv_prvI) apply simp_all 
  apply(rule nprv_addLemmaE[OF Suc.IH]) apply simp_all
  apply(rule nprv_dsjE0) apply auto
    apply(rule nprv_dsjIL) apply simp_all 
    apply(rule O6I) apply simp_all
    apply(rule nprv_hyp) apply simp_all
    (* *)
    apply(rule nprv_clear2_2) apply simp_all
    apply(rule nprv_eql_Num_casesE[of t n]) apply simp_all
      apply(rule nprv_dsjIL) apply simp_all 
      apply(rule nprv_eql_substE[of _ t "Num n" "LLq (Var xx) (suc (Num n))" xx]) apply auto 
        apply(rule nprv_hyp) apply simp_all
        (**)
        apply(rule prv_nprvI) apply simp_all
        apply(subst nn) apply(rule leq_prv_LLq_Num) apply simp
        (**)
        apply(rule nprv_hyp) apply simp_all
      (**)
      apply(rule O7E0[of n t]) apply auto 
        apply(rule nprv_eql_symE0) apply auto 
        apply(rule nprv_negE01) apply auto
        (* *)
        apply(rule nprv_dsjIR) apply simp_all
        apply(rule nprv_hyp) apply simp_all
  done
qed 

(* Rulification: *)
lemma prv_LLq_Num_casesE: 
"nprv (insert (LLq t (Num n)) F) \<psi> \<Longrightarrow>
 nprv (insert (LLq (Num n) t) F) \<psi> \<Longrightarrow>
 t \<in> atrm \<Longrightarrow> F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> 
 nprv F \<psi>"
by (rule nprv_addDsjLemmaE[OF prv_LLq_Num_dsj]) auto

lemmas prv_LLq_Num_casesE0 = prv_LLq_Num_casesE[OF nprv_hyp _, simped]
lemmas prv_LLq_Num_casesE1 = prv_LLq_Num_casesE[OF _ nprv_hyp, simped]
lemmas prv_LLq_Num_casesE01 = prv_LLq_Num_casesE[OF nprv_hyp nprv_hyp, simped] 

lemmas O8E = prv_LLq_Num_casesE 
lemmas O8E0 = prv_LLq_Num_casesE0
lemmas O8E1 = prv_LLq_Num_casesE1
lemmas O8E01 = prv_LLq_Num_casesE01
(* *)

lemma prv_imp_LLq_neg_Num_suc: 
assumes [simp]: "t \<in> atrm" 
shows "prv (imp (LLq t (suc (Num n))) 
                 (imp ((neg (eql t (suc (Num n))))) 
                      (LLq t (Num n))))"
apply(rule nprv_prvI) apply simp_all
apply(rule nprv_impI) apply simp_all
apply(rule nprv_impI) apply simp_all 
apply(rule O3E0[of t "Suc n"]) apply auto 
apply(rule nprv_clear3_3) apply auto
apply(rule nprv_ldsjE0) apply auto
subgoal for i
apply(rule nprv_clear3_2) apply auto 
apply(rule nprv_impI_rev2[of "{eql t (Num i)}" "neg (eql t (suc (Num n)))"])  apply auto 
apply(rule nprv_eql_substE[of _ t "Num i" "imp (neg (eql (Var xx) (suc (Num n)))) (LLq (Var xx) (Num n))" xx]) 
apply auto  
  apply(rule nprv_hyp) apply simp_all
  (**)
  apply(rule nprv_clear) apply simp_all
  apply(rule nprv_impI) apply simp_all 
  apply(cases "i = Suc n") apply simp_all
    apply(rule nprv_negE0) apply auto
    apply(rule nprv_eql_reflI) apply simp_all
    (* *)
    apply(rule prv_nprvI) apply simp_all
    apply(rule leq_prv_LLq_Num) apply simp_all
    (* *)
    apply(rule nprv_hyp) apply simp_all
. .

(* Rulification *)
lemmas nprv_LLq_neg_Num_sucI = nprv_addImp2LemmaI[OF prv_imp_LLq_neg_Num_suc, simped, rotated 3]
lemmas nprv_LLq_neg_Num_sucE = nprv_addImp2LemmaE[OF prv_imp_LLq_neg_Num_suc, simped, rotated 1]

lemmas nprv_LLq_neg_Num_sucE0 = nprv_LLq_neg_Num_sucE[OF nprv_hyp _ _, simped]
lemmas nprv_LLq_neg_Num_sucE1 = nprv_LLq_neg_Num_sucE[OF _ nprv_hyp _, simped]
lemmas nprv_LLq_neg_Num_sucE2 = nprv_LLq_neg_Num_sucE[OF _ _ nprv_hyp, simped] 
lemmas nprv_LLq_neg_Num_sucE01 = nprv_LLq_neg_Num_sucE[OF nprv_hyp nprv_hyp _, simped]
lemmas nprv_LLq_neg_Num_sucE02 = nprv_LLq_neg_Num_sucE[OF nprv_hyp _ nprv_hyp, simped]
lemmas nprv_LLq_neg_Num_sucE12 = nprv_LLq_neg_Num_sucE[OF _ nprv_hyp nprv_hyp, simped]
lemmas nprv_LLq_neg_Num_sucE012 = nprv_LLq_neg_Num_sucE[OF nprv_hyp nprv_hyp nprv_hyp, simped]
(* *)


lemma prv_ball_Num_imp_ball_suc: (* O9 *)
assumes [simp]: "x \<in> var" "\<phi> \<in> fmla" 
shows "prv (imp (ball x (Num n) \<phi>) 
                (ball x (suc (Num n)) (imp (neg (eql (Var x) (suc (Num n)))) \<phi>)))"
apply(rule nprv_prvI) apply simp_all
apply(rule nprv_impI) apply simp_all
apply(rule nprv_ballI) apply simp_all
apply(rule nprv_impI) apply simp_all
apply(rule nprv_LLq_neg_Num_sucE01) apply auto 
apply(rule nprv_clear4_2) apply simp_all apply(rule nprv_clear3_2) apply simp_all
apply(rule nprv_ballE0[of x "Num n" \<phi> _ "Var x"]) apply simp_all
  apply(rule nprv_hyp) apply simp_all
  apply(rule nprv_hyp) apply simp_all
done

(* Rulification: *)
lemmas prv_ball_Num_ball_sucI = nprv_addImpLemmaI[OF prv_ball_Num_imp_ball_suc, simped, rotated 4]  
lemmas prv_ball_Num_ball_sucE = nprv_addImpLemmaE[OF prv_ball_Num_imp_ball_suc, simped, rotated 2] 

lemmas prv_ball_Num_ball_sucE0 = prv_ball_Num_ball_sucE[OF nprv_hyp _, simped]
lemmas prv_ball_Num_ball_sucE1 = prv_ball_Num_ball_sucE[OF _ nprv_hyp, simped] 
lemmas prv_ball_Num_ball_sucE01 = prv_ball_Num_ball_sucE[OF nprv_hyp nprv_hyp, simped] 

lemmas O9I = prv_ball_Num_ball_sucI
lemmas O9E = prv_ball_Num_ball_sucE
lemmas O9E0 = prv_ball_Num_ball_sucE0
lemmas O9E1 = prv_ball_Num_ball_sucE1
lemmas O9E01 = prv_ball_Num_ball_sucE01
(* *)


(* Verifying the abstract assumptions needed for Godel_Rosser I: *)

lemma LLq_num:
assumes \<phi>[simp]: "\<phi> \<in> fmla"  "Fvars \<phi> = {zz}" and q: "q \<in> num" and p: "\<forall> p \<in> num. prv (subst \<phi> p zz)" 
shows "prv (all zz (imp (LLq (Var zz) q) \<phi>))" 
proof-
  obtain n where q: "q = Num n" using q num_Num by auto 
(* NB: We did not the whole strength of the assumption p -- we only needed that to hold for 
numerals smaller than n. Howevere, the abstract framework allowed us to make this strong assumption, 
and did not need to even assume an order on the numerals. *)
  show ?thesis unfolding q ball_def[symmetric] using p p num_Num by (intro O4) auto 
qed

lemma LLq_num2: 
assumes "p \<in> num"
shows "\<exists>P\<subseteq>num. finite P \<and> prv (dsj (sdsj {eql (Var yy) r |r. r \<in> P}) (LLq p (Var yy)))"
proof-
  obtain n where q[simp]: "p = Num n" using assms num_Num by auto
  have [simp]: "{eql (Var yy) r |r. \<exists>i. r = Num i \<and> i \<le> n} \<subseteq> fmla" by auto
  show ?thesis 
  apply(rule exI[of _ "{Num i | i . i \<le> n}"]) apply auto
  apply(rule nprv_prvI) apply auto
  apply(rule O8E[of "Var yy" n]) apply simp_all
    apply(rule nprv_dsjIL) apply auto
    apply(rule O3E0) apply auto
    apply(rule nprv_ldsjE0) apply auto 
    subgoal for i 
    apply(rule nprv_sdsjI[of _ "eql (Var yy) (Num i)"]) apply auto
    apply(rule nprv_hyp) apply auto .
    (**)
    apply(rule nprv_dsjIR) apply auto
    apply(rule nprv_hyp) apply auto
  done
qed 

end \<comment> \<open>context Deduct_Q\<close> 


(* The system Q embedding satisfies the abstract assumptions we needed for Godel-Rosser First: *)

sublocale Deduct_Q < lab: Deduct_with_PseudoOrder where Lq = "LLq (Var zz) (Var yy)"
apply standard apply auto[] using Fvars_Lq apply auto[]
using LLq_num apply auto[]
using LLq_num2 apply auto[]
done



end
