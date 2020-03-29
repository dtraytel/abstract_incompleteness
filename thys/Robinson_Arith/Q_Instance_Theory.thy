theory Q_Instance_Theory
  imports Embed_Q Q_Instance_Syntax_Deduction 
begin

lemma exi_ren: "y \<notin> Fvars \<phi> \<Longrightarrow> exi x \<phi> = exi y (\<phi>(x::=Var y))"
using exi_ren_subst_fresh Fvars_def by blast

lemma all_ren: "y \<notin> Fvars \<phi> \<Longrightarrow> all x \<phi> = all y (\<phi>(x::=Var y))"
by (simp add: exi_ren)

interpretation Syntax_Arith_aux where
      var = "UNIV :: name set"
  and trm = "UNIV :: trm set"
  and fmla = "UNIV :: fmla set"
  and num = num
  and Var = Var
  and FvarsT = Fvars
  and substT = "\<lambda>t u x. subst x u t"
  and Fvars = Fvars
  and subst = "\<lambda>A u x. subst_fmla A x u"
  and eql = eql and cnj = cnj and imp = imp and all = all
  and exi = exi and dsj = dsj and fls = fls
  and zer = zer and suc = suc and pls = pls and tms = tms
  apply unfold_locales by(auto simp: exi_ren all_ren)

lemma num_range_Num: "num = range Num" 
unfolding image_def proof auto
  fix t assume "t \<in> num" 
  then show "\<exists>n. t = Num n" 
  apply(induct t rule: trm.induct)   
  apply (auto elim: num.cases intro!: num.intros)
  apply (metis Num.simps(1)) 
  by (metis Num.simps(2) num.cases trm.distinct(3) trm.eq_iff(3))
next
  fix n show "Num n \<in> num"
  by (induct n) auto
qed  

interpretation Syntax_Arith where
      var = "UNIV :: name set"
  and trm = "UNIV :: trm set"
  and fmla = "UNIV :: fmla set"
  and num = num
  and Var = Var
  and FvarsT = Fvars
  and substT = "\<lambda>t u x. subst x u t"
  and Fvars = Fvars
  and subst = "\<lambda>A u x. subst_fmla A x u"
  and eql = eql and cnj = cnj and imp = imp and all = all
  and exi = exi and dsj = dsj and fls = fls and zer = zer 
  and suc = suc and pls = pls and tms = tms
  apply unfold_locales using num_range_Num by auto 

definition "the_Q_axioms \<equiv>
 {neg (zer EQ suc (Var xx)), 
  suc (Var xx) EQ suc (Var yy) IMP Var xx EQ Var yy,
  Var yy EQ zer OR exi xx (Var yy EQ suc (Var xx)), 
  pls (Var xx) zer EQ Var xx, 
  pls (Var xx) (suc (Var yy)) EQ suc (pls (Var xx) (Var yy)),
  tms (Var xx) zer EQ zer,
  tms (Var xx) (suc (Var yy)) EQ pls (tms (Var xx) (Var yy)) (Var xx)} "  

(* Assuming the theory is an extension of Q: *)
specification (specific_axioms)
  Q_included_in_specific_axioms: "the_Q_axioms \<subseteq> specific_axioms"
  by (rule exI [where x = "the_Q_axioms"], auto)


interpretation Deduct_Q where
      var = "UNIV :: name set"
  and trm = "UNIV :: trm set"
  and fmla = "UNIV :: fmla set"
  and num = num
  and Var = Var
  and FvarsT = Fvars
  and substT = "\<lambda>t u x. subst x u t"
  and Fvars = Fvars
  and subst = "\<lambda>A u x. subst_fmla A x u"
  and eql = eql and cnj = cnj and imp = imp and all = all
  and exi = exi and dsj = dsj and fls = fls and zer = zer 
  and suc = suc and pls = pls and tms = tms
  and prv = "(\<turnstile>) {}" 
  apply unfold_locales
  using Q_included_in_specific_axioms by (auto simp add: extra the_Q_axioms_def)

end
