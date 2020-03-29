theory Q_Instance_Sound
  imports Abstract.Standard_Model Q_Instance_Syntax_Deduction Sound_Theory_Syntax_Q
begin

interpretation Minimal_Truth_Soundness where
      var = "UNIV :: name set"
  and trm = "UNIV :: trm set"
  and fmla = "UNIV :: fmla set"
  and num = num
  and Var = Var
  and FvarsT = Fvars
  and substT = "\<lambda>t u x. subst x u t"
  and Fvars = Fvars
  and subst = "\<lambda>A u x. subst_fmla A x u"
  and eql = eql and cnj = cnj and dsj = dsj and imp = imp
  and all = all and exi = exi and fls = fls
  and bprv = "(\<turnstile>) {}"
  and isTrue = "eval_fmla e0"
  apply unfold_locales
  subgoal by (auto simp: fls_def)
  subgoal by simp
  subgoal by (auto simp only: ex_eval_fmla_iff_exists_num eval_fmla.simps  subst_fmla.simps)
  subgoal by (auto simp only: ex_eval_fmla_iff_exists_num)
  subgoal by (simp add: neg_def)
  subgoal by (auto dest: nprv_sound)
  done

end

