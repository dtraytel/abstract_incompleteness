(* Sound theory over the syntax of arithmetics *)

theory Sound_Theory_Syntax_Q
imports Theory_Syntax_Q
begin

specification (specific_axioms)
  specific_axioms_hold:  "\<And> ax. ax \<in> specific_axioms \<Longrightarrow> eval_fmla e ax"
  by (rule exI [where x = "{eql zer zer}"], auto)

text{*Soundness theorem!*}
theorem nprv_sound: assumes "H \<turnstile> A" shows "(\<forall>B\<in>H. eval_fmla e B) \<Longrightarrow> eval_fmla e A"
using assms
proof (induct arbitrary: e)
  case (Hyp A H) thus ?case
    by auto
next
  case (extra H) thus ?case
    by (metis specific_axioms_hold)
next
  case (Bool A H) thus ?case
    by (metis boolean_axioms_hold)
next
  case (eql A H) thus ?case
    by (metis equality_axioms_hold)
next
  case (Spec A H) thus ?case
    by (metis special_axioms_hold)
next
  case (MP H A B H') thus ?case
    by auto
next
  case (exiists H A B i e) thus ?case
    by auto (metis forget_eval_fmla)
qed

end