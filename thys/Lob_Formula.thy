(* The Lob formula, parameterized by a sentence \<phi>, defined by diagonalizing "imp P \<phi>". *)

theory Lob_Formula imports Diagonalization
begin 



(* To produce the Godel formula, we need representability of substitution and 
weak representability of provability:
 *)
locale Lob_Form =  
Deduct2
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv bprv
+
Repr_Subst
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv bprv
  enc
  S 
+
WRepr_Provability
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv bprv
  enc
  P
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var num FvarsT substT Fvars subst
and eql cnj imp all exi
and prv bprv
and enc ("\<langle>_\<rangle>")
and S
and P
(*  *)
begin

(* The Loeb formula (parameterized by another formula) *)
definition \<phi>L :: "'fmla \<Rightarrow> 'fmla" where "\<phi>L \<phi> \<equiv> diag (imp P \<phi>)"  

lemma \<phi>L[simp,intro]: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> \<phi>L \<phi> \<in> fmla"
and
Fvars_\<phi>L[simp]: "\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> Fvars (\<phi>L \<phi>) = {}"
  unfolding \<phi>L_def PP_def by auto

lemma bprv_\<phi>L_eqv: 
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi>  = {} \<Longrightarrow> bprv (eqv (\<phi>L \<phi>) (imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>))"
  unfolding \<phi>L_def PP_def using bprv_diag_eqv[of "imp P \<phi>"] by auto

lemma prv_\<phi>L_eqv: 
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi>  = {} \<Longrightarrow> prv (eqv (\<phi>L \<phi>) (imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>))"
  using bprv_prv[OF _ _ bprv_\<phi>L_eqv, simplified] by auto 
 
end \<comment> \<open>context Lob_Form\<close>



end 
