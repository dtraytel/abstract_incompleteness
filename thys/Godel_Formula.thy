(* The Godel formula, defined by diagonalizing the negation of the provability predicate. *)

theory Godel_Formula imports Diagonalization
begin 


(* To produce the Godel formula, we need the fls connective (hence negation),
and we need representability of substitution and weak representability of provability:
 *)
locale Godel_Form = 
(* Assuming the fls ("false") connective: *)
Deduct2_with_False
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  num
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
and fls
and prv bprv
and enc ("\<langle>_\<rangle>")
and S
and P
begin

(* The Goedel formula *)
definition \<phi>G :: 'fmla where "\<phi>G \<equiv> diag (neg P)"

lemma \<phi>G[simp,intro!]: "\<phi>G \<in> fmla"
and
Fvars_\<phi>G[simp]: "Fvars \<phi>G = {}"
  unfolding \<phi>G_def PP_def by auto

lemma bprv_\<phi>G_eqv: 
"bprv (eqv \<phi>G (neg (PP \<langle>\<phi>G\<rangle>)))"
  unfolding \<phi>G_def PP_def using bprv_diag_eqv[of "neg P"] by simp

lemma prv_\<phi>G_eqv: 
"prv (eqv \<phi>G (neg (PP \<langle>\<phi>G\<rangle>)))"
  using bprv_prv[OF _ _ bprv_\<phi>G_eqv, simplified] .
 
end \<comment> \<open>context Godel_Form\<close>

locale Godel_Form_with_Proofs =  
Repr_Subst
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv bprv
  enc
  S
+
Repr_Proofs 
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv bprv
  enc
  fls
  dsj 
  "proof" prfOf  
  encPf 
  Pf
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst num 
and eql cnj imp all exi 
and fls
and prv bprv
and enc ("\<langle>_\<rangle>")
and S
and dsj 
and "proof" :: "'proof set" and prfOf encPf 
and Pf

locale Godel_Form_from_Proofs = Godel_Form

sublocale Godel_Form_with_Proofs < Godel_Form_from_Proofs where P = P by standard
(* Note: The proof goes instantly because at this point the system knows about 
"sublocale Repr_Proofs < WRepr_Provability where P = P" *)


context Godel_Form_with_Proofs 
begin

lemma bprv_\<phi>G_eqv_not_exi_PPf: 
"bprv (eqv \<phi>G (neg (exi yy (PPf (Var yy) \<langle>\<phi>G\<rangle>))))"
proof-
  have P: "P = exi yy Pf" using P_def by (simp add: PPf_def2)
  hence "subst P \<langle>\<phi>G\<rangle> xx = subst (exi yy Pf) \<langle>\<phi>G\<rangle> xx" by auto
  hence "subst P \<langle>\<phi>G\<rangle> xx = exi yy (subst Pf \<langle>\<phi>G\<rangle> xx)" by simp
  thus ?thesis using bprv_\<phi>G_eqv by (simp add: wrepr.PP_def PPf_def2)
qed

lemma prv_\<phi>G_eqv_not_exi_PPf: 
"prv (eqv \<phi>G (neg (exi yy (PPf (Var yy) \<langle>\<phi>G\<rangle>))))"
using bprv_prv[OF _ _ bprv_\<phi>G_eqv_not_exi_PPf, simplified] .

lemma bprv_\<phi>G_eqv_all_not_PPf: 
"bprv (eqv \<phi>G (all yy (neg (PPf (Var yy) \<langle>\<phi>G\<rangle>))))"
  by (rule B.prv_eqv_trans[OF _ _ _ bprv_\<phi>G_eqv_not_exi_PPf B.prv_neg_exi_eqv_all_neg]) auto

lemma prv_\<phi>G_eqv_all_not_PPf: 
"prv (eqv \<phi>G (all yy (neg (PPf (Var yy) \<langle>\<phi>G\<rangle>))))"
using bprv_prv[OF _ _ bprv_\<phi>G_eqv_all_not_PPf, simplified] .

lemma bprv_eqv_all_not_PPf_imp_\<phi>G: 
"bprv (imp (all yy (neg (PPf (Var yy) \<langle>\<phi>G\<rangle>))) \<phi>G)"
  using bprv_\<phi>G_eqv_all_not_PPf by (auto intro: B.prv_imp_eqvER) 

lemma prv_eqv_all_not_PPf_imp_\<phi>G: 
"prv (imp (all yy (neg (PPf (Var yy) \<langle>\<phi>G\<rangle>))) \<phi>G)"
using bprv_prv[OF _ _ bprv_eqv_all_not_PPf_imp_\<phi>G, simplified] .
   

end \<comment> \<open>context Godel_Form_with_Proofs\<close>






end 
