(* This theory considers various encoding assumptions for formulas, 
computable functions etc.: *)

theory Abstract_Encoding imports Deduction
begin 

(* Assumed (not necessarily injective) encoding of formulas as numbers: *)
locale Encode = 
Deduct2
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  bprv prv
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst 
and num
and eql cnj imp all exi 
and bprv prv
+
fixes 
(*************************************)
(* Numeric formulas are assumed to be encoded as numerals: *)
enc :: "'fmla \<Rightarrow> 'trm" ("\<langle>_\<rangle>") 
assumes 
enc[simp,intro!]: "\<And> \<phi>. \<phi> \<in> fmla \<Longrightarrow> enc \<phi> \<in> num"
begin

end \<comment> \<open>context Encode\<close>


(* Explicit proofs (encoded as numbers), needed only for the harder half of Godel's first; not used 
in Godel's second, which only needs the easy half of Godel's first *)

locale Encode_Proofs = 
Encode
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv bprv
  enc 
+
Deduct2_with_Proofs  
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num  
  prv bprv
  "proof" prfOf 
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst 
and num
and eql cnj imp all exi 
and prv bprv
and enc ("\<langle>_\<rangle>")     
and fls dsj 
and "proof" :: "'proof set" and prfOf   
+
fixes encPf :: "'proof \<Rightarrow> 'trm"
assumes
encPf[simp,intro!]: "\<And> pf. pf \<in> proof \<Longrightarrow> encPf pf \<in> num"
 


(****************)
(****************)
(****************)
(* The below material is only used for the Jeroslow-style proof. *)

(* 
We assume the encodability of an abstract (unspecified) class of unary computable functions 
and the assumption that a particular function, "sub", is in this collection. 
This is used to prove a different diagonalization lemma (Jeroslow 1973). *)
locale Encode_UComput = 
Encode 
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv bprv
  enc 
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst 
and num
and eql cnj imp all exi 
and prv bprv
and enc ("\<langle>_\<rangle>")
+
(* Abstract (unspeficied) notion of unary "computable" function between numerals, which are encodable as numbeerals,  
and contain a special substitution-like function "sub \<phi>" for each formula \<phi>: *)
fixes ucfunc :: "('trm \<Rightarrow> 'trm) set"
  and encF :: "('trm \<Rightarrow> 'trm) \<Rightarrow> 'trm" 
  and sub :: "'fmla \<Rightarrow> 'trm \<Rightarrow> 'trm"  
(*  *)
assumes 
ucfunc[simp,intro!]: "\<And> f n. f \<in> ucfunc \<Longrightarrow> n \<in> num \<Longrightarrow> f n \<in> num"
and
encF[simp,intro!]: "\<And> f. f \<in> ucfunc \<Longrightarrow> encF f \<in> num"
and 
sub[simp]: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> sub \<phi> \<in> ucfunc"
and 
(* The function sub \<phi> takes any encoding of a function f and returns the encoding of the formula 
obtained by substituting for xx the value of f applied to its own encoding: 
*)
sub_enc: 
"\<And> \<phi> f. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {xx} \<Longrightarrow> f \<in> ucfunc \<Longrightarrow> 
    sub \<phi> (encF f) = enc (inst \<phi> (f (encF f)))"

(* For term-representation, we assume an encoding of a subset of 
some the term operators as numerals: *)
(* Assumed (not necessarily injective) encoding of formulas as numbers: *)
locale TermEncode = 
Deduct2
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  prv bprv
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst 
and num
and eql cnj imp all exi 
and prv bprv
+
fixes  
Ops ::  "('trm \<Rightarrow> 'trm) set" 
and
enc :: "('trm \<Rightarrow> 'trm) \<Rightarrow> 'trm" ("\<langle>_\<rangle>") 
assumes
Ops[simp,intro!]: "\<And>f t. f \<in> Ops \<Longrightarrow> t \<in> trm \<Longrightarrow> f t \<in> trm"
and  
enc[simp,intro!]: "\<And> f. f \<in> Ops \<Longrightarrow> enc f \<in> num"
and 
Ops_FvarsT[simp]: "\<And> f t. f \<in> Ops \<Longrightarrow> t \<in> trm \<Longrightarrow> FvarsT (f t) = FvarsT t"
and 
Ops_substT[simp]: "\<And> f t. f \<in> Ops \<Longrightarrow> t \<in> trm \<Longrightarrow> t1 \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow> 
  substT (f t) t1 x = f (substT t t1 x)"
begin

end \<comment> \<open>context TermEncode\<close>

(*<*)
end
(*>*)