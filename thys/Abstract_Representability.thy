(* Assumptions about various functions or relations being representable *)
theory Abstract_Representability imports Abstract_Encoding
begin 

(* Assume the provability predicate is "very-weakly" representable, 
in that one implication of the weak representability condition holds.   *)
locale WRepr_Provability =  
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
(* Weak represenatbility of provability, as a one-variable formula P, usually called the provability predicate: *)
fixes P :: 'fmla
assumes 
P[intro!,simp]: "P \<in> fmla"
and 
Fvars_P[simp]: "Fvars P = {xx}"
and  
HBL1: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv \<phi> \<Longrightarrow> bprv (subst P \<langle>\<phi>\<rangle> xx)"
begin

(* For all our (very-weak) representability assumptions, in addition to
 the representing formulas, 
here, P, we define a corresponding instantiation combinator, here the 
predicate PP. 
If we think of P as P(xx), then PP t is the instance PP(t)  *) 
definition PP where "PP \<equiv> \<lambda>t. subst P t xx"

lemma PP[simp]: "\<And>t. t \<in> trm \<Longrightarrow> PP t \<in> fmla"
  unfolding PP_def by auto

lemma Fvars_PP[simp]: "\<And>t. t \<in> trm \<Longrightarrow> Fvars (PP t) = FvarsT t"
  unfolding PP_def by (auto simp: Fvars_subst)

lemma [simp]: 
"n \<in> num \<Longrightarrow> subst (PP (Var yy)) n yy = PP n"
"n \<in> num \<Longrightarrow> subst (PP (Var xx)) n xx = PP n"
  unfolding PP_def by auto

lemma HBL1_PP: 
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv \<phi> \<Longrightarrow> bprv (PP \<langle>\<phi>\<rangle>)"
  using HBL1 unfolding PP_def by auto


end \<comment> \<open>WRepr_Provability\<close>



(* Representability of the negation function.    *)
locale Repr_Neg = 
Deduct2_with_False 
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  num
  prv bprv 
+
Encode
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv bprv
  enc 
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and eql cnj imp all exi 
and fls 
and num
and prv bprv
and enc ("\<langle>_\<rangle>")  
+
fixes 
(* Representability of the negation, as a formula N: *)
N :: 'fmla
(*  *)
assumes
(* N is a formula with free variables xx yy, usually written N(xx,yy) *)
N[simp,intro!]: "N \<in> fmla"
and 
Fvars_N[simp]: "Fvars N = {xx,yy}"
and 
neg_implies_prv_N: 
"\<And> \<phi>. 
  let NN = (\<lambda> t1 t2. psubst N [(t1,xx), (t2,yy)]) in   
   \<phi> \<in> fmla \<longrightarrow> Fvars \<phi> = {} \<longrightarrow> bprv (NN \<langle>\<phi>\<rangle> \<langle>neg \<phi>\<rangle>)"
and 
N_unique:
"\<And> \<phi>.  
  let NN = (\<lambda> t1 t2. psubst N [(t1,xx), (t2,yy)]) in
  \<phi> \<in> fmla \<longrightarrow> Fvars \<phi> = {} \<longrightarrow>
  bprv (all yy (all yy' 
    (imp (cnj (NN \<langle>\<phi>\<rangle> (Var yy)) (NN \<langle>\<phi>\<rangle> (Var yy'))) 
         (eql (Var yy) (Var yy')))))"
begin

(* NN is a notation, convenient for manipulating different (substitution) instances of N: 
If we think of N as N(xx,yy), then NN t1 t2 is the instance NN(t1,t2)  *)
definition NN where "NN \<equiv> \<lambda> t1 t2. psubst N [(t1,xx), (t2,yy)]"

lemma NN_def2: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> yy \<notin> FvarsT t1 \<Longrightarrow> 
 NN t1 t2 = subst (subst N t1 xx) t2 yy"
  unfolding NN_def apply(rule psubst_eq_rawpsubst2[simplified]) by auto

lemma NN_neg: 
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> bprv (NN \<langle>\<phi>\<rangle> \<langle>neg \<phi>\<rangle>)"
  using neg_implies_prv_N unfolding Let_def NN_def by meson 

lemma NN_unique:
  assumes "\<phi> \<in> fmla" "Fvars \<phi> = {}"
  shows "bprv (all yy (all yy' 
    (imp (cnj (NN \<langle>\<phi>\<rangle> (Var yy)) (NN \<langle>\<phi>\<rangle> (Var yy'))) 
         (eql (Var yy) (Var yy')))))"
  using assms N_unique unfolding Let_def NN_def by meson 

lemma NN[simp,intro]: 
"t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> NN t1 t2 \<in> fmla"
unfolding NN_def by auto

lemma Fvars_NN[simp]: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> yy \<notin> FvarsT t1 \<Longrightarrow> 
Fvars (NN t1 t2) = FvarsT t1 \<union> FvarsT t2"
by (auto simp add: NN_def2 Fvars_subst subst2_fresh_switch)

(*
lemma [simp]: "Fvars (NN (Var xx) (Var yy)) = {xx,yy}" 
"n \<in> num \<Longrightarrow> Fvars (NN n (Var yy')) = {yy'}" 
"Fvars (NN (Var xx) (Var xx')) = {xx,xx'}" 
  by auto
*)

lemma [simp]: 
"m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (NN m (Var yy)) n yy = NN m n"
"m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (NN m (Var yy')) n yy = NN m (Var yy')"
"m \<in> num \<Longrightarrow> subst (NN m (Var yy')) (Var yy) yy' = NN m (Var yy)"
"n \<in> num \<Longrightarrow> subst (NN (Var xx) (Var yy)) n xx = NN n (Var yy)"
"n \<in> num \<Longrightarrow> subst (NN (Var xx) (Var xx')) n xx = NN n (Var xx')"
"m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (NN m (Var xx')) n zz = NN m (Var xx')"
"n \<in> num \<Longrightarrow> subst (NN n (Var yy)) (Var xx') yy = NN n (Var xx')"
"m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (NN m (Var xx')) n xx' = NN m n"
  by (auto simp add: NN_def2 Fvars_subst subst2_fresh_switch) 


lemma  NN_unique2: 
assumes [simp]:"\<phi> \<in> fmla" "Fvars \<phi> = {}"
shows 
"bprv (all yy 
     (imp (NN \<langle>\<phi>\<rangle> (Var yy))  
          (eql \<langle>neg \<phi>\<rangle> (Var yy))))"
proof-
  have 1: "bprv (NN \<langle>\<phi>\<rangle> \<langle>neg \<phi>\<rangle>)"  
    using NN_neg[OF assms] . 
  have 2: "bprv (all yy' (  
             imp (cnj (NN \<langle>\<phi>\<rangle> \<langle>neg \<phi>\<rangle>)
                      (NN \<langle>\<phi>\<rangle> (Var yy')))
                 (eql \<langle>neg \<phi>\<rangle> (Var yy'))))" 
    using B.prv_allE[of yy, OF _ _ _ NN_unique, of "\<phi>" "\<langle>neg \<phi>\<rangle>"]
    by fastforce
  have 31: "bprv (all yy' (  
             imp (NN \<langle>\<phi>\<rangle> \<langle>neg \<phi>\<rangle>)
                 (imp (NN \<langle>\<phi>\<rangle> (Var yy'))
                      (eql \<langle>neg \<phi>\<rangle> (Var yy')))))"  
    using B.prv_all_imp_cnj_rev[OF _ _ _ _ 2] by simp
  have 32: "bprv (imp (NN \<langle>\<phi>\<rangle> \<langle>neg \<phi>\<rangle>)
                      (all yy' (imp (NN \<langle>\<phi>\<rangle> (Var yy'))
                                    (eql \<langle>neg \<phi>\<rangle> (Var yy')))))"
    apply(rule B.prv_all_imp[OF _ _ _ _ 31])
    by (auto simp: NN_def2 Fvars_subst) 
  have 33: "bprv (all yy' (imp (NN \<langle>\<phi>\<rangle> (Var yy'))
                              (eql \<langle>neg \<phi>\<rangle> (Var yy'))))"
    apply(rule B.prv_imp_mp [OF _ _ 32 1]) by auto
  thus ?thesis using B.all_subst_rename_prv[OF _ _ _ _ 33, of yy] by simp
qed

lemma NN_neg_unique:
assumes [simp]:"\<phi> \<in> fmla" "Fvars \<phi> = {}"
shows 
"bprv (imp (NN \<langle>\<phi>\<rangle> (Var yy))  
           (eql \<langle>neg \<phi>\<rangle> (Var yy)))" (is "bprv ?A")
proof-
  have 0: "bprv (all yy ?A)"
    using NN_unique2[of "\<phi>"] by simp
  show ?thesis apply(rule B.allE_id[OF _ _ 0]) by auto
qed

lemma NN_exi_cnj: 
assumes \<phi>[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}" and \<chi>[simp]: "\<chi> \<in> fmla"
assumes f: "Fvars \<chi> = {yy}"
shows "bprv (eqv (subst \<chi> \<langle>neg \<phi>\<rangle> yy) 
                 (exi yy (cnj \<chi> (NN \<langle>\<phi>\<rangle> (Var yy)))))"
(is "bprv (eqv ?A ?B)")
proof(intro B.prv_eqvI)   
  have yy: "yy \<in> var" by simp
  let ?N = "NN \<langle>\<phi>\<rangle> (Var yy)"
  have "bprv (imp (subst \<chi> \<langle>neg \<phi>\<rangle> yy) ((subst (cnj \<chi> ?N) \<langle>neg \<phi>\<rangle> yy)))" using NN_neg[OF \<phi>] 
    by (simp add: B.prv_imp_cnj B.prv_imp_refl B.prv_imp_triv)
  thus "bprv (imp ?A ?B)"   
    using NN num Var \<chi> cnj exi subst B.prv_exi_inst B.prv_prv_imp_trans yy 
    by (smt \<phi> enc in_num neg) 
next    
  have 00: "bprv (imp (eql \<langle>neg \<phi>\<rangle> (Var yy)) (imp \<chi> (subst \<chi> \<langle>neg \<phi>\<rangle> yy)))" 
    apply(rule B.prv_eql_subst_trm_id_rev) by auto
  have 11: "bprv (imp (NN \<langle>\<phi>\<rangle> (Var yy)) (imp \<chi> (subst \<chi> \<langle>neg \<phi>\<rangle> yy)))"  
    using 00 NN_neg_unique[OF \<phi>] 
    using NN num Var Variable \<phi> \<chi> eql imp subst B.prv_prv_imp_trans 
    by (metis (no_types, lifting) enc in_num neg)
  hence "bprv (imp (cnj \<chi> (NN \<langle>\<phi>\<rangle> (Var yy))) (subst \<chi> \<langle>neg \<phi>\<rangle> yy))"      
    by (simp add: 11 B.prv_cnj_imp_monoR2 B.prv_imp_com)
  hence 1: "bprv (all yy (imp (cnj \<chi> (NN \<langle>\<phi>\<rangle> (Var yy))) (subst \<chi> \<langle>neg \<phi>\<rangle> yy)))" 
    by (simp add: B.prv_all_gen)
  have 2: "Fvars (subst \<chi> \<langle>neg \<phi>\<rangle> yy) = {}" using f by (simp add: Fvars_subst)
  show "bprv (imp ?B ?A)" using 1 2  
    by (simp add: B.prv_exi_imp)
qed auto


end \<comment> \<open>Repr_Neg\<close>


(* Representability of an instance of the substitution function. 
(Under this hypothesis, we prove the standard diagonalization lemma.)  *)
locale Repr_Subst = 
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
fixes 
(* Representability of an instance of the substitution function, namely 
"diagonal substitution" which takes a formula \<phi> and sends it to subst \<phi> \<langle>\<phi>\<rangle> xx 
(for the fixed variable xx). This is assumed to be represented by a two-variable 
formula S: *)
S :: 'fmla
(*  *)
assumes
(* S is a formula with free variables xx yy, usually written S(xx,yy) *)
S[simp,intro!]: "S \<in> fmla"
and 
Fvars_S[simp]: "Fvars S = {xx,yy}"
and 
subst_implies_prv_S: 
"\<And> \<phi>.   
  let SS = (\<lambda> t1 t2. psubst S [(t1,xx), (t2,yy)]) in
  \<phi> \<in> fmla \<longrightarrow> Fvars \<phi> = {xx} \<longrightarrow>
  bprv (SS \<langle>\<phi>\<rangle> \<langle>subst \<phi> \<langle>\<phi>\<rangle> xx\<rangle>)"  
and 
S_unique:
"\<And> \<phi>. 
  let SS = (\<lambda> t1 t2. psubst S [(t1,xx), (t2,yy)]) in
  \<phi> \<in> fmla \<longrightarrow> Fvars \<phi> = {xx} \<longrightarrow>
  bprv (all yy (all yy' 
     (imp (cnj (SS \<langle>\<phi>\<rangle> (Var yy)) (SS \<langle>\<phi>\<rangle> (Var yy'))) 
          (eql (Var yy) (Var yy')))))"
begin

(* SS is the instance-combinator of S: *)
definition SS where "SS \<equiv> \<lambda> t1 t2. psubst S [(t1,xx), (t2,yy)]"

lemma SS_def2: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> 
 yy \<notin> FvarsT t1 \<Longrightarrow>
 SS t1 t2 = subst (subst S t1 xx) t2 yy"
  unfolding SS_def apply(rule psubst_eq_rawpsubst2[simplified])
  by auto

lemma subst_implies_prv_SS: 
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {xx} \<Longrightarrow> bprv (SS \<langle>\<phi>\<rangle> \<langle>subst \<phi> \<langle>\<phi>\<rangle> xx\<rangle>)"
using subst_implies_prv_S unfolding Let_def SS_def by meson 

lemma SS_unique:
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {xx} \<Longrightarrow>
 bprv (all yy (all yy' 
      (imp (cnj (SS \<langle>\<phi>\<rangle> (Var yy)) (SS \<langle>\<phi>\<rangle> (Var yy'))) 
           (eql (Var yy) (Var yy')))))"
using S_unique unfolding Let_def SS_def by meson 

lemma SS[simp,intro]: 
"t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> SS t1 t2 \<in> fmla"
unfolding SS_def by auto

lemma Fvars_SS[simp]: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> yy \<notin> FvarsT t1 \<Longrightarrow> 
Fvars (SS t1 t2) = FvarsT t1 \<union> FvarsT t2"
by (auto simp add: Fvars_subst SS_def2 subst2_fresh_switch)

(*
lemma [simp]: 
"Fvars (SS (Var xx) (Var yy)) = {xx,yy}" 
"n \<in> num \<Longrightarrow> Fvars (SS n (Var yy')) = {yy'}"
by auto
*)

lemma [simp]: 
"m \<in> num \<Longrightarrow> p \<in> num \<Longrightarrow> subst (SS m (Var yy)) p yy = SS m p" 
"m \<in> num \<Longrightarrow> subst (SS m (Var yy')) (Var yy) yy' = SS m (Var yy)" 
"m \<in> num \<Longrightarrow> p \<in> num \<Longrightarrow> subst (SS m (Var yy')) p yy' = SS m p" 
"m \<in> num \<Longrightarrow> p \<in> num \<Longrightarrow> subst (SS m (Var yy')) p yy = SS m (Var yy')"
"m \<in> num \<Longrightarrow> subst (SS (Var xx) (Var yy)) m xx = SS m (Var yy)"
by (auto simp add: SS_def2 Fvars_subst subst_comp_num Let_def)


end \<comment> \<open>context Repr_Subst\<close>


(**************************)
(* Alternative to the representability of (an instance of) the substitution function: 
representing the equivalent (instance of) "soft substitution":
instead of \<phi> \<mapsto> subst \<phi> \<langle>\<phi>\<rangle> xx, 
           \<phi> \<mapsto> softSubst \<phi> \<langle>\<phi>\<rangle> xx, i.e., exi xx (cnj (eql (Var xx) \<langle>\<phi>\<rangle>) \<phi>), 
*)
locale Repr_SoftSubst = 
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
fixes 
(* Representability of an instance of the substitution function, namely 
"diagonal substitution" which takes a formula \<phi> and sends it to subst \<phi> \<langle>\<phi>\<rangle> xx 
(for the fixed variable xx). This is assumed to be represented by a two-variable 
formula S: *)
S :: 'fmla
(*  *)
assumes
(* S is a formula with free variables xx yy, usually written S(xx,yy) *)
S[simp,intro!]: "S \<in> fmla"
and 
Fvars_S[simp]: "Fvars S = {xx,yy}"
and 
softSubst_implies_prv_S: 
"\<And> \<phi>.   
  let SS = (\<lambda> t1 t2. psubst S [(t1,xx), (t2,yy)]) in
  \<phi> \<in> fmla \<longrightarrow> Fvars \<phi> = {xx} \<longrightarrow>
  bprv (SS \<langle>\<phi>\<rangle> \<langle>softSubst \<phi> \<langle>\<phi>\<rangle> xx\<rangle>)"  
and 
S_unique:
"\<And> \<phi>. 
  let SS = (\<lambda> t1 t2. psubst S [(t1,xx), (t2,yy)]) in
  \<phi> \<in> fmla \<longrightarrow> Fvars \<phi> = {xx} \<longrightarrow>
  bprv (all yy (all yy' 
     (imp (cnj (SS \<langle>\<phi>\<rangle> (Var yy)) (SS \<langle>\<phi>\<rangle> (Var yy'))) 
          (eql (Var yy) (Var yy')))))"
begin

(* SS is the instance-combinator of S: *)
definition SS where "SS \<equiv> \<lambda> t1 t2. psubst S [(t1,xx), (t2,yy)]"

lemma SS_def2: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> 
 yy \<notin> FvarsT t1 \<Longrightarrow>
 SS t1 t2 = subst (subst S t1 xx) t2 yy"
  unfolding SS_def apply(rule psubst_eq_rawpsubst2[simplified])
  by auto

lemma softSubst_implies_prv_SS: 
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {xx} \<Longrightarrow> bprv (SS \<langle>\<phi>\<rangle> \<langle>softSubst \<phi> \<langle>\<phi>\<rangle> xx\<rangle>)"
using softSubst_implies_prv_S unfolding Let_def SS_def by meson 

lemma SS_unique:
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {xx} \<Longrightarrow>
 bprv (all yy (all yy' 
     (imp (cnj (SS \<langle>\<phi>\<rangle> (Var yy)) (SS \<langle>\<phi>\<rangle> (Var yy'))) 
          (eql (Var yy) (Var yy')))))"
using S_unique unfolding Let_def SS_def by meson 

lemma SS[simp,intro]: 
"t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> SS t1 t2 \<in> fmla"
unfolding SS_def by auto

lemma Fvars_SS[simp]: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> yy \<notin> FvarsT t1 \<Longrightarrow> 
Fvars (SS t1 t2) = FvarsT t1 \<union> FvarsT t2"
by (auto simp add: Fvars_subst SS_def2 subst2_fresh_switch)

(*
lemma [simp]: 
"Fvars (SS (Var xx) (Var yy)) = {xx,yy}" 
"n \<in> num \<Longrightarrow> Fvars (SS n (Var yy')) = {yy'}"
by auto
*)

lemma [simp]: 
"m \<in> num \<Longrightarrow> p \<in> num \<Longrightarrow> subst (SS m (Var yy)) p yy = SS m p" 
"m \<in> num \<Longrightarrow> subst (SS m (Var yy')) (Var yy) yy' = SS m (Var yy)" 
"m \<in> num \<Longrightarrow> p \<in> num \<Longrightarrow> subst (SS m (Var yy')) p yy' = SS m p" 
"m \<in> num \<Longrightarrow> p \<in> num \<Longrightarrow> subst (SS m (Var yy')) p yy = SS m (Var yy')"
"m \<in> num \<Longrightarrow> subst (SS (Var xx) (Var yy)) m xx = SS m (Var yy)"
by (auto simp add: SS_def2 Fvars_subst subst_comp_num Let_def)


end \<comment> \<open>context Repr_SoftSubst\<close>



locale Repr_Proofs = 
Encode_Proofs 
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv bprv
  enc 
  fls
  dsj
  "proof" prfOf  
  encPf 
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst 
and num
and eql cnj imp all exi 
and prv bprv
and enc ("\<langle>_\<rangle>")  
and fls dsj  
and "proof" :: "'proof set" and prfOf   
and encPf  
+ 
fixes Pf :: 'fmla
assumes
(* Pf is a formula with free variables xx yy, usually written Pf(xx,yy) *)
Pf[simp,intro!]: "Pf \<in> fmla"
and 
Fvars_Pf[simp]: "Fvars Pf = {yy,xx}"
and 
(* Strong representability of prfOf by Pf *)
prfOf_Pf: 
"\<And> prf \<phi>.  
  let PPf = (\<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]) in
  (prf \<in> proof \<and> \<phi> \<in> fmla \<and> Fvars \<phi> = {} \<longrightarrow>
   prfOf prf \<phi>
   \<longrightarrow>   
   bprv (PPf (encPf prf) \<langle>\<phi>\<rangle>))"
and 
not_prfOf_Pf: 
"\<And> prf \<phi>.  
  let PPf = (\<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]) in
  (prf \<in> proof \<and> \<phi> \<in> fmla \<and> Fvars \<phi> = {} \<longrightarrow>
   \<not> prfOf prf \<phi>
   \<longrightarrow>   
   bprv (neg (PPf (encPf prf) \<langle>\<phi>\<rangle>)))"
(* Note that the following axiom is also necessary to capture strong representability. 
It assumes that PPf is able to exclude the numbers that are not proof codes. 
(While it may sound reasonable to make a similar assumption regarding codes of formulas, 
this turns out not to be necessary for Godel's first.)*)
and 
Pf_encPf: 
"\<And> p \<phi>. let PPf = (\<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]) in 
  p \<in> num \<and> \<phi> \<in> fmla \<and> Fvars \<phi> = {} \<longrightarrow> p \<notin> encPf ` proof \<longrightarrow> bprv (neg (PPf p \<langle>\<phi>\<rangle>))"
begin 

definition PPf where "PPf \<equiv> \<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]"


(* PPf variant of the representability axioms: *)
lemma prfOf_PPf: 
assumes "prf \<in> proof" "\<phi> \<in> fmla" "Fvars \<phi> = {}" "prfOf prf \<phi>"
shows "bprv (PPf (encPf prf) \<langle>\<phi>\<rangle>)"
  using assms prfOf_Pf unfolding PPf_def by auto

lemma not_prfOf_PPf: 
assumes "prf \<in> proof" "\<phi> \<in> fmla" "Fvars \<phi> = {}" "\<not> prfOf prf \<phi>"
shows "bprv (neg (PPf (encPf prf) \<langle>\<phi>\<rangle>))"
  using assms not_prfOf_Pf unfolding PPf_def by auto

lemma PPf_encPf: 
  assumes "\<phi> \<in> fmla" "Fvars \<phi> = {}" and "p \<in> num" "p \<notin> encPf ` proof" 
  shows "bprv (neg (PPf p \<langle>\<phi>\<rangle>))"
using assms Pf_encPf unfolding PPf_def by auto
(* *)

lemma PPf[simp,intro!]: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> xx \<notin> FvarsT t1 \<Longrightarrow> PPf t1 t2 \<in> fmla"
  unfolding PPf_def by auto

lemma PPf_def2: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> xx \<notin> FvarsT t1 \<Longrightarrow> 
  PPf t1 t2 = subst (subst Pf t1 yy) t2 xx"
  unfolding PPf_def apply(rule psubst_eq_rawpsubst2[simplified]) by auto


lemma Fvars_PPf[simp]: 
"t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> xx \<notin> FvarsT t1 \<Longrightarrow> 
 Fvars (PPf t1 t2) = FvarsT t1 \<union> FvarsT t2"
by (auto simp add: PPf_def2 Fvars_subst subst2_fresh_switch)

(* lemma [simp]:
"Fvars (PPf (Var yy) (Var xx)) = {yy,xx}"  
"Fvars (PPf (Var zz) (Var xx')) = {zz,xx'}"
"m \<in> num \<Longrightarrow> Fvars (PPf (Var zz) m) = {zz}"
  by auto
*)

(* Here and elsewhere: hard to make into one or two uniform statements, 
given that we don't assume sufficiently powerful properties for trm substitution. 
So such lists would need to be maintained on an ad-hoc basis, keeping adding instances 
when needed. 
*)
lemma [simp]: 
(* *)
"n \<in> num \<Longrightarrow> subst (PPf (Var yy) (Var xx)) n xx = PPf (Var yy) n"
"m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (PPf (Var yy) m) n yy = PPf n m"
"n \<in> num \<Longrightarrow> subst (PPf (Var yy) (Var xx)) n yy = PPf n (Var xx)"
"m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (PPf m (Var xx)) n xx = PPf m n"
"m \<in> num \<Longrightarrow> subst (PPf (Var zz) (Var xx')) m zz = PPf m (Var xx')"
"m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (PPf m (Var xx')) n xx' = PPf m n"
"n \<in> num \<Longrightarrow> subst (PPf (Var zz) (Var xx')) n xx' = PPf (Var zz) n"
"m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (PPf (Var zz) n) m zz = PPf m n"
  by (auto simp add: PPf_def2 Fvars_subst subst2_fresh_switch) 
    
(* *)

lemma B_consistent_prfOf_iff_PPf: 
"B.consistent \<Longrightarrow> prf \<in> proof \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<longrightarrow> prfOf prf \<phi> \<longleftrightarrow> bprv (PPf (encPf prf) \<langle>\<phi>\<rangle>)"
  unfolding B.consistent_def3 using not_prfOf_PPf[of "prf" \<phi>] prfOf_PPf[of "prf" \<phi>] by force

lemma consistent_prfOf_iff_PPf: 
"consistent \<Longrightarrow> prf \<in> proof \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<longrightarrow> prfOf prf \<phi> \<longleftrightarrow> bprv (PPf (encPf prf) \<langle>\<phi>\<rangle>)"
  using B_consistent_prfOf_iff_PPf[OF dwf_dwfd.consistent_B_consistent] . 

(* Defining the representation of provability from that of proofs: *)

definition P :: "'fmla" where "P \<equiv> exi yy (PPf (Var yy) (Var xx))"

lemma P[simp,intro!]: "P \<in> fmla" and Fvars_P[simp]: "Fvars P = {xx}"
  unfolding P_def by (auto simp: PPf_def2)

(* We infer very-weak representability of provability from representability of proofs. 
(Actually, only the very-weak representability of the latter is needed for this task.) *)
lemma HBL1: 
assumes \<phi>: "\<phi> \<in> fmla" "Fvars \<phi> = {}" and p\<phi>: "prv \<phi>"
shows "bprv (subst P \<langle>\<phi>\<rangle> xx)"
proof- 
  obtain "prf" where pf: "prf \<in> proof" and "prfOf prf \<phi>" using prv_prfOf assms by auto  
  hence 0: "bprv (PPf (encPf prf) (enc \<phi>))"  
    using prfOf_PPf \<phi> by auto 
  have 1: "subst (subst Pf (encPf prf) yy) \<langle>\<phi>\<rangle> xx = subst (subst Pf \<langle>\<phi>\<rangle> xx) (substT (encPf prf) \<langle>\<phi>\<rangle> xx) yy" 
    apply(rule subst_compose_diff) using assms pf by auto
  show ?thesis using 0 unfolding P_def using assms 
    by (auto simp: PPf_def2 1 pf intro!: B.prv_exiI[of _ _ "encPf prf"]) 
qed

(* Used in several places, including the hard half of 
Godel I, the proof of Godel's formula's truth and the hard half of Godel-Rosser I  *)
lemma not_prv_prv_neg_PPf:
assumes [simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}" and p: "\<not> prv \<phi>" and n[simp]: "n \<in> num"
shows "bprv (neg (PPf n \<langle>\<phi>\<rangle>))"
proof-
  have "\<forall>prf\<in>proof. \<not> prfOf prf \<phi>" using prv_prfOf p by auto
  hence "\<forall>prf\<in>proof. bprv (neg (PPf (encPf prf) \<langle>\<phi>\<rangle>))" using not_prfOf_PPf by auto
  thus ?thesis using not_prfOf_PPf using PPf_encPf by (cases "n \<in> encPf ` proof") auto 
qed

lemma consistent_not_prv_not_prv_PPf:
assumes c: consistent 
and 0[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}" "\<not> prv \<phi>" "n \<in> num"
shows "\<not> bprv (PPf n \<langle>\<phi>\<rangle>)"
  using not_prv_prv_neg_PPf[OF 0] c[THEN dwf_dwfd.consistent_B_consistent] unfolding B.consistent_def3 by auto


end \<comment> \<open>context Repr_Proofs\<close>

sublocale Repr_Proofs < wrepr: WRepr_Provability 
  where P = P
  apply standard using HBL1 by auto


context Repr_Proofs
begin

lemma PP_PPf: 
assumes "\<phi> \<in> fmla"
shows "wrepr.PP \<langle>\<phi>\<rangle> = exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)"
by (metis FvarsT_Var FvarsT_num Var wrepr.PP_def PPf_def2 P_def Pf assms 
 empty_iff enc in_num inj_Variable insert_iff nat.distinct(1) subst_exi subst_same_Var xx yy)

(* The reverse HLB1 condition follows from a standard notion of \<omega>consistency for bprv
and strong representability of proofs:  *) 
lemma \<omega>consistentStd1_HBL1_rev: 
assumes oc: "B.\<omega>consistentStd1"
and \<phi>[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}"
and iPP: "bprv (wrepr.PP \<langle>\<phi>\<rangle>)"
shows "prv \<phi>"
proof-
  have 0: "bprv (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>))" using iPP by (simp add: PP_PPf) 
  {assume "\<not> prv \<phi>" 
   hence "\<forall>n \<in> num. bprv (neg (PPf n \<langle>\<phi>\<rangle>))" using not_prv_prv_neg_PPf by auto
   hence "\<not> bprv (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>))" 
   using oc unfolding B.\<omega>consistentStd1_def using \<phi> by auto 
   hence False using 0 by simp
  } 
  thus ?thesis by auto 
qed

 
end \<comment> \<open>context Repr_Proofs\<close>

(*<*)
end
(*>*)