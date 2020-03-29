(* Abstract notion of standard model and truth  *)
theory Standard_Model imports Abstract_Representability
begin 


(* Truth in a standard model *)
(* First some minimal assumptions, involving only imp and all: *)
locale Minimal_Truth = 
Syntax_with_Numerals_and_Connectives_False_Disj 
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and eql cnj imp all exi 
and fls
and dsj
and num  
+
(* The notion of truth for sentences: *)
fixes isTrue :: "'fmla \<Rightarrow> bool"
assumes   
not_isTrue_fls: "\<not> isTrue fls"
and 
isTrue_imp: 
"\<And>\<phi> \<psi>. \<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> Fvars \<psi> = {} \<Longrightarrow> 
  isTrue \<phi> \<Longrightarrow> isTrue (imp \<phi> \<psi>) \<Longrightarrow> isTrue \<psi>"
and
isTrue_all: 
"\<And>x \<phi>. x \<in> var \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {x} \<Longrightarrow> 
  (\<forall> n \<in> num. isTrue (subst \<phi> n x)) \<Longrightarrow> isTrue (all x \<phi>)"
and 
isTrue_exi: 
"\<And>x \<phi>. x \<in> var \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {x} \<Longrightarrow> 
  isTrue (exi x \<phi>) \<Longrightarrow> (\<exists> n \<in> num. isTrue (subst \<phi> n x))"
and 
isTrue_neg: 
"\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> 
  isTrue \<phi> \<or> isTrue (neg \<phi>)"
begin

lemma isTrue_neg_excl:
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow>   
 isTrue \<phi> \<Longrightarrow> isTrue (neg \<phi>) \<Longrightarrow> False"
  using isTrue_imp not_isTrue_fls unfolding neg_def by auto

lemma isTrue_neg_neg: 
assumes "\<phi> \<in> fmla" "Fvars \<phi> = {}"
and "isTrue (neg (neg \<phi>))"
shows "isTrue \<phi>"
using assms isTrue_neg isTrue_neg_excl by fastforce

end \<comment> \<open>context  Minimal_Truth\<close>

  

locale Minimal_Truth_Soundness = 
Minimal_Truth 
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  isTrue
+
B : Deduct_with_False_Disj
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
and bprv
and isTrue 
+
assumes 
(* We assume soundness of the provability for sentences (w.r.t. truth): *)
prv_sound_isTrue: 
"\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> 
  bprv \<phi> \<Longrightarrow> isTrue \<phi>"
begin

(* For sound theories, consistency is a fact rather than a hypothesis *)
lemma B_consistent: B.consistent
  unfolding B.consistent_def using not_isTrue_fls prv_sound_isTrue by blast

lemma prv_neg_excl:
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> 
  bprv \<phi> \<Longrightarrow> bprv (neg \<phi>) \<Longrightarrow> False"
  using isTrue_neg_excl[of \<phi>] prv_sound_isTrue by auto

lemma prv_imp_implies_isTrue: 
assumes [simp,intro!]: "\<phi> \<in> fmla" "\<chi> \<in> fmla" "Fvars \<phi> = {}" "Fvars \<chi> = {}"
and p: "bprv (imp \<phi> \<chi>)" and i: "isTrue \<phi>"
shows "isTrue \<chi>" 
proof-
  have "isTrue (imp \<phi> \<chi>)" using p by (intro prv_sound_isTrue) auto
  thus ?thesis using assms isTrue_imp by blast
qed

(* Sound theories are not only consistent, but also \<omega>consistent 
(in the strong, intuitionistic sense): *)
lemma B_\<omega>consistent: B.\<omega>consistent 
unfolding B.\<omega>consistent_def proof (safe del: notI)
  fix \<phi> x assume 0[simp,intro]: "\<phi> \<in> fmla"  "x \<in> var" and 1: "Fvars \<phi> = {x}"
  and 00: "\<forall>n\<in>num. bprv (neg (subst \<phi> n x))"
  hence "\<forall>n\<in>num. isTrue (neg (subst \<phi> n x))" 
    using 00 1 by (auto intro!: prv_sound_isTrue simp: Fvars_subst)
  hence "isTrue (all x (neg \<phi>))" by (simp add: "1" isTrue_all) 
  moreover 
  {have "bprv (imp (all x (neg \<phi>)) (neg (exi x \<phi>)))"  
    using B.prv_all_neg_imp_neg_exi by blast
   hence "isTrue (imp (all x (neg \<phi>)) (neg (exi x \<phi>)))"
    by (simp add: "1" prv_sound_isTrue)
  }
  ultimately have "isTrue (neg (exi x \<phi>))"
    by (metis 0 1 Diff_insert_absorb Fvars_all Fvars_exi Fvars_neg all
      exi insert_absorb insert_not_empty isTrue_imp neg)
  hence "\<not> isTrue (neg (neg (exi x \<phi>)))"  
    using 1 isTrue_neg_excl by force 
  thus "\<not> bprv (neg (neg (exi x \<phi>)))"  
    using "1" prv_sound_isTrue by auto 
qed 

lemma B_\<omega>consistentStd1: B.\<omega>consistentStd1
  using B_\<omega>consistent B.\<omega>consistent_impliesStd1 by blast

lemma B_\<omega>consistentStd2: B.\<omega>consistentStd2
  using B_\<omega>consistent B.\<omega>consistent_impliesStd2 by blast

end 


locale Minimal_Truth_Soundness_Proof_Repr = 
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
+ 
Minimal_Truth_Soundness
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  bprv
  isTrue
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and eql cnj imp all exi 
and fls
and dsj
and num
and prv bprv
and isTrue 
and enc ("\<langle>_\<rangle>") 
and "proof" :: "'proof set" and prfOf   
and encPf Pf 
begin


(* lemmas not_prv_not_prv_PPf = consistent_not_prv_not_prv_PPf[OF consistent] *)
lemmas prfOf_iff_PPf = B_consistent_prfOf_iff_PPf[OF B_consistent]
 
(* The provability predicate is decided by prv on encodings 
(just like with any predicate that "represents")   *)
lemma isTrue_prv_PPf_prf_or_neg: 
"prf \<in> proof \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> 
    bprv (PPf (encPf prf) \<langle>\<phi>\<rangle>) \<or> bprv (neg (PPf (encPf prf) \<langle>\<phi>\<rangle>))"
  using not_prfOf_PPf prfOf_PPf by blast

(* Hence that predicate is complete w.r.t. truth  *)
lemma isTrue_implies_prv_PPf_prf: 
"prf \<in> proof \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> 
   isTrue (PPf (encPf prf) \<langle>\<phi>\<rangle>) \<Longrightarrow> bprv (PPf (encPf prf) \<langle>\<phi>\<rangle>)"
  by (metis FvarsT_num Fvars_PPf Fvars_fls PPf 
Un_empty empty_iff enc encPf fls in_num isTrue_prv_PPf_prf_or_neg 
neg_def not_isTrue_fls prv_imp_implies_isTrue) 

(* ... and thanks to cleanness we can replace encoded proofs 
with arbitrary numerals in the completeness property:  *)
lemma isTrue_implies_prv_PPf: 
assumes [simp]: "n \<in> num" "\<phi> \<in> fmla" "Fvars \<phi> = {}" 
and iT: "isTrue (PPf n \<langle>\<phi>\<rangle>)"
shows "bprv (PPf n \<langle>\<phi>\<rangle>)" 
proof(cases "n \<in> encPf ` proof")
  case True  
  thus ?thesis  
    using iT isTrue_implies_prv_PPf_prf by auto  
next
  case False
  hence "bprv (neg (PPf n \<langle>\<phi>\<rangle>))" by (simp add: PPf_encPf)
  hence "isTrue (neg (PPf n \<langle>\<phi>\<rangle>))" by (intro prv_sound_isTrue) auto
  hence False using iT by (intro isTrue_neg_excl) auto
  thus ?thesis by auto
qed

(* In fact, by soundness we even have an iff: *)
lemma isTrue_iff_prv_PPf: 
"\<And> n \<phi>. n \<in> num \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> isTrue (PPf n \<langle>\<phi>\<rangle>) \<longleftrightarrow> bprv (PPf n \<langle>\<phi>\<rangle>)"
using isTrue_implies_prv_PPf  
using exists_no_Fvars not_isTrue_fls prv_sound_isTrue by auto

(*  Truth of the provability representation implies provability: *)
lemma isTrue_PP_implies_prv: 
assumes \<phi>[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}"
and iPP: "isTrue (wrepr.PP \<langle>\<phi>\<rangle>)"
shows "prv \<phi>"
proof-
  have "isTrue (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>))" using iPP unfolding PP_PPf[OF \<phi>(1)] .
  from isTrue_exi[OF _ _ _ this] 
  obtain n where n[simp]: "n \<in> num" and "isTrue (PPf n \<langle>\<phi>\<rangle>)" by auto
  hence pP: "bprv (PPf n \<langle>\<phi>\<rangle>)" using isTrue_implies_prv_PPf by auto
  hence "\<not> bprv (neg (PPf n \<langle>\<phi>\<rangle>))"  
  using prv_neg_excl[of "PPf n \<langle>\<phi>\<rangle>"] by auto 
  then obtain "prf" where "prf"[simp]: "prf \<in> proof" and nn: "n = encPf prf"  
  using assms n PPf_encPf \<phi>(1) by blast
  have "prfOf prf \<phi>" using pP unfolding nn using prfOf_iff_PPf by auto
  thus ?thesis using prv_prfOf by auto 
qed

(* The reverse HBL1 (now without the \<omega>consistencyStd assumption which holds here 
thanks to our truth-in-standard-model assumption) *)


lemmas HBL1_rev = \<omega>consistentStd1_HBL1_rev[OF B_\<omega>consistentStd1]
(* Note: Would also follow by soundness from isTrue_PP_implies_prv *)

end \<comment> \<open>Minimal_Truth_Soundness_Proof_Repr\<close>



(* Next: Proof recovery from HBL1_iff *)

locale Minimal_Truth_Soundness_HBL1iff_Compl_Pf = 
WRepr_Provability
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv bprv 
  enc 
  P
+
Minimal_Truth_Soundness
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  bprv
  isTrue
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
and enc ("\<langle>_\<rangle>") 
and prv bprv 
and P
and isTrue
+ 
fixes Pf :: 'fmla
assumes
(* Pf is a formula with free variables xx yy  *)
Pf[simp,intro!]: "Pf \<in> fmla"
and 
Fvars_Pf[simp]: "Fvars Pf = {yy,xx}"
and 
(* P relates to Pf internally just like a prv and a proofOf would 
relate: via an existential *)
P_Pf:
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow>
 let PPf = (\<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]) in 
 bprv (eqv (subst P \<langle>\<phi>\<rangle> xx) (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)))"
assumes 
(* We assume both HBL1 and HBL1_rev, i.e., an iff version: *)
HBL1_iff: "\<And> \<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> bprv (PP \<langle>\<phi>\<rangle>) \<longleftrightarrow> prv \<phi>"
and 
Compl_Pf: 
"\<And> n \<phi>. n \<in> num \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> 
 let PPf = (\<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]) in 
 isTrue (PPf n \<langle>\<phi>\<rangle>) \<longrightarrow> bprv (PPf n \<langle>\<phi>\<rangle>)"
begin  
  
definition PPf where "PPf \<equiv> \<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]"

lemma PP_deff: "PP t = subst P t xx" using PP_def by auto

lemma PP_PPf_eqv: 
  "\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> bprv (eqv (PP \<langle>\<phi>\<rangle>) (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)))"
  using PP_deff PPf_def P_Pf by auto

(*  *)
 
lemma PPf[simp,intro!]: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> xx \<notin> FvarsT t1 \<Longrightarrow> PPf t1 t2 \<in> fmla"
  unfolding PPf_def by auto

lemma PPf_def2: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> xx \<notin> FvarsT t1 \<Longrightarrow> 
  PPf t1 t2 = subst (subst Pf t1 yy) t2 xx"
  unfolding PPf_def by (rule psubst_eq_rawpsubst2[simplified]) auto

lemma Fvars_PPf[simp]: 
"t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> xx \<notin> FvarsT t1 \<Longrightarrow> 
 Fvars (PPf t1 t2) = FvarsT t1 \<union> FvarsT t2"
by (auto simp add: PPf_def2 Fvars_subst subst2_fresh_switch)

lemma [simp]: 
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

lemma PP_PPf: 
assumes "\<phi> \<in> fmla" "Fvars \<phi> = {}" shows "bprv (PP \<langle>\<phi>\<rangle>) \<longleftrightarrow> bprv (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>))"
  using assms PP_PPf_eqv[OF assms] B.prv_eqv_sym[OF _ _ PP_PPf_eqv[OF assms]]
  apply safe apply(rule B.prv_eqv_prv[of "PP \<langle>\<phi>\<rangle>" "exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)"])
  apply simp_all 
  apply(rule B.prv_eqv_prv[of "exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)" "PP \<langle>\<phi>\<rangle>" ]) by auto

lemma isTrue_implies_prv_PPf: 
"\<And> n \<phi>. n \<in> num \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow>  
 isTrue (PPf n \<langle>\<phi>\<rangle>) \<Longrightarrow> bprv (PPf n \<langle>\<phi>\<rangle>)"
  using Compl_Pf by(simp add: PPf_def)

lemma isTrue_iff_prv_PPf: 
"\<And> n \<phi>. n \<in> num \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> isTrue (PPf n \<langle>\<phi>\<rangle>) \<longleftrightarrow> bprv (PPf n \<langle>\<phi>\<rangle>)"
using isTrue_implies_prv_PPf  
  using exists_no_Fvars not_isTrue_fls prv_sound_isTrue by auto



(*  *)
 
(* Preparing to instantiate this alternative into the mainstream locale hierarchy: 
We define the "missing" proofs to be numerals, we encode them as the identity, 
and we "copy" prfOf from the corresponding predicate one-level-up, PPf.
*) 
definition "proof" :: "'trm set" where [simp]: "proof = num"
definition prfOf :: "'trm \<Rightarrow> 'fmla \<Rightarrow> bool" where   
  "prfOf n \<phi> \<equiv> bprv (PPf n \<langle>\<phi>\<rangle>)"  
definition encPf :: "'trm \<Rightarrow> 'trm" where [simp]: "encPf \<equiv> id"
(*  *)

lemma prv_exi_PPf_iff_isTrue:
assumes [simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}"  
shows "bprv (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)) \<longleftrightarrow> isTrue (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>))" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L thus ?R by (intro prv_sound_isTrue) auto
next
  assume ?R 
  obtain n where n[simp]: "n \<in> num" and i: "isTrue (PPf n \<langle>\<phi>\<rangle>)" using isTrue_exi[OF _ _ _ `?R`] by auto
  hence "bprv (PPf n \<langle>\<phi>\<rangle>)" by (auto simp: isTrue_iff_prv_PPf)
  thus ?L by (intro B.prv_exiI[of _ _ n]) auto
qed

lemma isTrue_exi_iff:
assumes [simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}"  
shows "isTrue (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)) \<longleftrightarrow> (\<exists>n\<in>num. isTrue (PPf n \<langle>\<phi>\<rangle>))" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L thus ?R using isTrue_exi[OF _ _ _ `?L`] by auto
next
  assume ?R
  then obtain n where n[simp]: "n \<in> num" and i: "isTrue (PPf n \<langle>\<phi>\<rangle>)" by auto
  hence "bprv (PPf n \<langle>\<phi>\<rangle>)" by (auto simp: isTrue_iff_prv_PPf)
  hence "bprv (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>))" by (intro B.prv_exiI[of _ _ n]) auto
  thus ?L by (intro prv_sound_isTrue) auto
qed

lemma prv_prfOf: 
assumes "\<phi> \<in> fmla" "Fvars \<phi> = {}"  
shows "prv \<phi> \<longleftrightarrow> (\<exists>n\<in>num. prfOf n \<phi>)"
proof-
  have "prv \<phi> \<longleftrightarrow> bprv (PP \<langle>\<phi>\<rangle>)" using HBL1_iff[OF assms] by simp
  also have "\<dots> \<longleftrightarrow> bprv (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>))" unfolding PP_PPf[OF assms] ..
  also have "\<dots> \<longleftrightarrow> isTrue (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>))" using prv_exi_PPf_iff_isTrue[OF assms] .
  also have "\<dots> \<longleftrightarrow> (\<exists>n\<in>num. isTrue (PPf n \<langle>\<phi>\<rangle>))" using isTrue_exi_iff[OF assms] .
  also have "\<dots> \<longleftrightarrow> (\<exists>n\<in>num. bprv (PPf n \<langle>\<phi>\<rangle>))" using isTrue_iff_prv_PPf[OF _ assms] by auto
  also have "\<dots> \<longleftrightarrow> (\<exists>n\<in>num. prfOf n \<phi>)" unfolding prfOf_def ..
  finally show ?thesis .
qed 

lemma prfOf_prv_Pf: 
assumes "n \<in> num" and "\<phi> \<in> fmla" "Fvars \<phi> = {}" and "prfOf n \<phi>"
shows "bprv (psubst Pf [(n, yy), (\<langle>\<phi>\<rangle>, xx)])" 
using assms unfolding prfOf_def by (auto simp: PPf_def2 psubst_eq_rawpsubst2) 

lemma isTrue_exi_iff_PP:
assumes [simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}"  
shows "isTrue (PP \<langle>\<phi>\<rangle>) \<longleftrightarrow> (\<exists>n\<in>num. isTrue (PPf n \<langle>\<phi>\<rangle>))"  
proof-
  have "bprv (eqv (PP \<langle>\<phi>\<rangle>) (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)))" 
    using PP_PPf_eqv by auto
  hence "bprv (imp (PP \<langle>\<phi>\<rangle>) (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)))"
  and "bprv (imp (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)) (PP \<langle>\<phi>\<rangle>))"  
  by (simp_all add: B.prv_imp_eqvEL B.prv_imp_eqvER)   
  thus ?thesis unfolding isTrue_exi_iff[OF assms, symmetric] 
  apply safe apply(rule prv_imp_implies_isTrue) apply simp_all
  apply(rule prv_imp_implies_isTrue) by simp_all
qed

end \<comment> \<open>context Minimal_Truth_Soundness_HBL1iff_Compl_Pf\<close>


locale Minimal_Truth_Soundness_HBL1iff_Compl_Pf_Compl_NegPf = 
Minimal_Truth_Soundness_HBL1iff_Compl_Pf
+
assumes    
Compl_NegPf: 
"\<And> n \<phi>. n \<in> num \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> 
 let PPf = (\<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]) in 
 isTrue (neg (PPf n \<langle>\<phi>\<rangle>)) \<longrightarrow> bprv (neg (PPf n \<langle>\<phi>\<rangle>))" 
begin

lemma isTrue_implies_prv_neg_PPf: 
"\<And> n \<phi>. n \<in> num \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow>  
 isTrue (neg (PPf n \<langle>\<phi>\<rangle>)) \<Longrightarrow> bprv (neg (PPf n \<langle>\<phi>\<rangle>))"
  using Compl_NegPf by(simp add: PPf_def) 

lemma isTrue_iff_prv_neg_PPf: 
"\<And> n \<phi>. n \<in> num \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> isTrue (neg (PPf n \<langle>\<phi>\<rangle>)) \<longleftrightarrow> bprv (neg (PPf n \<langle>\<phi>\<rangle>))"
using isTrue_implies_prv_neg_PPf  
  using exists_no_Fvars not_isTrue_fls prv_sound_isTrue by auto

lemma prv_PPf_decide: 
assumes [simp]: "n \<in> num" "\<phi> \<in> fmla" "Fvars \<phi> = {}"
and np: "\<not> bprv (PPf n \<langle>\<phi>\<rangle>)"
shows "bprv (neg (PPf n \<langle>\<phi>\<rangle>))"
proof-
  have "\<not> isTrue (PPf n \<langle>\<phi>\<rangle>)" using assms by (auto simp: isTrue_iff_prv_PPf)
  hence "isTrue (neg (PPf n \<langle>\<phi>\<rangle>))" using isTrue_neg[of "PPf n \<langle>\<phi>\<rangle>"] by auto
  thus ?thesis by (auto simp: isTrue_iff_prv_neg_PPf)
qed 

lemma not_prfOf_prv_neg_Pf: 
assumes n\<phi>: "n \<in> num" "\<phi> \<in> fmla" "Fvars \<phi> = {}" and "\<not> prfOf n \<phi>"
shows "bprv (neg (psubst Pf [(n, yy), (\<langle>\<phi>\<rangle>, xx)]))" 
  using assms prv_PPf_decide[OF n\<phi>] by (auto simp: prfOf_def  PPf_def2 psubst_eq_rawpsubst2)

end \<comment> \<open>context Minimal_Truth_Soundness_HBL1iff_Compl_Pf_Compl_NegPf\<close>

sublocale Minimal_Truth_Soundness_HBL1iff_Compl_Pf_Compl_NegPf < 
   repr: Repr_Proofs  
(* added label to avoid duplicated constant P, which is assumed 
in Minimal_Truth_Soundness_HBL1iff_Compl_Pf but defined in Repr_Proofs  
(they are of course extensionally equal).
*)
  where "proof" = "proof" and prfOf = prfOf and encPf = encPf  
  apply standard
  apply (auto simp: bprv_prv prv_prfOf prfOf_prv_Pf not_prfOf_prv_neg_Pf)
  done

(* Lemma 6 ("proof recovery") from the JAR paper: *)
sublocale Minimal_Truth_Soundness_HBL1iff_Compl_Pf_Compl_NegPf < 
  min_truth: Minimal_Truth_Soundness_Proof_Repr
where "proof" = "proof" and prfOf = prfOf and encPf = encPf
  apply standard 
  done



(* FOR THE CLASSICAL REASONING VERSION *)

locale Minimal_Truth_Soundness_HBL1iff_prv_Compl_Pf = 
WRepr_Provability
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv bprv 
  enc 
  P
+
Minimal_Truth_Soundness
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  bprv
  isTrue
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
and enc ("\<langle>_\<rangle>") 
and prv bprv 
and P
and isTrue
+ 
fixes Pf :: 'fmla
assumes
(* Pf is a formula with free variables xx yy  *)
Pf[simp,intro!]: "Pf \<in> fmla"
and 
Fvars_Pf[simp]: "Fvars Pf = {yy,xx}"
and 
(* P relates to Pf internally just like a prv and a proofOf would 
relate: via an existential *)
P_Pf:
"\<phi> \<in> fmla \<Longrightarrow>
 let PPf = (\<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]) in 
 bprv (eqv (subst P \<langle>\<phi>\<rangle> xx) (exi yy (PPf (Var yy) \<langle>\<phi>\<rangle>)))"
assumes 
(* We assume, in addition to HBL1, the strong form of HBL1_rev: *)
HBL1_rev_prv: "\<And> \<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv (PP \<langle>\<phi>\<rangle>) \<Longrightarrow> prv \<phi>"
and 
Compl_Pf: 
"\<And> n \<phi>. n \<in> num \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> 
 let PPf = (\<lambda> t1 t2. psubst Pf [(t1,yy), (t2,xx)]) in 
 isTrue (PPf n \<langle>\<phi>\<rangle>) \<longrightarrow> bprv (PPf n \<langle>\<phi>\<rangle>)"
begin 

lemma HBL1_rev: 
  assumes f: "\<phi> \<in> fmla" and fv: "Fvars \<phi> = {}" and bp: "bprv (PP \<langle>\<phi>\<rangle>)"
  shows "prv \<phi>"
  using assms by (auto intro!: HBL1_rev_prv bprv_prv[OF _ _ bp])

lemma HBL1_iff: "\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> bprv (PP \<langle>\<phi>\<rangle>) \<longleftrightarrow> prv \<phi>"
  using HBL1 HBL1_rev unfolding PP_def by auto

lemma HBL1_iff_prv: "\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv (PP \<langle>\<phi>\<rangle>) \<longleftrightarrow> prv \<phi>"
  apply safe
  using HBL1_rev_prv apply simp
  using bprv_prv HBL1_PP by auto 

end (* context Minimal_Truth_Soundness_HBL1iff_prv_Compl_Pf *)

sublocale Minimal_Truth_Soundness_HBL1iff_prv_Compl_Pf < 
mts_prv_mts: Minimal_Truth_Soundness_HBL1iff_Compl_Pf where Pf = Pf
  apply standard  
  using P_Pf HBL1_rev HBL1_PP Compl_Pf by auto


locale Minimal_Truth_Soundness_HBL1iff_prv_Compl_Pf_Classical = 
Minimal_Truth_Soundness_HBL1iff_prv_Compl_Pf
+
assumes   
(*NB: we don't really need to assume classical reasoning (double negation) all throughout, 
but only for the provability predicate: *)
classical_P: "\<And> \<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> let PP = (\<lambda>t. subst P t xx) in 
  prv (neg (neg (PP \<langle>\<phi>\<rangle>))) \<Longrightarrow> prv (PP \<langle>\<phi>\<rangle>)"
begin

lemma classical_PP: "\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv (neg (neg (PP \<langle>\<phi>\<rangle>))) \<Longrightarrow> prv (PP \<langle>\<phi>\<rangle>)"
  using classical_P unfolding PP_def by auto


end \<comment> \<open>context Minimal_Truth_Soundness_HBL1iff_Compl_Pf_Variant_Classic\<close>



  


end 
