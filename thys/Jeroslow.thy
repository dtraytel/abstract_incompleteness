theory Jeroslow imports 
Abstract_Representability Diagonalization PseudoTerms
begin 

(* The Jeroslow assumptions: *)
(*****************************)

locale Jeroslow_Diagonalization = 
Deduct_with_False_Disj_Rename
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  prv 
+
Encode
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv prv
  enc 
(* +
TermEncode
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv prv
  Ops tenc  *)
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and eql cnj imp all exi 
and fls 
and dsj
and num
and prv 
and enc ("\<langle>_\<rangle>")  
+   
fixes F :: "('trm \<Rightarrow> 'trm) set"
  and encF :: "('trm \<Rightarrow> 'trm) \<Rightarrow> 'fmla" 
  and N :: "'trm \<Rightarrow> 'trm"
  and ssap :: "'fmla \<Rightarrow> 'trm \<Rightarrow> 'trm"  
(*  *)
assumes 
(* For the members f of F, we only care about their action on numerals: *)
F[simp,intro!]: "\<And> f n. f \<in> F \<Longrightarrow> n \<in> num \<Longrightarrow> f n \<in> num"
and
encF[simp,intro!]: "\<And> f. f \<in> F \<Longrightarrow> encF f \<in> ptrm (Suc 0)"
and 
N[simp,intro!]: "N \<in> F" 
and 
ssap[simp]: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {inp} \<Longrightarrow> ssap \<phi> \<in> F"
(*  *)
and 
ReprF: "\<And>f n. f \<in> F \<Longrightarrow> n \<in> num \<Longrightarrow> prveqlPT (instInp (encF f) n) (f n)"
and
CapN: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> N \<langle>\<phi>\<rangle> = \<langle>neg \<phi>\<rangle>"
and  
CapSS: (* We consider formulas \<psi> of one variable, called "inp": *)
"\<And> \<psi> f. \<psi> \<in> fmla \<Longrightarrow> Fvars \<psi> = {inp} \<Longrightarrow> f \<in> F \<Longrightarrow> 
    ssap \<psi> \<langle>encF f\<rangle> = \<langle>cmpP \<psi> 0 (instInp (encF f) \<langle>encF f\<rangle>)\<rangle>" 
begin 

lemma encF_fmla[simp,intro!]: "\<And> f. f \<in> F \<Longrightarrow> encF f \<in> fmla"
by auto

lemma enc_trm: "\<phi> \<in> fmla \<Longrightarrow> \<langle>\<phi>\<rangle> \<in> trm"
by auto
  

definition \<tau>J :: "'fmla \<Rightarrow> 'fmla" where 
"\<tau>J \<psi> \<equiv> instInp (encF (ssap \<psi>)) (\<langle>encF (ssap \<psi>)\<rangle>)"

definition \<phi>J :: "'fmla \<Rightarrow> 'fmla" where 
"\<phi>J \<psi> \<equiv> cmpP \<psi> 0 (\<tau>J \<psi>)" 

lemma \<tau>J[simp]: 
assumes "\<psi> \<in> fmla" and "Fvars \<psi> = {inp}"
shows "\<tau>J \<psi> \<in> ptrm 0"
unfolding \<tau>J_def apply(rule instInp)
using assms by auto

lemma \<tau>J_fmla[simp]: 
assumes "\<psi> \<in> fmla" and "Fvars \<psi> = {inp}"
shows "\<tau>J \<psi> \<in> fmla"
using \<tau>J[OF assms] unfolding ptrm_def by auto

lemma FvarsT_\<tau>J[simp]: 
assumes "\<psi> \<in> fmla" and "Fvars \<psi> = {inp}"
shows "Fvars (\<tau>J \<psi>) = {out}"
using \<tau>J[OF assms] unfolding ptrm_def by auto

lemma \<phi>J[simp]: 
assumes "\<psi> \<in> fmla" and "Fvars \<psi> = {inp}"
shows "\<phi>J \<psi> \<in> fmla"
unfolding \<phi>J_def apply(rule cmpP_fmla)
using assms by auto

lemma Fvars_\<phi>J[simp]: 
assumes "\<psi> \<in> fmla" and "Fvars \<psi> = {inp}"
shows "Fvars (\<phi>J \<psi>) = {}"
using assms unfolding \<phi>J_def by (auto simp: Fvars_cmpP2)

lemma diagonalization: 
assumes \<psi>[simp]: "\<psi> \<in> fmla" and [simp]: "Fvars \<psi> = {inp}"
shows "prveqlPT (\<tau>J \<psi>) \<langle>cmpP \<psi> 0 (\<tau>J \<psi>)\<rangle> \<and> 
       prv (eqv (\<phi>J \<psi>) (instInp \<psi> \<langle>\<phi>J \<psi>\<rangle>))"
proof 
  define f where "f \<equiv> ssap \<psi>" 
  have f[simp]: "f \<in> F" unfolding f_def using assms by auto
  have ff: "f \<langle>encF f\<rangle> = \<langle>cmpP \<psi> 0 (\<tau>J \<psi>)\<rangle>"
  using assms unfolding f_def \<tau>J_def by (intro CapSS) auto

  show "prveqlPT (\<tau>J \<psi>) \<langle>cmpP \<psi> 0 (\<tau>J \<psi>)\<rangle>" 
  using ReprF[OF f, of "\<langle>encF f\<rangle>"]  
  unfolding \<tau>J_def[of \<psi>, unfolded f_def[symmetric],symmetric] ff[symmetric]
  by auto 
  from prveqlPT_prv_instInp_eqv_cmpP[OF \<psi>, of "\<tau>J \<psi>", OF _ _ _ _ this,
           unfolded \<phi>J_def[symmetric]]
  show "prv (eqv (\<phi>J \<psi>) (instInp \<psi> \<langle>\<phi>J \<psi>\<rangle>))"
  by auto  
qed 


end \<comment> \<open>context Jeroslow_Diagonalization\<close>

context WRepr_Provability 
begin

(* Changing the variable (from xx to inp) in the provability predicate: *)
definition "Pinp \<equiv> subst P (Var inp) xx"
lemma PP_Pinp: "t \<in> trm \<Longrightarrow> PP t = instInp Pinp t"
unfolding PP_def Pinp_def instInp_def by auto

end (* context WRepr_Provability  *)

locale Jeroslow_Godel_Second =  
Jeroslow_Diagonalization 
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  dsj
  num
  prv 
  enc    
  F encF N ssap
+
WRepr_Provability
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv prv
  enc
  P
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and eql cnj imp all exi 
and fls 
and dsj
and num
and prv 
and enc ("\<langle>_\<rangle>")  
and P
and F encF N ssap
+ 
assumes  
SHBL3: "\<And>\<tau>. \<tau> \<in> ptrm 0 \<Longrightarrow> prv (imp (cmpP Pinp 0 \<tau>) (instInp Pinp \<langle>cmpP Pinp 0 \<tau>\<rangle>))"
begin

(* A version of HBL1 that uses the inp variable: *)
lemma HBL1_inp: 
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv \<phi> \<Longrightarrow> prv (instInp Pinp \<langle>\<phi>\<rangle>)"
unfolding Pinp_def instInp_def by (auto intro: HBL1)
  
(* Consistency formula a la Jeroslow: *)
definition jcons :: "'fmla" where 
"jcons \<equiv> all xx (neg (cnj (instInp Pinp (Var xx)) 
                           (cmpP Pinp 0 (instInp (encF N) (Var (xx))))))" 

lemma prv_eql_subst_trm3:
"x \<in> var \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> 
prv (eql t1 t2) \<Longrightarrow> prv (subst \<phi> t1 x) \<Longrightarrow> prv (subst \<phi> t2 x)"
using prv_eql_subst_trm2  
  by (meson subst prv_imp_mp) 

lemma Pinp[simp,intro!]: "Pinp \<in> fmla" 
and Fvars_Pinp[simp]: "Fvars Pinp = {inp}"
unfolding Pinp_def by (auto simp: Fvars_subst)

lemma ReprF_combineWith_CapN: 
assumes "\<phi> \<in> fmla" and "Fvars \<phi> = {}"
shows "prveqlPT (instInp (encF N) \<langle>\<phi>\<rangle>) \<langle>neg \<phi>\<rangle>" 
using assms unfolding CapN[symmetric, OF assms] by (intro ReprF) auto  
 
theorem jeroslow_godel_second: 
assumes consistent
(* Implicit unreasonable assumption under which Jeroslow's formulation works: *)
assumes unreasonable:
        "let \<psi> = cmpP Pinp (Suc 0) (encF N); 
             \<tau> = \<tau>J \<psi>; 
             \<phi> = cmpP (cmpP Pinp (Suc 0) (encF N)) 0 \<tau>;  
             \<phi>' = cmpP Pinp 0 (cmpP (encF N) 0 \<tau>) 
         in prv (eql \<langle>\<phi>\<rangle> \<langle>\<phi>'\<rangle>)"
shows "\<not> prv jcons"
proof 
  assume *: "prv jcons"

  define \<psi> where "\<psi> \<equiv> cmpP Pinp (Suc 0) (encF N)"
  define \<tau> where "\<tau> \<equiv> \<tau>J \<psi>"
  define \<phi> where "\<phi> \<equiv> \<phi>J \<psi>"
  have \<psi>[simp,intro]: "\<psi> \<in> fmla" "Fvars \<psi> = {inp}" 
  unfolding \<psi>_def by (auto simp: Fvars_cmpP2) 
  have \<tau>[simp,intro]: "\<tau> \<in> ptrm 0" "\<tau> \<in> fmla" "Fvars \<tau> = {out}" 
    unfolding \<tau>_def by auto
  have [simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}" unfolding \<phi>_def by auto

  define eN\<tau> where "eN\<tau> \<equiv> cmpP (encF N) 0 \<tau>"
  have eN\<tau>[simp]: "eN\<tau> \<in> ptrm 0" "eN\<tau> \<in> fmla" "Fvars eN\<tau> = {out}"
   unfolding eN\<tau>_def by (auto simp: cmpP1 Fvars_cmpP)
  define \<phi>' where "\<phi>' \<equiv> cmpP Pinp 0 eN\<tau>" 
  have [simp]: "\<phi>' \<in> fmla" "Fvars \<phi>' = {}" unfolding \<phi>'_def by (auto simp: Fvars_cmpP)

  have \<phi>\<phi>': "prv (imp \<phi> \<phi>')" and \<phi>'\<phi>: "prv (imp \<phi>' \<phi>)" and \<phi>e\<phi>': "prv (eqv \<phi> \<phi>')"
   unfolding \<phi>_def \<phi>J_def \<phi>'_def eN\<tau>_def \<tau>_def[symmetric] unfolding \<psi>_def
   using prv_cmpP_compose[of Pinp "encF N" \<tau>] by auto

  from diagonalization[OF \<psi>]
  have "prveqlPT \<tau> \<langle>cmpP \<psi> 0 \<tau>\<rangle>" and **: "prv (eqv \<phi> (instInp \<psi> \<langle>\<phi>\<rangle>))" 
  unfolding \<tau>_def[symmetric] \<phi>_def[symmetric] by auto
  have "**1": "prv (imp \<phi> (instInp \<psi> \<langle>\<phi>\<rangle>))" "prv (imp (instInp \<psi> \<langle>\<phi>\<rangle>) \<phi>)"
   using prv_imp_eqvEL[OF _ _ **] prv_imp_eqvER[OF _ _ **] by auto

  from SHBL3[OF eN\<tau>(1)] 
  have "prv (imp (cmpP Pinp 0 eN\<tau>) (instInp Pinp \<langle>cmpP Pinp 0 eN\<tau>\<rangle>))" .
  hence "prv (imp \<phi>' (instInp Pinp \<langle>\<phi>'\<rangle>))" unfolding \<phi>'_def .
  from prv_prv_imp_trans[OF _ _ _ \<phi>\<phi>' this]
  have 0: "prv (imp \<phi> (instInp Pinp \<langle>\<phi>'\<rangle>))" by auto

  note unr = unreasonable[unfolded Let_def 
    \<phi>_def[unfolded \<phi>J_def \<tau>_def[symmetric], symmetric] \<psi>_def[symmetric] 
      \<tau>_def[symmetric] eN\<tau>_def[symmetric] \<phi>'_def[symmetric] \<phi>J_def] 

  have 1: "prv (imp \<phi> (instInp Pinp \<langle>\<phi>\<rangle>))"
  apply(rule nprv_prvI, auto)
  apply(rule nprv_impI, auto)
  apply(rule nprv_addLemmaE[OF unr], auto)
  apply(rule nprv_addImpLemmaE[OF 0], auto intro: nprv_hyp)
  apply(rule nprv_clear3_3, auto)
  apply(rule nprv_eql_substE01[of "\<langle>\<phi>\<rangle>" "\<langle>\<phi>'\<rangle>" _ "instInp Pinp (Var xx)" xx], 
     auto simp: instInp_def nprv_hyp) . 

  have 2: "prv (imp \<phi> (cnj (instInp Pinp \<langle>\<phi>\<rangle>) 
                           (instInp \<psi> \<langle>\<phi>\<rangle>)))"
  apply(rule nprv_prvI, auto)
  apply(rule nprv_impI, auto)
  apply(rule nprv_cnjI, auto)
  subgoal apply(rule nprv_addImpLemmaE[OF 1], auto intro: nprv_hyp) .
  subgoal apply(rule nprv_addImpLemmaE[OF "**1"(1)], auto intro: nprv_hyp) . .

  define z where "z \<equiv> Variable (Suc (Suc 0))" 
  have z_facts[simp]: "z \<in> var" "z \<noteq> xx" "z \<notin> Fvars Pinp"
    "out \<noteq> z \<and> z \<noteq> out" "inp \<noteq> z \<and> z \<noteq> inp" 
   unfolding z_def by auto
  have 30: "subst (cmpP Pinp 0 (instInp (encF N) (Var xx))) \<langle>\<phi>\<rangle> xx = 
            cmpP Pinp 0 (instInp (encF N) \<langle>\<phi>\<rangle>)" 
  unfolding z_def[symmetric] instInp_def cmpP_def Let_def apply auto 
  apply(subst subst_compose_diff, auto)
  apply(subst subst_subst, auto simp: Fvars_subst)
  apply(subst subst_notIn[of _ _ xx], auto simp: Fvars_subst)
  apply(subst subst_compose_diff, auto) . 

  have 31: "subst (instInp Pinp (Var xx)) \<langle>\<phi>\<rangle> xx = 
            instInp Pinp \<langle>\<phi>\<rangle>" unfolding instInp_def by auto
              

  have 3: "prv (neg (cnj (instInp Pinp \<langle>\<phi>\<rangle>) 
                         (instInp \<psi> \<langle>\<phi>\<rangle>)))"
  apply(rule nprv_prvI, auto)
  apply(rule nprv_addLemmaE[OF *, unfolded jcons_def], auto)
  apply(rule nprv_allE0[of _ _ _ "\<langle>\<phi>\<rangle>"], auto  simp: 30 31)
  apply(rule nprv_clear2_2, auto)
  apply(rule nprv_negI, auto)
  apply(rule nprv_negE0, auto)
  apply(rule nprv_clear2_2, auto)
  apply(rule nprv_cnjE0, auto)
  apply(rule nprv_clear3_3, auto)
  apply(rule nprv_cnjI, auto)
  subgoal 
    apply(auto intro: nprv_hyp) .
  subgoal 
    apply(rule nprv_clear2_1, auto)
    apply(auto simp: nprv_hyp instInp_cmpP \<psi>_def) . .

  have ***: "prv (neg \<phi>)"
  apply(rule nprv_prvI, auto) 
  apply(rule nprv_negI, auto) 
  apply(rule nprv_addImpLemmaE[OF 2], auto simp: nprv_hyp)
  apply(rule nprv_addLemmaE[OF 3], auto)
  apply(rule nprv_negE0, auto simp: nprv_hyp) .

  have 4: "prv (instInp Pinp \<langle>neg \<phi>\<rangle>)" using HBL1_inp[OF _ _ ***] by auto

  have 5: "prveqlPT (instInp (encF N) \<langle>\<phi>\<rangle>) \<langle>neg \<phi>\<rangle>"
    using ReprF_combineWith_CapN[of \<phi>] by auto

  have 6: "prv (cmpP Pinp 0 (instInp (encF N) \<langle>\<phi>\<rangle>))"
  apply(rule nprv_prvI, auto)
  apply(rule nprv_addLemmaE[OF 4], auto)
  apply(rule prveqlPT_nprv_cmpP_instInp[OF _ _ _ _ _ 5], auto simp: instInp) .

  note lem = "**1"(2)[unfolded \<psi>_def]
  have "prv \<phi>"
  apply(rule nprv_prvI, auto)
  apply(rule nprv_addLemmaE[OF 6], auto)
  apply(rule nprv_addImpLemmaE[OF lem], auto simp: nprv_hyp instInp_cmpP) .

  from this *** `consistent` show False unfolding consistent_def3 by auto
qed   
   
 
 

end \<comment> \<open>context Jeroslow_Godel_Second\<close>

 
 
end 

