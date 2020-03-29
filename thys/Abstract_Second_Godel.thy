theory Abstract_Second_Godel imports Abstract_First_Godel Derivability_Conditions
begin

(* We assume all three derivability conditions, and the Godel Formula: *)
locale Godel_Second_Assumptions = 
Deriv_Cond
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi 
  prv bprv
  enc
  P
+
Godel_Form  
  var trm fmla Var num FvarsT substT Fvars subst
  eql cnj imp all exi 
  fls
  prv bprv
  enc
  S
  P
for 
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set" 
and Var FvarsT substT Fvars subst  
and num
and eql cnj imp all exi 
and prv bprv
and enc ("\<langle>_\<rangle>")
and S 
and P 
and fls
begin 

lemma P_G:
"bprv (imp (PP \<langle>\<phi>G\<rangle>) (PP \<langle>fls\<rangle>))"
proof-
  have 0: "prv (imp \<phi>G (neg (PP \<langle>\<phi>G\<rangle>)))" 
  using prv_\<phi>G_eqv by (intro prv_imp_eqvEL) auto
  have 1: "bprv (PP \<langle>imp \<phi>G (neg (PP \<langle>\<phi>G\<rangle>))\<rangle>)"
  using HBL1_PP[OF _ _ 0] by simp 
  have 2: "bprv (imp (PP \<langle>\<phi>G\<rangle>) (PP \<langle>neg (PP \<langle>\<phi>G\<rangle>)\<rangle>))" 
  using HBL2_imp2[OF _ _  _ _ 1] by simp
  have 3: "bprv (imp (PP \<langle>\<phi>G\<rangle>) (PP \<langle>PP \<langle>\<phi>G\<rangle>\<rangle>))" 
    using HBL3[OF \<phi>G] by simp
  have 23: "bprv (imp (PP \<langle>\<phi>G\<rangle>)
                      (cnj (PP \<langle>PP \<langle>\<phi>G\<rangle>\<rangle>) 
                           (PP \<langle>neg (PP \<langle>\<phi>G\<rangle>)\<rangle>)))"
  using B.prv_imp_cnj[OF _ _ _ 3 2] by simp
  have 4: "bprv (imp (cnj (PP \<langle>PP \<langle>\<phi>G\<rangle>\<rangle>) 
                          (PP \<langle>neg (PP \<langle>\<phi>G\<rangle>)\<rangle>)) 
                     (PP \<langle>fls\<rangle>))" 
    using HBL2[of "PP \<langle>\<phi>G\<rangle>" fls] unfolding neg_def[symmetric] by simp
  show ?thesis using B.prv_prv_imp_trans[OF _ _ _ 23 4] by simp
qed 

(* First the "direct", positive formulation: *)
lemma godel_second_pos:
assumes "prv (neg (PP \<langle>fls\<rangle>))"
shows "prv fls"
proof- 
  note PG = bprv_prv[OF _ _ P_G, simplified]
  have "prv (neg (PP \<langle>\<phi>G\<rangle>))" 
  using PG assms unfolding neg_def by (rule prv_prv_imp_trans[rotated 3]) auto 
  hence "prv \<phi>G" using prv_\<phi>G_eqv by (rule prv_eqv_prv_rev[rotated 2]) auto
  thus ?thesis 
  (* the only part of Godel's first theorem that is needed: *) 
  using godel_first_theEasyHalf_pos by simp
qed

(* Then the more standard, counterpositive formulation: *)
theorem godel_second:
"consistent \<Longrightarrow> \<not> prv (neg (PP \<langle>fls\<rangle>))"
using godel_second_pos unfolding consistent_def by auto


(* 
It is an immediate consequence of Godel II and HLB1 and HLB2 that 
(assuming consistency) 
prv (neg PP \<langle>\<phi>\<rangle>) holds for _no_ sentence, provable or not. 
The theory is omniscient about what it can prove (thanks to HLB1), 
but completely ignorant about what it cannot prove. 
*)

corollary not_prv_neg_PP:
assumes c: "consistent" and [simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}"
shows "\<not> prv (neg (PP \<langle>\<phi>\<rangle>))"  
proof
  assume 0: "prv (neg (PP \<langle>\<phi>\<rangle>))"  
  have "prv (imp fls \<phi>)" by simp
  hence "bprv (PP \<langle>imp fls \<phi>\<rangle>)" by (intro HBL1_PP) auto
  hence "bprv (imp (PP \<langle>fls\<rangle>) (PP \<langle>\<phi>\<rangle>))" by (intro HBL2_imp2) auto
  hence "bprv (imp (neg (PP \<langle>\<phi>\<rangle>)) (neg (PP \<langle>fls\<rangle>)))" by (intro B.prv_imp_neg_rev) auto  
  from prv_imp_mp[OF _ _ bprv_prv[OF _ _ this, simplified] 0, simplified] 
  have "prv (neg (PP \<langle>fls\<rangle>))" . 
  thus False using godel_second[OF c] by simp
qed

  

end \<comment> \<open>Godel_Second_Assumptions\<close>
 
end 



