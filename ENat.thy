(*
  Title:  Natural numbers extended with infinity
  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
  Version: Isabelle/HOL 2020
  Date:    2019
  ID:      $Id: ENat.thy 152662 2020-08-06 09:54:41Z tklenze $
*)

section \<open>Extended natural numbers\<close> 

theory ENat
imports
   "HOL-Library.BNF_Corec" Main 
begin

subsection \<open>Type definition\<close>  

codatatype enat =
    Zero 
  | Succ (pred: enat)

thm enat.coinduct

primcorec infty :: enat ("\<infinity>") where
  "infty = Succ infty"           


subsection \<open>Addition\<close>

primcorec eplus :: "enat \<Rightarrow> enat \<Rightarrow> enat" where
  "eplus x y = (if x = Zero then y else Succ (eplus (pred x) y))"
 
thm eplus.code 
thm eplus.simps
thm eplus.ctr


text \<open>Basic equalities\<close>

lemma eplus_Zero [simp]: "eplus Zero x = x"
  by (simp add: eplus.code)

lemma eplus_Succ [simp]: "eplus (Succ x) y = Succ (eplus x y)"
  by (simp add: eplus.ctr)

lemma eplus_Zero_right [simp]: "eplus x Zero = x"
proof (coinduction arbitrary: x rule: enat.coinduct)
  case Eq_enat
  then show ?case by (simp)
qed

lemma eplus_Succ_right: "eplus x (Succ y) = Succ (eplus x y)"
proof (coinduction arbitrary: x rule: enat.coinduct_strong)
  case Eq_enat
  then show ?case 
    by (simp_all, cases x) (auto)
qed


text \<open>Instantiate additive commutative monoid type class.\<close>

instantiation enat :: comm_monoid_add 
begin 

definition zero_enat_def:
  "0 \<equiv> Zero"

definition plus_enat_def:
  "x + y \<equiv> eplus x y"

instance proof
  fix a b c::enat
  show "a + b + c = a + (b + c)"
  proof (coinduction arbitrary: a rule: enat.coinduct_strong)
    case Eq_enat
    then show ?case by (auto simp add: plus_enat_def)      (* magically .... *)
  qed
next
  fix a b::enat 
  show "a + b = b + a"
  proof (coinduction arbitrary: b rule: enat.coinduct_strong)
    case Eq_enat
    then show ?case 
      apply (auto simp add: plus_enat_def)
      apply (cases a, auto)
      apply (cases b, auto simp add: eplus_Succ_right)
      done
  qed
next
  fix a::enat
  show "0 + a = a"
    by (simp add: zero_enat_def plus_enat_def)
qed

end

text \<open>Declare plus as a friend for corecursive function definitions.\<close>

friend_of_corec plus :: "enat \<Rightarrow> enat \<Rightarrow> enat" where
  "x + y = (case x of Zero \<Rightarrow> (case y of Zero \<Rightarrow> Zero | Succ z \<Rightarrow> Succ z) 
                    | Succ z \<Rightarrow> Succ (z + y))"
  by (unfold plus_enat_def, subst eplus.code, simp split: enat.split) transfer_prover

lemma succ_not_zero [simp]: "Succ x \<noteq> 0"
  by (simp add: zero_enat_def)

lemma infty_not_zero [simp]: "\<infinity> \<noteq> 0"
  by (subst infty.code) simp

lemma enat_not_zero: "x \<noteq> 0 \<Longrightarrow> \<exists>y. x = Succ y"
  unfolding zero_enat_def
  by (cases x) (simp_all)

lemma plus_enat_Succ [simp]: "Succ x + y = Succ (x + y)"
  by (simp add: plus_enat_def)

lemma plus_enat_Succ_right [simp]: "x + Succ y = Succ (x + y)"
  by (simp add: plus_enat_def eplus_Succ_right)

lemma plus_enat_zero [simp]: "(x::enat) + y = 0 \<longleftrightarrow> x = 0 \<and> y = 0"
  by (simp add: plus_enat_def zero_enat_def)


fun nat2enat :: "nat \<Rightarrow> enat" where
    "nat2enat 0 = 0"
  | "nat2enat (Suc x) = Succ (nat2enat x)"

lemma nat2enat_plus [simp]: "nat2enat (x + y) = nat2enat x + nat2enat y"
  by (induction x) simp_all


text \<open>Equalities involving @{term \<infinity>}. Uniqueness lemma enables short proofs if applicable.\<close>

lemma infty_unique:      
  assumes "x = Succ x" shows "x = \<infinity>" 
  using assms 
proof(coinduction rule: enat.coinduct)
  case (Eq_enat)
  then show ?case by (auto dest: arg_cong [of _ _ pred])
qed

lemma plus_enat_Infty_left [simp]: "\<infinity> + x = \<infinity>"
  by (rule infty_unique) (subst infty.code, simp)

lemma plus_enat_Infty_right [simp]: "x + \<infinity> = \<infinity>"
  by (rule infty_unique) (subst infty.code, simp)

lemma Succ_x_infty [simp]: "Succ x = \<infinity> \<longleftrightarrow> x = \<infinity>"
  by (subst infty.code) auto

lemma plus_enat_non_zero_cancel_infty:
  assumes "x + y = x" "y \<noteq> 0" 
  shows "x = \<infinity>"
  using assms 
  unfolding zero_enat_def
proof (coinduction arbitrary: x rule: enat.coinduct)
  case Eq_enat
  then show ?case
    by (auto dest: enat_not_zero[unfolded zero_enat_def])
qed

lemmas plus_enat_non_zero_cancel_inftys = 
  plus_enat_non_zero_cancel_infty plus_enat_non_zero_cancel_infty[OF sym]


text \<open>Cancelation for addition only holds for finite canceled summands.\<close>

lemma plus_enat_cancel_left: 
  assumes "x + y = x + z" "x \<noteq> \<infinity>" 
  shows "y = z"
  using assms
proof (coinduction arbitrary: x y z rule: enat.coinduct)
  case Eq_enat
  then show ?case
    by (fold zero_enat_def) (auto dest: plus_enat_non_zero_cancel_inftys dest!: enat_not_zero)
qed

lemma plus_enat_cancel_right: 
  assumes "x + z = y + z" "z \<noteq> \<infinity>" 
  shows "x = y"
  using assms
  by (subst (asm) (1 2) add.commute) (simp add: plus_enat_cancel_left)


(* Checks: *)

thm Groups.ac_simps

lemma "x + 0 = (x::enat)" by (simp add: Groups.ac_simps)
lemma "x + \<infinity>  = \<infinity>" by (simp add: Groups.ac_simps)
lemma "y + \<infinity> + 0 + z = \<infinity>" by (simp add: Groups.ac_simps)
lemma "(x::enat) + y + z = y + z + x" by (simp add: Groups.ac_simps)

subsection \<open>Countably infinite sums\<close>
(*
declare [[bnf_internals,function_internals]]
*)
corecursive esum_from :: "(nat \<Rightarrow> enat) \<Rightarrow> nat \<Rightarrow> enat" where
  "esum_from f x = (if \<forall>k \<ge> x. f k = 0 then 0
                    else if f x = 0 then esum_from f (Suc x) 
                    else Succ (pred (f x) + esum_from f (Suc x)))"
proof (relation "measure (\<lambda>(f, x). (LEAST k. x \<le> k \<and> f k \<noteq> 0) - x)"; clarsimp)
  fix f::"nat \<Rightarrow> enat" and x::nat and k::nat
  assume H: "f x = 0" "x \<le> k" "f k \<noteq> 0"
  then have "(LEAST k. x \<le> k \<and> f k \<noteq> 0) = (LEAST k. Suc x \<le> k \<and> f k \<noteq> 0)"
    by (metis Suc_leD antisym_conv not_less_eq_eq) 
  moreover have "Suc x \<le> (LEAST k. Suc x \<le> k \<and> f k \<noteq> 0)" using H
    by (metis (mono_tags, lifting) LeastI_ex antisym not_less_eq_eq)
  ultimately 
  show "(LEAST k. Suc x \<le> k \<and> f k \<noteq> 0) - Suc x < (LEAST k. x \<le> k \<and> f k \<noteq> 0) - x"
    by auto
qed

abbreviation esum :: "(nat \<Rightarrow> enat) \<Rightarrow> enat" where 
  "esum f \<equiv> esum_from f 0"


text \<open>Prove a uniqueness lemma for later reasoning about @{term esum}.\<close>

thm esum_from.inner_induct

lemma plus_enat_Succ_pred: "x \<noteq> 0 \<Longrightarrow> Succ (pred x + y) = x + y"
  by (drule enat_not_zero) clarsimp

lemma esum_from_rec: "esum_from f x = f x + esum_from f (Suc x)"
  apply (subst esum_from.code, auto)
  apply (subst esum_from.code, auto)
  apply (auto dest: enat_not_zero)
  done

lemma esum_from_unique:
  assumes "\<And>x. g x = (if \<forall>k \<ge> x. f k = 0 then 0
                      else if f x = 0 then g (Suc x) 
                      else Succ (pred (f x) + g (Suc x)))"
  shows "g = esum_from f"
proof (rule ext)
  show "g x = esum_from f x" for x 
proof(coinduction arbitrary: x rule: enat.coinduct_upto)
  case (Eq_enat)
  show ?case
      apply (induction arg\<equiv>"(f, x)" arbitrary: x rule: esum_from.inner_induct)
    apply (subst (1 2 4) assms)
    apply (subst (1 2 4) esum_from.code)
    apply (auto intro: enat.cong_intros)
    done
qed
qed

lemma esum_from_Suc: 
  "esum_from f (Suc k) = esum_from (\<lambda>k. f (Suc k)) k"
  apply (rule fun_cong [where f="\<lambda>k. esum_from f (Suc k)"])
  apply (rule esum_from_unique, auto)
    apply (subst (1) esum_from.code, auto) 
    subgoal for x k by (cases k, auto)
   apply (subst (1) esum_from.code, auto)
  apply (subst (1) esum_from.code, auto)
  done


subsection \<open>Infinite sums over arbitrary sets\<close>

\<comment> \<open>FIXME: does this already exists somewhere?\<close>

definition support :: "('a \<Rightarrow> 'b::zero) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "support f A = {x. x \<in> A \<and> f x \<noteq> 0}"

lemma support_subset: "support f A \<subseteq> A"
  by (simp add: support_def)

lemma support_finite: "finite A \<Longrightarrow> finite (support f A)"
  by (simp add: support_def)


definition esum_bset :: "'a set \<Rightarrow> ('a \<Rightarrow> enat) \<Rightarrow> enat" where
  "esum_bset A f = (if finite (support f A) 
                    then \<Sum> x \<in> support f A. f x 
                    else \<infinity>)" 

abbreviation esum_set where 
  "esum_set \<equiv> esum_bset UNIV"


text \<open>Properties of arbitrary sums.\<close>

lemma esum_bset_finite: "finite A \<Longrightarrow> esum_bset A f = (\<Sum> x \<in> A. f x)"
  by (metis (mono_tags) esum_bset_def sum.empty' sum.eq_sum sum.non_neutral' 
            support_def support_finite)

\<comment> \<open>more TBA\<close>



subsection \<open>Extended cardinality for sets\<close>

definition ecard :: "'a set \<Rightarrow> enat" where
  "ecard A \<equiv> if finite A then nat2enat (card A) else \<infinity>"

lemma ecard_finite [simp]: "finite A \<Longrightarrow> ecard A = nat2enat (card A)"
  by (auto simp add: ecard_def)

lemma ecard_infinite [simp]: "infinite A \<Longrightarrow> ecard A = \<infinity>"
  by (auto simp add: ecard_def)

lemma ecard_non_empty [simp]: "ecard (A) \<noteq> 0 \<longleftrightarrow> A \<noteq> {}" 
by (auto simp add: ecard_def zero_enat_def split: if_splits elim!: nat2enat.elims)

lemma ecard_union_disjoint: "A \<inter> B = {} \<Longrightarrow> ecard (A \<union> B) = ecard A + ecard B"
  by (auto simp add: ecard_def card_Un_disjoint Groups.ac_simps)

lemma ecard_inj_image: "inj_on f A \<Longrightarrow> ecard (f`A) = ecard A"
  by (auto simp add: ecard_def card_image finite_image_iff)


lemma ecard_Int_if_vimage:                                   (* ugly, decompose *)
  "ecard ((\<lambda>x. if P x then f x else g x) -` {y} \<inter> A) 
   = ecard (f -` {y} \<inter> (A \<inter> {x. P x})) + ecard (g -` {y} \<inter> (A \<inter> -{x. P x}))" 
proof -
  have "((\<lambda>x. if P x then f x else g x) -` {y} \<inter> A) 
      = (f -` {y} \<inter> (A \<inter> {x. P x})) \<union> (g -` {y} \<inter> (A \<inter> -{x. P x}))" by auto
  then show ?thesis by (simp add: ecard_union_disjoint)
qed


end