(*
  Title:  Multisets based on extended natural numbers
  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
  Version: Isabelle/HOL 2020
  Date:    2019
  ID:      $Id: EMultiset.thy 152662 2020-08-06 09:54:41Z tklenze $
*)

section \<open>Extended Multisets\<close>

theory EMultiset
imports
   Main ENat 
begin

subsection \<open>Type definition and basic lemmas\<close>

text \<open>Define the type of multisets and instantiate the type class of additive abelian monoids.\<close>

typedef 'a emultiset = "UNIV :: ('a \<Rightarrow> enat) set" morphisms mcount mk_ems
 by simp

declare mk_ems_inverse [simp]
declare mcount_inverse [simp]

setup_lifting type_definition_emultiset


instantiation emultiset :: (type) comm_monoid_add begin

lift_definition zero_emultiset :: "'a emultiset" is "\<lambda>_. 0" .

lift_definition plus_emultiset :: "'a emultiset \<Rightarrow> 'a emultiset \<Rightarrow> 'a emultiset" is 
  "(\<lambda>m1 m2 x. m1 x + m2 x)" .

instance 
  by intro_classes (transfer; auto simp add: Groups.ac_simps)+

end

lemma mcount_empty [simp]: "mcount 0 x = 0"
  by (simp add: zero_emultiset_def)

lemma mcount_plus [simp]: "mcount (X + Y) z = mcount X z + mcount Y z"
  by (simp add: plus_emultiset_def)


text \<open>Equality of multisets.\<close>

lemma emultiset_eq: "X = Y \<longleftrightarrow> (\<forall>z. mcount X z = mcount Y z)" 
  by (auto simp add: mcount_inject [symmetric])


text \<open>Define some additional functions and prove some basic lemmas.\<close>

definition melem :: "'a \<Rightarrow> 'a emultiset \<Rightarrow> bool" (infix "#\<in>#" 60) where
  "x #\<in># X \<longleftrightarrow> mcount X x \<noteq> 0"

abbreviation mnotelem :: "'a \<Rightarrow> 'a emultiset \<Rightarrow> bool" (infix "#\<notin>#" 60) where
  "x #\<notin># X \<equiv> \<not>x #\<in># X"

lemma notelem_empty [simp]: "x #\<notin># 0"
  by (simp add: melem_def)

lemma elem_mplus [simp]: "x #\<in># X + Y \<longleftrightarrow> x  #\<in># X \<or> x #\<in># Y"
  by (simp add: melem_def plus_emultiset_def)


definition msingle :: "'a \<Rightarrow> 'a emultiset" ("{#(_)#}") where
  "{# x #} = mk_ems ((mcount 0)(x := Succ 0))"

lemma mcount_single [simp]: "mcount {# x #} y = (if x = y then Succ 0 else 0)"
  by (simp add: msingle_def)

lemma elem_msingle [simp]: "x #\<in># {# x #}"
  by (simp add: melem_def msingle_def)

lemma elem_minsert_eq: "x #\<in># X \<longleftrightarrow> (\<exists>Y. X = {# x #} + Y)" (is "?A \<longleftrightarrow> ?B")
    by (auto simp add: melem_def emultiset_eq dest!: enat_not_zero 
             intro: exI [of _ "mk_ems (\<lambda>z. if z = x then y else mcount X z )" for y])

lemma minsert_implies_elem: "X = {# x #} + Y \<Longrightarrow> x #\<in># X"
  by (auto simp add: elem_minsert_eq)

lemma empty_no_elem [simp]: "{# x #} + M \<noteq> 0"
  by (auto dest: minsert_implies_elem[OF sym])


definition mmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b emultiset \<Rightarrow> 'a emultiset" where   \<comment> \<open>FIXME: misnomer?\<close>  
  "mmap f m = mk_ems (\<lambda>x. mcount m (f x))"

lemma mmap_plus [simp]: "mmap f (X + Y) = mmap f X + mmap f Y"
  by (auto simp add: mmap_def plus_emultiset_def)


definition msupport :: "'a emultiset \<Rightarrow> 'a set" where
  "msupport X = {x. mcount X x \<noteq> 0}"

lemma msupport_empty [simp, intro!]: "msupport 0 = {}"
  by (simp add: msupport_def)

lemma msupport_plus [simp]: "msupport (g + h) = msupport g \<union> msupport h"
  by (auto simp add: msupport_def)


text \<open>Cancellation. Does not hold in general, since @{prop "x + \<infinity> = \<infinity>"}.) \<close>

lemma plus_emultiset_cancel_left:  
  assumes "X + Y = X + Z" "\<forall>x. mcount X x \<noteq> \<infinity>"
  shows "Y = Z"
  using assms
  by (fastforce simp add: emultiset_eq elim: plus_enat_cancel_left)

lemma minsert_cancel_left: "{# x #} + Y = {# x #} + Z \<Longrightarrow> Y = Z"    (* special case *)
  by (auto elim!: plus_emultiset_cancel_left split: if_splits)

lemma minsert_match: 
  assumes "{# x #} + X = {# y #} + Y" "y #\<notin># X"   
  shows "x = y \<and> X = Y"
proof -
  from assms have "x = y"  
    by (auto simp add: emultiset_eq melem_def msingle_def split: if_splits dest: spec[of _ y])
  with assms have "X = Y" 
    apply (auto simp add: emultiset_eq melem_def msingle_def)
    subgoal for z 
      apply (drule spec[of _ z], simp split: if_splits) 
      done
    done
  with \<open>x = y\<close> show ?thesis ..
qed


subsection \<open>Countably infinite sums\<close>

definition msum_from :: "(nat \<Rightarrow> 'a emultiset) \<Rightarrow> nat \<Rightarrow> 'a emultiset" where
  "msum_from mf i = mk_ems (\<lambda>x. (esum_from (\<lambda>k. mcount (mf k) x) i))"

abbreviation msum :: "(nat \<Rightarrow> 'a emultiset) \<Rightarrow> 'a emultiset" where
  "msum mf \<equiv> msum_from mf 0"

lemma msum_from_rec: "msum_from hf k = hf k + msum_from hf (Suc k)"
  apply (simp add: msum_from_def)
  apply (subst esum_from_rec)
  apply (simp add: plus_emultiset_def)
  done

lemma msum_from_Suc: "msum_from hf (Suc k) = msum_from (\<lambda>k. hf (Suc k)) k"
  by (simp add: msum_from_def esum_from_Suc)

subsection \<open>Infinite sums over arbitrary sets\<close>

definition msum_bset :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b emultiset) \<Rightarrow> 'b emultiset" where
  "msum_bset A mf = mk_ems (\<lambda>b. esum_bset A (\<lambda>a. mcount (mf a) b))"

abbreviation msum_set where 
  "msum_set \<equiv> msum_bset UNIV"


text \<open>Properties of arbitrary sums of multisets\<close>

\<comment> \<open>TBA\<close>




subsection \<open>Multiset image and range for functions\<close>

term sum    (* works only for finie sets! *)
term "\<lambda>f A. (\<Sum> x\<in>A. {# f x #})"


definition mimage :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b emultiset" where
  "mimage f A = mk_ems (\<lambda>y. ecard (f-`{y} \<inter> A))"

abbreviation mrange :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b emultiset" where
  "mrange f \<equiv> mimage f UNIV"

lemma mimage_empty [simp]: "mimage f {} = 0"
  by (auto simp add: mimage_def zero_emultiset_def)

lemma mimage_elem_eq: "y #\<in># mimage f A \<longleftrightarrow> y \<in> f`A"
  by (force simp add: mimage_def melem_def mmap_def)

lemma mcount_mimage_const: "mcount (mimage (\<lambda>x. c) A) c = ecard A"      (* sanity check *)
  by (auto simp add: mimage_def)

lemma mimage_const:  
  "mimage (\<lambda>x. c) A = mk_ems ((mcount 0)(c := ecard A))"  (is "?L = ?R")
proof -
  have "mcount ?L = mcount ?R" by (auto simp add: mimage_def mmap_def)
  then show ?thesis by (simp add: mcount_inject del: mk_ems_inverse)
qed

lemma mimage_const_single: "mimage (\<lambda>x. c) {z} = {# c #}"
  by (auto simp add: mimage_const msingle_def)

lemma mimage_if: 
  "mimage (\<lambda>x. if P x then f x else g x) A = mimage f (A \<inter> {x. P x}) + mimage g (A \<inter> -{x. P x})"
  by (auto simp add: mimage_def plus_emultiset_def ecard_Int_if_vimage)

lemmas mrange_if = mimage_if [where A=UNIV, simplified]


subsection \<open>Multiset image and range for maps\<close>

abbreviation mmimage :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b emultiset" where      (* mimage for maps *)
  "mmimage f A \<equiv> mmap Some (mimage f A)"

abbreviation mmrange :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'b emultiset" where      (* mrange for maps *)
  "mmrange f \<equiv> mmimage f UNIV"

lemmas mmimage_def = mimage_def 

lemma mmimage_empty [simp]: "mmimage Map.empty A = 0"
  by (auto simp add: mmimage_def mmap_def zero_emultiset_def)

lemma mmimage_elem_eq: "y #\<in># mmimage f A \<longleftrightarrow> Some y \<in> f`A"
  by (force simp add: mmimage_def melem_def mmap_def)

lemma mmimage_const:  
  "mmimage (\<lambda>x. Some c) A = mk_ems ((mcount 0)(c := ecard A))"  (is "?L = ?R")
proof -
  have "mcount ?L = mcount ?R" by (auto simp add: mmimage_def mmap_def)
  then show ?thesis by (simp add: mcount_inject del: mk_ems_inverse)
qed

lemma mmimage_const_single: "mmimage (\<lambda>x. Some c) {z} = {# c #}"
  by (auto simp add: mmimage_const msingle_def)

lemma mmimage_if: 
  "mmimage (\<lambda>x. if P x then f x else g x) A = mmimage f (A \<inter> {x. P x}) + mmimage g (A \<inter> -{x. P x})" 
  by (auto simp add: mimage_if)

lemmas mmrange_if = mmimage_if [where A=UNIV, simplified]


end