(*
  Igloo Case Study: Replication 
  Primary-Backup Replication

  $Id: Primary_Backup_1.thy 150717 2020-03-23 10:18:17Z tklenze $

  Author: Tobias Klenze <tobias.klenze@inf.ethz.ch>
  Date: December 2019
*)

section \<open>Utilities for the Primary Backup Case Study\<close>

theory Utils
  imports
    "../../Event_Systems" 
    "HOL-Library.Sublist"
    "HOL-Library.Countable_Set"
begin

subsection\<open>Definitions\<close>

typedef cid = "(UNIV::nat set)" by simp

instance cid :: countable 
  apply(rule countable_classI[where f=Rep_cid])
  by (simp add: Rep_cid_inject)

type_synonym sid = nat (*we conveniently use nat here because we need this type to be ordered.  *)

abbreviation fun_upd2 where
 "fun_upd2 P p1 p2 r \<equiv> P(p1 := (P p1)(p2 := r))"

abbreviation fun_upd3 where
 "fun_upd3 P p1 p2 p3 r \<equiv> P(p1 := fun_upd2 (P p1) p2 p3 r)"

lemma multiple_Inv: "\<lbrakk>Inv E I; Inv E J\<rbrakk> \<Longrightarrow> Inv E (\<lambda>s. I s \<and> J s)"
  by (auto simp add: Inv_def)

fun least :: "('a::ord) set \<Rightarrow> 'a option" where 
  "least H = (if H = {} then None else Some (LEAST x. x \<in> H))"

fun is_head where
  "is_head y (x#xs) = (x = y)"
| "is_head y [] = False"

lemma is_head_ex[dest]: "is_head m (buf s ra)
    \<Longrightarrow> \<exists>xs. buf s ra = m # xs "
  using is_head.elims(2) by fastforce


subsection\<open>Rules for proving sortedness and equivalence of lists\<close>
text\<open>Rules for proving @{term inv_order} invariant in @{text Primary_Backup_1}.\<close>

(*rule that we can apply with ! to get the proof goals in the right form below.*)
lemma neq_list_False: "\<lbrakk>a@a2 \<noteq> b@b2; a@a2 = b@b2\<rbrakk> \<Longrightarrow> False"
  by auto

(*a simple rule to help with the case that all channels and local states stay unmodified*)
lemma l2_ident:  "\<lbrakk>l1 = l1'; l2 = l2'\<rbrakk> \<Longrightarrow> l1 @ l2 = l1' @ l2'" by simp

lemma l2_fwd: "\<lbrakk>l1 = l1'@[x]; l2' = x#l2\<rbrakk> \<Longrightarrow> l1 @ l2 = l1' @ l2'" by simp


lemma sorted_wrt_drop_middle: "sorted_wrt P (l1@l2@l3) \<Longrightarrow> sorted_wrt P (l1@l3)"
  by (simp add: sorted_wrt_append)

lemma sorted_wrt_drop_end: "sorted_wrt P (l1@l2) \<Longrightarrow> sorted_wrt P l1"
  by (simp add: sorted_wrt_append)

lemma sorted_wrt_may_drop_second:
  "\<lbrakk>sorted_wrt prefix (e#l1@l2@l3@l4); l1 = x # l1' \<or> l1 = l1'; e' = e; l2' = l2; l3' = l3; l4' = l4\<rbrakk> 
  \<Longrightarrow> sorted_wrt prefix (e'#l1'@l2'@l3'@l4')"
  by auto

lemma sorted_wrt_fwd_second:
  "\<lbrakk>sorted_wrt prefix (e#l1@l2@l3@l4); l1 = x # l1';l2' = l2; l3' = l3; l4' = l4\<rbrakk> 
  \<Longrightarrow> sorted_wrt prefix (x#l1'@l2'@l3'@l4')"
  by auto

lemma sorted_wrt_append_last:
  "\<lbrakk>sorted_wrt prefix (x#l1@l2@l3@[e]); prefix e e'; x' = x; l1' = l1; l2' = l2; l3' = l3 @ [e']\<rbrakk> 
  \<Longrightarrow> sorted_wrt prefix (x'#l1'@l2'@l3'@[e'])"
  by (auto simp add: sorted_wrt_append)

lemma sorted_prefix_app:
"\<lbrakk>sorted_wrt prefix (sb # li @ lc @ lo @ [sp]); prefix sp sp'\<rbrakk> \<Longrightarrow> 
  sorted_wrt prefix (sb # li @ lc @ lo @ [sp', sp'])"
  using append_assoc sorted_wrt_append by fastforce

lemma sorted_prefix_rm:
"\<lbrakk>sorted_wrt prefix (sb # h # li @ lc @ lo @ [sp])\<rbrakk> \<Longrightarrow> 
  sorted_wrt prefix (h # li @ lc @ lo @ [sp])"
  by auto


end