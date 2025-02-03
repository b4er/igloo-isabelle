(*******************************************************************************

  Project: Development of Security Protocols by Refinement
  Module:  Refinement/a0i_agree.thy (Isabelle/HOL 2020)
  ID:      $Id: a0i_agree.thy 152662 2020-08-06 09:54:41Z tklenze $
  Author:  Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  One-Way authentication protocols
  Initial Model: Injective agreement

  Copyright (c) 2009-2019 Christoph Sprenger
  Licence: LGPL
*******************************************************************************)

section \<open>Injective Agreement\<close>

theory a0i_agree imports a0n_agree
begin

text \<open>This refinement adds injectiveness to the agreement property.\<close>


(******************************************************************************)
subsection \<open>State\<close>
(******************************************************************************)

text \<open>The state and observations are the same as in the previous model.\<close>

type_synonym
  'd a0i_state = "'d a0n_state"

abbreviation
  a0i_init :: "'ds a0n_state \<Rightarrow> bool"
where
  "a0i_init \<equiv> a0n_init"


(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

text \<open>We just refine the commit event. Everything else remains the same.\<close>

abbreviation
  a0i_running :: "agent list \<Rightarrow> 'ds \<Rightarrow> 'ds a0i_state \<Rightarrow> 'ds a0i_state \<Rightarrow> bool"
where 
  "a0i_running \<equiv> a0n_running"

lemmas a0i_running_def = a0n_running_def


definition 
  a0i_commit :: "agent list \<Rightarrow> 'ds \<Rightarrow> 'ds a0i_state \<Rightarrow> 'ds a0i_state \<Rightarrow> bool"
where 
  "a0i_commit h d s s' \<longleftrightarrow>
    \<comment> \<open>guards:\<close>
    (set h \<subseteq> good \<longrightarrow> (Commit h d \<notin> signals s \<and> Running h d \<in> signals s)) \<and>

    \<comment> \<open>actions:\<close>
    s' = s\<lparr> 
      signals := signals s \<union> {Commit h d} 
    \<rparr>"

text \<open>Transition system.\<close>

type_synonym 'ds a0i_event = "'ds a0n_event"

abbreviation a0i_Running where "a0i_Running \<equiv> a0n_Running"
abbreviation a0i_Commit where "a0i_Commit \<equiv> a0n_Commit"
abbreviation a0i_Skip where "a0i_Skip \<equiv> a0n_Skip"

fun a0i_trans :: "'ds a0i_state \<Rightarrow> 'ds a0i_event \<Rightarrow> 'ds a0i_state \<Rightarrow> bool" where
  "a0i_trans s (a0i_Running h d) s' \<longleftrightarrow> a0i_running h d s s'" |
  "a0i_trans s (a0i_Commit h d) s' \<longleftrightarrow> a0i_commit h d s s'" |
  "a0i_trans s (a0i_Skip) s' \<longleftrightarrow> (s = s')"

lemmas a0i_trans_defs = a0i_running_def a0i_commit_def
lemmas a0i_trans_induct = a0i_trans.induct [case_names a0i_running a0i_commit a0i_skip]


definition 
  a0i :: "('ds a0i_event, 'ds a0i_state) ES" where
  "a0i \<equiv> \<lparr>
    init = a0i_init,
    trans = a0i_trans
  \<rparr>"

lemmas a0i_defs = 
  a0n_defs a0i_def a0i_commit_def

lemma trans_a0i_eq [simp]: "(a0i: s \<midarrow>e\<rightarrow> s') \<longleftrightarrow> a0i_trans s e s'"
  by (auto simp add: a0i_def)


(******************************************************************************)
subsection \<open>Invariants\<close>
(******************************************************************************)

subsubsection \<open>Uniqueness of commits\<close>
(******************************************************************************)

text \<open>Note: index-free formalization of uniqueness property appears to work much better
than one using indices into the trace.\<close>

definition 
  a0i_inv1t_1commit :: "'ds a0i_event trace \<Rightarrow> 'ds a0i_state \<Rightarrow> bool" 
where
  "a0i_inv1t_1commit \<tau> s \<longleftrightarrow> (\<forall>h d.
     set h \<subseteq> good \<longrightarrow> 
       (\<forall>\<tau>'. \<tau> = \<tau>' @ [a0i_Commit h d] \<longrightarrow> a0i_Commit h d \<notin> set \<tau>') \<and>
       (a0i_Commit h d \<in> set \<tau> \<longrightarrow> Commit h d \<in> signals s)
  )"

lemmas a0i_inv1t_1commitI = a0i_inv1t_1commit_def [THEN iffD2, rule_format]
lemmas a0i_inv1t_1commitE [elim] = a0i_inv1t_1commit_def [THEN iffD1, elim_format, rule_format]


text \<open>Pure trace invariant implied.\<close>

definition 
  a0i_inv2t_1commit :: "'ds a0i_event trace \<Rightarrow> bool" 
where
  "a0i_inv2t_1commit \<tau> \<longleftrightarrow> (\<forall>h d \<tau>'. 
     set h \<subseteq> good \<longrightarrow> \<tau> = \<tau>' @ [a0i_Commit h d] \<longrightarrow> a0i_Commit h d \<notin> set \<tau>'
  )"

lemmas a0i_inv2t_1commitI = a0i_inv2t_1commit_def [THEN iffD2, rule_format]


lemma a0i_inv2t_1commit [simp, intro]: "a0i \<Turnstile>\<^sub>E\<^sub>S Collect a0i_inv2t_1commit"
proof (rule trace_property_rule[where I="a0i_inv1t_1commit"])
  fix s0 :: "'ds a0i_state"
  assume "init a0i s0"
  then show "a0i_inv1t_1commit [] s0"
    by (auto simp add: a0n_defs intro!: a0i_inv1t_1commitI)
next
  fix s :: "'ds a0i_state" and s' \<tau> e s''
  assume "init a0i s" "a0i: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'" "a0i: s'\<midarrow>e\<rightarrow> s''" "a0i_inv1t_1commit \<tau> s'" 
  then show "a0i_inv1t_1commit (\<tau> @ [e]) s''"
    by (induction s' e s'' rule: a0i_trans_induct)
       (fastforce simp add: a0i_trans_defs intro!: a0i_inv1t_1commitI)+
next
  fix \<tau> and s :: "'ds a0n_state"
  assume "a0i_inv1t_1commit \<tau> s" 
  then show "\<tau> \<in> Collect a0i_inv2t_1commit"
    by (auto intro!: a0i_inv2t_1commitI)
qed 


subsubsection \<open>Injective agreement\<close>
(******************************************************************************)

definition a0i_inv3t_iagree :: "'ds a0i_event trace \<Rightarrow> bool" where
  "a0i_inv3t_iagree \<tau> \<longleftrightarrow> a0n_inv3t_niagree \<tau> \<and> a0i_inv2t_1commit \<tau>"

lemmas a0i_inv3t_iagreeI = a0i_inv3t_iagree_def [THEN iffD2, rule_format]
lemmas a0i_inv3t_iagreeE [elim] = a0i_inv3t_iagree_def [THEN iffD1, elim_format, rule_format]

text \<open>Proved after the refinement below.\<close>


(******************************************************************************)
subsection \<open>Refinement\<close>
(******************************************************************************)

theorem a0i_refines_a0n [simp, intro]: "a0i \<sqsubseteq>\<^sub>id a0n" 
proof (intro simulate_ES_fun[where h=id, simplified] conjI)
  fix s0 :: "'ds a0i_state"
  assume "init a0i s0"
  then show "init a0n s0" by (simp add: a0i_defs)
next
  fix s:: "'ds a0i_state" and a and s':: "'ds a0i_state" 
  assume "a0i: s\<midarrow>a\<rightarrow> s'"
  then show "a0n: s\<midarrow>id a\<rightarrow> s'"
    by (cases a) (auto simp add: a0n_commit_def a0i_commit_def)
qed

corollary a0i_trace_includes_a0n [simp, intro]: "traces a0i \<subseteq> traces a0n"
  by (intro simulation_soundness[where \<pi>=id, simplified] a0i_refines_a0n)


(******************************************************************************)
subsection \<open>Derived invariant: injective agreement\<close>
(******************************************************************************)

corollary a0i_inv2t_iagree: "a0i \<Turnstile>\<^sub>E\<^sub>S Collect a0i_inv3t_iagree" 
  using a0i_inv3t_iagreeI a0n_inv3t_niagree a0i_trace_includes_a0n a0i_inv2t_1commit 
  by (blast intro!: trace_propertyI)


end
