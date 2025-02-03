(*******************************************************************************

  Project: Development of Security Protocols by Refinement
  One-Way authentication protocols
  Initial Model: Non-injective agreement 

  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
  Version: Isabelle/HOL 2020
*******************************************************************************)

section \<open>Non-injective Agreement\<close>

theory a0n_agree 
  imports 
    Agents Infra (* Refinement *) 
    "Igloo.Event_Systems"
begin

text \<open>The initial model abstractly specifies entity authentication, where 
one agent/role authenticates another. More precisely, this property corresponds 
to non-injective agreement on a data set \<open>ds\<close>. We use Running and Commit 
signals to obtain a protocol-independent extensional specification.\<close>

text \<open>Proof tool configuration. Avoid annoying automatic unfolding of
\<open>dom\<close>.\<close>

declare domIff [simp, iff del]


(******************************************************************************)
subsection \<open>State\<close>
(******************************************************************************)

text \<open>Signals. At this stage there are no protocol runs yet. All we model
are the signals that indicate a certain progress of a protocol run by one 
agent/role (Commit signal) and the other role (Running signal). The signals 
contain a list of agents that are assumed to be honest and a polymorphic data 
set to be agreed upon, which is instantiated later. 

Usually, the agent list will contain the names of the two agents who want to
agree on the data, but sometimes one of the agents is honest by assumption 
(e.g., the server) or the honesty of additional agents needs to be assumed
for the agreement to hold.\<close>

datatype 'ds signal =
  Running "agent list" "'ds" 
| Commit "agent list" "'ds"

record 'ds a0n_state = 
  signals :: "'ds signal set"     \<comment> \<open>set of signals\<close>

definition 
  a0n_init :: "'ds a0n_state \<Rightarrow> bool"
where
  "a0n_init s \<longleftrightarrow> s = \<lparr> signals = {} \<rparr>"


(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

text \<open>Running signal, indicating end of responder run.\<close>

definition 
  a0n_running :: "agent list \<Rightarrow> 'ds \<Rightarrow> 'ds a0n_state \<Rightarrow> 'ds a0n_state \<Rightarrow> bool"
where 
  "a0n_running h d s s' \<longleftrightarrow>
    \<comment> \<open>actions:\<close>
    s' = s\<lparr> 
      signals := signals s \<union> {Running h d}
    \<rparr>"


text \<open>Commit signal, marking end of initiator run.\<close>

definition 
  a0n_commit :: "agent list \<Rightarrow> 'ds \<Rightarrow> 'ds a0n_state \<Rightarrow> 'ds a0n_state \<Rightarrow> bool"
where 
  "a0n_commit h d s s' \<longleftrightarrow>
    \<comment> \<open>guards:\<close>
    (set h \<subseteq> good \<longrightarrow> Running h d \<in> signals s) \<and>     

    \<comment> \<open>actions:\<close>
    s' = s\<lparr> 
      signals := signals s \<union> {Commit h d} 
    \<rparr>"


text \<open>Transition system.\<close>

datatype 'ds a0n_event = 
  a0n_Commit "agent list" "'ds" |
  a0n_Running "agent list" "'ds" |
  a0n_Skip 

fun a0n_trans :: "'ds a0n_state \<Rightarrow> 'ds a0n_event \<Rightarrow> 'ds a0n_state \<Rightarrow> bool" where
  "a0n_trans s (a0n_Running h d) s' \<longleftrightarrow> a0n_running h d s s'" |
  "a0n_trans s (a0n_Commit h d) s' \<longleftrightarrow> a0n_commit h d s s'" |
  "a0n_trans s (a0n_Skip) s' \<longleftrightarrow> (s = s')"

lemmas a0n_trans_defs = a0n_running_def a0n_commit_def
lemmas a0n_trans_induct = a0n_trans.induct [case_names a0n_running a0n_commit a0n_skip]

definition 
  a0n :: "('ds a0n_event, 'ds a0n_state) ES" where
  "a0n = \<lparr>
    init = a0n_init,
    trans = a0n_trans
  \<rparr>"

lemmas a0n_defs = 
  a0n_def a0n_init_def  
  a0n_running_def a0n_commit_def 

lemma trans_a0n_eq [simp]: "(a0n: s \<midarrow>e\<rightarrow> s') \<longleftrightarrow> a0n_trans s e s'"
  by (auto simp add: a0n_def)


(******************************************************************************)
subsection \<open>Invariants\<close>
(******************************************************************************)

subsection \<open>inv1: non-injective agreement (state invariant, OBSOLETE)\<close>
(******************************************************************************)

text \<open>This is an extensional variant of Lowe's \emph{non-injective agreement}
of the first with the second agent (by convention) in \<open>h\<close> on data 
\<open>d\<close> [Lowe97]. 
\<close>

definition 
  a0n_inv1_niagree :: "'ds a0n_state \<Rightarrow> bool" 
where
  "a0n_inv1_niagree s \<longleftrightarrow> (\<forall>h d.   
     set h \<subseteq> good \<longrightarrow> 
       Commit h d \<in> signals s \<longrightarrow> Running h d \<in> signals s)"

lemmas a0n_inv1_niagreeI = a0n_inv1_niagree_def [THEN iffD2, rule_format]
lemmas a0n_inv1_niagreeE [elim] = a0n_inv1_niagree_def [THEN iffD1, elim_format, rule_format]


text \<open>Invariance proof.\<close>

lemma PO_a0n_inv1_niagree [simp, intro]: "reach a0n s \<Longrightarrow> a0n_inv1_niagree s"
proof (induction rule: reach.induct)
  case (reach_init s)
  then show ?case 
    by (auto simp add: a0n_defs intro: a0n_inv1_niagreeI)
next
  case (reach_trans s e s')
  then show ?case 
    by (induction s e s' rule: a0n_trans_induct)
       (fastforce simp add: a0n_trans_defs intro!: a0n_inv1_niagreeI)+
qed


subsection \<open>inv1: non-injective agreement (trace invariant)\<close>
(******************************************************************************)

definition 
  a0n_inv2t_niagree :: "'ds a0n_event trace \<Rightarrow> 'ds a0n_state \<Rightarrow> bool" 
where
  "a0n_inv2t_niagree \<tau> s \<longleftrightarrow> (\<forall>h d. set h \<subseteq> good \<longrightarrow> 
       (a0n_Commit h d \<in> set \<tau> \<or> Running h d \<in> signals s) \<longrightarrow> a0n_Running h d \<in> set \<tau>)"

lemmas a0n_inv2t_niagreeI = a0n_inv2t_niagree_def [THEN iffD2, rule_format]
lemmas a0n_inv2t_niagreeE [elim] = a0n_inv2t_niagree_def [THEN iffD1, elim_format, rule_format]

text \<open>Pure trace invariant implied.\<close>

definition 
  a0n_inv3t_niagree :: "'ds a0n_event trace \<Rightarrow> bool" 
where
  "a0n_inv3t_niagree \<tau> \<longleftrightarrow> (\<forall>h d. 
     set h \<subseteq> good \<longrightarrow> a0n_Commit h d \<in> set \<tau>  \<longrightarrow> a0n_Running h d \<in> set \<tau>)"

lemmas a0n_inv3t_niagreeI = a0n_inv3t_niagree_def [THEN iffD2, rule_format]
lemmas a0n_inv3t_niagreeE [elim] = a0n_inv3t_niagree_def [THEN iffD1, elim_format, rule_format]


lemma a0n_inv3t_niagree [simp, intro]: "a0n \<Turnstile>\<^sub>E\<^sub>S Collect a0n_inv3t_niagree"
proof (rule trace_property_rule[where I="a0n_inv2t_niagree"])
  fix s0 :: "'ds a0n_state"
  assume "init a0n s0"
  then show "a0n_inv2t_niagree [] s0"
    by (auto simp add: a0n_defs intro!: a0n_inv2t_niagreeI)
next
  fix s :: "'ds a0n_state" and s' \<tau> e s''
  assume "init a0n s" "a0n: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'" "a0n: s'\<midarrow>e\<rightarrow> s''" "a0n_inv2t_niagree \<tau> s'" 
  then show "a0n_inv2t_niagree (\<tau> @ [e]) s''"
    by (induction s' e s'' rule: a0n_trans_induct)
       (fastforce simp add: a0n_trans_defs intro!: a0n_inv2t_niagreeI)+
next
  fix \<tau> and s :: "'ds a0n_state"
  assume "a0n_inv2t_niagree \<tau> s" 
  then show "\<tau> \<in> Collect a0n_inv3t_niagree"
    by (auto intro!: a0n_inv3t_niagreeI)
qed 


end




