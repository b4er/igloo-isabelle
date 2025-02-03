(*******************************************************************************

  Igloo Case Study: One-Way authentication protocols

  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
  Version: Isabelle/HOL 2020
  Date:    2019
  ID:      $Id: m3_sig.thy 152662 2020-08-06 09:54:41Z tklenze $
  
*******************************************************************************)

section \<open>Refinement 3a: Signature-based Dolev-Yao Protocol\<close>

theory m3_sig imports m2_auth_chan "infrastructure/Message"
begin

text \<open>We implement the channel protocol of the previous refinement with
signatures and add a full-fledged Dolev-Yao adversary.  In this variant, the
adversary is realized using Paulson's closure operators for message derivation
(as opposed to a collection of one-step derivation events a la Strand spaces).
\<close>

text \<open>Proof tool configuration. Avoid annoying automatic unfolding of
\<open>dom\<close> (again).\<close>

declare domIff [simp, iff del]
declare analz_into_parts [dest]


(******************************************************************************)
subsection \<open>State\<close>
(******************************************************************************)

text \<open>We extend the state of @{term m1} with insecure and authentic
channels between each pair of agents.\<close>

record m3_state = m1_state +
  IK :: "msg set"                             \<comment> \<open>intruder knowledge\<close>

abbreviation IK0 where
  "IK0 \<equiv> (Key`priK`bad) \<union> (Key`range pubK) \<union> (Key`shrK`bad)"

definition
  m3_init :: "m3_state \<Rightarrow> bool"
where
  "m3_init s \<longleftrightarrow> s = \<lparr>
     init_runs = Map.empty,
     resp_runs = Map.empty,
     IK = IK0
  \<rparr>"


(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

text \<open>Each event refines the corresponding L2 event.\<close>

definition 
  m3_init_start :: "rid \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> m3_state \<Rightarrow> m3_state \<Rightarrow> bool" 
where  
  "m3_init_start Ra A B s s1 \<longleftrightarrow>  

     \<comment> \<open>guards\<close>
     Ra \<notin> dom (init_runs s) \<and>      \<comment> \<open>new run\<close>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr> 
       init_runs := (init_runs s)(Ra \<mapsto> \<lparr> agts = [A, B], store = [] \<rparr>)  
     \<rparr>"

definition 
  m3_resp_start :: "rid \<Rightarrow> agent \<Rightarrow> m3_state \<Rightarrow> m3_state \<Rightarrow> bool" 
where  
  "m3_resp_start Rb B s s1 \<longleftrightarrow>  

     \<comment> \<open>guards\<close>
     Rb \<notin> dom (resp_runs s) \<and>       \<comment> \<open>new run\<close>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr> 
       resp_runs := (resp_runs s)(Rb \<mapsto> \<lparr> agts = [B], store = [] \<rparr>)  
     \<rparr>"

definition
  m3_init_send :: "[rid, agent, agent, nonce] \<Rightarrow> m3_state \<Rightarrow> m3_state \<Rightarrow> bool"
where
  "m3_init_send Ra A B Na s s1 \<longleftrightarrow>

     \<comment> \<open>guards\<close>
     init_runs s Ra = Some \<lparr> agts = [A, B], store = [] \<rparr> \<and>
     Na = #[Init,Ra,0] \<and>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr>
       IK := insert \<lbrace>Agent A, Agent B, Nonce Na\<rbrace> (IK s)    \<comment> \<open>send msg 1\<close>
     \<rparr>"

definition
  m3_resp_recv :: "[rid, agent, agent, nonce, nonce] \<Rightarrow> m3_state \<Rightarrow> m3_state \<Rightarrow> bool"
where
  "m3_resp_recv Rb B A Nb Na s s1 \<longleftrightarrow>

     \<comment> \<open>guards\<close>
     resp_runs s Rb = Some \<lparr> agts = [B], store = [] \<rparr> \<and>
     Nb = #[Resp,Rb,0] \<and>

     \<lbrace>Agent A, Agent B, Nonce Na\<rbrace> \<in> IK s \<and>            \<comment> \<open>receive msg 1\<close>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr>
       resp_runs := (resp_runs s)(Rb \<mapsto> \<lparr> agts = [B, A], store = [aNon Na] \<rparr>)
     \<rparr>"

definition
  m3_resp_send :: "[rid, agent, agent, nonce, nonce] \<Rightarrow> m3_state \<Rightarrow> m3_state \<Rightarrow> bool"
where
  "m3_resp_send Rb B A Nb Na s s1 \<longleftrightarrow>

     \<comment> \<open>guards\<close>
     resp_runs s Rb = Some \<lparr> agts = [B, A], store = [aNon Na] \<rparr> \<and>
     Nb = #[Resp,Rb,0] \<and>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr>                                                     
       IK := insert (Crypt (priK B) \<lbrace>Nonce Nb, Nonce Na, Agent A\<rbrace>) (IK s)  \<comment> \<open>send msg 2\<close>
     \<rparr>"

definition
  m3_init_recv :: "[rid, agent, agent, nonce, nonce] \<Rightarrow> m3_state \<Rightarrow> m3_state \<Rightarrow> bool"
where
  "m3_init_recv Ra A B Na Nb s s1 \<longleftrightarrow>

     \<comment> \<open>guards\<close>
     init_runs s Ra = Some \<lparr> agts = [A, B], store = [] \<rparr> \<and>
     Na = #[Init,Ra,0] \<and>

     Crypt (priK B) \<lbrace>Nonce Nb, Nonce Na, Agent A\<rbrace> \<in> IK s \<and> \<comment> \<open>recv msg 2\<close>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr>
       init_runs := (init_runs s)(Ra \<mapsto> \<lparr> agts = [A, B], store = [aNon Nb] \<rparr>)
     \<rparr>"


text \<open>The intruder messages are now generated by a full-fledged Dolev-Yao intruder.\<close>

definition
  m3_DY_fake :: "m3_state \<Rightarrow> m3_state \<Rightarrow> bool"
where
  "m3_DY_fake s s1 \<longleftrightarrow>

     \<comment> \<open>actions:\<close>
     s1 = s\<lparr> IK := synth (analz (IK s)) \<rparr>"


text \<open>Transition system.\<close>

type_synonym m3_event = m2_event

abbreviation m3_Init_start where "m3_Init_start \<equiv> m2_Init_start"
abbreviation m3_Resp_start where "m3_Resp_start \<equiv> m2_Resp_start"
abbreviation m3_Init_send where "m3_Init_send \<equiv> m2_Init_send"
abbreviation m3_Resp_recv where "m3_Resp_recv \<equiv> m2_Resp_recv"
abbreviation m3_Resp_send where "m3_Resp_send \<equiv> m2_Resp_send"
abbreviation m3_Init_recv where "m3_Init_recv \<equiv> m2_Init_recv"
abbreviation m3_DY_Fake where "m3_DY_Fake \<equiv> m2_Fake"
abbreviation m3_Skip where "m3_Skip \<equiv> m2_Skip"

fun m3_trans :: "m3_state \<Rightarrow> m3_event \<Rightarrow> m3_state \<Rightarrow> bool" where
  "m3_trans s (m3_Init_start R A B) s' \<longleftrightarrow> m3_init_start R A B s s'" |
  "m3_trans s (m3_Resp_start R B) s' \<longleftrightarrow> m3_resp_start R B s s'" |
  "m3_trans s (m3_Init_send Ra A B Na) s' \<longleftrightarrow> m3_init_send Ra A B Na s s'" |
  "m3_trans s (m3_Resp_recv Rb B A Nb Na) s' \<longleftrightarrow> m3_resp_recv Rb B A Nb Na s s'" |
  "m3_trans s (m3_Resp_send Rb B A Nb Na) s' \<longleftrightarrow> m3_resp_send Rb B A Nb Na s s'" |
  "m3_trans s (m3_Init_recv Ra A B Na Nb) s' \<longleftrightarrow> m3_init_recv Ra A B Na Nb s s'" |
  "m3_trans s (m3_DY_Fake) s' \<longleftrightarrow> m3_DY_fake s s'" |
  "m3_trans s (m3_Skip) s' \<longleftrightarrow> (s = s')"

lemmas m3_trans_defs = 
  m3_init_start_def m3_resp_start_def m3_init_send_def m3_resp_recv_def m3_resp_send_def 
  m3_init_recv_def m3_DY_fake_def

lemmas m3_trans_induct = 
  m3_trans.induct [case_names 
    m3_init_start m3_resp_start m3_init_send m3_resp_recv m3_resp_send m3_init_recv m3_DY_fake m3_skip
  ] 

definition
  m3 :: "(m3_event, m3_state) ES" where
  "m3 \<equiv> \<lparr>
    init = m3_init,
    trans = m3_trans
  \<rparr>"

lemmas m3_defs = m3_def m3_init_def m3_trans_defs

lemma trans_m3_eq [simp]: "(m3: s\<midarrow>e\<rightarrow> s') \<longleftrightarrow> m3_trans s e s'"
  by (auto simp add: m3_def)


(******************************************************************************)
subsection \<open>Invariants\<close>
(******************************************************************************)

text \<open>The following invariants do not depend on the protocol messages.
We want to keep this compilation refinement from channel protocols to
full-fledged Dolev-Yao protocols as generic as possible.\<close>


subsubsection \<open>inv1: Long-term key secrecy\<close>
(******************************************************************************)

text \<open>Private signing keys are secret, that is, the intruder exactly knows the
private keys of corrupted agents.\<close>

definition
  m3_inv1_lkeysec :: "m3_state \<Rightarrow> bool" where
  "m3_inv1_lkeysec s \<longleftrightarrow> (\<forall> A.
     Key (priK A) \<in> analz (IK s) \<longleftrightarrow> A \<in> bad
  )"

lemmas m3_inv1_lkeysecI = m3_inv1_lkeysec_def [THEN iffD2, rule_format]
lemmas m3_inv1_lkeysecE [elim] = m3_inv1_lkeysec_def [THEN iffD1, elim_format, rule_format]


lemma PO_m3_inv1_lkeysec [simp, intro]: "reach m3 s \<Longrightarrow> m3_inv1_lkeysec s"
proof (induction rule: reach.induct)
  case (reach_init s)
  then show ?case 
    by (auto simp add: m3_defs intro!: m3_inv1_lkeysecI)
next
  case (reach_trans s e s')
  then show ?case 
    by (induction s e s' rule: m3_trans_induct)
       (auto simp add: m3_trans_defs intro!: m3_inv1_lkeysecI)
qed


(******************************************************************************)
subsection \<open>Refinement\<close>
(******************************************************************************)

text \<open>Automatic tool tuning. Tame too-agressive pair decomposition, which is
declared as a safe elim rule ([elim!]).\<close>

lemmas MPair_parts [rule del, elim]
lemmas MPair_analz [rule del, elim]


subsubsection \<open>Simulation relation\<close>
(******************************************************************************)

abbreviation
  nonces :: "msg set \<Rightarrow> nonce set"
where
  "nonces H \<equiv> {N. Nonce N \<in> analz H}"

abbreviation
  ink :: "chmsg set \<Rightarrow> nonce set"
where
  "ink H \<equiv> {N. aNon N \<in> extr ik0 H}"


text \<open>Abstraction function on sets of messages.\<close>

inductive_set
  abs_msg :: "msg set \<Rightarrow> chmsg set"
  for H :: "msg set"
where
  am_M1:
    "\<lbrace>Agent A, Agent B, Nonce Na\<rbrace> \<in> H
  \<Longrightarrow> Insec A B (Msg [aNon Na]) \<in> abs_msg H"

| am_M2:
    "Crypt (priK B) \<lbrace>Nonce Nb, Nonce Na, Agent A\<rbrace> \<in> H
  \<Longrightarrow> Auth B A (Msg [aNon Nb, aNon Na]) \<in> abs_msg H"


text \<open>The simulation relation is canonical. It states that the protocol
messages in the intruder knowledge refine the abstract messages appearing in
the channels @{term Insec} and @{term Auth}.\<close>

definition
  R23_msgs :: "m3_state \<Rightarrow> m2_state \<Rightarrow> bool" where
  "R23_msgs s t \<longleftrightarrow> abs_msg (parts (IK s)) \<subseteq> chan t"   \<comment> \<open>with \<open>parts\<close>!\<close>

definition
  R23_ink :: "m3_state \<Rightarrow> m2_state \<Rightarrow> bool" where
  "R23_ink s t \<longleftrightarrow> nonces (IK s) \<subseteq> ink (chan t)"

definition
  R23_preserved :: "m3_state \<Rightarrow> m2_state \<Rightarrow> bool" where
  "R23_preserved s t \<longleftrightarrow> init_runs s = init_runs t \<and> resp_runs s = resp_runs t"

definition
  R23 :: "m3_state \<Rightarrow> m2_state \<Rightarrow> bool" where
  "R23 s t \<longleftrightarrow> R23_msgs s t \<and> R23_ink s t \<and> R23_preserved s t"

lemmas R23_defs = R23_def R23_msgs_def R23_ink_def R23_preserved_def


text \<open>Mediator function: nothing new.\<close>

lemmas R23_msgsI = R23_msgs_def [THEN iffD2, rule_format]
lemmas R23_msgsE [elim] = R23_msgs_def [THEN iffD1, elim_format]

lemmas R23_inkI = R23_ink_def [THEN iffD2, rule_format]
lemmas R23_inkE [elim] = R23_ink_def [THEN iffD1, elim_format]

lemmas R23_preservedI = R23_preserved_def [THEN iffD2, rule_format]
lemmas R23_preservedE [elim] = R23_preserved_def [THEN iffD1, elim_format]

lemmas R23_I = R23_def [THEN iffD2, rule_format]
lemmas R23_E [elim!] = R23_def [THEN iffD1, elim_format]

lemmas R23_intros = R23_I R23_msgsI R23_inkI R23_preservedI


subsubsection \<open>Facts about the abstraction function\<close>
(******************************************************************************)

declare abs_msg.intros [intro!]
declare abs_msg.cases [elim!]

text \<open>Abstraction of concretely fakeable message yields abstractly fakeable
messages. This is the key lemma for the refinement of the intruder.\<close>

lemma abs_msg_DY_subset_fakeable:
  "\<lbrakk> R23_msgs s t; R23_ink s t; m3_inv1_lkeysec s \<rbrakk>
  \<Longrightarrow> abs_msg (synth (analz (IK s))) \<subseteq> fake ik0 (dom (runs t)) (chan t)"
 by (auto 4 4)


subsubsection \<open>Refinement proof\<close>
(******************************************************************************)

theorem m3_refines_m2: "m3 \<sqsubseteq>\<^sub>id m2"
proof (intro simulate_ES_with_invariant [where I="m3_inv1_lkeysec"])
  fix s0
  assume "init m3 s0" 
  then show "\<exists>t0. init m2 t0 \<and> R23 s0 t0"
    by (auto simp add: m2_defs m3_defs intro!: R23_intros) 
next    
  fix s t a s'
  assume "R23 s t" and "m3_inv1_lkeysec s" and "m3: s\<midarrow>a\<rightarrow> s'"
  then show "\<exists>t'. (m2: t\<midarrow>id a\<rightarrow> t') \<and> R23 s' t'"
  proof (induction s a s' rule: m3_trans_induct)
    case (m3_init_start s Ra A B s')
    then show ?case by (auto 4 3 simp add: m2_defs m3_defs intro!: R23_intros)
  next
    case (m3_resp_start s Rb B s')
    then show ?case by (auto 4 3 simp add: m2_defs m3_defs intro!: R23_intros)
  next
    case (m3_init_send s Ra A B Na s')
    then show ?case by (auto 4 4 simp add: m2_defs m3_defs intro!: R23_intros)
  next
    case (m3_resp_recv s Rb B A Nb Na s')
    then show ?case by (auto 4 3 simp add: m2_defs m3_defs intro!: R23_intros)
  next
    case (m3_resp_send s Rb B A Nb Na s')
    then show ?case by (auto 4 4 simp add: m2_defs m3_defs intro!: R23_intros)
    next
    case (m3_init_recv s Ra A B Na Nb s')
    then show ?case by (auto 4 3 simp add: m2_defs m3_defs intro!: R23_intros)
  next
    case (m3_DY_fake s s')
    then show ?case by (auto 4 5 simp add: m2_defs m3_defs intro!: R23_intros)
  qed simp
qed simp

corollary m3_traced_included_m2: "traces m3 \<subseteq> traces m2"
  by (intro simulation_soundness_id m3_refines_m2)

end


