(*******************************************************************************

  Igloo Case Study: One-Way authentication protocols

  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
  Version: Isabelle/HOL 2020
  Date:    2019
  ID:      $Id: m2_auth_chan.thy 152662 2020-08-06 09:54:41Z tklenze $
  
*******************************************************************************)

section \<open>Refinement 2a: Authentic Channel Protocol\<close>

theory m2_auth_chan 
  imports 
    m1_auth 
    "infrastructure/Channels"
begin

text \<open>We refine the abstract authentication protocol to a version of the 
ISO/IEC 9798-3 protocol using abstract channels. In standard protocol notation, 
the original protocol is specified as follows.
\[
\begin{array}{llll}
  \mathrm{M1.} & A \rightarrow B & : & A, B, N_A \\
  \mathrm{M2.} & B \rightarrow A & : & \{N_B, N_A, A\}_{K^{-1}(B)} 
\end{array}
\]
We introduce insecure channels between pairs of agents for the first message and 
authentic channels for the second.\<close>

declare domIff [simp, iff del]


(******************************************************************************)
subsection \<open>State\<close>
(******************************************************************************)

text \<open>State: we extend the state with insecure and authentic channels 
defined above.\<close>

record m2_state = m1_state +
  chan :: "chmsg set"

definition 
  m2_init :: "m2_state \<Rightarrow> bool" 
where 
  "m2_init s \<longleftrightarrow> s = \<lparr> 
     init_runs = Map.empty, 
     resp_runs = Map.empty, 
     chan = {}
  \<rparr>"


(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

definition    \<comment> \<open>refines @{term "m1_init_start"}\<close> 
  m2_init_start :: "rid \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> m2_state \<Rightarrow> m2_state \<Rightarrow> bool" 
where  
  "m2_init_start Ra A B s s1 \<longleftrightarrow>  

     \<comment> \<open>guards\<close>
     Ra \<notin> dom (init_runs s) \<and>   \<comment> \<open>new run\<close>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr> 
       init_runs := (init_runs s)(Ra \<mapsto> \<lparr> agts = [A, B], store = [] \<rparr>)  
     \<rparr>"

definition    \<comment> \<open>refines @{term "m1_resp_start"}\<close> 
  m2_resp_start :: "rid \<Rightarrow> agent \<Rightarrow> m2_state \<Rightarrow> m2_state \<Rightarrow> bool" 
where  
  "m2_resp_start Rb B s s1 \<longleftrightarrow>  

     \<comment> \<open>guards\<close>
     Rb \<notin> dom (resp_runs s) \<and>   \<comment> \<open>new run\<close>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr> 
       resp_runs := (resp_runs s)(Rb \<mapsto> \<lparr> agts = [B], store = [] \<rparr>)  
     \<rparr>"

definition    \<comment> \<open>refines @{term skip}\<close>
  m2_init_send :: "rid \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> nonce \<Rightarrow> m2_state \<Rightarrow> m2_state \<Rightarrow> bool" 
where
  "m2_init_send Ra A B Na s s1 \<longleftrightarrow>
     \<comment> \<open>guards\<close>
     init_runs s Ra = Some \<lparr> agts = [A, B], store = [] \<rparr> \<and>
     Na = #[Init,Ra,0] \<and>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr>
       chan := insert (Insec A B (Msg [aNon Na])) (chan s)  
     \<rparr>"

definition    \<comment> \<open>refines @{term "m1_resp_read"}\<close>
  m2_resp_recv :: "rid \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> nonce \<Rightarrow> nonce \<Rightarrow> m2_state \<Rightarrow> m2_state \<Rightarrow> bool"
where
  "m2_resp_recv Rb B A Nb Na s s1 \<longleftrightarrow>
     \<comment> \<open>guards\<close>
     resp_runs s Rb = Some \<lparr> agts = [B], store = [] \<rparr> \<and>

     Insec A B (Msg [aNon Na]) \<in> chan s \<and>                          \<comment> \<open>rcv M1\<close>
     Nb = #[Resp,Rb,0] \<and>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr> 
       resp_runs := (resp_runs s)(Rb \<mapsto> \<lparr> agts = [B, A], store = [aNon Na] \<rparr>) 
     \<rparr>"

definition    \<comment> \<open>refines @{term skip}\<close>
  m2_resp_send :: "rid \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> nonce \<Rightarrow> nonce \<Rightarrow> m2_state \<Rightarrow> m2_state \<Rightarrow> bool"
where
  "m2_resp_send Rb B A Nb Na s s1 \<longleftrightarrow>
     \<comment> \<open>guards\<close>
     resp_runs s Rb = Some \<lparr> agts = [B, A], store = [aNon Na] \<rparr>  \<and>
     Nb = #[Resp,Rb,0] \<and>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr> 
       chan := insert (Auth B A (Msg [aNon Nb, aNon Na])) (chan s)  \<comment> \<open>snd M2\<close>
     \<rparr>"

definition    \<comment> \<open>refines @{term "m1_init_read_auth"}\<close>
  m2_init_recv :: "rid \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> nonce \<Rightarrow> nonce \<Rightarrow> m2_state \<Rightarrow> m2_state \<Rightarrow> bool"
where
  "m2_init_recv Ra A B Na Nb s s1 \<longleftrightarrow>
     \<comment> \<open>guards\<close>
     init_runs s Ra = Some \<lparr> agts = [A, B], store = [] \<rparr> \<and>
     Na = #[Init,Ra,0] \<and>

     Auth B A (Msg [aNon Nb, aNon Na]) \<in> chan s \<and>            \<comment> \<open>recv M2\<close>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr> 
       init_runs := (init_runs s)(Ra \<mapsto> \<lparr> agts = [A, B], store = [aNon Nb] \<rparr>)
     \<rparr>"


text \<open>Intruder fake event.\<close>

abbreviation used_ids where
  "used_ids s \<equiv> {(Init, R) | R. R \<in> dom (init_runs s)} \<union> {(Resp, R) | R. R \<in> dom (resp_runs s)}"


definition     \<comment> \<open>refines @{term Id}\<close> 
  m2_fake :: "m2_state \<Rightarrow> m2_state \<Rightarrow> bool"
where
  "m2_fake s s1 \<longleftrightarrow> 

    \<comment> \<open>actions:\<close>
    s1 = s\<lparr> chan := fake ik0 (used_ids s) (chan s) \<rparr>"


text \<open>Transition system.\<close>

datatype m2_event = 
  m2_Init_start rid agent agent |
  m2_Resp_start rid agent |
  m2_Init_send rid agent agent nonce |
  m2_Resp_recv rid agent agent nonce nonce |
  m2_Resp_send rid agent agent nonce nonce |
  m2_Init_recv rid agent agent nonce nonce |
  m2_Fake |
  m2_Skip

fun m2_trans :: "m2_state \<Rightarrow> m2_event \<Rightarrow> m2_state \<Rightarrow> bool" where
  "m2_trans s (m2_Init_start R A B) s' \<longleftrightarrow> m2_init_start R A B s s'" |
  "m2_trans s (m2_Resp_start R B) s' \<longleftrightarrow> m2_resp_start R B s s'" |
  "m2_trans s (m2_Init_send Ra A B Na) s' \<longleftrightarrow> m2_init_send Ra A B Na s s'" |
  "m2_trans s (m2_Resp_recv Rb A B Nb Na) s' \<longleftrightarrow> m2_resp_recv Rb A B Nb Na s s'" |
  "m2_trans s (m2_Resp_send Rb A B Nb Na) s' \<longleftrightarrow> m2_resp_send Rb A B Nb Na s s'" |
  "m2_trans s (m2_Init_recv Ra A B Na Nb) s' \<longleftrightarrow> m2_init_recv Ra A B Na Nb s s'" |
  "m2_trans s (m2_Fake) s' \<longleftrightarrow> m2_fake s s'" |
  "m2_trans s (m2_Skip) s'\<longleftrightarrow> (s = s')"

lemmas m2_trans_defs = 
  m2_init_start_def m2_resp_start_def m2_init_send_def m2_resp_recv_def m2_resp_send_def 
  m2_init_recv_def m2_fake_def

lemmas m2_trans_induct = m2_trans.induct [case_names 
    m2_init_start m2_resp_start m2_init_send m2_resp_recv m2_resp_send m2_init_recv m2_fake m2_skip
  ]

definition
  m2 :: "(m2_event, m2_state) ES" where
  "m2 \<equiv> \<lparr>
    init = m2_init,
    trans = m2_trans
  \<rparr>"

lemmas m2_defs = 
  m2_def m2_init_def m2_trans_defs

lemma trans_m2_eq [simp]: "(m2: s \<midarrow>e\<rightarrow> s') \<longleftrightarrow> m2_trans s e s'"
  by (auto simp add: m2_def)


(******************************************************************************)
subsection \<open>Invariants\<close>
(******************************************************************************)

subsubsection \<open>Authentic channel and responder\<close>
(******************************************************************************)

text \<open>This property relates the messages in the authentic channel to the 
responder run frame.\<close>

definition 
  m2_inv1_auth :: "m2_state \<Rightarrow> bool" where
  "m2_inv1_auth s \<longleftrightarrow> (\<forall>A B Na Nb. 
     Auth B A (Msg [aNon Nb, aNon Na]) \<in> chan s \<longrightarrow> B \<notin> bad \<longrightarrow> A \<notin> bad \<longrightarrow> 
       (\<exists>Rb. resp_runs s Rb = Some \<lparr> agts = [B, A], store = [aNon Na] \<rparr> \<and> Nb = #[Resp,Rb,0])
  )"

lemmas m2_inv1_authI = m2_inv1_auth_def [THEN iffD2, rule_format]
lemmas m2_inv1_authE [elim] = m2_inv1_auth_def [THEN iffD1, elim_format, rule_format]
lemmas m2_inv1_authD [dest] = m2_inv1_auth_def [THEN iffD1, rule_format, rotated 1]


text \<open>Invariance proof.\<close>

lemma PO_m2_inv2 [simp, intro]: "reach m2 s \<Longrightarrow> m2_inv1_auth s"
proof (induction s rule: reach.induct)
  case (reach_init s)
  then show ?case 
    by (auto simp add: m2_defs intro!: m2_inv1_authI) 
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction s e s' rule: m2_trans_induct)
    case (m2_resp_recv s Rb A B Nb Na s')
    then show ?case 
      by (auto simp add: m2_trans_defs intro!: m2_inv1_authI dest: dom_lemmas)
         (metis list.simps(3) m2_inv1_authD option.inject run_state.ext_inject)
  next
    case (m2_init_recv s Ra A B Na Nb s')
    then show ?case 
      by (auto simp add: m2_trans_defs intro!: m2_inv1_authI)
  qed (auto 4 4 simp add: m2_trans_defs intro!: m2_inv1_authI dest: dom_lemmas)
qed


(******************************************************************************)
subsection \<open>Refinement\<close>
(******************************************************************************)

text \<open>The mediator function maps receive events to read events and send events to skip.\<close>

fun \<pi>\<^sub>2 :: "m2_event \<Rightarrow> m1_event" where
  "\<pi>\<^sub>2 (m2_Init_start R A B) = (m1_Init_start R A B)" |
  "\<pi>\<^sub>2 (m2_Resp_start R B) = (m1_Resp_start R B)" |
  "\<pi>\<^sub>2 (m2_Resp_recv Rb B A Nb Na) = (m1_Resp_read Rb B A Nb Na)" |
  "\<pi>\<^sub>2 (m2_Init_recv Ra A B Na Nb) = (m1_Init_read_auth Ra A B Na Nb)" |
  "\<pi>\<^sub>2 _ = m1_Skip" 

fun h\<^sub>2 :: "m2_state \<Rightarrow> m1_state" where
  "h\<^sub>2 s = \<lparr> init_runs = init_runs s, resp_runs = resp_runs s \<rparr>"


theorem m2_refines_m1: "m2 \<sqsubseteq>\<^sub>\<pi>\<^sub>2 m1"
proof (intro simulate_ES_fun_with_invariant[where I="m2_inv1_auth"] conjI)
  fix s0
  assume "init m2 s0" 
  then show "init m1 (h\<^sub>2 s0)"
    by (auto simp add: m1_defs m2_defs)
next
  fix s a s'
  assume "m2: s\<midarrow>a\<rightarrow> s'" and "m2_inv1_auth s"
  with \<open>m2: s\<midarrow>a\<rightarrow> s'\<close> show "m1: h\<^sub>2 s\<midarrow>\<pi>\<^sub>2 a\<rightarrow> h\<^sub>2 s'"
    by (induction s a s' rule: m2_trans_induct)
       (auto simp add: m1_trans_defs m2_trans_defs)     \<comment> \<open>invariant is needed for step3\<close>
qed simp

corollary m2_trace_included_m1: "map \<pi>\<^sub>2`traces m2 \<subseteq> traces m1"
  by (intro simulation_soundness m2_refines_m1)


end
