(*******************************************************************************

  Igloo Case Study: One-Way authentication protocols

  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
  Version: Isabelle/HOL 2020
  Date:    2019
  ID:      $Id: m1_auth.thy 152662 2020-08-06 09:54:41Z tklenze $
  
*******************************************************************************)

chapter \<open>Igloo Case Study: Security Protocol\<close>

text \<open>In this chapter, we derive our unilateral authentication protocol. We have a single abstract 
model at Level 1. We then refine this model into a channel protocol (Level 2), using authentic channels.
We then refine it into a cryptographic protocols (Level 3) using signatures.

In the fourth model we implement message terms with a abstract "bitstrings" using an abstract 
crypto algebra. The fifth model decomposes the monolithic model into families of components (one for
initiators, one for responders) and the environment. In the last model, we convert each of the 
components into a trace-equivalent IO specification.
\<close>


section \<open>Refinement 1: Abstract Protocol\<close>

theory m1_auth imports "infrastructure/Runs" "infrastructure/a0i_agree"
begin

(* declare option.split_asm [split] *)
declare domIff [simp, iff del]

(******************************************************************************)
subsection \<open>State\<close>
(******************************************************************************)

text \<open>We introduce protocol runs.\<close>

record m1_state = 
  init_runs :: "runs"
  resp_runs :: "runs"

definition 
  m1_init :: "m1_state \<Rightarrow> bool" where
  "m1_init s \<longleftrightarrow> s = \<lparr> 
     init_runs = Map.empty, 
     resp_runs = Map.empty 
  \<rparr>"


(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

definition   \<comment> \<open>refines @{term skip}\<close>
  m1_init_start :: "rid \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> m1_state \<Rightarrow> m1_state \<Rightarrow> bool" 
where  
  "m1_init_start Ra A B s s1 \<longleftrightarrow>  

     \<comment> \<open>guards\<close>
     Ra \<notin> dom (init_runs s) \<and>   \<comment> \<open>new run\<close>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr> 
       init_runs := (init_runs s)(Ra \<mapsto> \<lparr> agts = [A, B], store = [] \<rparr>)  
     \<rparr>"

definition   \<comment> \<open>refines @{term skip}\<close>
  m1_resp_start :: "rid \<Rightarrow> agent \<Rightarrow> m1_state \<Rightarrow> m1_state \<Rightarrow> bool" 
where  
  "m1_resp_start Rb B s s1 \<longleftrightarrow>  

     \<comment> \<open>guards\<close>
     Rb \<notin> dom (resp_runs s) \<and>    \<comment> \<open>new run\<close>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr> 
       resp_runs := (resp_runs s)(Rb \<mapsto> \<lparr> agts = [B], store = [] \<rparr>)  
     \<rparr>"

definition   \<comment> \<open>refines @{term a0i_running}\<close>
  m1_resp_read :: "rid \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> nonce \<Rightarrow> nonce \<Rightarrow> m1_state \<Rightarrow> m1_state \<Rightarrow> bool" 
where
  "m1_resp_read Rb B A Nb Na s s1 \<longleftrightarrow>      \<comment> \<open>@{term Na} and @{term A} completely arbitrary\<close>

     \<comment> \<open>guards\<close>
     resp_runs s Rb = Some \<lparr> agts = [B], store = [] \<rparr> \<and>
     Nb = #[Resp,Rb,0] \<and>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr>
       resp_runs := (resp_runs s)(Rb \<mapsto> \<lparr> agts = [B, A], store = [aNon Na] \<rparr>)
     \<rparr>"

definition   \<comment> \<open>refines @{term a0i_commit}\<close>
  m1_init_read_auth :: 
    "rid \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> nonce \<Rightarrow> nonce \<Rightarrow> m1_state \<Rightarrow> m1_state \<Rightarrow> bool" 
where
  "m1_init_read_auth Ra A B Na Nb s s1 \<longleftrightarrow>

     \<comment> \<open>guards\<close>
     init_runs s Ra = Some \<lparr> agts = [A, B], store = [] \<rparr> \<and>
     Na = #[Init,Ra,0] \<and>

     \<comment> \<open>authentication guard:\<close>
     (A \<notin> bad \<and> B \<notin> bad \<longrightarrow> (\<exists>Rb. 
        Nb = #[Resp,Rb,0] \<and> resp_runs s Rb = Some \<lparr> agts = [B, A], store = [aNon Na] \<rparr> )) \<and>

     \<comment> \<open>actions\<close>
     s1 = s\<lparr>
       init_runs := (init_runs s)(Ra \<mapsto> \<lparr> agts = [A, B], store = [aNon Nb] \<rparr> )
     \<rparr>"


text \<open>Transition system.\<close>

datatype m1_event = 
  m1_Init_start rid agent agent |
  m1_Resp_start rid agent |
  m1_Resp_read rid agent agent nonce nonce |
  m1_Init_read_auth rid agent agent nonce nonce |
  m1_Skip

fun m1_trans :: "m1_state \<Rightarrow> m1_event \<Rightarrow> m1_state \<Rightarrow> bool" where
  "m1_trans s (m1_Init_start R A B) s' \<longleftrightarrow> m1_init_start R A B s s'" |
  "m1_trans s (m1_Resp_start R B) s' \<longleftrightarrow> m1_resp_start R B s s'" |
  "m1_trans s (m1_Resp_read Rb A B Nb Na) s' \<longleftrightarrow> m1_resp_read Rb A B Nb Na s s'" |
  "m1_trans s (m1_Init_read_auth Ra A B Na Nb) s' \<longleftrightarrow> m1_init_read_auth Ra A B Na Nb s s'" |
  "m1_trans s (m1_Skip) s' \<longleftrightarrow> s = s'"

lemmas m1_trans_defs = 
  m1_init_start_def m1_resp_start_def m1_resp_read_def m1_init_read_auth_def

lemmas m1_trans_induct = 
  m1_trans.induct [case_names m1_init_start m1_resp_start m1_resp_read m1_init_read_auth m1_skip]

definition
  m1 :: "(m1_event, m1_state) ES" where
  "m1 \<equiv> \<lparr>
    init = m1_init,
    trans = m1_trans
  \<rparr>"

lemmas m1_defs = 
  m1_def m1_init_def m1_trans_defs

lemma trans_m1_eq [simp]: "(m1: s \<midarrow>e\<rightarrow> s') \<longleftrightarrow> m1_trans s e s'"
  by (auto simp add: m1_def)


(******************************************************************************)
subsection \<open>Refinement\<close>
(******************************************************************************)

text \<open>Define mediator function on events and refinement mapping on states.\<close>

fun \<pi>\<^sub>1 :: "m1_event \<Rightarrow> (nonce \<times> nonce) a0i_event" where
  "\<pi>\<^sub>1 (m1_Resp_read Rb B A Nb Na) = a0i_Running [A, B] (Na, Nb)" |
  "\<pi>\<^sub>1 (m1_Init_read_auth Ra A B Na Nb) = a0i_Commit [A, B] (Na, Nb)" |
  "\<pi>\<^sub>1 _ = a0i_Skip"

definition h\<^sub>1 :: "m1_state \<Rightarrow> (nonce \<times> nonce) a0i_state" where
  "h\<^sub>1 s = \<lparr> 
     signals = 
       {Running [A, B] (Na, #[Resp,Rb,0]) | A B Na Rb. 
          resp_runs s Rb = Some \<lparr> agts = [B, A], store = [aNon Na] \<rparr>} \<union> 
       {Commit [A, B] (#[Init,Ra,0], Nb) | A B Ra Nb. 
          init_runs s Ra = Some \<lparr> agts = [A, B], store = [aNon Nb] \<rparr>} 
   \<rparr>"

theorem m1_refines_a0i: "m1 \<sqsubseteq>\<^sub>\<pi>\<^sub>1 a0i"
proof (intro simulate_ES_fun conjI)
  fix s0 
  assume "init m1 s0"
  then show "init a0i (h\<^sub>1 s0)"
    by (auto simp add: m1_defs a0i_defs h\<^sub>1_def)
next
  fix s a s'
  assume "m1: s\<midarrow>a\<rightarrow> s'"
  then show "a0i: h\<^sub>1 s\<midarrow>\<pi>\<^sub>1 a\<rightarrow> h\<^sub>1 s'"
  proof (induction s a s' rule: m1_trans_induct)
    case (m1_init_start s R A B s1)
    then show ?case 
      by (auto simp add: m1_trans_defs h\<^sub>1_def) (metis map_definedness_contra)+
  next
    case (m1_resp_start s R B s1)
    then show ?case 
      by (auto simp add: m1_trans_defs h\<^sub>1_def) (metis map_definedness_contra)+
  next
    case (m1_resp_read s Rb A B Nb Na s1)
    then show ?case 
      by (fastforce simp add: m1_trans_defs a0i_trans_defs h\<^sub>1_def)
  next
    case (m1_init_read_auth s Ra B A Nb Na s1)
    then show ?case 
      by (fastforce simp add: m1_trans_defs a0i_trans_defs h\<^sub>1_def)
  next
    case (m1_skip s s')
    then show ?case 
      by (auto simp add: m1_defs)
  qed
qed

corollary m1_trace_included_a0i: "map \<pi>\<^sub>1`traces m1 \<subseteq> traces a0i"
  by (intro simulation_soundness m1_refines_a0i)


end
