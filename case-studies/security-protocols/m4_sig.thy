(*******************************************************************************

  Igloo Case Study: One-Way authentication protocols

  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
  Version: Isabelle/HOL 2020
  Date:    2019
  ID:      $Id: m4_sig.thy 152662 2020-08-06 09:54:41Z tklenze $
  
*******************************************************************************)

section \<open>Refinement 4: Signature-based Dolev-Yao Protocol Implementation\<close>

theory m4_sig
  imports 
    m3_sig 
    "infrastructure/Crypto_Algebra"
begin

text \<open>We implement the message terms of the signature-based challenge-response
protocol from the previous refinement with abstract "bitstrings" using an 
abstract "crypto algebra" (in fact, just an injective mapping @{term \<gamma>} from 
messages into an abstract type of "bitstrings").\<close>

text \<open>Proof tool configuration. Avoid annoying automatic unfolding of
\<open>dom\<close> (again).\<close>

declare domIff [simp, iff del]


(******************************************************************************)
subsection \<open>Component/role parameters and assumptions\<close>
(******************************************************************************)

text \<open>We defined locales that capture the parameters of each component/role
along with assumptions about them.\<close>

locale initiator = crypto_algebra \<alpha> for \<alpha> :: "('b :: countable) \<Rightarrow> msg" + 
  fixes Ra :: rid
    and A :: agent
    and B :: agent
    and addrB :: "'a::countable"
    and pubKB :: 'b
  assumes
    resp_pubK: "\<alpha> pubKB = Key (pubK B)"

locale responder = crypto_algebra \<alpha> for \<alpha> :: "('b :: countable) \<Rightarrow> msg" + 
  fixes Rb :: rid
    and B :: agent 
    and priKB :: 'b
  assumes
    resp_priK: "\<alpha> priKB = Key (priK B)"


(******************************************************************************)
subsection \<open>State\<close>
(******************************************************************************)

text \<open>In preparation of the subsequent decomposition, we partition the state into system 
state (runs) and environment state (intruder knowledge). The intruder knowledge is now a 
set of abstract bitstrings.\<close>

text \<open>Some type definitions outside the locale. We extend the run state with additional fields.\<close>

record ('a, 'b) init_run_state = run_state + 
  ibuf :: "('a \<times> 'b) set"     \<comment> \<open>input buffer (address, message)\<close>
  obuf :: "'b option"          \<comment> \<open>output buffer (only message, single place)\<close>

record ('a, 'b) resp_run_state = "('a, 'b) init_run_state" + 
  addrA :: "'a option"         \<comment> \<open>initiator's network address\<close>
  
type_synonym 'b m4e_state = "'b set"                                \<comment> \<open>concrete intruder knowledge\<close>
type_synonym ('a, 'b) m4i_state = "rid \<rightharpoonup> ('a, 'b) init_run_state"  \<comment> \<open>initiator runs\<close>
type_synonym ('a, 'b) m4r_state = "rid \<rightharpoonup> ('a, 'b) resp_run_state"  \<comment> \<open>responder runs\<close>
type_synonym ('a, 'b) m4s_state = "('a, 'b) m4i_state \<times> ('a, 'b) m4r_state" \<comment> \<open>initiator and responder\<close>
type_synonym ('a, 'b) m4_state = "'b m4e_state \<times> ('a, 'b) m4s_state"  \<comment> \<open>complete state\<close>   

text \<open>Abbreviations for state projections.\<close>

abbreviation CIK :: "('a, 'b) m4_state \<Rightarrow> 'b m4e_state" where "CIK u \<equiv> fst u"
abbreviation init_runs :: "('a, 'b) m4_state \<Rightarrow> ('a, 'b) m4i_state" where "init_runs u \<equiv> fst (snd u)"
abbreviation resp_runs :: "('a, 'b) m4_state \<Rightarrow> ('a, 'b) m4r_state" where "resp_runs u \<equiv> snd (snd u)"

type_synonym ('a, 'b) m4_state_trans = "('a, 'b) m4_state \<Rightarrow> ('a, 'b) m4_state \<Rightarrow> bool"


lemma dom_runs_obtain_init_run_state:   
  assumes "R \<in> dom runz" obtains agts store ib ob where 
    "runz R = Some \<lparr> agts = agts, store = store, ibuf = ib, obuf = ob \<rparr>"
  using assms
  by (metis domD init_run_state.cases)

lemma dom_runs_obtain_resp_run_state:   
  assumes "R \<in> dom runz" obtains agts store ib ob ad where 
    "runz R = Some \<lparr> agts = agts, store = store, ibuf = ib, obuf = ob, addrA = ad \<rparr>"
  using assms
  by (metis (mono_tags, opaque_lifting) domIff init_run_state.surjective not_None_eq 
      resp_run_state.ext_surjective run_state.cases run_state.ext_inject)

lemmas dom_runs_obtain_run_state = dom_runs_obtain_init_run_state dom_runs_obtain_resp_run_state


context crypto_algebra begin

abbreviation CIK0 where
  "CIK0 \<equiv> \<alpha>-`((Key`priK`bad) \<union> (Key`range pubK) \<union> (Key`shrK`bad))"  

definition
  m4_init :: "('a, 'b) m4_state \<Rightarrow> bool"
where
  "m4_init s \<longleftrightarrow> s = (
     CIK0,
     Map.empty, 
     Map.empty 
  )"

end

(******************************************************************************)
subsection \<open>Events\<close>
(******************************************************************************)

text \<open>We align the parameters of the events with the I/O library used for the implementation.
Since standard send and receive operations do not allow conditions on messages, we use 
input and output buffers to decouple the system components from the environment.\<close>


subsubsection \<open>Initiator internal events\<close>
(******************************************************************************)

context initiator begin

definition    \<comment> \<open>refines @{term "m3_init_start"}\<close> 
  m4_init_start :: "('a, 'b) m4_state_trans" 
where  
  "m4_init_start u u1 \<longleftrightarrow> 
     \<comment> \<open>guards\<close>
     Ra \<notin> dom (init_runs u) \<and>        \<comment> \<open>new run\<close>

     \<comment> \<open>actions\<close>
     u1 = (
       CIK u,
       (init_runs u)(Ra \<mapsto> \<lparr> agts = [A, B], store = [], ibuf = {}, obuf = None \<rparr>),
       resp_runs u
     )"

definition     \<comment> \<open>refines @{term "m3_resp_start"}\<close> 
  m4_init_put_M1 :: "'b \<Rightarrow> nonce \<Rightarrow> ('a, 'b) m4_state_trans"
where
  "m4_init_put_M1 bs Na u u1 \<longleftrightarrow> 
     \<comment> \<open>guards\<close>
     (\<exists>ib. init_runs u Ra = Some \<lparr> agts = [A, B], store = [], ibuf = ib, obuf = None \<rparr>) \<and>
     Na = #[Init,Ra,0] \<and>              \<comment> \<open>generate a fresh nonce\<close>
     \<lbrace>Agent A, Agent B, Nonce Na\<rbrace> = \<alpha> bs \<and>

     \<comment> \<open>actions\<close>
     u1 = (
       CIK u,
       (init_runs u)(Ra \<mapsto> the (init_runs u Ra)\<lparr> 
         obuf := Some bs 
       \<rparr>),
       resp_runs u
     )"

definition
  m4_init_get_M2 :: "'b \<Rightarrow> nonce \<Rightarrow> nonce \<Rightarrow> ('a, 'b) m4_state_trans"
where
  "m4_init_get_M2 bs Na Nb u u1 \<longleftrightarrow> 

     \<comment> \<open>guards\<close>
     (\<exists>ib ob ad. 
       init_runs u Ra = Some \<lparr> agts = [A, B], store = [], ibuf = ib, obuf = ob \<rparr> \<and>
       (ad, bs) \<in> ib \<and> Crypt (priK B) \<lbrace>Nonce Nb, Nonce Na, Agent A\<rbrace> = \<alpha> bs) \<and>
     Na = #[Init,Ra,0] \<and>

     \<comment> \<open>actions\<close>
     u1 = (
       CIK u,
       (init_runs u)(Ra \<mapsto> the (init_runs u Ra)\<lparr> store := [aNon Nb], obuf := None \<rparr>), 
       resp_runs u
     )"

end  \<comment> \<open>context initiator\<close>


subsubsection \<open>Responder events\<close>
(******************************************************************************)

context responder begin

definition    \<comment> \<open>refines @{term "m3_resp_start"}\<close>
  m4_resp_start :: "('a, 'b) m4_state_trans" 
where  
  "m4_resp_start u u1 \<longleftrightarrow> 

     \<comment> \<open>guards\<close>
     Rb \<notin> dom (resp_runs u) \<and>        \<comment> \<open>new run\<close>

     \<comment> \<open>actions\<close>
     u1 = (
       CIK u,
       init_runs u,
       (resp_runs u)(Rb \<mapsto> \<lparr> agts = [B], store = [], ibuf = {}, obuf = None, addrA = None \<rparr>)
     )"

definition
  m4_resp_get_M1 :: "'a \<Rightarrow> 'b \<Rightarrow> agent \<Rightarrow> nonce \<Rightarrow> nonce \<Rightarrow> ('a, 'b) m4_state_trans"
where
  "m4_resp_get_M1 ad bs A Nb Na u u1 \<longleftrightarrow> (

     \<comment> \<open>guards\<close>
     (\<exists>ib ob. 
       resp_runs u Rb = Some \<lparr> agts = [B], store = [], ibuf = ib, obuf = ob, addrA = None \<rparr> \<and>
       (ad, bs) \<in> ib \<and> \<lbrace>Agent A, Agent B, Nonce Na\<rbrace> = \<alpha> bs) \<and>
     Nb = #[Resp,Rb,0] \<and> 

     \<comment> \<open>actions\<close>
     u1 = (
       CIK u,
       init_runs u,
       (resp_runs u)(Rb \<mapsto> the (resp_runs u Rb)\<lparr> 
         agts := [B, A], store := [aNon Na], obuf := None, addrA := Some ad
       \<rparr>) 
     )
  )"

definition
  m4_resp_put_M2 :: "'a \<Rightarrow> 'b \<Rightarrow> agent \<Rightarrow> nonce \<Rightarrow> nonce \<Rightarrow> ('a, 'b) m4_state_trans"
where
  "m4_resp_put_M2 ad bs A Nb Na u u1 \<longleftrightarrow> 

     \<comment> \<open>guards\<close>
     (\<exists>ib. 
       resp_runs u Rb = Some \<lparr> 
         agts = [B, A], store = [aNon Na], ibuf = ib, obuf = None, addrA = Some ad 
       \<rparr>) \<and> 
     Nb = #[Resp,Rb,0] \<and>
     Crypt (priK B) \<lbrace>Nonce Nb, Nonce Na, Agent A\<rbrace> = \<alpha> bs \<and>

     \<comment> \<open>actions\<close>
     u1 = (
       CIK u,
       init_runs u,
       (resp_runs u)(Rb \<mapsto> the (resp_runs u Rb)\<lparr> 
         obuf := Some bs
       \<rparr>)
     )"

end \<comment> \<open>context responder\<close>


subsubsection \<open>I/O events\<close>
(******************************************************************************)

text \<open>Events to send and receive messages to and from the network.
Had to separate initiator and responder events, since ... [CHECK]\<close>

context initiator begin

definition
  m4_init_recv :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) m4_state_trans"
where
  "m4_init_recv ad bs u u1 \<longleftrightarrow>      \<comment> \<open>receiver gets sender's address and data\<close>

     \<comment> \<open>guards\<close>
     Ra \<in> dom (init_runs u) \<and>
     bs \<in> CIK u \<and>

     \<comment> \<open>actions\<close>
     u1 = (
       CIK u,
       (init_runs u)(Ra \<mapsto> (the (init_runs u Ra))\<lparr> 
         ibuf := insert (ad, bs) (ibuf (the (init_runs u Ra))) 
       \<rparr>),
       resp_runs u
     )"

definition
  m4_init_send :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) m4_state_trans"
where
  "m4_init_send ad bs u u1 \<longleftrightarrow>      \<comment> \<open>sender provides receiver's address and data\<close>  

     \<comment> \<open>guards\<close>
     Ra \<in> dom (init_runs u) \<and> 
     obuf (the (init_runs u Ra)) = Some bs \<and> 
     ad = addrB \<and>                   \<comment> \<open>fix the network address to the initiator's parameter\<close>

     \<comment> \<open>actions\<close>
     u1 = (
       insert bs (CIK u),
       init_runs u,
       resp_runs u
     )"

end \<comment> \<open>initiator\<close>


context responder begin

definition
  m4_resp_recv :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) m4_state_trans"
where
  "m4_resp_recv ad bs u u1 \<longleftrightarrow>      \<comment> \<open>receiver gets sender's address and data\<close>

     \<comment> \<open>guards\<close>
     Rb \<in> dom (resp_runs u) \<and>
     bs \<in> CIK u \<and>

     \<comment> \<open>actions\<close>
     u1 = (
       CIK u,
       init_runs u,
       (resp_runs u)(Rb \<mapsto> (the (resp_runs u Rb))\<lparr> 
         ibuf := insert (ad, bs) (ibuf (the (resp_runs u Rb))) 
       \<rparr>)
     )"

definition
  m4_resp_send :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) m4_state_trans"
where
  "m4_resp_send ad bs u u1 \<longleftrightarrow>      \<comment> \<open>sender provides receiver's address and data\<close>

     \<comment> \<open>guards\<close>
     Rb \<in> dom (resp_runs u) \<and> 
     obuf (the (resp_runs u Rb)) = Some bs \<and>
     addrA (the (resp_runs u Rb)) = Some ad \<and>

     \<comment> \<open>actions\<close>
     u1 = (
       insert bs (CIK u),
       init_runs u,
       resp_runs u
     )"

end \<comment> \<open>context responder\<close>


subsubsection \<open>Attacker internal event\<close>
(******************************************************************************)

text \<open>The intruder messages are now generated by a full-fledged Dolev-Yao intruder.\<close>

definition (in crypto_algebra)
  m4_CDY_fake :: "('a, 'b) m4_state_trans"
where
  "m4_CDY_fake u u1 \<longleftrightarrow>

     \<comment> \<open>actions:\<close>
     u1 = (
       csynth (canalz (CIK u)),
       init_runs u,
       resp_runs u
     )"


subsubsection \<open>Transition system\<close>
(******************************************************************************)

text \<open>Construct locales representing initiator and responder families. These fix the
component parameters to the run identifier and are used to construct the complete system 
model below.\<close>

locale initiator_family = crypto_algebra \<alpha> for \<alpha> :: "('b::countable) \<Rightarrow> msg" +
  fixes ip_A :: "rid \<Rightarrow> agent"
    and ip_B :: "rid \<Rightarrow> agent"
    and ip_addrB :: "rid \<Rightarrow> 'a::countable"
    and ip_pubKB :: "rid \<Rightarrow> 'b"
  assumes 
    ip_pubKB [simp]: "\<alpha> (ip_pubKB Ra) = Key (pubK (ip_B Ra))"
begin

sublocale ini: initiator \<alpha> Ra "ip_A Ra" "ip_B Ra" "ip_addrB Ra" "ip_pubKB Ra" for Ra 
  by unfold_locales simp

term ini.m4_init_start

end

locale responder_family = crypto_algebra \<alpha> for \<alpha> :: "('b::countable) \<Rightarrow> msg" +
  fixes rp_B :: "rid \<Rightarrow> agent"
    and rp_priKB :: "rid \<Rightarrow> 'b"
  assumes 
    rp_priKB [simp]: "\<alpha> (rp_priKB Ra) = Key (priK (rp_B Rb))"
begin

sublocale rsp: responder \<alpha> Rb "rp_B Rb" "rp_priKB Rb" for Rb
  by unfold_locales simp

term rsp.m4_resp_start

end


text \<open>Events no longer show components parameters, which have fixed above.\<close>

datatype ('a, 'b) m4_event = 
  m4_Init_start rid |
  m4_Init_put_M1 rid 'b nonce |
  m4_Init_get_M2 rid 'b nonce nonce |
  m4_Init_send rid 'a 'b |
  m4_Init_recv rid 'a 'b |
  m4_Resp_start rid |
  m4_Resp_get_M1 rid 'a 'b agent nonce nonce |
  m4_Resp_put_M2 rid 'a 'b agent nonce nonce |
  m4_Resp_send rid 'a 'b |
  m4_Resp_recv rid 'a 'b |
  m4_CDY_Fake |
  m4_Skip


text \<open>Locale for complete system model; imports instances of initiator and responder families.\<close>

locale complete_system = initiator_family \<alpha> + responder_family \<alpha> 
  for \<alpha> :: "('b::countable) \<Rightarrow> msg" 
begin

fun m4_trans :: "('a, 'b) m4_state \<Rightarrow> ('a, 'b) m4_event \<Rightarrow> ('a, 'b) m4_state \<Rightarrow> bool" where
  \<comment> \<open>initiator events\<close>
  "m4_trans s (m4_Init_start Ra) s' \<longleftrightarrow> ini.m4_init_start Ra s s'" |
  "m4_trans s (m4_Init_put_M1 Ra bs Na) s' \<longleftrightarrow> ini.m4_init_put_M1 Ra bs Na s s'" |
  "m4_trans s (m4_Init_get_M2 Ra bs Na Nb) s' \<longleftrightarrow> ini.m4_init_get_M2 Ra bs Na Nb s s'" |
  "m4_trans s (m4_Init_send R ad bs) s' \<longleftrightarrow> ini.m4_init_send R ad bs s s'" |
  "m4_trans s (m4_Init_recv R ad bs) s' \<longleftrightarrow> ini.m4_init_recv R ad bs s s'" |
  \<comment> \<open>responder events\<close>
  "m4_trans s (m4_Resp_start Rb) s' \<longleftrightarrow> rsp.m4_resp_start Rb s s'" |
  "m4_trans s (m4_Resp_get_M1 Rb A adA bs Nb Na) s' \<longleftrightarrow> rsp.m4_resp_get_M1 Rb A adA bs Nb Na s s'" |
  "m4_trans s (m4_Resp_put_M2 Rb A adA bs Nb Na) s' \<longleftrightarrow> rsp.m4_resp_put_M2 Rb A adA bs Nb Na s s'" |
  "m4_trans s (m4_Resp_send R ad bs) s' \<longleftrightarrow> rsp.m4_resp_send R ad bs s s'" |
  "m4_trans s (m4_Resp_recv R ad bs) s' \<longleftrightarrow> rsp.m4_resp_recv R ad bs s s'" |
  \<comment> \<open>attacker event and skip\<close>
  "m4_trans s (m4_CDY_Fake) s' \<longleftrightarrow> m4_CDY_fake s s'" |
  "m4_trans s (m4_Skip) s' \<longleftrightarrow> (s = s')"

lemmas m4_trans_defs = 
  ini.m4_init_start_def ini.m4_init_put_M1_def ini.m4_init_get_M2_def 
  ini.m4_init_recv_def ini.m4_init_send_def 
  rsp.m4_resp_start_def rsp.m4_resp_get_M1_def rsp.m4_resp_put_M2_def 
  rsp.m4_resp_recv_def rsp.m4_resp_send_def 
  m4_CDY_fake_def

lemmas m4_trans_induct = 
  m4_trans.induct [case_names 
    m4_init_start m4_init_put_M1 m4_init_get_M2 m4_init_send m4_init_recv 
    m4_resp_start m4_resp_get_M1 m4_resp_put_M2 m4_resp_send m4_resp_recv
    m4_CDY_fake m4_skip
  ]

definition
  m4 :: "(('a::countable, 'b) m4_event, ('a, 'b) m4_state) ES" where
  "m4 \<equiv> \<lparr>
    init = m4_init,
    trans = m4_trans
  \<rparr>"

lemmas m4_defs = m4_def m4_init_def m4_trans_defs

lemma trans_m4_eq [simp]: "(m4: s \<midarrow>e\<rightarrow> s') \<longleftrightarrow> m4_trans s e s'"
  by (auto simp add: m4_def)


(******************************************************************************)
subsection \<open>Invariants\<close>
(******************************************************************************)

subsubsection \<open>inv1: Input buffer messages contains intruder's messages\<close>
(******************************************************************************)

text \<open>Invariant stating that all "regular" messages in input buffer come from the intruder.\<close>

definition 
  m4_inv1_ibuf :: "('a, 'b) m4_state \<Rightarrow> bool" where
  "m4_inv1_ibuf u \<longleftrightarrow> (\<forall>R ad bs. 
     (R \<in> dom (init_runs u) \<longrightarrow> (ad, bs) \<in> ibuf (the (init_runs u R)) \<longrightarrow> bs \<in> CIK u) \<and>
     (R \<in> dom (resp_runs u) \<longrightarrow> (ad, bs) \<in> ibuf (the (resp_runs u R)) \<longrightarrow> bs \<in> CIK u) 
  )"

lemmas m4_inv1_ibufI = m4_inv1_ibuf_def [THEN iffD2, rule_format]
lemmas m4_inv1_ibufE [elim] = m4_inv1_ibuf_def [THEN iffD1, elim_format, rule_format]
lemmas m4_inv1_ibufD1 [dest] = m4_inv1_ibuf_def [THEN iffD1, rule_format, THEN conjunct1, rule_format]
lemmas m4_inv1_ibufD2 [dest] = m4_inv1_ibuf_def [THEN iffD1, rule_format, THEN conjunct2, rule_format]


text \<open>Invariance proof.\<close>

lemma m4_inv1_ibuf [simp, intro]: "reach m4 s \<Longrightarrow> m4_inv1_ibuf s"
proof (induction s rule: reach.induct)
  case (reach_init s)
  then show ?case 
    by (auto simp add: m4_defs intro!: m4_inv1_ibufI) 
next
  case (reach_trans s e s')
  then show ?case 
  proof (induction s e s' rule: m4_trans_induct)
    case (m4_CDY_fake s s')
    then show ?case
      by (auto simp add: m4_trans_defs csynth_canalz_eq synth.Inj intro!: m4_inv1_ibufI)
  qed (fastforce simp add: m4_trans_defs intro!: m4_inv1_ibufI dest: dom_lemmas)+
qed 


subsubsection \<open>inv2: Output buffer contains only protocol messages\<close>
(******************************************************************************)

text \<open>Invariant stating that output buffer contains only protocol messages.
The auxiliary definition below introduces some abstraction that improves proof automation.\<close>

definition init_protocol_message :: "rid \<Rightarrow> agent list \<Rightarrow> atom list \<Rightarrow> 'b \<Rightarrow> bool" where 
  "init_protocol_message R agents rs bs \<longleftrightarrow> 
     (\<exists>A B. agents = [A, B] \<and> rs = [] \<and>  
            \<alpha> bs = \<lbrace>Agent A, Agent B, Nonce (#[Init,R,0])\<rbrace>)"

definition resp_protocol_message :: "rid \<Rightarrow> agent list \<Rightarrow> atom list \<Rightarrow> 'b \<Rightarrow> bool" where
  "resp_protocol_message R agents rs bs \<longleftrightarrow> 
     (\<exists>A B Na. agents = [B, A] \<and> rs = [aNon Na] \<and> 
               \<alpha> bs = Crypt (priK B) \<lbrace>Nonce (#[Resp,R,0]), Nonce Na, Agent A\<rbrace>)"

lemmas init_protocol_messageI [intro] = init_protocol_message_def [THEN iffD2, rule_format]
lemmas init_protocol_messageE [elim] = init_protocol_message_def [THEN iffD1, elim_format]

lemmas resp_protocol_messageI [intro] = resp_protocol_message_def [THEN iffD2, rule_format]
lemmas resp_protocol_messageE [elim] = resp_protocol_message_def [THEN iffD1, elim_format]

definition 
  m4_inv2_obuf :: "('a, 'b) m4_state \<Rightarrow> bool" where
  "m4_inv2_obuf u \<longleftrightarrow> (\<forall>R agts rs ib bs ado. 
     (init_runs u R = Some \<lparr> agts = agts, store = rs, ibuf = ib, obuf = Some bs \<rparr> \<longrightarrow> 
       init_protocol_message R agts rs bs) \<and> 
     (resp_runs u R = Some \<lparr> agts = agts, store = rs, ibuf = ib, obuf = Some bs, addrA = ado \<rparr> \<longrightarrow> 
       resp_protocol_message R agts rs bs) 
  )" 

lemmas m4_inv2_obufI = m4_inv2_obuf_def [THEN iffD2, rule_format]
lemmas m4_inv2_obufE [elim] = m4_inv2_obuf_def [THEN iffD1, elim_format, rule_format]
lemmas m4_inv2_obufD [dest] = m4_inv2_obuf_def [THEN iffD1, rule_format, rotated 1]


text \<open>Invariance proof.\<close>

lemma m4_inv2_obuf [simp, intro]: "reach m4 s \<Longrightarrow> m4_inv2_obuf s"
proof (induction s rule: reach.induct)
  case (reach_init s)
  then show ?case 
    by (auto simp add: m4_defs intro!: m4_inv2_obufI) 
next
  case (reach_trans s e s')
  then show ?case
  proof (induction s e s' rule: m4_trans_induct)
  qed (auto 4 3 simp add: m4_trans_defs intro!: m4_inv2_obufI elim: dom_runs_obtain_run_state)
qed


(******************************************************************************)
subsection \<open>Refinement\<close>
(******************************************************************************)

fun m3_event_of_msg :: "rid \<Rightarrow> msg \<Rightarrow> m3_event" where 
  "m3_event_of_msg R (\<lbrace>Agent A, Agent B, Nonce Na\<rbrace>) = m3_Init_send R A B Na" |
  "m3_event_of_msg R (Crypt (priK B) \<lbrace>Nonce Nb, Nonce Na, Agent A\<rbrace>) = m3_Resp_send R B A Nb Na" |
  "m3_event_of_msg _ _ = m3_Skip"

thm m3_event_of_msg.induct 
thm m3_event_of_msg.cases 


fun \<pi>\<^sub>4 :: "('a, 'b) m4_event \<Rightarrow> m3_event" where
  \<comment> \<open>Initiator internal events\<close>
  "\<pi>\<^sub>4 (m4_Init_start R) = m3_Init_start R (ip_A R) (ip_B R)" |
  "\<pi>\<^sub>4 (m4_Init_put_M1 Ra bs Na) = m3_Skip" |
  "\<pi>\<^sub>4 (m4_Init_get_M2 Ra bs Na Nb) = m3_Init_recv Ra (ip_A Ra) (ip_B Ra) Na Nb" |
  \<comment> \<open>Responder internal events\<close>
  "\<pi>\<^sub>4 (m4_Resp_start R) = m3_Resp_start R (rp_B R)" |
  "\<pi>\<^sub>4 (m4_Resp_get_M1 Rb adA bs A Nb Na) = m3_Resp_recv Rb (rp_B Rb) A Nb Na " |
  "\<pi>\<^sub>4 (m4_Resp_put_M2 Rb adA bs A Nb Na) = m3_Skip" |
  \<comment> \<open>Send and receive\<close>
  "\<pi>\<^sub>4 (m4_Init_recv R ad bs) = m3_Skip" |    
  "\<pi>\<^sub>4 (m4_Init_send R ad bs) = m3_event_of_msg R (\<alpha> bs)" |   
  "\<pi>\<^sub>4 (m4_Resp_recv R ad bs) = m3_Skip" |    
  "\<pi>\<^sub>4 (m4_Resp_send R ad bs) = m3_event_of_msg R (\<alpha> bs)" |   
  \<comment> \<open>Intruder event and skip\<close>
  "\<pi>\<^sub>4 (m4_CDY_Fake) = m3_DY_Fake" |
  "\<pi>\<^sub>4 (m4_Skip) = m3_Skip"


text \<open>Define the simulation relation. Abstract initiator and responder run states to 
abstract run state by forgetting additional fields.\<close>

fun abs_run_state :: "'c run_state_scheme \<Rightarrow> run_state" where
  "abs_run_state rs = \<lparr> agts = agts rs, store = store rs \<rparr>"

fun abs_runs :: "(rid \<rightharpoonup> 'c run_state_scheme) \<Rightarrow> (rid \<rightharpoonup> run_state)" where
  "abs_runs runz R = map_option abs_run_state (runz R)"

lemma abs_init_runs_dom_eq [simp]: "dom (abs_runs runz) = dom runz"  
  by (auto simp add: domIff)

lemma abs_init_runs_ibuf_upd [simp]:
  "R \<in> dom runz \<Longrightarrow> abs_runs (runz(R \<mapsto> (the (runz R))\<lparr> ibuf := b \<rparr>)) = abs_runs runz"
  by (auto simp add: domIff)


fun h\<^sub>3\<^sub>4 :: "('a, 'b) m4_state \<Rightarrow> m3_state" where
  "h\<^sub>3\<^sub>4 u = \<lparr> 
     m1_state.init_runs = abs_runs (init_runs u), 
     m1_state.resp_runs = abs_runs (resp_runs u), 
     IK = \<alpha>`CIK u 
  \<rparr>"


theorem m4_refines_m3: "m4 \<sqsubseteq>\<^sub>\<pi>\<^sub>4 m3"
proof (intro simulate_ES_fun_with_invariant[where I="\<lambda>s. m4_inv1_ibuf s \<and> m4_inv2_obuf s"])
  fix s0
  assume "init m4 s0" 
  then show "init m3 (h\<^sub>3\<^sub>4 s0)"
    by (auto simp add: m3_defs m4_defs image_Un surj_alpha)
next    
  fix s t and e::"('a,'b) m4_event" and s'
  assume "m4: s\<midarrow>e\<rightarrow> s'" and "m4_inv1_ibuf s \<and> m4_inv2_obuf s" 
  then show "m3: h\<^sub>3\<^sub>4 s \<midarrow>\<pi>\<^sub>4 e\<rightarrow> h\<^sub>3\<^sub>4 s'"
  proof (induction s e s' rule: m4_trans_induct)
    case (m4_init_start s R s')
    then show ?case by (auto simp add: m3_defs m4_defs)
  next
    case (m4_init_put_M1 s Ra bs Na s')
    then show ?case by (auto simp add: m3_defs m4_defs)
  next
    case (m4_init_get_M2 s Ra bs Na Nb s')
    then show ?case 
      \<comment> \<open>requires inv1.\<close>
      by (auto simp add: m3_defs m4_defs intro!: imageI dest: dom_lemmas)
  next
    case (m4_resp_start s Rb s')
    then show ?case by (auto simp add: m3_defs m4_defs)
  next
    case (m4_resp_get_M1 s Rb A ad bs Nb Na s')
    then show ?case 
      \<comment> \<open>requires inv1.\<close>
      by (auto simp add: m3_defs m4_defs intro!: imageI dest: dom_lemmas)
  next
    case (m4_resp_put_M2 s Rb A ad bs Nb Na s')
    then show ?case by (auto simp add: m3_defs m4_defs)
  next
    case (m4_init_recv s R ad bs s')
    then show ?case by (auto simp add: m3_defs m4_defs )
  next
    case (m4_init_send s R ad bs s')
    then show ?case 
      \<comment> \<open>requires inv2.\<close>
      by (auto 4 3 simp add: m3_defs m4_defs elim!: dom_runs_obtain_init_run_state)
  next
    case (m4_resp_recv s R ad bs s')
    then show ?case by (auto simp add: m3_defs m4_defs)
  next
    case (m4_resp_send s R ad bs s')
    then show ?case 
      \<comment> \<open>requires inv2.\<close>
      by (auto 4 3 simp add: m3_defs m4_defs elim!: dom_runs_obtain_resp_run_state)
  next
    case (m4_CDY_fake s s')
    then show ?case 
      by (auto simp add: m3_defs m4_defs csynth_canalz_eq surj_alpha)
  qed simp
qed simp   

    
corollary m4_traced_included_m3: "map \<pi>\<^sub>4`traces m4 \<subseteq> traces m3"
  by (intro simulation_soundness m4_refines_m3)

end \<comment> \<open>locale complete system\<close>


end


