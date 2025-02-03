(*******************************************************************************

  Igloo Case Study: One-Way authentication protocols

  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
  Version: Isabelle/HOL 2020
  Date:    2019
  ID:      $Id: m5_sig.thy 152662 2020-08-06 09:54:41Z tklenze $
  
*******************************************************************************)

section \<open>Refinement 5: Decompositon of Signature-based Protocol Implementation\<close>

theory m5_sig 
  imports 
    m4_sig 
    "Igloo.Event_Systems_into_IO_Processes"
    "Igloo.Interleaving"
    "Igloo.Composition"
    "Igloo.Decomposition"
begin

text \<open>We decompose the protocol implementation into an environment model and an run-id-indexed 
family of models, one for each run id.\<close>

(******************************************************************************)
subsection \<open>Environment model\<close> 
(******************************************************************************)

subsubsection \<open>State\<close>

type_synonym 'b m5e_state = "'b m4e_state"

definition (in crypto_algebra) m5e_init :: "'b m5e_state \<Rightarrow> bool" where
  "m5e_init cik \<longleftrightarrow> cik = CIK0"


subsubsection \<open>Events\<close>

datatype ('a, 'b) m5e_event = 
  m5e_Send 'a 'b |
  m5e_Recv 'a 'b |
  m5e_CDY_Fake |
  m5e_Skip

context crypto_algebra begin

text \<open>Send and receive events for arbitrary messages.\<close>

definition
  m5e_send :: "'a \<Rightarrow> 'b \<Rightarrow> 'b m5e_state \<Rightarrow> 'b m5e_state \<Rightarrow> bool"
where
  "m5e_send ad bs cik cik1 \<longleftrightarrow>    \<comment> \<open>address is a dummy parameter, not modeled\<close>
     \<comment> \<open>actions\<close>
     cik1 = insert bs cik"        \<comment> \<open>send a message\<close>
     
definition
  m5e_recv :: "'a \<Rightarrow> 'b \<Rightarrow> 'b m5e_state \<Rightarrow> 'b m5e_state \<Rightarrow> bool"
where
  "m5e_recv ad bs cik cik1 \<longleftrightarrow>

     \<comment> \<open>guards\<close>
     bs \<in> cik \<and>            \<comment> \<open>receive a message\<close>

     \<comment> \<open>actions\<close>
     cik1 = cik"


text \<open>Intruder event.\<close>

definition
  m5e_CDY_fake :: "'b m5e_state \<Rightarrow> 'b m5e_state \<Rightarrow> bool"
where
  "m5e_CDY_fake cik cik1 \<longleftrightarrow>

     \<comment> \<open>actions:\<close>
     cik1 = csynth (canalz cik)"


fun m5e_trans :: "'b m5e_state \<Rightarrow> ('a, 'b) m5e_event \<Rightarrow> 'b m5e_state \<Rightarrow> bool" where
  "m5e_trans t (m5e_Send ad bs) t' \<longleftrightarrow> m5e_send ad bs t t'" |
  "m5e_trans t (m5e_Recv ad bs) t' \<longleftrightarrow> m5e_recv ad bs t t'" |
  "m5e_trans t (m5e_CDY_Fake) t' \<longleftrightarrow> m5e_CDY_fake t t'" |
  "m5e_trans t (m5e_Skip) t' \<longleftrightarrow> t = t'" 

lemmas m5e_trans_defs = m5e_send_def m5e_recv_def m5e_CDY_fake_def
lemmas m5e_trans_induct = m5e_trans.induct [case_names m5e_send m5e_recv m5e_CDY_fake m5e_skip]


subsubsection \<open>Event system\<close>

definition m5e :: "(('a, 'b) m5e_event, 'b m5e_state) ES" where 
  "m5e = \<lparr> init = m5e_init, trans = m5e_trans \<rparr>"

lemmas m5e_defs = m5e_def m5e_init_def m5e_trans_defs

end \<comment> \<open>context crypto algebra\<close>


(******************************************************************************)
subsection \<open>System component model: initiator and responder\<close> 
(******************************************************************************)

text \<open>We have two component types, inititors and responders.\<close>


subsubsection \<open>Initiator model\<close>
(******************************************************************************)

type_synonym ('a, 'b) m5i_state = "('a, 'b) init_run_state option"     \<comment> \<open>None before creation\<close>

definition m5i_init :: "('a, 'b) m5i_state" where
  "m5i_init = None"


text \<open>Define the type of values.\<close>

datatype ('a, 'b) ival = 
  iv_Unit |
  iv_M1 'b nonce |
  iv_M2 'b nonce nonce |
  iv_IO 'a 'b

instance ival :: (countable, countable) countable
  by countable_datatype


text \<open>Define the basic I/O operations.\<close>

datatype bio5i = 
  B_m5i_init_start | B_m5i_init_put_M1 | B_m5i_init_get_M2 | B_m5i_recv | B_m5i_send | B_m5i_skip

lemma bio5i_UNIV: 
  "UNIV = {B_m5i_init_start, B_m5i_init_put_M1, B_m5i_init_get_M2, B_m5i_recv, B_m5i_send, B_m5i_skip}"
  by (blast intro: bio5i.exhaust)

instance bio5i :: finite
proof
  show "finite (UNIV::bio5i set)" by (auto simp add: bio5i_UNIV)
qed

text \<open>Define the input typing. We instantiate the Typing locale inside the initiator locale. 
Using "sublocale" rather than "instantiation" ensures that the instantiation is dynamic, i.e., 
additions to the Typing locale by later theory imports will be available inside the initiator 
locale.\<close>

fun bio5i_typing :: "bio5i \<Rightarrow> ('a::countable, 'b::countable) ival \<Rightarrow> ('a, 'b) ival set" where
  "bio5i_typing B_m5i_recv _ = range (prod.case_prod iv_IO)" |   \<comment> \<open>the only input\<close>
  "bio5i_typing _          _ = {iv_Unit}"

sublocale initiator \<subseteq> bio5i : Typing bio5i_typing
  by unfold_locales (auto elim: bio5i_typing.elims)


text \<open>Define some constructor-style abbreviations for events that can actually occur.\<close>

abbreviation m5i_Init_start_act :: "(bio5i, ('a, 'b) ival) action" where 
  "m5i_Init_start_act \<equiv> ActBio B_m5i_init_start iv_Unit iv_Unit"

abbreviation m5i_Init_put_M1_act :: "'b \<Rightarrow> nonce \<Rightarrow> (bio5i, ('a, 'b) ival) action" where 
  "m5i_Init_put_M1_act bs Na \<equiv> ActBio B_m5i_init_put_M1 (iv_M1 bs Na) iv_Unit"

abbreviation m5i_Init_get_M2_act :: "'b \<Rightarrow> nonce \<Rightarrow> nonce \<Rightarrow> (bio5i, ('a, 'b) ival) action" where 
  "m5i_Init_get_M2_act bs Na Nb \<equiv> ActBio B_m5i_init_get_M2 (iv_M2 bs Na Nb) iv_Unit"

abbreviation m5i_Recv_act :: "'a \<Rightarrow> 'b \<Rightarrow> (bio5i, ('a, 'b) ival) action" where 
  "m5i_Recv_act ad bs \<equiv> ActBio B_m5i_recv iv_Unit (iv_IO ad bs)"

abbreviation m5i_Send_act :: "'a \<Rightarrow> 'b \<Rightarrow> (bio5i, ('a, 'b) ival) action" where 
  "m5i_Send_act ad bs \<equiv> ActBio B_m5i_send (iv_IO ad bs) iv_Unit"

abbreviation m5i_Skip_act :: "(bio5i, ('a, 'b) ival) action" where 
  "m5i_Skip_act \<equiv> ActBio B_m5i_skip iv_Unit iv_Unit"


text \<open>We will below rename the action-based events into a new datatype in order to make 
the definition of the synchronization map more efficient.\<close>

datatype ('a, 'b) m5i_event =
  m5i_Init_start |
  m5i_Init_put_M1 'b nonce |
  m5i_Init_get_M2 'b nonce nonce | 
  m5i_Recv 'a 'b |
  m5i_Send 'a 'b |
  m5i_Skip |
  m5i_Stop         \<comment> \<open>non-executable\<close>

text \<open>Map action-based events to simpler events datatype. Non-typable combinations 
are not executable and are mapped to a stop event.\<close>

fun \<rho> :: "(bio5i, ('a, 'b) ival) action \<Rightarrow> ('a, 'b) m5i_event" where
  "\<rho> m5i_Init_start_act = m5i_Init_start" |
  "\<rho> (m5i_Init_put_M1_act bs Na) = m5i_Init_put_M1 bs Na" |
  "\<rho> (m5i_Init_get_M2_act bs Na Nb) = m5i_Init_get_M2 bs Na Nb" | 
  "\<rho> (m5i_Recv_act ad bs) = m5i_Recv ad bs" |
  "\<rho> (m5i_Send_act ad bs) = m5i_Send ad bs" |
  "\<rho> m5i_Skip_act = m5i_Skip" |
  "\<rho> _ = m5i_Stop"

lemma \<rho>_invert [simp]:
  "\<rho> x = m5i_Init_start \<longleftrightarrow> x = m5i_Init_start_act"
  "\<rho> x = m5i_Init_put_M1 bs Na \<longleftrightarrow> x = m5i_Init_put_M1_act bs Na" 
  "\<rho> x = m5i_Init_get_M2 bs Na Nb \<longleftrightarrow> x = m5i_Init_get_M2_act bs Na Nb" 
  "\<rho> x = m5i_Recv ad bs \<longleftrightarrow> x = m5i_Recv_act ad bs" 
  "\<rho> x = m5i_Send ad bs \<longleftrightarrow> x = m5i_Send_act ad bs" 
  "\<rho> x = m5i_Skip \<longleftrightarrow> x = m5i_Skip_act" 
  by (auto elim: \<rho>.elims)


text \<open>Define the actual events.\<close>

context initiator begin

definition
  m5i_init_start :: "(('a, 'b) m5i_state, ('a, 'b) ival) guarded_update" 
where  
  "m5i_init_start rs v = \<lparr>
     guard = rs = None \<and> v = iv_Unit,
     update = \<lambda>_. Some \<lparr> agts = [A, B], store = [], ibuf = {}, obuf = None \<rparr>
  \<rparr>"

definition
  m5i_init_put_M1 :: "(('a, 'b) m5i_state, ('a, 'b) ival) guarded_update"
where
  "m5i_init_put_M1 rs v = (case v of 
     iv_M1 bs Na \<Rightarrow> \<lparr>
       guard = (\<exists>ib. rs = Some \<lparr> agts = [A, B], store = [], ibuf = ib, obuf = None \<rparr>) \<and>
               Na = #[Init,Ra,0] \<and> \<lbrace> Agent A, Agent B, Nonce Na \<rbrace> = \<alpha> bs,       
       update = \<lambda>_. Some (the rs\<lparr> obuf := Some bs \<rparr>)
     \<rparr> |
     _ \<Rightarrow> gNull rs v
  )"

definition
  m5i_init_get_M2 :: "(('a, 'b) m5i_state, ('a, 'b) ival) guarded_update"
where
  "m5i_init_get_M2 rs v = (case v of 
     iv_M2 bs Na Nb \<Rightarrow> \<lparr>
       guard = (\<exists>ib ob ad. 
                  rs = Some \<lparr> agts = [A, B], store = [], ibuf = ib, obuf = ob \<rparr> \<and>
                  (ad, bs) \<in> ib \<and> Crypt (priK B) \<lbrace>Nonce Nb, Nonce Na, Agent A\<rbrace> = \<alpha> bs) \<and>
               Na = #[Init,Ra,0],
       update = \<lambda>_. Some (the rs\<lparr> store := [aNon Nb], obuf := None \<rparr>) 
     \<rparr> |
     _ \<Rightarrow> gNull rs v
  )"

definition
  m5i_send :: "(('a, 'b) m5i_state, ('a, 'b) ival) guarded_update"
where
  "m5i_send rs v = (case v of 
      iv_IO ad bs \<Rightarrow> \<lparr>
        guard = rs \<noteq> None \<and> obuf (the rs) = Some bs \<and> ad = addrB,
        update = \<lambda>_. rs 
      \<rparr> |
      _ \<Rightarrow> gNull rs v
  )"

definition
  m5i_recv :: "(('a, 'b) m5i_state, ('a, 'b) ival) guarded_update"
where
  "m5i_recv rs v = \<lparr>
     guard = rs \<noteq> None \<and> v = iv_Unit,
     update = \<lambda>w. 
       case w of 
         iv_IO ad bs \<Rightarrow> Some (the rs\<lparr> ibuf := insert (ad, bs) (ibuf (the rs)) \<rparr>) |
         _ \<Rightarrow> rs    \<comment> \<open>never used due to typing\<close>
  \<rparr>"

lemmas m5i_trans_defs =
  m5i_init_start_def m5i_init_put_M1_def m5i_init_get_M2_def m5i_send_def m5i_recv_def


text \<open>Define an I/O-guarded event system for initiators and instantiate it with fixed parameters 
depending on the run id.\<close>

fun m5i_ioges :: "(('a, 'b) m5i_state, bio5i, ('a, 'b) ival) IOGES" 
where
  "m5i_ioges B_m5i_init_start = m5i_init_start" |
  "m5i_ioges B_m5i_init_put_M1 = m5i_init_put_M1" |
  "m5i_ioges B_m5i_init_get_M2 = m5i_init_get_M2" |
  "m5i_ioges B_m5i_send = m5i_send" |
  "m5i_ioges B_m5i_recv = m5i_recv" |
  "m5i_ioges B_m5i_skip = gSkip" 


text \<open>Parametrized event system for initiators.\<close>

abbreviation m5i_base :: "((bio5i, ('a::countable, 'b) ival) action, ('a, 'b) m5i_state) ES" where 
  "m5i_base \<equiv> bio5i.IOGES_to_ES (m5i_ioges) ((=) m5i_init)"

definition m5i :: "(('a::countable, 'b) m5i_event, ('a, 'b) m5i_state) ES" where 
  "m5i = (m5i_base)\<lceil>\<rho>\<rceil>"

lemmas m5i_defs = 
  m5i_def bio5i.IOGES_to_ES_def m5i_trans_defs m5i_init_def 

end \<comment> \<open>context initiator\<close>

term initiator.m5i


subsubsection \<open>Responder model\<close>
(******************************************************************************)

type_synonym ('a, 'b) m5r_state = "('a, 'b) resp_run_state option"     \<comment> \<open>None before creation\<close>

definition m5r_init :: "('a, 'b) m5r_state" where
  "m5r_init = None"


text \<open>Define the type of values.\<close>

datatype ('a, 'b) rval = 
  rv_Unit |
  rv_Int 'a 'b agent nonce nonce |
  rv_IO 'a 'b

instance rval :: (countable, countable) countable
  by countable_datatype


text \<open>Define the basic I/O operations.\<close>

datatype bio5r = 
  B_m5r_resp_start | B_m5r_resp_get_M1 | B_m5r_resp_put_M2 | B_m5r_recv | B_m5r_send | B_m5r_skip

lemma bio5r_UNIV: 
  "UNIV = {B_m5r_resp_start, B_m5r_resp_get_M1, B_m5r_resp_put_M2, B_m5r_recv, B_m5r_send, B_m5r_skip}"
  by (blast intro: bio5r.exhaust)

instance bio5r :: finite
proof
  show "finite (UNIV::bio5r set)" by (auto simp add: bio5r_UNIV)
qed

text \<open>Define the input typing. We instantiate the Typing locale inside the responder locale. 
Using "sublocale" rather than "instantiation" ensures that the instantiation is dynamic, i.e., 
additions to the Typing locale by further theory imports will be available inside the responder 
locale.\<close>

fun bio5r_typing :: "bio5r \<Rightarrow> ('a, 'b) rval \<Rightarrow> ('a, 'b) rval set" where
  "bio5r_typing B_m5r_recv _ = range (prod.case_prod rv_IO)" |    \<comment> \<open>the only input\<close>
  "bio5r_typing _          _ = {rv_Unit}"

sublocale responder \<subseteq> bio5r : Typing bio5r_typing
  by unfold_locales (auto elim: bio5r_typing.elims)


text \<open>Define some constructor-style abbreviations for events that can actually occur.\<close>

abbreviation m5r_Resp_start_act :: "(bio5r, ('a, 'b) rval) action" where 
  "m5r_Resp_start_act \<equiv> ActBio B_m5r_resp_start rv_Unit rv_Unit"

abbreviation 
  m5r_Resp_get_M1_act :: "'a \<Rightarrow> 'b \<Rightarrow> agent \<Rightarrow> nonce \<Rightarrow> nonce \<Rightarrow> (bio5r, ('a, 'b) rval) action" 
where  
  "m5r_Resp_get_M1_act ad bs A Nb Na \<equiv> ActBio B_m5r_resp_get_M1 (rv_Int ad bs A Nb Na) rv_Unit"

abbreviation 
  m5r_Resp_put_M2_act :: "'a \<Rightarrow> 'b \<Rightarrow> agent \<Rightarrow> nonce \<Rightarrow> nonce \<Rightarrow> (bio5r, ('a, 'b) rval) action" 
where 
  "m5r_Resp_put_M2_act ad bs A Nb Na \<equiv> ActBio B_m5r_resp_put_M2 (rv_Int ad bs A Nb Na) rv_Unit"

abbreviation m5r_Recv_act :: "'a \<Rightarrow> 'b \<Rightarrow> (bio5r, ('a, 'b) rval) action" where 
  "m5r_Recv_act ad bs \<equiv> ActBio B_m5r_recv rv_Unit (rv_IO ad bs)"

abbreviation m5r_Send_act :: "'a \<Rightarrow> 'b \<Rightarrow> (bio5r, ('a, 'b) rval) action" where 
  "m5r_Send_act ad bs \<equiv> ActBio B_m5r_send (rv_IO ad bs) rv_Unit"

abbreviation m5r_Skip_act :: "(bio5r, ('a, 'b) rval) action" where 
  "m5r_Skip_act \<equiv> ActBio B_m5r_skip rv_Unit rv_Unit"


text \<open>We will below rename the action-based events into a new datatype in order to make 
the definition of the synchronization map more efficient.\<close>

datatype ('a, 'b) m5r_event = 
  m5r_Resp_start |
  m5r_Resp_get_M1 'a 'b agent nonce nonce |
  m5r_Resp_put_M2 'a 'b agent nonce nonce |
  m5r_Recv 'a 'b |
  m5r_Send 'a 'b |
  m5r_Skip |
  m5r_Stop         \<comment> \<open>non-executable\<close>

text \<open>Map action-based events to simpler datatype events. All "strange" combinations 
are not executable and are mapped to a stop event.\<close>

fun \<beta> :: "(bio5r, ('a, 'b) rval) action \<Rightarrow> ('a, 'b) m5r_event" where
  "\<beta> m5r_Resp_start_act = m5r_Resp_start" |
  "\<beta> (m5r_Resp_get_M1_act ad bs A Nb Na) = m5r_Resp_get_M1 ad bs A Nb Na" |
  "\<beta> (m5r_Resp_put_M2_act ad bs A Nb Na) = m5r_Resp_put_M2 ad bs A Nb Na" |
  "\<beta> (m5r_Recv_act ad bs) = m5r_Recv ad bs" |
  "\<beta> (m5r_Send_act ad bs) = m5r_Send ad bs" |
  "\<beta> m5r_Skip_act = m5r_Skip" |
  "\<beta> _ = m5r_Stop"

lemma \<beta>_invert [simp]:
  "\<beta> x = m5r_Resp_start \<longleftrightarrow> x = m5r_Resp_start_act"
  "\<beta> x = m5r_Resp_get_M1 ad bs A Nb Na \<longleftrightarrow> x = m5r_Resp_get_M1_act ad bs A Nb Na" 
  "\<beta> x = m5r_Resp_put_M2 ad bs A Nb Na \<longleftrightarrow> x = m5r_Resp_put_M2_act ad bs A Nb Na"
  "\<beta> x = m5r_Recv ad bs \<longleftrightarrow> x = m5r_Recv_act ad bs" 
  "\<beta> x = m5r_Send ad bs \<longleftrightarrow> x = m5r_Send_act ad bs" 
  "\<beta> x = m5r_Skip \<longleftrightarrow> x = m5r_Skip_act" 
  by (auto elim: \<beta>.elims)


context responder begin

definition
  m5r_resp_start :: 
    "(('a, 'b) m5r_state, ('a, 'b) rval) guarded_update" 
where  
  "m5r_resp_start rs v = \<lparr>
     guard = rs = None \<and> v = rv_Unit,
     update = \<lambda>_. Some \<lparr> agts = [B], store = [], ibuf = {}, obuf = None, addrA = None \<rparr>
  \<rparr>"

definition
  m5r_resp_get_M1 :: "(('a, 'b) m5r_state, ('a, 'b) rval) guarded_update"
where
  "m5r_resp_get_M1 rs v = (case v of 
     rv_Int ad bs A Nb Na \<Rightarrow> \<lparr>
       guard = (\<exists>ob ib. 
                  rs = Some \<lparr> agts = [B], store = [], ibuf = ib, obuf = ob, addrA = None \<rparr> \<and>
                  (ad, bs) \<in> ib \<and> \<lbrace>Agent A, Agent B, Nonce Na\<rbrace> = \<alpha> bs) \<and>
                Nb = #[Resp,Rb,0],
       update = \<lambda>_. Some ((the rs)\<lparr> agts := [B, A], store := [aNon Na], obuf := None, addrA := Some ad \<rparr>) 
     \<rparr> |
     _ \<Rightarrow> gNull rs v
  )"

definition
  m5r_resp_put_M2 :: "(('a, 'b) m5r_state, ('a, 'b) rval) guarded_update"
where
  "m5r_resp_put_M2 rs v = (case v of 
       rv_Int ad bs A Nb Na \<Rightarrow> \<lparr>
         guard = (\<exists>ib. rs = Some \<lparr> agts = [B, A], store = [aNon Na], 
                                   ibuf = ib, obuf = None, addrA = Some ad \<rparr>) \<and> 
                 Nb = #[Resp,Rb,0] \<and> Crypt (priK B) \<lbrace>Nonce Nb, Nonce Na, Agent A\<rbrace> = \<alpha> bs,
         update = \<lambda>_. Some (the rs\<lparr> obuf := Some bs \<rparr>) 
     \<rparr> |
       _ \<Rightarrow> gNull rs v
  )"

definition
  m5r_send :: "(('a, 'b) m5r_state, ('a, 'b) rval) guarded_update"
where
  "m5r_send rs v = (case v of 
      rv_IO ad bs \<Rightarrow> \<lparr>
        guard = rs \<noteq> None \<and> addrA (the rs) = Some ad \<and> obuf (the rs) = Some bs,
        update = \<lambda>_. rs 
      \<rparr> |
      _ \<Rightarrow> gNull rs v
  )"

definition
  m5r_recv :: "(('a, 'b) m5r_state, ('a, 'b) rval) guarded_update"
where
  "m5r_recv rs v = \<lparr>
     guard = rs \<noteq> None \<and> v = rv_Unit,
     update = \<lambda>w. 
       case w of 
         rv_IO ad bs \<Rightarrow> Some (the rs\<lparr> ibuf := insert (ad, bs) (ibuf (the rs)) \<rparr>) |
         _ \<Rightarrow> rs    \<comment> \<open>never used due to typing\<close>
  \<rparr>"

lemmas m5r_trans_defs =
  m5r_resp_start_def m5r_resp_get_M1_def m5r_resp_put_M2_def m5r_send_def m5r_recv_def 


text \<open>Define an I/O-guarded event system for responders and instantiate it with fixed parameters 
depending on the run id.\<close>

fun m5r_ioges :: "(('a, 'b) m5r_state, bio5r, ('a, 'b) rval) IOGES"
where
  "m5r_ioges B_m5r_resp_start = m5r_resp_start" |
  "m5r_ioges B_m5r_resp_get_M1 = m5r_resp_get_M1" |
  "m5r_ioges B_m5r_resp_put_M2 = m5r_resp_put_M2" |
  "m5r_ioges B_m5r_send = m5r_send" |
  "m5r_ioges B_m5r_recv = m5r_recv" |
  "m5r_ioges B_m5r_skip = gSkip" 


text \<open>Parametrized event system for responders\<close>

abbreviation m5r_base :: "((bio5r, ('a::countable, 'b) rval) action, ('a, 'b) m5r_state) ES" where 
  "m5r_base \<equiv> bio5r.IOGES_to_ES m5r_ioges ((=) m5r_init)"

definition m5r :: "(('a::countable, 'b) m5r_event, ('a, 'b) m5r_state) ES" where 
  "m5r = (m5r_base)\<lceil>\<beta>\<rceil>"

lemmas m5r_defs = m5r_def m5r_init_def bio5r.IOGES_to_ES_def m5r_trans_defs 

end \<comment> \<open>context responder\<close>

term responder.m5r


(******************************************************************************)
subsection \<open>Composed system model\<close> 
(*****************************************************************************)

text \<open>We first build the system from the two system component types.\<close>

type_synonym ('a, 'b) m5s_state = "(rid \<Rightarrow> ('a, 'b) m5i_state) \<times> (rid \<Rightarrow> ('a, 'b) m5r_state)"
type_synonym ('a, 'b) m5s_event = "rid \<times> ('a, 'b) m5i_event + rid \<times> ('a, 'b) m5r_event"


context complete_system
begin

abbreviation m5s :: "(('a::countable, 'b) m5s_event, ('a, 'b) m5s_state) ES" where 
  "m5s \<equiv> (\<parallel>\<parallel> ini.m5i) || (\<parallel>\<parallel> rsp.m5r)"

lemmas m5s_defs = ini.m5i_defs rsp.m5r_defs


(******************************************************************************)
subsection \<open>Complete system model and decomposition correctness\<close> 
(******************************************************************************)

text \<open>Next we compose the system with the environment. We use the events from the previous model
as the target.\<close>

fun \<chi> :: "('a, 'b) m5e_event \<times> ('a, 'b) m5s_event \<rightharpoonup> ('a, 'b) m4_event" where
  \<comment> \<open>initiator internal events\<close>
  "\<chi> (m5e_Skip, Inl (Ra, m5i_Init_start)) = 
    Some (m4_Init_start Ra)" |
  "\<chi> (m5e_Skip, Inl (Ra, m5i_Init_put_M1 bs Na)) = 
     Some (m4_Init_put_M1 Ra bs Na)" |
  "\<chi> (m5e_Skip, Inl (Ra, m5i_Init_get_M2 bs Na Nb)) = 
     Some (m4_Init_get_M2 Ra bs Na Nb)" |

  \<comment> \<open>responder internal events\<close>
  "\<chi> (m5e_Skip, Inr (Rb, m5r_Resp_start)) =
    Some (m4_Resp_start Rb)" |
  "\<chi> (m5e_Skip, Inr (Rb, m5r_Resp_get_M1 ad bs A Nb Na)) = 
     Some (m4_Resp_get_M1 Rb ad bs A Nb Na)" |
  "\<chi> (m5e_Skip, Inr (Rb, m5r_Resp_put_M2 ad bs A Nb Na)) = 
     Some (m4_Resp_put_M2 Rb ad bs A Nb Na)" |

  \<comment> \<open>synchronized send and receive events\<close>
  "\<chi> (m5e_Recv ad' bs', Inl (Ra, m5i_Recv ad bs)) =
     (if ad = ad' \<and> bs = bs' then Some (m4_Init_recv Ra ad bs) else None)" |
  "\<chi> (m5e_Send ad' bs', Inl (Ra, m5i_Send ad bs)) = 
     (if ad = ad' \<and> bs = bs' then Some (m4_Init_send Ra ad bs) else None)" |
  "\<chi> (m5e_Recv ad' bs', Inr (Rb, m5r_Recv ad bs)) =
     (if ad = ad' \<and> bs = bs' then Some (m4_Resp_recv Rb ad bs) else None)" |
  "\<chi> (m5e_Send ad' bs', Inr (Rb, m5r_Send ad bs)) = 
     (if ad = ad' \<and> bs = bs' then Some (m4_Resp_send Rb ad bs) else None)" |

  \<comment> \<open>environment internal event\<close>
  "\<chi> (m5e_CDY_Fake, Inl (R, m5i_Skip)) = Some m4_CDY_Fake" |
  "\<chi> (m5e_CDY_Fake, Inr (R, m5r_Skip)) = Some m4_CDY_Fake" |

  \<comment> \<open>skip and blocked combinations\<close>
  "\<chi> (m5e_Skip, Inl (R, m5i_Skip)) = Some m4_Skip" |
  "\<chi> (m5e_Skip, Inr (R, m5r_Skip)) = Some m4_Skip" |
  "\<chi> _ = None"
(*
  Warnings: Isabelle bug?
*)

lemma \<chi>_invert [simp]:
  "\<chi> x = Some (m4_Init_start Ra) \<longleftrightarrow> 
     x = (m5e_Skip, Inl (Ra, m5i_Init_start))" 
  "\<chi> x = Some (m4_Init_put_M1 Ra bs Na) \<longleftrightarrow>
     x = (m5e_Skip, Inl (Ra, m5i_Init_put_M1 bs Na))"
  "\<chi> x = Some (m4_Init_get_M2 Ra bs Na Nb) \<longleftrightarrow>
     x = (m5e_Skip, Inl (Ra, m5i_Init_get_M2 bs Na Nb))" 
  "\<chi> x = Some (m4_Init_recv R ad bs) \<longleftrightarrow>
     x = (m5e_Recv ad bs, Inl (R, m5i_Recv ad bs))"
  "\<chi> x = Some (m4_Init_send R ad bs) \<longleftrightarrow>
     x = (m5e_Send ad bs, Inl (R, m5i_Send ad bs))"

  "\<chi> x = Some (m4_Resp_start Rb) \<longleftrightarrow>
     x = (m5e_Skip, Inr (Rb, m5r_Resp_start))" 
  "\<chi> x = Some (m4_Resp_get_M1 Rb ad bs A Nb Na) \<longleftrightarrow>
     x = (m5e_Skip, Inr (Rb, m5r_Resp_get_M1 ad bs A Nb Na))" 
  "\<chi> x = Some (m4_Resp_put_M2 Rb ad bs A Nb Na) \<longleftrightarrow> 
     x = (m5e_Skip, Inr (Rb, m5r_Resp_put_M2 ad bs A Nb Na))"
  "\<chi> x = Some (m4_Resp_recv R ad bs) \<longleftrightarrow>
     x = (m5e_Recv ad bs, Inr (R, m5r_Recv ad bs))"
  "\<chi> x = Some (m4_Resp_send R ad bs) \<longleftrightarrow>
     x = (m5e_Send ad bs, Inr (R, m5r_Send ad bs))"

  "\<chi> x = Some m4_CDY_Fake \<longleftrightarrow> 
     (\<exists>R. x = (m5e_CDY_Fake, Inl (R, m5i_Skip)) \<or> x = (m5e_CDY_Fake, Inr (R, m5r_Skip)))"
  "\<chi> x = Some m4_Skip \<longleftrightarrow> 
     (\<exists>R. x = (m5e_Skip, Inl (R, m5i_Skip)) \<or> x = (m5e_Skip, Inr (R, m5r_Skip)))"
  by (auto elim: \<chi>.elims)


abbreviation m5 :: "(('a::countable, 'b) m4_event, 'b m5e_state \<times> ('a, 'b) m5s_state) ES" where 
  "m5 \<equiv> (m5e \<parallel>\<chi> m5s)"

lemmas m5_defs = m5e_defs m5s_defs


lemma m4_equiv_m5: "traces m4 = traces m5"
proof (induction rule: decomposition_env_system_equiv)
  case (surj u g u')
  then show ?case 
    by (induction u g u' rule: m4_trans_induct) 
       (auto 4 5 simp add: m4_defs)
next
  case (init s t)
  then show ?case by (cases t) (auto simp add: m4_defs m5_defs)
next
  case (trans e f g s t s' t')
  then show ?case
  by (induction "(s, t)" g "(s', t')" rule: m4_trans_induct)
     (cases t, cases t', fastforce simp add: m4_defs m5_defs)+
qed

end  \<comment> \<open>context complete system\<close>

end
