(*
  Igloo Case Study: Replication 
  Primary-Backup Replication

  Author: Tobias Klenze <tobias.klenze@inf.ethz.ch>
  Date: December 2019
*)
section \<open>Primary-Backup Replication, Decomposition\<close>

theory Primary_Backup_2
  imports
    "Primary_Backup_1"
    "HOL-Library.Countable_Set"
    "../../Interleaving"
    "../../Event_Composition"
    "../../Composition"
    "../../Decomposition"
    "../../Event_Systems_into_IO_Processes"
begin
text\<open>In this theory, we decompose the global system into a model m2sys and an environment m2e.
m2sys is further decomposed into a family of event systems for clients (each event system 
representing an individual client), and, similarly, a family of event systems for servers.
We then show that the re-composition of these component event systems and the environment yield a 
global event system that is trace equivalent to the protocol model m1.\<close>

instance m1_sync :: (countable) countable
  by countable_datatype

declare if_split_asm [split]

type_synonym 'uop m2_event = "'uop m1_event"

type_synonym 'uop m2_sync = "'uop m1_sync"
type_synonym 'uop m2_upd = "'uop m1_upd"

(******************************************************************************)
subsection \<open>Environment model\<close> 
(******************************************************************************)

subsection \<open>State\<close>

record 'uop m2e_state = 
  e_cschan :: "cid \<Rightarrow> sid \<Rightarrow> 'uop m1_upd_fifo"       \<comment> \<open>channel from client to server\<close>
  e_scchan :: "sid \<Rightarrow> cid \<Rightarrow> 'uop m1_upd_fifo"       \<comment> \<open>channel from server to client\<close>
  e_sschan :: "sid \<Rightarrow> sid \<Rightarrow> 'uop m1_sync_fifo"       \<comment> \<open>channel from server to server\<close>
  e_uops :: "'uop set" 
  e_live :: "sid set" 

context loc1 begin
definition m2e_init :: "'uop m2e_state" where
  "m2e_init = \<lparr> 
    e_cschan = \<lambda>_ _. [],
    e_scchan = \<lambda>_ _. [],
    e_sschan = \<lambda>_ _. [],
    e_uops = {},
    e_live = sidset\<rparr>"

datatype ('uop::countable) m2e_event = 
  B_E_cssend cid sid "'uop m1_upd" | B_E_sssend sid sid "'uop m2_sync" | 
  B_E_scsend sid cid "'uop m1_upd" | 
  B_E_csrecv cid sid "'uop m1_upd" | B_E_ssrecv sid sid "'uop m2_sync" | 
  B_E_screcv sid cid "'uop m1_upd" | 
  B_E_gen_uop 'uop | B2_E_Detect_failure agent sid | B_skip2e

abbreviation fun_upd2_app where "fun_upd2_app buf a b m \<equiv> fun_upd2 buf a b ((buf a b)@[m])"
abbreviation fun_upd2_rm where "fun_upd2_rm buf a b \<equiv> fun_upd2 buf a b (tl (buf a b))"

definition m2e_cssend where 
  "m2e_cssend s cid sid m \<equiv> (=) (s\<lparr>e_cschan := fun_upd2_app (e_cschan s) cid sid m\<rparr>)"
definition m2e_sssend where 
  "m2e_sssend s sid sid' m \<equiv> (=) (s\<lparr>e_sschan := fun_upd2_app (e_sschan s) sid sid' m\<rparr>)"
definition m2e_scsend where 
  "m2e_scsend s sid cid m \<equiv> (=) (s\<lparr>e_scchan := fun_upd2_app (e_scchan s) sid cid m\<rparr>)"
definition m2e_csrecv where 
  "m2e_csrecv s cid sid m s' \<equiv> ss_recv_msg s e_cschan cid sid m 
    \<and> s'=(s\<lparr>e_cschan := fun_upd2_rm (e_cschan s) cid sid\<rparr>)"
definition m2e_ssrecv where 
  "m2e_ssrecv s sid sid' m s' \<equiv> ss_recv_msg s e_sschan sid sid' m 
    \<and> s'=(s\<lparr>e_sschan := fun_upd2_rm (e_sschan s) sid sid'\<rparr>)"
definition m2e_screcv where 
  "m2e_screcv s sid cid m s' \<equiv> ss_recv_msg s e_scchan sid cid m 
    \<and> s'=(s\<lparr>e_scchan := fun_upd2_rm (e_scchan s) sid cid\<rparr>)"
definition m2e_gen_uop where
  "m2e_gen_uop s op s' \<longleftrightarrow> op \<notin> e_uops s \<and> s' = s\<lparr> e_uops := insert op (e_uops s)\<rparr>"
definition m2e_detect_failure where
  "m2e_detect_failure s ag sid s' \<equiv>
    (if sid \<in> e_live s then ag = Server sid \<and> s' = s\<lparr> e_live := remove sid (e_live s)\<rparr> else s'=s)"

fun m2e_trans :: "'uop::countable m2e_state \<Rightarrow> 'uop m2e_event \<Rightarrow> 'uop m2e_state \<Rightarrow> bool"  where
  "m2e_trans s (B_E_cssend cid sid m) s' \<longleftrightarrow> m2e_cssend s cid sid m s'" |
  "m2e_trans s (B_E_sssend cid sid m') s' \<longleftrightarrow> m2e_sssend s cid sid m' s'" |
  "m2e_trans s (B_E_scsend sid cid m) s' \<longleftrightarrow> m2e_scsend s sid cid m s'" |
  "m2e_trans s (B_E_csrecv cid sid m) s' \<longleftrightarrow> m2e_csrecv s cid sid m s'" |
  "m2e_trans s (B_E_ssrecv cid sid m') s' \<longleftrightarrow> m2e_ssrecv s cid sid m' s'" |
  "m2e_trans s (B_E_screcv sid cid m) s' \<longleftrightarrow> m2e_screcv s sid cid m s'" |
  "m2e_trans s (B_E_gen_uop op) s' \<longleftrightarrow> m2e_gen_uop s op s'" |
  "m2e_trans s (B2_E_Detect_failure ag sid) s' \<longleftrightarrow> m2e_detect_failure s ag sid s'" |
  "m2e_trans s _ s' \<longleftrightarrow> (s = s')"

definition m2e :: "('uop::countable m2e_event, 'uop m2e_state) ES"
  where "m2e \<equiv> \<lparr>init = (=) m2e_init, trans = m2e_trans\<rparr>"

lemmas m2e_trans_defs = m2e_cssend_def m2e_sssend_def m2e_scsend_def m2e_csrecv_def m2e_ssrecv_def 
  m2e_screcv_def m2e_gen_uop_def m2e_detect_failure_def
lemmas m2e_defs = m2e_def m2e_init_def m2e_trans_defs
end

(******************************************************************************)
subsection \<open>System component model: Client and Server\<close> 
(******************************************************************************)
text \<open>We have two component types, Clients and Servers.\<close>

locale loc2 = loc1 +  
  fixes addr :: "agent \<Rightarrow> 'ADDR::countable"
  assumes addr_inj: "inj addr"
begin
lemma addr_simp[simp]: "addr x = addr y \<longleftrightarrow> x = y" using addr_inj by (auto dest: injD)
lemma inv_addr_addr[simp]: "inv addr (addr ag) = ag" using addr_inj by auto
end

subsubsection \<open>Client model\<close>
(******************************************************************************)

record 'uop m2_state_client = 
  c_live :: "sid set" \<comment> \<open>set of servers believed to be alive by the client\<close>
  c_pend :: "sid \<Rightarrow> 'uop \<Rightarrow> bool" \<comment> \<open>client's pending requests to a certain server with a given uop\<close>
  c_csobuf :: "sid \<Rightarrow> 'uop m1_upd_fifo"       \<comment> \<open>output buffer, messages from client to server\<close>
  c_scibuf :: "sid \<Rightarrow> 'uop m1_upd_fifo"       \<comment> \<open>input buffer, messages from server to client.\<close>
type_synonym 'uop m2c_state = "cid \<Rightarrow> 'uop m2_state_client"


definition (in loc2) m2c_init :: "'uop m2_state_client" where
  "m2c_init = \<lparr> 
    c_live = sidset,
    c_pend = \<lambda>_ _. False, 
    c_csobuf = \<lambda>_ . [], 
    c_scibuf = \<lambda>_ . []\<rparr>"


text \<open>Define the type of values.\<close>

datatype ('uop::countable, 'ADDR) cval = 
  cUnit | 
  cUpdate 'ADDR "'uop m2_upd" |
  cInt1 sid 'uop |
  cInt2 sid 'uop "'uop history" |
  cInt3 sid

instance cval :: (countable, countable) countable
  by countable_datatype

datatype bio2cIN = B2_C_repeat_req | B2_C_res
datatype bio2cIO = B2_C_req | B2_C_detect_failure | B2_C_Send | B2_C_Recv
type_synonym bio2c = "(bio2cIN, bio2cIO) events"

lemma bio2cIN_UNIV: "UNIV = {B2_C_repeat_req, B2_C_res}"
  by (auto)(metis (full_types) bio2cIN.exhaust bio2cIO.exhaust)
lemma bio2cIO_UNIV: "UNIV = {B2_C_req, B2_C_detect_failure, B2_C_Send, B2_C_Recv}"
  by (auto)(metis (full_types) bio2cIN.exhaust bio2cIO.exhaust)

lemma bio2c_UNIV:
  "UNIV = {IN B2_C_repeat_req, IN B2_C_res, 
           IO B2_C_req, IO B2_C_detect_failure, IO B2_C_Send, IO B2_C_Recv, Skip, Stop}"
  apply auto
  apply (rule events.exhaust)
  by (auto intro: bio2cIN.exhaust bio2cIO.exhaust)

instance bio2cIN :: finite
proof show "finite (UNIV::bio2cIN set)" by (auto simp add: bio2cIN_UNIV) qed

instance bio2cIO :: finite
proof show "finite (UNIV::bio2cIO set)" by (auto simp add: bio2cIO_UNIV) qed

instance events :: (finite, finite) finite
proof 
  have "finite (insert Stop (insert Skip (IN`(UNIV :: 'a set) \<union> IO`(UNIV :: 'b set))))"
    by (auto intro: finite_imageI)
  moreover
  have foo: "UNIV = insert Stop (insert Skip (IN`(UNIV :: 'a set) \<union> IO`(UNIV :: 'b set)))"
    apply auto
    subgoal for x by (cases x) auto
    done
  ultimately show "finite (UNIV::('a, 'b) events set)" by simp
qed


fun (in loc2) bio2cType :: "bio2c \<Rightarrow> (('uop::countable, 'ADDR) cval) \<Rightarrow> (('uop, 'ADDR) cval) set" where 
  "bio2cType (IO B2_C_Recv) _ = {m | m sid x . m = cUpdate (addr (Server sid)) x}" |
  "bio2cType _                 _ = {cUnit}"

abbreviation c_csobuf_rm where "c_csobuf_rm s a \<equiv> s\<lparr>c_csobuf := (c_csobuf s)(a := tl (c_csobuf s a))\<rparr>"
abbreviation c_scibuf_rm where "c_scibuf_rm s a \<equiv> s\<lparr>c_scibuf := (c_scibuf s)(a := tl (c_scibuf s a))\<rparr>" (*needed?*)

datatype 'uop::countable m2c_IN_event =
  m2c_evt_repeat_req sid 'uop |
  m2c_evt_res sid 'uop "'uop history"

datatype ('uop::countable, 'ADDR) m2c_IO_event =
  m2c_evt_req sid 'uop |
  m2c_evt_detect_failure sid | 
  m2c_evt_Send 'ADDR "'uop m2_upd" |
  m2c_evt_Recv 'ADDR "'uop m2_upd"

type_synonym ('uop, 'ADDR) m2c_event = "(('uop) m2c_IN_event, ('uop, 'ADDR) m2c_IO_event) events"

fun \<rho>_IN :: "(bio2cIN, ('uop::countable, 'ADDR) cval) action \<Rightarrow> ('uop) m2c_IN_event option" where
  "\<rho>_IN (ActBio B2_C_repeat_req (cInt1 sid op) cUnit) = Some (m2c_evt_repeat_req sid op)" |
  "\<rho>_IN (ActBio B2_C_res (cInt2 sid op h) cUnit) = Some (m2c_evt_res sid op h)" |
  "\<rho>_IN _ = None"

fun \<rho>_IO :: "(bio2cIO, ('uop::countable, 'ADDR) cval) action \<Rightarrow> ('uop, 'ADDR) m2c_IO_event option" where
  "\<rho>_IO (ActBio B2_C_req (cInt1 sid op) cUnit) = Some (m2c_evt_req sid op)" |
  "\<rho>_IO (ActBio B2_C_detect_failure (cInt3 sid) cUnit) = Some (m2c_evt_detect_failure sid)" | 
  "\<rho>_IO (ActBio B2_C_Send (cUpdate adr m) cUnit) = Some (m2c_evt_Send adr m)" |
  "\<rho>_IO (ActBio B2_C_Recv cUnit (cUpdate adr m)) = Some (m2c_evt_Recv adr m)" | 
  "\<rho>_IO _ = None"

fun \<rho> :: "(bio2c, ('uop::countable, 'ADDR) cval) action \<Rightarrow> 
          (('uop) m2c_IN_event, ('uop, 'ADDR) m2c_IO_event) events" where
  "\<rho> (ActBio (IN e) v w) = (case \<rho>_IN (ActBio e v w) of Some evt \<Rightarrow> IN evt | _ \<Rightarrow> Stop)" |
  "\<rho> (ActBio (IO e) v w) = (case \<rho>_IO (ActBio e v w) of Some evt \<Rightarrow> IO evt | _ \<Rightarrow> Stop)" |
  "\<rho> (ActBio Skip _ _) = Skip" |
  "\<rho> _ = Stop"

lemma \<rho>_IN_invert [simp]:
  "\<rho>_IN x = Some (m2c_evt_repeat_req sid op) \<longleftrightarrow> x = ActBio B2_C_repeat_req (cInt1 sid op) cUnit"
  "\<rho>_IN x = Some (m2c_evt_res sid op h) \<longleftrightarrow> x = ActBio B2_C_res (cInt2 sid op h) cUnit"
  by (auto elim: \<rho>_IN.elims)

lemma \<rho>_IO_invert [simp]:
  "\<rho>_IO x = Some (m2c_evt_req sid op) \<longleftrightarrow> x = ActBio B2_C_req (cInt1 sid op) cUnit"
  "\<rho>_IO x = Some (m2c_evt_detect_failure sid) \<longleftrightarrow> x = ActBio B2_C_detect_failure (cInt3 sid) cUnit"
  "\<rho>_IO x = Some (m2c_evt_Send adr m) \<longleftrightarrow> x = ActBio B2_C_Send (cUpdate adr m) cUnit"
  "\<rho>_IO x = Some (m2c_evt_Recv adr m) \<longleftrightarrow> x = ActBio B2_C_Recv cUnit (cUpdate adr m)"
  by (auto elim: \<rho>_IO.elims)

lemma \<rho>_invert [simp]:
  "\<rho> x = IN (m2c_evt_repeat_req sid op) \<longleftrightarrow> x = ActBio (IN B2_C_repeat_req) (cInt1 sid op) cUnit"
  "\<rho> x = IN (m2c_evt_res sid op h) \<longleftrightarrow> x = ActBio (IN B2_C_res) (cInt2 sid op h) cUnit"
  "\<rho> x = IO (m2c_evt_req sid op) \<longleftrightarrow> x = ActBio (IO B2_C_req) (cInt1 sid op) cUnit"
  "\<rho> x = IO (m2c_evt_detect_failure sid) \<longleftrightarrow> x = ActBio (IO B2_C_detect_failure) (cInt3 sid) cUnit"
  "\<rho> x = IO (m2c_evt_Send adr m) \<longleftrightarrow> x = ActBio (IO B2_C_Send) (cUpdate adr m) cUnit"
  "\<rho> x = IO (m2c_evt_Recv adr m) \<longleftrightarrow> x = ActBio (IO B2_C_Recv) cUnit (cUpdate adr m)"
  "\<rho> x = Skip \<longleftrightarrow> (\<exists>y z . x = ActBio Skip y z)"
  by (auto elim!: \<rho>.elims simp add: option.case_eq_if) 

context loc2 begin
sublocale client: Typing bio2cType by unfold_locales (auto elim!: bio2cType.elims)

definition c_prim :: "'uop m2_state_client \<Rightarrow> sid option" where 
  "c_prim s = least (c_live s)"

text\<open>Internal IO Events\<close>
definition m2c_repeat_req :: "cid \<Rightarrow> ('uop::countable m2_state_client, ('uop, 'ADDR) cval) guarded_update" where
  "m2c_repeat_req i s v \<equiv> 
    \<lparr>guard = (case v of cInt1 sid op \<Rightarrow> (\<exists> sid' . c_pend s sid' op \<and> sid' \<notin> c_live s \<and> c_prim s = Some sid)
             | _ \<Rightarrow> False),
     update = (\<lambda>w. (case v of cInt1 sid op \<Rightarrow> 
          s\<lparr>c_csobuf := (c_csobuf s)(sid := c_csobuf s sid @ [m1_Upd_req op]),
            c_pend := fun_upd2 (c_pend s) sid op True\<rparr>))\<rparr>"

definition m2c_res :: "cid \<Rightarrow> ('uop::countable m2_state_client, ('uop, 'ADDR) cval) guarded_update" where
  "m2c_res i s v \<equiv> 
    \<lparr>guard = (case v of cInt2 sid op h \<Rightarrow> is_head (m1_Upd_res op h) (c_scibuf s sid) | _ \<Rightarrow> False),
     update = (\<lambda>w. (case v of cInt2 sid op h \<Rightarrow>
          s\<lparr>c_scibuf := (c_scibuf s)(sid := tl (c_scibuf s sid)),
            c_pend := fun_upd2 (c_pend s) sid op False\<rparr>))\<rparr>"

text\<open>Real IO Events\<close>
definition m2c_req :: "cid \<Rightarrow> ('uop::countable m2_state_client, ('uop, 'ADDR) cval) guarded_update" where
  "m2c_req i s v \<equiv> 
    (case v of cInt1 sid op \<Rightarrow> 
      \<lparr>guard = c_prim s = Some sid ,
       update = (\<lambda>w. 
          s\<lparr>c_csobuf := (c_csobuf s)(sid := c_csobuf s sid @ [m1_Upd_req op]),
            c_pend := fun_upd2 (c_pend s) sid op True\<rparr>)\<rparr>
    | _ \<Rightarrow> gNull s v)"

definition m2c_detect_failure where
  "m2c_detect_failure i s v = 
    (case v of cInt3 sid \<Rightarrow> 
      \<lparr>guard = True,
      update = (\<lambda> w . s\<lparr> c_live := remove sid (c_live s) \<rparr>)\<rparr>
    | _ \<Rightarrow> gNull s v)"

definition m2c_send where
  "m2c_send i s v \<equiv> 
    \<lparr>guard = 
      (case v of cUpdate adr m \<Rightarrow> 
        (case (inv addr) adr of Server sid \<Rightarrow> is_head m (c_csobuf s sid)
        | _ \<Rightarrow> False)
      | _ \<Rightarrow> False),
     update = (\<lambda>w. 
      (case v of cUpdate adr m \<Rightarrow> 
        (case (inv addr) adr of Server sid \<Rightarrow> c_csobuf_rm s sid)))\<rparr>"

definition m2c_receive where
  "m2c_receive i s v \<equiv> \<lparr>
     guard = (v = cUnit), 
     update = (\<lambda>w. 
        (case w of cUpdate adr m \<Rightarrow> 
          (case (inv addr) adr of Server sid \<Rightarrow> s\<lparr>c_scibuf := (c_scibuf s)(sid := c_scibuf s sid @ [m])\<rparr>
          | _ \<Rightarrow> s) \<comment> \<open>typing ensures the sender is a Server\<close>
         | _ \<Rightarrow> s)) \<rparr>" \<comment> \<open>typing ensures that w is a message, not cUnit or some internal value\<close>

fun m2c_ioges :: "cid \<Rightarrow> ('uop::countable m2_state_client, bio2c, ('uop,'ADDR) cval) IOGES" where
  "m2c_ioges i (IN B2_C_repeat_req) = m2c_repeat_req i"
| "m2c_ioges i (IN B2_C_res) = m2c_res i"
| "m2c_ioges i (IO B2_C_req) = m2c_req i"
| "m2c_ioges i (IO B2_C_detect_failure) = m2c_detect_failure i"
| "m2c_ioges i (IO B2_C_Recv) = m2c_receive i"
| "m2c_ioges i (IO B2_C_Send) = m2c_send i"
| "m2c_ioges i Skip = gSkip"
| "m2c_ioges i Stop = gNull"

definition m2c_fES_base where
  "m2c_fES_base i \<equiv> client.IOGES_to_ES (m2c_ioges i) ((=) m2c_init)"

definition m2c_fES where
  "m2c_fES i \<equiv> (m2c_fES_base i)\<lceil>\<rho>\<rceil>"

definition m2c :: "(cid \<times> ('uop::countable m2c_IN_event, ('uop, 'ADDR) m2c_IO_event) events, 
                    cid \<Rightarrow> 'uop m2_state_client) ES" where
  "m2c = \<parallel>\<parallel> m2c_fES"

lemma init_m2c[simp]: "init (\<parallel>\<parallel> m2c_fES) = (=) (\<lambda>_. m2c_init)"
  by (auto simp add: interleave_fES_def m2c_fES_def m2c_fES_base_def client.IOGES_to_ES_def)

lemmas m2c_trans_defs = 
  m2c_repeat_req_def m2c_res_def m2c_detect_failure_def m2c_req_def m2c_send_def m2c_receive_def
lemmas m2c_defs = m2c_def m2c_trans_defs m2c_fES_def m2c_fES_base_def m2c_init_def client.IOGES_to_ES_trans

lemma \<rho>_Stop[dest]: 
  "\<lbrakk>\<rho> (ActBio bio v w) = Stop; guard (m2c_ioges i bio c v); w \<in> bio2cType bio v\<rbrakk> \<Longrightarrow> False"
  apply(cases bio, auto)
  subgoal for x1 by(auto 3 4 intro: bio2cIN.exhaust[of x1] cval.exhaust[of v] simp add: m2c_defs)+
  subgoal for x1 by(auto 3 4 intro: bio2cIO.exhaust[of x1] cval.exhaust[of v] simp add: m2c_defs)+
  done

end


subsubsection \<open>Server model\<close>
(******************************************************************************)
record 'uop m2_state_server = 
  s_live :: "sid set"
  s_hist :: "sid \<Rightarrow> 'uop history"
  s_pend :: "'uop history"
  s_uopcid :: "'uop \<Rightarrow> cid option"
  s_scobuf :: "cid \<Rightarrow> 'uop m1_upd_fifo"       \<comment> \<open>output buffer, messages from server to client.\<close>
  s_csibuf :: "cid \<Rightarrow> 'uop m1_upd_fifo"       \<comment> \<open>input buffer, messages from client to server.\<close>
  s_ssobuf :: "sid \<Rightarrow> 'uop m1_sync_fifo" \<comment> \<open>output buffer, messages from server to server\<close>
  s_ssibuf :: "sid \<Rightarrow> 'uop m1_sync_fifo" \<comment> \<open>input buffer, messages from server to server.\<close>
type_synonym 'uop m2s_state = "sid \<Rightarrow> 'uop m2_state_server"

definition (in loc2) m2s_init :: "'uop m2_state_server" where
  "m2s_init = \<lparr> 
    s_live = sidset,
    s_hist = \<lambda>_ . [], 
    s_pend = [], 
    s_uopcid = \<lambda>_ . None, 
    s_scobuf = \<lambda>_. [], 
    s_csibuf = \<lambda>_. [], 
    s_ssobuf = \<lambda>_. [], 
    s_ssibuf = \<lambda>_. []\<rparr>"

text \<open>Define the type of values.\<close>

datatype ('uop::countable, 'ADDR) sval = 
  sUnit | 
  sSync   'ADDR "'uop m2_sync" | 
  sUpdate 'ADDR "'uop m2_upd" |
  sInt1 cid 'uop "'uop history"|
  sInt2 sid 'uop "'uop history"|
  sInt3 sid

instance sval :: (countable, countable) countable
  by countable_datatype


datatype bio2sIN = B2_P_req | B2_P_res | B2_B_sync | B2_S_purge
datatype bio2sIO = B2_S_Detect_failure | B2_S_Send | B2_S_Recv
type_synonym bio2s = "(bio2sIN, bio2sIO) events"

lemma bio2sIN_UNIV: "UNIV = {B2_P_req, B2_P_res, B2_B_sync, B2_S_purge}"
  by (auto)(metis bio2sIN.exhaust)
lemma bio2sIO_UNIV: "UNIV = {B2_S_Detect_failure, B2_S_Send, B2_S_Recv}"
  by (auto)(metis bio2sIO.exhaust)

lemma bio2s_UNIV:
  "UNIV = {IN B2_P_req, IN B2_P_res, IN B2_B_sync, IN B2_S_purge,  
           IO B2_S_Detect_failure, IO B2_S_Send, IO B2_S_Recv, Skip, Stop}"
  apply auto
  apply (rule events.exhaust)
  by (auto intro: bio2sIN.exhaust bio2sIO.exhaust)

instance bio2sIN :: finite
proof show "finite (UNIV::bio2sIN set)" by (auto simp add: bio2sIN_UNIV) qed
instance bio2sIO :: finite
proof show "finite (UNIV::bio2sIO set)" by (auto simp add: bio2sIO_UNIV) qed

fun (in loc2) bio2sType :: "bio2s \<Rightarrow> (('uop::countable, 'ADDR) sval) \<Rightarrow> (('uop, 'ADDR) sval) set" where
  "bio2sType (IO B2_S_Recv) _ = {m | m cid x . m = sUpdate (addr (Client cid)) x} \<union>
                                {m | m sid x . m =   sSync (addr (Server sid)) x}" |
  "bio2sType _              _ = {sUnit}"

abbreviation s_scobuf_rm where "s_scobuf_rm s a \<equiv> s\<lparr>s_scobuf := (s_scobuf s)(a := tl (s_scobuf s a))\<rparr>"
abbreviation s_csibuf_rm where "s_csibuf_rm s a \<equiv> s\<lparr>s_csibuf := (s_csibuf s)(a := tl (s_csibuf s a))\<rparr>"
abbreviation s_ssibuf_rm where "s_ssibuf_rm s a \<equiv> s\<lparr>s_ssibuf := (s_ssibuf s)(a := tl (s_ssibuf s a))\<rparr>"
abbreviation s_ssobuf_rm where "s_ssobuf_rm s a \<equiv> s\<lparr>s_ssobuf := (s_ssobuf s)(a := tl (s_ssobuf s a))\<rparr>"
abbreviation s_recv_upd where   "s_recv_upd s buf a b m \<equiv> \<exists> xs . buf s a b = (m#xs)"

datatype ('uop::countable) m2s_IN_event =
  m2p_evt_req cid 'uop "'uop history"|
  m2p_evt_res cid 'uop "'uop history"|
  m2b_evt_sync sid 'uop "'uop history"|
  m2s_evt_purge sid

datatype ('uop::countable, 'ADDR) m2s_IO_event =
  m2s_evt_detect_failure sid |
  m2s_evt_Send_upd 'ADDR "'uop m2_upd" |
  m2s_evt_Send_sync 'ADDR "'uop m2_sync" |
  m2s_evt_Recv_upd 'ADDR "'uop m2_upd" |
  m2s_evt_Recv_sync 'ADDR "'uop m2_sync"

type_synonym ('uop, 'ADDR) m2s_event = "(('uop) m2s_IN_event, ('uop, 'ADDR) m2s_IO_event) events"

fun \<beta>_IN :: "(bio2sIN, ('uop::countable, 'ADDR) sval) action \<Rightarrow> ('uop) m2s_IN_event option" where
  "\<beta>_IN (ActBio B2_P_req (sInt1 cid op h) sUnit) = Some (m2p_evt_req cid op h)" |
  "\<beta>_IN (ActBio B2_P_res (sInt1 cid op h) sUnit) = Some (m2p_evt_res cid op h)" |
  "\<beta>_IN (ActBio B2_B_sync (sInt2 sid op h) sUnit) = Some (m2b_evt_sync sid op h)" |
  "\<beta>_IN (ActBio B2_S_purge (sInt3 sid) sUnit) = Some (m2s_evt_purge sid)" |
  "\<beta>_IN _ = None"

fun \<beta>_IO :: "(bio2sIO, ('uop::countable, 'ADDR) sval) action \<Rightarrow> ('uop, 'ADDR) m2s_IO_event option" where
  "\<beta>_IO (ActBio B2_S_Detect_failure (sInt3 sid) sUnit) = Some (m2s_evt_detect_failure sid)" |
  "\<beta>_IO (ActBio B2_S_Send (sUpdate adr m) sUnit) = Some (m2s_evt_Send_upd adr m)" |
  "\<beta>_IO (ActBio B2_S_Send (sSync adr m) sUnit) = Some (m2s_evt_Send_sync adr m)" |
  "\<beta>_IO (ActBio B2_S_Recv sUnit (sUpdate adr m)) = Some (m2s_evt_Recv_upd adr m)" |
  "\<beta>_IO (ActBio B2_S_Recv sUnit (sSync adr m)) = Some (m2s_evt_Recv_sync adr m)" |
  "\<beta>_IO _ = None"

fun \<beta> :: "(bio2s, ('uop::countable, 'ADDR) sval) action \<Rightarrow> 
          (('uop) m2s_IN_event, ('uop, 'ADDR) m2s_IO_event) events" where
  "\<beta> (ActBio (IN e) v w) = (case \<beta>_IN (ActBio e v w) of Some evt \<Rightarrow> IN evt | _ \<Rightarrow> Stop)" |
  "\<beta> (ActBio (IO e) v w) = (case \<beta>_IO (ActBio e v w) of Some evt \<Rightarrow> IO evt | _ \<Rightarrow> Stop)" |
  "\<beta> (ActBio Skip _ _) = Skip" |
  "\<beta> _ = Stop"

lemma \<beta>_IN_invert [simp]:
  "\<beta>_IN x = Some (m2p_evt_req cid op h) \<longleftrightarrow> x = ActBio B2_P_req (sInt1 cid op h) sUnit"
  "\<beta>_IN x = Some (m2p_evt_res cid op h) \<longleftrightarrow> x = ActBio B2_P_res (sInt1 cid op h) sUnit"
  "\<beta>_IN x = Some (m2b_evt_sync sid op h) \<longleftrightarrow> x = ActBio B2_B_sync (sInt2 sid op h) sUnit"
  "\<beta>_IN x = Some (m2s_evt_purge sid) \<longleftrightarrow> x = ActBio B2_S_purge (sInt3 sid) sUnit"
  by (auto elim: \<beta>_IN.elims)

lemma \<beta>_IO_invert [simp]:
  "\<beta>_IO x = Some (m2s_evt_detect_failure sid) \<longleftrightarrow> x = ActBio B2_S_Detect_failure (sInt3 sid) sUnit"
  "\<beta>_IO x = Some (m2s_evt_Send_upd adr m) \<longleftrightarrow> x = ActBio B2_S_Send (sUpdate adr m) sUnit"
  "\<beta>_IO x = Some (m2s_evt_Send_sync adr m') \<longleftrightarrow> x = ActBio B2_S_Send (sSync adr m') sUnit"
  "\<beta>_IO x = Some (m2s_evt_Recv_upd adr m) \<longleftrightarrow> x = ActBio B2_S_Recv sUnit (sUpdate adr m)"
  "\<beta>_IO x = Some (m2s_evt_Recv_sync adr m') \<longleftrightarrow> x = ActBio B2_S_Recv sUnit (sSync adr m')"
  by (auto elim: \<beta>_IO.elims)

lemma \<beta>_invert [simp]:
  "\<beta> x = IN (m2p_evt_req cid op h) \<longleftrightarrow> x = ActBio (IN B2_P_req) (sInt1 cid op h) sUnit"
  "\<beta> x = IN (m2p_evt_res cid op h) \<longleftrightarrow> x = ActBio (IN B2_P_res) (sInt1 cid op h) sUnit"
  "\<beta> x = IN (m2b_evt_sync sid op h) \<longleftrightarrow> x = ActBio (IN B2_B_sync) (sInt2 sid op h) sUnit"
  "\<beta> x = IN (m2s_evt_purge sid) \<longleftrightarrow> x = ActBio (IN B2_S_purge) (sInt3 sid) sUnit"
  "\<beta> x = IO (m2s_evt_detect_failure sid) \<longleftrightarrow> x = ActBio (IO B2_S_Detect_failure) (sInt3 sid) sUnit"
  "\<beta> x = IO (m2s_evt_Send_upd adr m) \<longleftrightarrow> x = ActBio (IO B2_S_Send) (sUpdate adr m) sUnit"
  "\<beta> x = IO (m2s_evt_Send_sync adr m') \<longleftrightarrow> x = ActBio (IO B2_S_Send) (sSync adr m') sUnit"
  "\<beta> x = IO (m2s_evt_Recv_upd adr m) \<longleftrightarrow> x = ActBio (IO B2_S_Recv) sUnit (sUpdate adr m)"
  "\<beta> x = IO (m2s_evt_Recv_sync adr m') \<longleftrightarrow> x = ActBio (IO B2_S_Recv) sUnit (sSync adr m')"
  "\<beta> x = Skip \<longleftrightarrow> (\<exists>y z . x = ActBio Skip y z)"
  by (auto elim!: \<beta>.elims simp add: option.case_eq_if)

context loc2 begin
sublocale server: Typing bio2sType by unfold_locales (auto elim!: bio2sType.elims)

definition live2_geq where
  "live2_geq s p \<equiv> { x. x  \<ge> p \<and> x \<in> s_live s}"

definition m2p_req where
  "m2p_req i s v \<equiv> 
    \<lparr>guard = 
      (case v of sInt1 cid op h \<Rightarrow> 
        i \<in> s_live s \<and> is_head (m1_Upd_req op) (s_csibuf s cid) \<and> h = cond_app (s_pend s) op
      | _ \<Rightarrow> False),
     update = (\<lambda> w . 
      (case v of sInt1 cid op h \<Rightarrow> 
    s\<lparr>
      s_live := live2_geq s i,
      s_csibuf := (s_csibuf s)(cid := tl (s_csibuf s cid)),
      s_ssobuf := 
        (\<lambda> rcv . (if rcv > i \<and> rcv \<in> s_live s
                  then (s_ssobuf s rcv) @ [m1_Sync_req op h] else s_ssobuf s rcv)),
      s_pend := h,
      s_uopcid := (s_uopcid s)(op := Some cid)
      \<rparr>))\<rparr>"

definition singleton_live2 where
  "singleton_live2 s i \<equiv> 
    (\<forall>b . b \<in> s_live s \<longrightarrow> b = i)"

lemma singleton_live2I: "\<lbrakk>\<And> b . b \<in> s_live s \<Longrightarrow> b = sid\<rbrakk> \<Longrightarrow> singleton_live2 s sid" 
  by(simp add: singleton_live2_def)

lemma singleton_live2D: "\<lbrakk>singleton_live2 s sid; b \<in> s_live s\<rbrakk>\<Longrightarrow> b = sid" 
  by(simp add: singleton_live2_def)

definition collect_res2 where
  "collect_res2 s i op h \<equiv> 
    (if singleton_live2 s i
     then s_pend s = h
     else (\<forall>sid' \<in> s_live s. i \<noteq> sid' 
          \<longrightarrow> is_head (m1_Sync_res op h) (s_ssibuf s sid')))"

lemma collect_res2I: 
  "\<lbrakk>\<And>sid'. \<lbrakk>sid' \<in> s_live s; sid \<noteq> sid'\<rbrakk> 
  \<Longrightarrow> is_head (m1_Sync_res op h) (s_ssibuf s sid');
  singleton_live2 s sid \<Longrightarrow> s_pend s = h\<rbrakk> \<Longrightarrow> collect_res2 s sid op h"
  by(auto simp add: collect_res2_def dest: singleton_live2D)

lemma collect_res2D: 
  "\<lbrakk>collect_res2 s sid op h; sid' \<in> s_live s; sid \<noteq> sid'\<rbrakk> 
  \<Longrightarrow> is_head (m1_Sync_res op h) (s_ssibuf s sid')"
  "\<lbrakk>collect_res2 s sid op h; singleton_live2 s sid\<rbrakk> 
  \<Longrightarrow> s_pend s = h"
  by(auto simp add: collect_res2_def dest: singleton_live2D)

definition m2p_res where
  "m2p_res i s v \<equiv>
    \<lparr>guard = case v of sInt1 cid op h \<Rightarrow>
      i \<in> s_live s \<and> collect_res2 s i op h \<and> s_uopcid s op = Some cid | _ \<Rightarrow> False,
         update = (\<lambda> w . case v of sInt1 cid op h \<Rightarrow>
    s\<lparr>
      s_scobuf := (s_scobuf s)(cid := s_scobuf s cid @ [m1_Upd_res op h]),
      s_ssibuf := (\<lambda> a . (if a \<in> s_live s \<and> a \<noteq> i then 
          tl (s_ssibuf s a) else (s_ssibuf s a))),
      s_hist := (\<lambda>sid' . if sid' \<in> s_live s then h else s_hist s sid')
      \<rparr>)\<rparr>"

definition m2b_sync where
  "m2b_sync i s v \<equiv>
     \<lparr>guard = case v of sInt2 p op h \<Rightarrow> 
        i \<in> s_live s \<and> p \<in> s_live s \<and> is_head (m1_Sync_req op h) (s_ssibuf s p) | _ \<Rightarrow> False,
      update = (\<lambda> w . case v of sInt2 p op h \<Rightarrow> 
    s\<lparr>
      s_live := live2_geq s p,
      s_hist := (s_hist s)(p := h, i := h),
      s_ssibuf := (s_ssibuf s)(p := tl (s_ssibuf s p)),
      s_ssobuf := (s_ssobuf s)(p := s_ssobuf s p @ [m1_Sync_res op h]),
      s_pend := h
      \<rparr>)\<rparr>"

definition m2s_purge where
  "m2s_purge i s v \<equiv>
    \<lparr>guard = case v of sInt3 sid \<Rightarrow> \<exists> m . is_head m (s_ssibuf s sid) | _ \<Rightarrow> False,
    update = (\<lambda>w. case v of sInt3 sid \<Rightarrow> s_ssibuf_rm s sid)\<rparr>"

definition m2s_send where
  "m2s_send i s v \<equiv> 
    \<lparr>guard = 
    case v of sUpdate adr m \<Rightarrow> (case (inv addr) adr of Client cid \<Rightarrow> is_head m (s_scobuf s cid) | _ \<Rightarrow> False)
            | sSync adr m \<Rightarrow> (case (inv addr) adr of Server sid \<Rightarrow> is_head m (s_ssobuf s sid) | _ \<Rightarrow> False)
            | _ \<Rightarrow> False,
     update = (\<lambda>w. 
    case v of sUpdate adr m \<Rightarrow> (case (inv addr) adr of Client cid \<Rightarrow> s_scobuf_rm s cid)
            | sSync adr m \<Rightarrow> (case (inv addr) adr of Server sid \<Rightarrow> s_ssobuf_rm s sid))\<rparr>"

text\<open>typing ensures that w is a sUpdate or sSync message, not something else, and that sUpdate is 
received from a Client and sSync from a Server.\<close>
definition m2s_receive where
  "m2s_receive i s v \<equiv> \<lparr>
     guard = (v = sUnit), 
     update = (\<lambda>w. 
      (case w of 
          sUpdate adr m \<Rightarrow> 
            (case (inv addr) adr of Client cid \<Rightarrow> 
              s\<lparr>s_csibuf := (s_csibuf s)(cid := s_csibuf s cid @ [m])\<rparr>)  
        | sSync adr m \<Rightarrow> 
            (case (inv addr) adr of Server sid \<Rightarrow> 
              (if sid \<in> s_live s then 
                s\<lparr>s_ssibuf := (s_ssibuf s)(sid := s_ssibuf s sid @ [m])\<rparr>
               else s))))\<rparr>" 

definition m2s_detect_failure where
  "m2s_detect_failure i s v = 
    \<lparr>guard = (case v of sInt3 sid \<Rightarrow> True | _ \<Rightarrow> False),
    update = (\<lambda> w . (case v of sInt3 sid \<Rightarrow> s\<lparr> s_live := remove sid (s_live s)\<rparr> ))\<rparr>"

fun m2s_ioges :: "sid \<Rightarrow> ('uop::countable m2_state_server, bio2s, ('uop,'ADDR) sval) IOGES" where
  "m2s_ioges i (IN B2_P_req) = m2p_req i"
| "m2s_ioges i (IN B2_P_res) = m2p_res i"
| "m2s_ioges i (IN B2_B_sync) = m2b_sync i"
| "m2s_ioges i (IN B2_S_purge) = m2s_purge i"
| "m2s_ioges i (IO B2_S_Detect_failure) = m2s_detect_failure i"
| "m2s_ioges i (IO B2_S_Recv) = m2s_receive i"
| "m2s_ioges i (IO B2_S_Send) = m2s_send i"
| "m2s_ioges i Skip = gSkip"
| "m2s_ioges i Stop = gNull"

definition m2s_fES_base where
  "m2s_fES_base i \<equiv> server.IOGES_to_ES (m2s_ioges i) ((=) m2s_init)"

definition m2s_fES where
  "m2s_fES i \<equiv> (m2s_fES_base i)\<lceil>\<beta>\<rceil>"

definition m2s :: "(sid \<times> ('uop::countable m2s_IN_event, ('uop, 'ADDR) m2s_IO_event) events, 
                    sid \<Rightarrow> 'uop m2_state_server) ES" where
  "m2s = \<parallel>\<parallel> m2s_fES"

lemma init_m2s[simp]: "init (\<parallel>\<parallel> m2s_fES) = (=) (\<lambda>_. m2s_init)"
  by (auto simp add: interleave_fES_def m2s_fES_def m2s_fES_base_def server.IOGES_to_ES_def)

lemmas m2s_trans_defs = m2p_req_def m2p_res_def m2b_sync_def m2s_purge_def 
  m2s_receive_def m2s_send_def m2s_detect_failure_def

lemmas m2s_defs = m2s_def m2s_fES_def m2s_fES_base_def m2s_trans_defs m2s_init_def server.IOGES_to_ES_trans


lemma \<beta>_Stop[dest]: 
  "\<lbrakk>\<beta> (ActBio bio v w) = Stop; guard (m2s_ioges i bio c v); w \<in> bio2sType bio v\<rbrakk> \<Longrightarrow> False"
  apply(cases bio, auto)
  subgoal for x1 by(auto 3 4 intro: bio2sIN.exhaust[of x1] sval.exhaust[of v] simp add: m2s_defs)+
  subgoal for x1 by(auto 3 4 intro: bio2sIO.exhaust[of x1] sval.exhaust[of v] simp add: m2s_defs)+
done

end

(*****************************************************************************)
subsection \<open>Composed system model\<close> 
(*****************************************************************************)

text \<open>We first build the system from the two system component types.\<close>

type_synonym 'uop m2sys_state = "'uop m2c_state \<times> 'uop m2s_state"
type_synonym ('uop, 'ADDR) m2sys_event = "cid \<times> ('uop, 'ADDR) m2c_event + sid \<times> ('uop, 'ADDR) m2s_event"

type_synonym 'uop m2sys_IN_event = "cid \<times> 'uop m2c_IN_event + sid \<times> 'uop m2s_IN_event"
type_synonym ('uop, 'ADDR) m2sys_IO_event = 
  "cid \<times> ('uop, 'ADDR) m2c_IO_event + sid \<times> ('uop, 'ADDR) m2s_IO_event"

context loc2
begin

text\<open>The system contains both the family of components of clients, and the family of components of
servers, but not (yet) the environment. The primed version is before rewriting the events in such a 
way that we combine the event labels of both types of components.\<close>
abbreviation m2sys' :: "(('uop::countable, 'ADDR) m2sys_event, 'uop m2sys_state) ES" where 
  "m2sys' \<equiv> m2c || m2s"

abbreviation m2sys :: "(('uop::countable m2sys_IN_event, ('uop, 'ADDR) m2sys_IO_event) events, 
                         'uop m2sys_state) ES" where
  "m2sys \<equiv> ievent_dist m2sys'"

lemmas m2sys_defs = m2c_defs m2s_defs ievent_dist_def

(******************************************************************************)
subsection \<open>Composition of components and environment models into a global model\<close> 
(******************************************************************************)
text\<open>The Client's synchronized IO events (send and receive as well as retrieval of fresh uops and
detecting failures.\<close>
fun \<chi>_IO_Client :: "'uop::countable m2e_event \<Rightarrow> cid \<Rightarrow> ('uop, 'ADDR) m2c_IO_event  \<rightharpoonup> 'uop m1_event" where
  "\<chi>_IO_Client (B_E_gen_uop op) i (m2c_evt_req sid op') = 
    (if op=op' then Some (B1_C_req i sid op False) else None)" |
  "\<chi>_IO_Client (B_E_cssend cid sid m) i (m2c_evt_Send adr m') = 
    (if addr (Server sid) = adr \<and> m = m' \<and> cid = i then Some (B1_cs_Send i sid m) else None)" |
  "\<chi>_IO_Client (B_E_screcv sid cid m) i (m2c_evt_Recv adr m') = 
    (if addr (Server sid) = adr \<and> m = m' \<and> cid = i then Some (B1_sc_Recv sid i m) else None)" |
  "\<chi>_IO_Client (B2_E_Detect_failure ag sid) i (m2c_evt_detect_failure sid') = 
    (if sid' = sid \<and> ag = Client i then Some (B1_Detect_failure (Client i) sid) else None)" |
  "\<chi>_IO_Client _ _ _ = None"

text\<open>The Server's synchronized IO events (send and receive as well as detecting failures.\<close>
fun \<chi>_IO_Server :: "'uop::countable m2e_event \<Rightarrow> sid \<Rightarrow> ('uop, 'ADDR) m2s_IO_event  \<rightharpoonup> 'uop m1_event" where
  "\<chi>_IO_Server (B_E_scsend sid cid m) i (m2s_evt_Send_upd adr m') = 
    (if addr (Client cid) = adr \<and> m = m' \<and> sid = i then Some (B1_sc_Send i cid m) else None)" |
  "\<chi>_IO_Server (B_E_sssend sid sid' m) i (m2s_evt_Send_sync adr m') = 
    (if addr (Server sid') = adr \<and> m = m' \<and> sid = i then Some (B1_ss_Send i sid' m) else None)" |
  "\<chi>_IO_Server (B_E_csrecv cid sid m) i (m2s_evt_Recv_upd adr m') = 
    (if addr (Client cid) = adr \<and> m = m' \<and> sid = i then Some (B1_cs_Recv cid i m) else None)" |
  "\<chi>_IO_Server (B_E_ssrecv sid sid' m) i (m2s_evt_Recv_sync adr m') = 
    (if addr (Server sid) = adr \<and> m = m' \<and> sid' = i then Some (B1_ss_Recv sid i m) else None)" |
  "\<chi>_IO_Server (B2_E_Detect_failure ag sid) i (m2s_evt_detect_failure sid') = 
    (if sid' = sid \<and> ag = Server i then Some (B1_Detect_failure (Server i) sid) else None)" |
  "\<chi>_IO_Server _ _ _ = None"

text\<open>Internal events that only synchronize with the environment Skip event.\<close>
fun \<chi>_IN_Client :: "cid \<Rightarrow> 'uop::countable m2c_IN_event \<Rightarrow> 'uop m1_event option"  where 
  "\<chi>_IN_Client i (m2c_evt_repeat_req sid op) = Some (B1_C_req i sid op True)"
| "\<chi>_IN_Client i (m2c_evt_res sid op h) = Some (B1_C_res i sid op h)"

fun \<chi>_IN_Server :: "sid \<Rightarrow> 'uop::countable m2s_IN_event \<Rightarrow> 'uop m1_event option"  where 
  "\<chi>_IN_Server i (m2p_evt_req cid op h) = Some (B1_P_req i cid op h)"
| "\<chi>_IN_Server i (m2p_evt_res sid op h) = Some (B1_P_res i sid op h)"
| "\<chi>_IN_Server i (m2b_evt_sync sid op h) = Some (B1_B_sync i sid op h)"
| "\<chi>_IN_Server i (m2s_evt_purge sid) = Some (B1_S_purge sid i)"

text\<open>Combine the events from two parametrized event systems as well as the environment and map them 
to @{term m1_event}.\<close>
fun \<chi> :: "'uop::countable m2e_event \<times> 
    ('uop::countable m2sys_IN_event, ('uop, 'ADDR) m2sys_IO_event) events \<rightharpoonup> 'uop m1_event" where
  "\<chi> (ee, IO (Inl (i, x))) = \<chi>_IO_Client ee i x"
| "\<chi> (ee, IO (Inr (i, x))) = \<chi>_IO_Server ee i x"
| "\<chi> (B_skip2e, IN (Inl (i, x))) = \<chi>_IN_Client i x"
| "\<chi> (B_skip2e, IN (Inr (i, x))) = \<chi>_IN_Server i x"
| "\<chi> (B_skip2e, Skip) = Some B1_Skip"
| "\<chi> _ = None"

lemmas \<chi>_elims = \<chi>_IO_Client.elims \<chi>_IO_Server.elims \<chi>_IN_Client.elims \<chi>_IN_Server.elims \<chi>.elims

(*i: client, j: server*)
lemma \<chi>_invert [simp]:
  "\<chi> x = Some (B1_C_req i sid op False) \<longleftrightarrow> x = (B_E_gen_uop op, IO (Inl (i, m2c_evt_req sid op)))"
  "\<chi> x = Some (B1_C_req i sid op True) \<longleftrightarrow> x = (B_skip2e, IN (Inl (i, m2c_evt_repeat_req sid op)))"
  "\<chi> x = Some (B1_C_res i sid op h) \<longleftrightarrow> x = (B_skip2e, IN (Inl (i, m2c_evt_res sid op h)))"
  "\<chi> x = Some (B1_P_req j cid op h) \<longleftrightarrow> x = (B_skip2e, IN (Inr (j, m2p_evt_req cid op h)))"
  "\<chi> x = Some (B1_P_res j cid op h) \<longleftrightarrow> x = (B_skip2e, IN (Inr (j, m2p_evt_res cid op h)))"
  "\<chi> x = Some (B1_B_sync j sid op h) \<longleftrightarrow> x = (B_skip2e, IN (Inr (j, m2b_evt_sync sid op h)))"
  "\<chi> x = Some (B1_S_purge sid j) \<longleftrightarrow> x = (B_skip2e, IN (Inr (j, m2s_evt_purge sid)))"
  "\<chi> x = Some (B1_cs_Send i sid upd) \<longleftrightarrow> x = (B_E_cssend i sid upd, IO (Inl (i, m2c_evt_Send (addr (Server sid)) upd)))"
  "\<chi> x = Some (B1_sc_Send j cid upd) \<longleftrightarrow> x = (B_E_scsend j cid upd, IO (Inr (j, m2s_evt_Send_upd (addr (Client cid)) upd)))"
  "\<chi> x = Some (B1_ss_Send j sid syn) \<longleftrightarrow> x = (B_E_sssend j sid syn, IO (Inr (j, m2s_evt_Send_sync (addr (Server sid)) syn)))"
  "\<chi> x = Some (B1_cs_Recv cid j upd) \<longleftrightarrow> x = (B_E_csrecv cid j upd, IO (Inr (j, m2s_evt_Recv_upd (addr (Client cid)) upd)))"
  "\<chi> x = Some (B1_sc_Recv sid i upd) \<longleftrightarrow> x = (B_E_screcv sid i upd, IO (Inl (i, m2c_evt_Recv (addr (Server sid)) upd)))"
  "\<chi> x = Some (B1_ss_Recv sid j syn) \<longleftrightarrow> x = (B_E_ssrecv sid j syn, IO (Inr (j, m2s_evt_Recv_sync (addr (Server sid)) syn)))"
  "\<chi> x = Some (B1_Detect_failure (Client i) sid) \<longleftrightarrow> x = (B2_E_Detect_failure (Client i) sid, IO (Inl (i, m2c_evt_detect_failure sid)))"
  "\<chi> x = Some (B1_Detect_failure (Server j) sid) \<longleftrightarrow> x = (B2_E_Detect_failure (Server j) sid, IO (Inr (j, m2s_evt_detect_failure sid)))"
  "\<chi> x = Some (B1_Skip) \<longleftrightarrow> x = (B_skip2e, Skip)"
  by(auto elim!: \<chi>_elims dest: HOL.sym) (*takes a few seconds*)


text\<open>Define the global event system as the composition under @{term "\<chi>"} of the environment event system and 
the sys event system (defined as the binary interleaving of the Client and Server event systems).\<close>
definition m2 :: "(('uop::countable) m1_event, 'uop m2e_state \<times> 'uop m2sys_state) ES" where 
  "m2 \<equiv> (m2e \<parallel>\<chi> m2sys)"

lemmas m2_defs = m2_def m2e_defs m2sys_defs

(******************************************************************************)
subsection \<open>Simulation relation between m1 and m2\<close> 
(******************************************************************************)
text\<open>We define a bijection between states of m1 and m2. (The bijection is shown as part of the
@{text m1_equiv_m2} lemma.)\<close>
fun med21  :: "'uop::countable m2e_state \<times> (cid \<Rightarrow> 'uop m2_state_client) \<times> 
                              (sid \<Rightarrow> 'uop m2_state_server) \<Rightarrow> 'uop m1_state" where
  "med21 (e, (c, s)) = \<lparr> 
    live = \<lambda>ag. (case ag of Server sid \<Rightarrow> s_live (s sid) | Client cid \<Rightarrow> c_live (c cid)),
    cpend = \<lambda>cid . c_pend (c cid), 
    csobuf = \<lambda>i. c_csobuf (c i), 
    scibuf = \<lambda>i j. c_scibuf (c j) i, 
    hist = \<lambda>i. s_hist (s i), 
    spend = \<lambda>i. s_pend (s i), 
    uopcid = \<lambda>i. s_uopcid (s i), 
    scobuf = \<lambda>i. s_scobuf (s i), 
    csibuf = \<lambda>i j. s_csibuf (s j) i, 
    ssobuf = \<lambda>i. s_ssobuf (s i), 
    ssibuf = \<lambda>i j. s_ssibuf (s j) i, 
    cschan = e_cschan e, 
    scchan = e_scchan e, 
    sschan = e_sschan e, 
    uops = e_uops e, 
    elive = e_live e\<rparr>"

fun inv_med21 where
  "inv_med21 s = 
(\<lparr> 
    e_cschan = cschan s,
    e_scchan = scchan s,
    e_sschan = sschan s,
    e_uops = uops s,
    e_live = elive s\<rparr>, 
(\<lambda>i . \<lparr> 
    c_live = live s (Client i),
    c_pend = cpend s i, 
    c_csobuf = csobuf s i, 
    c_scibuf = \<lambda>j . scibuf s j i\<rparr>),
(\<lambda>i . \<lparr> 
    s_live = live s (Server i),
    s_hist = hist s i, 
    s_pend = spend s i, 
    s_uopcid = uopcid s i, 
    s_scobuf = scobuf s i, 
    s_csibuf = \<lambda>j . csibuf s j i, 
    s_ssobuf = ssobuf s i, 
    s_ssibuf = \<lambda>j . ssibuf s j i\<rparr>))"

lemma live_geq_med21: "\<lbrakk>live s_abstract = case_agent P (\<lambda>sid. s_live (s sid))\<rbrakk>
    \<Longrightarrow> live2_geq (s sid) p = live_geq s_abstract sid p"
  by(auto simp add: live2_geq_def live_geq_def)

lemma singleton_live_med21: "\<lbrakk>med21 (e, c, s) = s_abstract; s sid = s_concrete\<rbrakk>
    \<Longrightarrow> singleton_live2 s_concrete sid \<longleftrightarrow> singleton_live s_abstract sid"
  by(auto intro!: singleton_liveI singleton_live2I dest: singleton_liveD singleton_live2D)

lemma collect_res_med21: "\<lbrakk>med21 (e, c, s) = s_abstract; s sid = s_concrete\<rbrakk>
    \<Longrightarrow> collect_res2 s_concrete sid op h \<longleftrightarrow> collect_res s_abstract sid op h"
  by(auto simp add: live_geq_med21 singleton_live_med21 intro!: collect_resI collect_res2I 
          dest: collect_resD collect_res2D)

lemma prim_med21:
"\<lbrakk>c_prim (c cid) = Some sid; live s_concrete = case_agent (\<lambda>cid. c_live (c cid)) (\<lambda>sid. s_live (s' sid))\<rbrakk>
    \<Longrightarrow> prim s_concrete (Client cid) = Some sid "
  by(auto simp add: c_prim_def prim_def)

(******************************************************************************)
subsection \<open>Lemmas for proving trace equivalence of m1 and m2\<close> 
(******************************************************************************)
subsubsection \<open>Expanding record definitions and proof rules for state equality\<close> 
lemma c_expand: "\<lbrakk>c_live (c i) = x; c_pend (c i) = y; c_csobuf (c i) = z; c_scibuf (c i) = zz\<rbrakk>
  \<Longrightarrow> c i = \<lparr>c_live = x, c_pend = y, c_csobuf = z, c_scibuf = zz\<rparr>"
  by simp

lemma c_eq: "\<lbrakk>c_live (c i) = c_live (c' i); c_pend (c i) = c_pend (c' i); 
c_csobuf (c i) = c_csobuf (c' i); c_scibuf (c i) = c_scibuf (c' i)\<rbrakk>
  \<Longrightarrow> (c::cid \<Rightarrow> 'uop m2_state_client) i = c' i"
  by simp

lemma s_expand: "\<lbrakk>s_live (s i) = r1; s_hist (s i) = r2; s_pend (s i) = r3; s_uopcid (s i) = r4;
s_scobuf (s i) = r5; s_csibuf (s i) = r6; s_ssobuf (s i) = r7; s_ssibuf (s i) = r8\<rbrakk>
  \<Longrightarrow> s i = \<lparr>s_live = r1, s_hist = r2, s_pend = r3, s_uopcid = r4, s_scobuf = r5, s_csibuf = r6,
             s_ssobuf = r7, s_ssibuf = r8\<rparr>"
  by simp

lemma s_eq: "\<lbrakk>s_live (s i) = s_live (s' i); s_hist (s i) = s_hist (s' i); 
s_pend (s i) = s_pend (s' i); s_uopcid (s i) = s_uopcid (s' i); 
s_scobuf (s i) = s_scobuf (s' i); s_csibuf (s i) = s_csibuf (s' i);
s_ssobuf (s i) = s_ssobuf (s' i); s_ssibuf (s i) = s_ssibuf (s' i)\<rbrakk>
  \<Longrightarrow> (s::sid \<Rightarrow> 'uop m2_state_server) i = s' i"
  by simp

lemmas state_eqI[intro!] = s_eq[THEN ext] c_eq[THEN ext] s_eq c_eq

subsubsection \<open>Equality of record fields\<close> 
text\<open>These lemmas are mostly used as elim rules.\<close>

text\<open>Lemmas on fields that are not updated.\<close>
lemma fld_eq: "(\<lambda>i. fld (c' i)) = (\<lambda>i. fld (c i)) \<Longrightarrow> fld (c' i) = fld (c i)"
  by (auto dest!: fun_cong)

lemma ibuf_eq: "(\<lambda>i j. buf (s' j) i) = (\<lambda>i j. buf (s j) i) \<Longrightarrow> buf (s' j) = buf (s j)"
  apply(drule arg_cong) by auto

text\<open>Lemmas on fields that are updated.\<close>
lemma fld_upd_eq: "(\<lambda>i. fld (s' i)) = (\<lambda>i. fld (s i))(sa := (fld (s sa))(ra := xs))
    \<Longrightarrow> fld (s' sa) = (\<lambda>a. if a = ra then xs else fld (s sa) a)"
  by(auto dest!: fun_cong intro!: ext)

text\<open>This lemma is used for ibufs, where the order of parameters is reversed in the translation to 
the abstract state.\<close>
lemma fld_upd_eq2: "(\<lambda>i j. fld (s' j) i) = (\<lambda>i j. fld (s j) i)(sa := (\<lambda>j. fld (s j) sa)(ra := xs))
    \<Longrightarrow> fld (s' ra) = (\<lambda>a. if a = sa then xs else fld (s ra) a)"
  apply(rule ext)
  subgoal for x
  apply(cases "x=sa")
    subgoal by (auto dest!: fun_cong[where ?f="(\<lambda>j. fld (s' j) sa)"] fun_cong[where x=x])
  by (fastforce dest: fun_cong[where ?f="(\<lambda>j. fld (s' j) x)", where x=ra] fun_cong[where x=x])
  done

lemma fld_upd_if: "\<lbrakk>(\<lambda>i. fld (s' i)) = (\<lambda>i. fld (s i))(sid :=
        \<lambda>rcv. if P sid rcv
               then Q' s sid rcv
               else R' s sid rcv); \<And>rcv. Q' s sid rcv = Q s sid rcv; \<And>rcv. R' s sid rcv = R s sid rcv\<rbrakk>
    \<Longrightarrow> fld (s' sid) = (\<lambda>rcv. if P sid rcv then Q s sid rcv else R s sid rcv)"
  by(auto dest!: fun_cong intro!: ext)

lemma fld_upd_eq2_eq:
  "\<lbrakk>(\<lambda>i j. fld (s' j) i) = (\<lambda>i j. fld (s j) i)(sa := (\<lambda>j. fld (s j) sa)(ra := xs)); i \<noteq> ra\<rbrakk>
    \<Longrightarrow> fld (s' i) = fld (s i)"
  by (fastforce dest: fun_cong)

lemma fld_fun_upd2_if:
  "(\<lambda>cid. fld (c' cid)) = (\<lambda>cid. fld (c cid))(cid := fun_upd2 (fld (c cid)) sid op bool)
  \<Longrightarrow> fld (c' cid) = 
   (\<lambda>x. if x = sid then \<lambda>x. (x = op \<longrightarrow> bool) \<and> (x \<noteq> op \<longrightarrow> fld (c cid) sid x) else fld (c cid) x)"
  by(rule ext, drule fun_cong, auto)

lemma fld_upd2: (*s_hist*)
"(\<lambda>i. fld (s' i)) = (\<lambda>i. fld (s i))(sid := (fld (s sid))(p := h, sid := h))
    \<Longrightarrow> fld (s' sid) = (\<lambda>a. if a = sid then h else if a = p then h else fld (s sid) a)"
"\<lbrakk>(\<lambda>i. fld (s' i)) = (\<lambda>i. fld (s i))(sid := (fld (s sid))(p := h, sid := h)); i \<noteq> sid\<rbrakk>
    \<Longrightarrow> fld (s' i) = fld (s i)"
  subgoal
    apply(rule ext)
    apply auto
    by (auto intro!: ext dest!: fun_cong)
  apply(rule ext)
  by (auto dest!: fun_cong)

lemma fld_upd1: (*s_pend*)
"(\<lambda>i. fld (s' i)) = (\<lambda>i. fld (s i))(sid := h) \<Longrightarrow> fld (s' sid) = h "
"\<lbrakk>(\<lambda>i. fld (s' i)) = (\<lambda>i. fld (s i))(sid := h); i \<noteq> sid\<rbrakk> \<Longrightarrow> fld (s' i) = fld (s i)"
  by (auto dest!: fun_cong)

lemma fld_loc_upd: 
  "\<lbrakk>s' x = upd s x; \<forall>i'. i' \<noteq> x \<longrightarrow> s' i' = s i'; s' x = upd s x \<Longrightarrow> fld (s' x) = fld (s x)\<rbrakk>
   \<Longrightarrow> fld (s' sid) = fld (s sid)"
  by(cases "sid = x", auto)
lemmas fld_loc_upd_rot = fld_loc_upd[rotated]

lemma fld_fun_upd_upd: "\<lbrakk>(\<lambda>i. buf (s' i)) = (\<lambda>i. buf (s i))(sa := (buf (s sa))(ra := y)); sa \<noteq> sid\<rbrakk>
       \<Longrightarrow> buf (s' sid) = buf (s sid)"
  by(auto simp add: fun_upd_def dest: fun_cong)

subsubsection\<open>Helping lemmas relating to "live" state and agent splits\<close>
lemma s_live_eq: "\<lbrakk>s' x = upd s x; \<forall>i'. i' \<noteq> x \<longrightarrow> s' i' = s i'; s' x = upd s x \<Longrightarrow> s_live (s' x) = s_live (s x)\<rbrakk>
       \<Longrightarrow> s_live (s' sid) = s_live (s sid)"
  by(cases "sid = x", auto)
lemma c_live_eq: "\<lbrakk>s' x = upd s x; \<forall>i'. i' \<noteq> x \<longrightarrow> s' i' = s i'; s' x = upd s x \<Longrightarrow> c_live (s' x) = c_live (s x)\<rbrakk>
       \<Longrightarrow> c_live (s' sid) = c_live (s sid)"
  by(cases "sid = x", auto)

lemma case_agent_eq_split: 
  "\<lbrakk>\<And>cid . x = Client cid \<Longrightarrow> P' cid = P cid; \<And>sid . x = Server sid \<Longrightarrow> Q' sid = Q sid\<rbrakk>
  \<Longrightarrow> (case x of Client cid \<Rightarrow> P cid | Server sid \<Rightarrow> Q sid) = 
      (case x of Client cid \<Rightarrow> P' cid | Server sid \<Rightarrow> Q' sid)"
  by(cases x, auto)

lemma agent_cases: "\<lbrakk>\<And> cid . x = Client cid \<Longrightarrow> P x; \<And> sid. x = Server sid \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> P x"
  by(cases x, auto)

lemma case_agent_eq:
  "case_agent (\<lambda>cid. c_live (c1 cid)) (\<lambda>sid. s_live (s1 sid)) = 
   case_agent (\<lambda>cid. c_live (c2 cid)) (\<lambda>sid. s_live (s2 sid))
\<Longrightarrow> (\<lambda>cid. c_live (c1 cid)) = (\<lambda>cid. c_live (c2 cid)) \<and> (\<lambda>sid. s_live (s1 sid)) = (\<lambda>sid. s_live (s2 sid))"
  by (metis agent.simps)

lemma case_agent_upd_Client[elim]:
  "case_agent c1 s1 = (case_agent c2 s2)(Client cid := x) \<Longrightarrow> s1 y = s2 y"
  "\<lbrakk>case_agent c1 s1 = (case_agent c2 s2)(Client cid := x); z \<noteq> cid\<rbrakk> \<Longrightarrow> c1 z = c2 z"
  "\<lbrakk>case_agent c1 s1 = (case_agent c2 s2)(Client cid := x); z = cid\<rbrakk> \<Longrightarrow> c1 z = x"
  by(auto intro!: ext dest: fun_cong[of _ _ "Client _"] fun_cong[of _ _ "Server _"])

lemma case_agent_upd_Server[elim]:
  "case_agent c1 s1 = (case_agent c2 s2)(Server sid := x) \<Longrightarrow> c1 y = c2 y"
  "\<lbrakk>case_agent c1 s1 = (case_agent c2 s2)(Server sid := x); z \<noteq> sid\<rbrakk> \<Longrightarrow> s1 z = s2 z"
  "\<lbrakk>case_agent c1 s1 = (case_agent c2 s2)(Server sid := x); z = sid\<rbrakk> \<Longrightarrow> s1 z = x"
  by(auto intro!: ext dest: fun_cong[of _ _ "Client _"] fun_cong[of _ _ "Server _"])


subsubsection\<open>Lemmas used to show the equivalence of initial states\<close>
lemma case_agent_live_const: 
  "case_agent (\<lambda>cid. c_live (c cid)) (\<lambda>sid. s_live (s sid)) = (\<lambda>_. H) 
  \<Longrightarrow> c_live (c i) = H \<and> s_live (s j) = H"
  by(auto dest: fun_cong[of _ _ "Client i"] fun_cong[of _ _ "Server j"])

lemma case_agent_eq_live[simp]: 
  "case_agent (\<lambda>cid. P (Client cid)) (\<lambda>sid. P (Server sid)) = (\<lambda>ag . P ag)"
  "case_agent (\<lambda>cid. Q) (\<lambda>sid. Q) = (\<lambda>ag . Q)"
  by(auto simp add: fun_eq_iff intro: agent_cases)

lemma case_agent_c_live:
  "case_agent (\<lambda>cid. c_live (c' cid)) (\<lambda>sid. s_live (s' sid)) 
 = case_agent (\<lambda>cid. c_live (c cid)) (\<lambda>sid. s_live (s sid))
    \<Longrightarrow> c_live (c' sa) = c_live (c sa)"
  by(auto dest!: case_agent_eq)(auto dest!: fun_cong)

lemma case_agent_s_live:
  "case_agent (\<lambda>cid. c_live (c' cid)) (\<lambda>sid. s_live (s' sid)) 
 = case_agent (\<lambda>cid. c_live (c cid)) (\<lambda>sid. s_live (s sid))
    \<Longrightarrow> s_live (s' sa) = s_live (s sa)"
  by(auto dest!: case_agent_eq)(auto dest!: fun_cong)

lemma fun_cong_field: "\<lbrakk>(\<lambda>i. R (s' i)) = P s; P s sid = Q s sid\<rbrakk>
    \<Longrightarrow> R (s' sid) = Q s sid"
  by metis
lemma fun_cong_field2: assumes "(\<lambda>i j. R (s' j) i) = P s" "\<And>x . P s x sid = Q s sid x"
  shows "R (s' sid) = Q s sid"
  apply(rule ext) 
  subgoal for x
    using assms(1) apply-
    apply(drule fun_cong[of _ _ x])
    apply(drule fun_cong[of _ _ sid])
    apply auto
    using assms(2) by auto
  done

subsubsection\<open>Collection of lemmas\<close>

lemmas fld_up_eqs = fld_upd_eq fld_upd_eq2 fld_upd_eq2_eq fld_upd_if fld_upd1 fld_fun_upd2_if fld_upd2
lemmas ibuf_eqs = ibuf_eq[of c_scibuf] ibuf_eq[of s_csibuf] ibuf_eq[of s_ssibuf]
lemmas fld_eqs = fld_eq[of s_pend] fld_eq[of s_hist] fld_eq[of s_uopcid] 
  fld_eq[of s_scobuf] fld_eq[of s_ssobuf] fld_eq[of c_pend] fld_eq[of c_csobuf]
lemmas field_eqs = fld_eqs ibuf_eqs case_agent_c_live case_agent_s_live


subsection\<open>Trace Equivalence Proof\<close>

lemmas m1_trans_induct = 
  m1_trans.induct [case_names 
    B1_C_req B1_C_res B1_P_req B1_P_res B1_B_sync B1_S_purge B1_cs_Send B1_sc_Send B1_ss_Send 
    B1_cs_Recv B1_sc_Recv B1_ss_Recv B1_Detect_failure B1_Skip
  ]

(*used to decompose the trace equivalence goal into three subgoals*)
lemma iffConjI: "\<lbrakk>P \<Longrightarrow> Q; P \<Longrightarrow> R; \<lbrakk>Q; R\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P \<longleftrightarrow> Q \<and> R"
  by blast

declare equalityI [rule del]
declare iffI [rule del]

lemma m1_equiv_m2: "traces m1 = traces m2"
proof (unfold m2_def, induction rule: decomposition_env_system_equiv_upto[where \<rho>=med21])
  case (surj u g u')
  show ?case 
    apply (induction u g u' rule: m1_trans.induct, auto)
    subgoal for _ _ _ is_resend by(cases is_resend, auto)
    subgoal for agt _ by(cases agt, auto)
    done
next
  case bij
  then show ?case
    apply(auto intro!: bijI equalityI)
    apply(rule injI) 
    subgoal for x y (*inj med21*)
      by(cases x, cases y, auto simp add: m1_defs elim!: field_eqs)  
    subgoal for x (*\<And>x. x \<in> range med21*)
      by(rule image_eqI[where ?x = "inv_med21 x"], auto)
    done
next
  case (init e sys s1)
  then show ?case
    apply(cases sys)
    apply (auto intro!: iffI equalityI)
    by (auto simp add: m1_defs m2_defs dest: case_agent_live_const elim: fun_cong_field fun_cong_field2)
next
  case (trans evte evtf g e sys e' sys')
  then show ?case
    apply(cases sys) subgoal for c s
      apply(cases sys') subgoal for c' s'
proof (induction "med21 (e, (c, s))" g "med21 (e', (c', s'))" rule: m1_trans_induct)
  case (B1_C_req cid sid op is_resend)
  then show ?case 
  proof(intro iffConjI, simp_all only:) (*only apply simplification for sys=(c,s) and sys'=(c',s')*)
    assume assum: "\<chi> (evte, evtf) = Some (B1_C_req cid sid op is_resend)" 
           "m1: med21 (e, c, s)\<midarrow>B1_C_req cid sid op is_resend\<rightarrow> med21 (e', c', s')"
    then have s_def[simp]: "\<And>x. s' x = s x"
      by(auto simp add: m1_defs m2e_defs m2s_defs elim: field_eqs)
    from assum show "m2e: e\<midarrow>evte\<rightarrow> e'"
      by(cases is_resend, auto simp add: m1_defs m2e_defs m2c_defs cond_request_def
                                  elim!: field_eqs fld_fun_upd_upd fld_up_eqs)
    from assum show "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      by(cases is_resend, auto simp add: m1_defs m2_defs cond_request_def c_prim_def prim_def
                                  elim!: field_eqs fld_fun_upd_upd fld_up_eqs)
  next
    assume "\<chi> (evte, evtf) = Some (B1_C_req cid sid op is_resend)" 
           "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
    then show "m1: med21 (e, c, s)\<midarrow>B1_C_req cid sid op is_resend\<rightarrow> med21 (e', c', s')"
      by(cases is_resend, auto simp add: m1_defs m2_defs cond_request_def intro: c_live_eq[of c',symmetric] 
            intro!: ext case_agent_eq_split elim: fld_loc_upd[of c'] prim_med21) (*takes ~20sec*)
  qed
next
  case (B1_C_res cid sid op h)
  then show ?case 
  proof(intro iffConjI, simp_all only:)
    assume assum: "\<chi> (evte, evtf) = Some (B1_C_res cid sid op h)" 
           "m1: med21 (e, c, s)\<midarrow>B1_C_res cid sid op h\<rightarrow> med21 (e', c', s')"
    then have s_def[simp]: "\<And>x. s' x = s x"
      by(auto simp add: m1_defs m2e_defs m2s_defs elim: field_eqs)
    from assum show "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      by(auto simp add: m1_defs m2_defs elim!: field_eqs fld_fun_upd_upd fld_up_eqs)
    next
      assume "\<chi> (evte, evtf) = Some (B1_C_res cid sid op h)" 
             "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      then show "m1: med21 (e, c, s)\<midarrow>B1_C_res cid sid op h\<rightarrow> med21 (e', c', s')"
        by(auto simp add: m1_defs m2_defs intro: c_live_eq[of c',symmetric] 
              intro!: ext elim: fld_loc_upd[of c'] intro!: case_agent_eq_split)
  qed
next
  case (B1_P_req sid cid op h')
  then show ?case 
  proof(intro iffConjI, simp_all only:)
    assume assum: "\<chi> (evte, evtf) = Some (B1_P_req sid cid op h')" 
           "m1: med21 (e, c, s)\<midarrow>B1_P_req sid cid op h'\<rightarrow> med21 (e', c', s')"
    then have c_def[simp]: "\<And>x. c' x = c x"
      by(auto simp add: m1_defs m2e_defs m2s_defs elim: case_agent_upd_Server elim: field_eqs)
    from assum show "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      by(auto simp add: m1_defs m2_defs live_geq_def live2_geq_def
          elim!: field_eqs fld_fun_upd_upd fld_up_eqs fld_upd_if[of _ _ s])
    next
      assume "\<chi> (evte, evtf) = Some (B1_P_req sid cid op h')" 
             "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      then show "m1: med21 (e, c, s)\<midarrow>B1_P_req sid cid op h'\<rightarrow> med21 (e', c', s')"
        by(auto 3 4 simp add: m1_defs iffI m2_defs intro!: ext case_agent_eq_split live_geq_med21 elim: fld_loc_upd_rot)
  qed
next
  case (B1_P_res sid cid op h)
  then show ?case 
  proof(intro iffConjI, simp_all only:)
    assume assum: "\<chi> (evte, evtf) = Some (B1_P_res sid cid op h)" 
           "m1: med21 (e, c, s)\<midarrow>B1_P_res sid cid op h\<rightarrow> med21 (e', c', s')"
    then have c_def[simp]: "\<And>x. c' x = c x"
      by(auto simp add: m1_defs m2e_defs m2s_defs elim: case_agent_upd_Server elim: field_eqs)
    from assum show "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      by(auto simp add: m1_defs m2_defs collect_res_med21 elim!: field_eqs fld_fun_upd_upd fld_up_eqs 
          fun_cong_field[of s_hist s' _ s sid] fun_cong_field2[of s_ssibuf s' _ s])
    next
      assume "\<chi> (evte, evtf) = Some (B1_P_res sid cid op h)" 
             "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      then show "m1: med21 (e, c, s)\<midarrow>B1_P_res sid cid op h\<rightarrow> med21 (e', c', s')"
        by(auto 3 4 simp add: m1_defs m2_defs collect_res_med21 intro!: ext case_agent_eq_split 
            intro: iffI elim: fld_loc_upd_rot s_live_eq[of s', symmetric, rotated])
  qed
next
  case (B1_B_sync sid pr op h)
  then show ?case 
  proof(intro iffConjI, simp_all only:)
    assume assum: "\<chi> (evte, evtf) = Some (B1_B_sync sid pr op h)" 
           "m1: med21 (e, c, s)\<midarrow>B1_B_sync sid pr op h\<rightarrow> med21 (e', c', s')"
    then have c_def[simp]: "\<And>x. c' x = c x"
      by(auto simp add: m1_defs m2e_defs m2s_defs elim: case_agent_upd_Server elim: field_eqs)
    from assum show "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      by(auto simp add: m1_defs m2_defs live_geq_def live2_geq_def
          elim!: field_eqs fld_fun_upd_upd fld_up_eqs)
    next
      assume "\<chi> (evte, evtf) = Some (B1_B_sync sid pr op h)" 
             "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      then show "m1: med21 (e, c, s)\<midarrow>B1_B_sync sid pr op h\<rightarrow> med21 (e', c', s')"
        by(auto 3 4 simp add: m1_defs m2_defs live_geq_def live2_geq_def intro!: ext case_agent_eq_split 
            intro: iffI elim: fld_loc_upd_rot)
  qed
next
  case (B1_S_purge a b)
  then show ?case 
  proof(intro iffConjI, simp_all only:)
    assume assum: "\<chi> (evte, evtf) = Some (B1_S_purge a b)" 
           "m1: med21 (e, c, s)\<midarrow>B1_S_purge a b\<rightarrow> med21 (e', c', s')"
    then have c_def[simp]: "\<And>x. c' x = c x"
      by(auto simp add: m1_defs m2e_defs m2s_defs elim: field_eqs)
    from assum show "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      by(auto simp add: m1_defs m2_defs elim!: field_eqs fld_fun_upd_upd fld_up_eqs)
    next
      assume "\<chi> (evte, evtf) = Some (B1_S_purge a b)" 
             "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      then show "m1: med21 (e, c, s)\<midarrow>B1_S_purge a b\<rightarrow> med21 (e', c', s')"
        by(auto simp add: m1_defs m2_defs elim: fld_loc_upd[of s',symmetric] fld_loc_upd[of s']
              intro!: ext case_agent_eq_split)
  qed
next
  case (B1_cs_Send sa ra m)
  then show ?case 
  proof(intro iffConjI, simp_all only:)
    assume assum: "\<chi> (evte, evtf) = Some (B1_cs_Send sa ra m)" 
           "m1: med21 (e, c, s)\<midarrow>B1_cs_Send sa ra m\<rightarrow> med21 (e', c', s')"
    then have s_def[simp]: "\<And>x. s' x = s x"
      by(auto simp add: m1_defs m2e_defs m2s_defs elim: field_eqs)
    from assum show "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      by(auto simp add: m1_defs m2_defs elim!: field_eqs fld_fun_upd_upd fld_up_eqs)
    next
      assume "\<chi> (evte, evtf) = Some (B1_cs_Send sa ra m)" 
             "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      then show "m1: med21 (e, c, s)\<midarrow>B1_cs_Send sa ra m\<rightarrow> med21 (e', c', s')"
        by(auto simp add: m1_defs m2_defs intro: c_live_eq[of c',symmetric] 
              intro!: ext elim: fld_loc_upd[of c'] intro!: case_agent_eq_split)
  qed
next
  case (B1_sc_Send sa ra m)
  then show ?case 
  proof(intro iffConjI, simp_all only:)
    assume assum: "\<chi> (evte, evtf) = Some (B1_sc_Send sa ra m)" 
           "m1: med21 (e, c, s)\<midarrow>B1_sc_Send sa ra m\<rightarrow> med21 (e', c', s')"
    then have c_def[simp]: "\<And>x. c' x = c x"
      by(auto simp add: m1_defs m2e_defs m2s_defs elim: field_eqs)
    from assum show "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      by(auto simp add: m1_defs m2_defs elim!: field_eqs fld_fun_upd_upd fld_up_eqs)
    next
      assume "\<chi> (evte, evtf) = Some (B1_sc_Send sa ra m)" 
             "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      then show "m1: med21 (e, c, s)\<midarrow>B1_sc_Send sa ra m\<rightarrow> med21 (e', c', s')"
        by(auto simp add: m1_defs m2_defs intro: s_live_eq[of s',symmetric] 
              intro!: ext elim: fld_loc_upd[of s'] intro!: case_agent_eq_split)
  qed
next
  case (B1_ss_Send sa ra m)
  then show ?case 
  proof(intro iffConjI, simp_all only:)
    assume assum: "\<chi> (evte, evtf) = Some (B1_ss_Send sa ra m)" 
           "m1: med21 (e, c, s)\<midarrow>B1_ss_Send sa ra m\<rightarrow> med21 (e', c', s')"
    then have c_def[simp]: "\<And>x. c' x = c x"
      by(auto simp add: m1_defs m2e_defs m2s_defs elim: field_eqs)
    from assum show "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      by(auto simp add: m1_defs m2_defs elim!: field_eqs fld_fun_upd_upd fld_up_eqs)
    next
      assume "\<chi> (evte, evtf) = Some (B1_ss_Send sa ra m)" 
             "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      then show "m1: med21 (e, c, s)\<midarrow>B1_ss_Send sa ra m\<rightarrow> med21 (e', c', s')"
        by(auto simp add: m1_defs m2_defs intro: s_live_eq[of s',symmetric] 
              intro!: ext elim: fld_loc_upd[of s'] intro!: case_agent_eq_split)
  qed
next
  case (B1_cs_Recv sa ra m)
  then show ?case 
  proof(intro iffConjI, simp_all only:)
    assume assum: "\<chi> (evte, evtf) = Some (B1_cs_Recv sa ra m)" 
           "m1: med21 (e, c, s)\<midarrow>B1_cs_Recv sa ra m\<rightarrow> med21 (e', c', s')"
    then have c_def[simp]: "\<And>x. c' x = c x"
      by(auto simp add: m1_defs m2e_defs m2s_defs elim: field_eqs)
    from assum show "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      by(auto simp add: m1_defs m2_defs elim!: field_eqs fld_fun_upd_upd fld_up_eqs)
    next
      assume "\<chi> (evte, evtf) = Some (B1_cs_Recv sa ra m)" 
             "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      then show "m1: med21 (e, c, s)\<midarrow>B1_cs_Recv sa ra m\<rightarrow> med21 (e', c', s')"
        by(auto simp add: m1_defs m2_defs intro: s_live_eq[of s',symmetric] 
              intro!: ext elim: fld_loc_upd[of s'] intro!: case_agent_eq_split)
  qed
next
  case (B1_sc_Recv sa ra m)
  then show ?case 
  proof(intro iffConjI, simp_all only:)
    assume assum: "\<chi> (evte, evtf) = Some (B1_sc_Recv sa ra m)" 
           "m1: med21 (e, c, s)\<midarrow>B1_sc_Recv sa ra m\<rightarrow> med21 (e', c', s')"
    then have s_def[simp]: "\<And>x. s' x = s x"
      by(auto simp add: m1_defs m2e_defs m2s_defs elim: field_eqs)
    from assum show "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      by(auto simp add: m1_defs m2_defs elim!: field_eqs fld_fun_upd_upd fld_up_eqs)
    next
      assume "\<chi> (evte, evtf) = Some (B1_sc_Recv sa ra m)" 
             "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      then show "m1: med21 (e, c, s)\<midarrow>B1_sc_Recv sa ra m\<rightarrow> med21 (e', c', s')"
        by(auto simp add: m1_defs m2_defs intro: c_live_eq[of c',symmetric] 
              intro!: ext elim: fld_loc_upd[of c'] intro!: case_agent_eq_split)
  qed
next
  case (B1_ss_Recv sa ra m)
  then show ?case 
  proof(intro iffConjI, simp_all only:)
    assume assum: "\<chi> (evte, evtf) = Some (B1_ss_Recv sa ra m)" 
           "m1: med21 (e, c, s)\<midarrow>B1_ss_Recv sa ra m\<rightarrow> med21 (e', c', s')"
    then have c_def[simp]: "\<And>x. c' x = c x"
      by(auto simp add: m1_defs m2e_defs m2s_defs elim: field_eqs)
    from assum show "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      by(auto simp add: m1_defs m2_defs elim!: field_eqs fld_fun_upd_upd fld_up_eqs)
    next
      assume "\<chi> (evte, evtf) = Some (B1_ss_Recv sa ra m)" 
             "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      then show "m1: med21 (e, c, s)\<midarrow>B1_ss_Recv sa ra m\<rightarrow> med21 (e', c', s')"
        by(auto simp add: m1_defs m2_defs intro: s_live_eq[of s',symmetric] 
              intro!: ext elim: fld_loc_upd[of s'] intro!: case_agent_eq_split)
  qed
next
  case (B1_Detect_failure agt sid)
  then show ?case 
  proof(intro iffConjI, simp_all only:)
    assume assum: "\<chi> (evte, evtf) = Some (B1_Detect_failure agt sid)" 
           "m1: med21 (e, c, s)\<midarrow>B1_Detect_failure agt sid\<rightarrow> med21 (e', c', s')"
    from assum show "m2e: e\<midarrow>evte\<rightarrow> e'"
      by(cases agt, auto simp add: m1_defs m2e_defs m2c_defs m2s_defs  
                         elim!: field_eqs fld_fun_upd_upd fld_up_eqs)
    from assum show "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      by(cases agt, auto simp add: m1_defs m2_defs elim!: field_eqs fld_fun_upd_upd fld_up_eqs intro: sym)
  next
      assume "\<chi> (evte, evtf) = Some (B1_Detect_failure agt sid)" 
             "m2e: e\<midarrow>evte\<rightarrow> e'" "ievent_dist (m2c || m2s): (c, s)\<midarrow>evtf\<rightarrow> (c', s')"
      then show "m1: med21 (e, c, s)\<midarrow>B1_Detect_failure agt sid\<rightarrow> med21 (e', c', s')"
        apply-
        apply(rule agent_cases[where x=agt])
        by (auto 3 4 simp add: m1_defs m2_defs intro: c_live_eq[of c',symmetric] s_live_eq[of s',symmetric] 
              intro!: ext elim: fld_loc_upd[of c'] fld_loc_upd[of s'] intro!: case_agent_eq_split) 
  qed
next
  case B1_Skip
  then show ?case by(auto intro!: iffI simp add: m1_defs m2_defs
                  elim!: field_eqs[symmetric] field_eqs)
qed
  done (*cases sys*)
  done (*cases sys'*)
qed

(******************************************************************************)
subsection \<open>Property preservation\<close>
(******************************************************************************)
lemma m2_backup_consistency: "m2 \<Turnstile>\<^sub>E\<^sub>S Collect backup_consistent"
  using m1_backup_consistency
  by(auto simp add: m1_equiv_m2[symmetric] intro!: trace_propertyI elim: trace_propertyE)


end (*locale*)

end
