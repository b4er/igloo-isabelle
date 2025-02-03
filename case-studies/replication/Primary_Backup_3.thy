(*
  Igloo Case Study: Replication 
  Primary-Backup Replication

  Author: Tobias Klenze <tobias.klenze@inf.ethz.ch>
          Christoph Sprenger (sprenger@inf.ethz.ch)
  Date: December 2019
*)

section \<open>Primary-Backup Replication\<close>
text\<open>Here, we separately translate the guarded event systems of both client and server given in the 
previous model into a trace-equivalent IO specification.\<close>


theory Primary_Backup_3
  imports
    "Primary_Backup_2"
    "Igloo.Event_Systems_into_IO_Processes"
    "Igloo.IO_Processes_into_IO_Separation_Logic"
    "Igloo.IO_Behavior"
begin

text \<open>Set up some useful simplification and congruence rules for simplifying the 
translation of event systems into I/O specs.\<close>

lemma cval_case_const: 
  "(case cval of cUnit \<Rightarrow> c | cUpdate _ _ \<Rightarrow> c | cInt1 _ _ \<Rightarrow> c | cInt2 _ _ _ \<Rightarrow> c | cInt3 _ \<Rightarrow> c) = c"
  by (simp split: cval.splits)

lemma sval_case_const:
  "(case sval of sUnit \<Rightarrow> c | sSync _ _ \<Rightarrow> c | sUpdate _ _ \<Rightarrow> c | sInt1 _ _ _ \<Rightarrow> c  
      | sInt2 _ _ _ \<Rightarrow> c  | sInt3 _ \<Rightarrow> c ) = c"
  by (simp split: sval.splits)

lemma cval_case_distribR: 
  "(case cval of cUnit \<Rightarrow> f1 | cUpdate x1 x2 \<Rightarrow> f2 x1 x2 | cInt1 x1 x2 \<Rightarrow> f3 x1 x2 
    | cInt2 x1 x2 x3 \<Rightarrow> f4 x1 x2 x3 | cInt3 x1 \<Rightarrow> f5 x1) z =
   (case cval of cUnit \<Rightarrow> f1 z | cUpdate x1 x2 \<Rightarrow> f2 x1 x2 z | cInt1 x1 x2 \<Rightarrow> f3 x1 x2 z 
    | cInt2 x1 x2 x3 \<Rightarrow> f4 x1 x2 x3 z | cInt3 x1 \<Rightarrow> f5 x1 z)"
  by (simp split: cval.splits)

lemma sval_case_distribR:
  "(case sval of sUnit \<Rightarrow> f1 | sSync x1 x2 \<Rightarrow> f2 x1 x2 | sUpdate x1 x2 \<Rightarrow> f3 x1 x2 
    | sInt1 x1 x2 x3 \<Rightarrow> f4 x1 x2 x3 | sInt2 x1 x2 x3 \<Rightarrow> f5 x1 x2 x3 | sInt3 x1 \<Rightarrow> f6 x1) z
 = (case sval of sUnit \<Rightarrow> f1 z | sSync x1 x2 \<Rightarrow> f2 x1 x2 z | sUpdate x1 x2 \<Rightarrow> f3 x1 x2 z 
    | sInt1 x1 x2 x3 \<Rightarrow> f4 x1 x2 x3 z | sInt2 x1 x2 x3 \<Rightarrow> f5 x1 x2 x3 z | sInt3 x1 \<Rightarrow> f6 x1 z)"
  by (simp split: sval.splits)

lemmas val_case_distrib_simps = 
  cval.case_distrib[where h=embedp] 
  cval.case_distrib[where h=guard] cval.case_distrib[where h=update] 
  cval_case_distribR cval_case_const
  sval.case_distrib[where h=embedp] 
  sval.case_distrib[where h=guard] sval.case_distrib[where h=update] 
  sval_case_distribR sval_case_const

lemmas if_distrib_simps =
  if_distrib[where f=embedp] if_distrib[where f=guard] if_distrib[where f=update] 
  if_distribR 

lemmas iospec_simps =
  lBChoice.simps embedp_VChoice_is_AllStar 
  if_distrib_simps val_case_distrib_simps

lemmas iospec_congs [cong] = 
  arg_cong[where f="\<forall>\<^sup>\<star>"] if_cong cval.case_cong sval.case_cong 

declare if_split [split del]


(******************************************************************************)
subsection \<open>Client's I/O specification\<close>
(******************************************************************************)

context loc2
begin

definition m3c_proc :: "cid \<Rightarrow> 'uop m2_state_client \<Rightarrow> (bio2c, ('uop::countable, 'ADDR) cval) process" where
  "m3c_proc i s = pr (m2c_ioges i) s"    

text \<open>Embedding of the process into I/O spec.\<close>

definition m3c_iospec :: "place \<Rightarrow> cid \<Rightarrow> 'uop m2_state_client \<Rightarrow> (bio2c, ('uop::countable, 'ADDR) cval) cassn" where 
  "m3c_iospec t i s = embedp (m3c_proc i s) t"

text \<open>Correctness of the translation to the I/O spec.\<close>

lemma m2c_ioges_trace_equiv_iospec_m3c:
    "client.traces_assn (ExT (\<lambda>t. CTok t \<star> m3c_iospec t i s))
   = traces (client.IOGES_to_ES (m2c_ioges i) ((=) s))" (is "?L = ?R")
proof-
  have "?L = client.traces_opsem (m3c_proc i s)" 
    by(simp add: m3c_iospec_def client.trace_equivalences)
  also have "... = ?R" 
    by (simp add: m3c_proc_def client.emb_opsem_equiv)
  finally show ?thesis by simp
qed

subsubsection \<open>Unfolding of the I/O specification\<close>
(******************************************************************************)

definition bio2c_list :: "bio2c list" where
  "bio2c_list = [
     IN B2_C_repeat_req, IN B2_C_res, IO B2_C_req, 
           IO B2_C_detect_failure, IO B2_C_Send, IO B2_C_Recv, Skip, Stop
   ]"

lemma bio2c_list_UNIV: "set bio2c_list = (UNIV::bio2c set)" 
  using bio2c_UNIV by (auto simp add: bio2c_list_def)

text \<open>Here, including parameters.\<close>

definition m3c_proc_ord where
  "m3c_proc_ord i s \<equiv> lPr bio2c_list (m2c_ioges i) s"

lemmas m3c_proc_ord_defs = m3c_proc_ord_def bio2c_list_def

lemma m3c_proc_opsem_equiv_m3c_proc_ord: 
  "client.traces_opsem (m3c_proc i s) = client.traces_opsem (m3c_proc_ord i s)"
by (simp add: m3c_proc_def m3c_proc_ord_def client.bisim_lPr_pr bio2c_list_UNIV)


text \<open>Redefine the I/O spec and prove a fixed point equation.\<close>

term "embedp (m3c_proc_ord i s) T"

definition m3c_iospec_ord :: 
  "place \<Rightarrow> cid \<Rightarrow> 'uop m2_state_client \<Rightarrow> (bio2c, ('uop::countable, 'ADDR) cval) cassn" 
where 
  "m3c_iospec_ord T i s = embedp (m3c_proc_ord i s) T"

lemmas m3c_iospec_ord_defs = m3c_iospec_ord_def m3c_proc_ord_defs


text \<open>Prove a fixed point equation. This form can be translated to the input language of 
a program verifier (Nagini, VeriFast).\<close>

abbreviation m3c_repeat_req where
  "m3c_repeat_req T i s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if case v of
        cInt1 sid op \<Rightarrow> (\<exists> sid' . c_pend s sid' op \<and> sid' \<notin> c_live s \<and> c_prim s = Some sid)
      | _ \<Rightarrow> False
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio (IN B2_C_repeat_req) T v X T' \<star>
      m3c_iospec_ord T' i 
        (case v of cInt1 sid op \<Rightarrow> 
          s\<lparr>c_csobuf := (c_csobuf s)(sid := c_csobuf s sid @ [m1_Upd_req op]),
            c_pend := fun_upd2 (c_pend s) sid op True\<rparr>))) 
    else Bool True)"

abbreviation m3c_res where
  "m3c_res T i s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if case v of
        cInt2 sid op h \<Rightarrow> is_head (m1_Upd_res op h) (c_scibuf s sid)
      | _ \<Rightarrow> False
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio (IN B2_C_res) T v X T' \<star>
      m3c_iospec_ord T' i 
        (case v of cInt2 sid op h \<Rightarrow> 
          s\<lparr>c_scibuf := (c_scibuf s)(sid := tl (c_scibuf s sid)),
            c_pend := fun_upd2 (c_pend s) sid op False\<rparr>))) 
    else Bool True)"

abbreviation m3c_detect_failure where
  "m3c_detect_failure T i s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if case v of
        cInt3 sid \<Rightarrow> True
      | _ \<Rightarrow> False
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio (IO B2_C_detect_failure) T v X T' \<star>
      m3c_iospec_ord T' i 
        (case v of cInt3 sid\<Rightarrow> 
          s\<lparr> c_live := (c_live s) - {sid} \<rparr> | _ \<Rightarrow> s))) 
    else Bool True)"

text\<open>The client request makes the following environment assumption: op is a freshly generated, 
unique value. In practice, a sufficiently long random value can be used.\<close>
abbreviation m3c_req where
  "m3c_req T i s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if case v of
        cInt1 sid op \<Rightarrow> c_prim s = Some sid
      | _ \<Rightarrow> False
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio (IO B2_C_req) T v X T' \<star>
      m3c_iospec_ord T' i 
        (case v of cInt1 sid op \<Rightarrow> 
          s\<lparr>c_csobuf := (c_csobuf s)(sid := c_csobuf s sid @ [m1_Upd_req op]),
            c_pend := fun_upd2 (c_pend s) sid op True\<rparr> | _ \<Rightarrow> s))) 
    else Bool True)"

abbreviation m3c_send where
  "m3c_send T i s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if case v of cUpdate adr m \<Rightarrow> 
      (case (inv addr) adr of Server sid \<Rightarrow> is_head m (c_csobuf s sid) | _ \<Rightarrow> False)
      | _ \<Rightarrow> False
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio (IO B2_C_Send) T v X T' \<star>
      m3c_iospec_ord T' i 
        (case v of cUpdate adr m \<Rightarrow> 
          (case (inv addr) adr of Server sid \<Rightarrow> 
            c_csobuf_rm s sid)))) 
    else Bool True)"

abbreviation m3c_receive where
  "m3c_receive T i s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if v = cUnit
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio (IO B2_C_Recv) T v X T' \<star>
      m3c_iospec_ord T' i 
        (case X of cUpdate adr m \<Rightarrow> 
          (case (inv addr) adr of Server sid \<Rightarrow> s\<lparr>c_scibuf := (c_scibuf s)(sid := c_scibuf s sid @ [m])\<rparr>
          | _ \<Rightarrow> s) \<comment> \<open>typing ensures the sender is a Server\<close>
        | _ \<Rightarrow> s))) \<comment> \<open>typing ensures that received term X is an update message, not sUnit or an internal value\<close>
    else Bool True)"

abbreviation m3c_skip where
  "m3c_skip T i s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if True
    then ExT (\<lambda>T'. ExV (\<lambda>X. CBio Skip T v X T' \<star> m3c_iospec_ord T' i s))
    else Bool True)"

abbreviation m3c_stop where
  "m3c_stop T i s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if False
    then ExT (\<lambda>T'. ExV (\<lambda>X. CBio Stop T v X T' \<star> m3c_iospec_ord T' i s))
    else Bool True)"

lemma m3c_iospec_ord:
  "m3c_iospec_ord T i s = 
     m3c_repeat_req T i s \<star>
    (m3c_res T i s \<star>
    (m3c_req T i s \<star>
    (m3c_detect_failure T i s \<star>
    (m3c_send T i s \<star>
    (m3c_receive T i s \<star>
    (m3c_skip T i s \<star> 
    (m3c_stop T i s \<star> 
    Bool True)))))))"

  \<comment> \<open>Note first method works on LHS only\<close>
  by (simp add: m3c_iospec_ord_def[where T=T] m3c_proc_ord_defs lPr.code[where s="s"])
     (auto simp add: m3c_iospec_ord_def m3c_proc_ord_defs m2c_trans_defs iospec_simps remove_def)

text \<open>This lemma proves the equivalence between the original, unordered IO-spec, and the unfolded,
      ordered IO-spec.\<close>

lemma translation_iospec_m3c:
  "client.traces_assn (ExT (\<lambda>T. CTok T \<star> m3c_iospec T i s)) = 
   client.traces_assn (ExT (\<lambda>T. CTok T \<star> m3c_iospec_ord T i s))"
  by (auto simp add: m3c_iospec_def m3c_iospec_ord_def m3c_proc_ord_def 
                     m3c_proc_opsem_equiv_m3c_proc_ord
           intro: client.traces_assn_embedI del: equalityI)



text \<open>Correctness of the unfolding of the I/O spec.\<close>

abbreviation client_iospec_traces where
  "client_iospec_traces i \<equiv> client.traces_assn (ExT (\<lambda>t. CTok t \<star> m3c_iospec_ord t i m2c_init))"

lemma m3c_IOGES_trace_equiv_iospec:
    "client_iospec_traces i = traces (m2c_fES_base i)"
  by(simp add: m2c_fES_base_def m2c_ioges_trace_equiv_iospec_m3c[symmetric] m3c_iospec_ord_def 
               m3c_iospec_def client.trace_equivalences[symmetric] m3c_proc_opsem_equiv_m3c_proc_ord)

lemma m3c_IOGES_trace_equiv_iospec_\<rho>:
  "client_iospec_traces i \<lceil>\<rho>\<rceil> = traces (m2c_fES i)"
  by(simp add: m2c_fES_def traces_relabel_eq m3c_IOGES_trace_equiv_iospec)


end \<comment> \<open>context initiator\<close>


(******************************************************************************)
subsection \<open>Server's I/O specification\<close>
(******************************************************************************)

context loc2 begin

definition m3s_proc :: "sid \<Rightarrow> 'uop m2_state_server \<Rightarrow> (bio2s, ('uop::countable, 'ADDR) sval) process" where
  "m3s_proc i s = pr (m2s_ioges i) s" 

text \<open>Embedding of the process into I/O spec.\<close>

definition m3s_iospec :: "place \<Rightarrow> sid \<Rightarrow> 'uop m2_state_server \<Rightarrow> (bio2s, ('uop::countable, 'ADDR) sval) cassn" where 
  "m3s_iospec t i s = embedp (m3s_proc i s) t"

text \<open>Correctness of the translation to the I/O spec.\<close>

lemma m2s_ioges_trace_equiv_iospec_m3s:
    "server.traces_assn (ExT (\<lambda>t. CTok t \<star> m3s_iospec t i s))
   = traces (server.IOGES_to_ES (m2s_ioges i) ((=) s))" (is "?L = ?R")
proof-
  have "?L = server.traces_opsem (m3s_proc i s)" 
    by(simp add: m3s_iospec_def server.trace_equivalences)
  also have "... = ?R" 
    by (simp add: m3s_proc_def server.emb_opsem_equiv)
  finally show ?thesis by simp
qed

subsubsection \<open>Unfolding of the I/O specification\<close>
(******************************************************************************)

definition bio2s_list :: "bio2s list" where
  "bio2s_list = [
     IN B2_P_req, IN B2_P_res, IN B2_B_sync, IN B2_S_purge, 
     IO B2_S_Detect_failure, IO B2_S_Send, IO B2_S_Recv, Skip, Stop
   ]"

lemma bio2s_list_UNIV: "set bio2s_list = (UNIV::bio2s set)" 
  using bio2s_UNIV by (auto simp add: bio2s_list_def)

text \<open>Here, including parameters.\<close>

definition m3s_proc_ord where
  "m3s_proc_ord i s \<equiv> lPr bio2s_list (m2s_ioges i) s"

lemmas m3s_proc_ord_defs = m3s_proc_ord_def bio2s_list_def

lemma m3s_proc_opsem_equiv_m3s_proc_ord: 
  "server.traces_opsem (m3s_proc i s) = server.traces_opsem (m3s_proc_ord i s)"
by (simp add: m3s_proc_def m3s_proc_ord_def server.bisim_lPr_pr bio2s_list_UNIV)


text \<open>Redefine the I/O spec and prove a fixed point equation.\<close>

definition m3s_iospec_ord :: 
  "place \<Rightarrow> sid \<Rightarrow> 'uop m2_state_server \<Rightarrow> (bio2s, ('uop::countable, 'ADDR) sval) cassn" 
where 
  "m3s_iospec_ord T i s = embedp (m3s_proc_ord i s) T"

lemmas m3s_iospec_ord_defs = m3s_iospec_ord_def m3s_proc_ord_defs


text \<open>Prove a fixed point equation. This form can be translated to the input language of 
a program verifier (Nagini, VeriFast).\<close>

abbreviation m3p_req where
  "m3p_req T i s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if case v of sInt1 cid op h \<Rightarrow> 
          i \<in> s_live s \<and> is_head (m1_Upd_req op) (s_csibuf s cid) \<and> h = cond_app (s_pend s) op
        | _ \<Rightarrow> False
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio (IN B2_P_req) T v X T' \<star>
      m3s_iospec_ord T' i 
      (case v of sInt1 cid op h \<Rightarrow> 
    s\<lparr>
      s_live := {sid' . sid' \<ge> i \<and> sid' \<in> s_live s},
      s_csibuf := (s_csibuf s)(cid := tl (s_csibuf s cid)),
      s_ssobuf := 
        (\<lambda> rcv . (if rcv > i \<and> rcv \<in> s_live s
                  then (s_ssobuf s rcv) @ [m1_Sync_req op h] else s_ssobuf s rcv)),
      s_pend := h,
      s_uopcid := (s_uopcid s)(op := Some cid)
      \<rparr>)))
    else Bool True)"

abbreviation m3p_res where
  "m3p_res T i s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if case v of sInt1 cid op h \<Rightarrow> 
          i \<in> s_live s \<and> collect_res2 s i op h \<and> s_uopcid s op = Some cid
        | _ \<Rightarrow> False
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio (IN B2_P_res) T v X T' \<star>
      m3s_iospec_ord T' i 
      (case v of sInt1 cid op h \<Rightarrow> 
    s\<lparr>
      s_scobuf := (s_scobuf s)(cid := s_scobuf s cid @ [m1_Upd_res op h]),
      s_ssibuf := (\<lambda> a . (if a \<in> s_live s \<and> a \<noteq> i then 
          tl (s_ssibuf s a) else (s_ssibuf s a))),
      s_hist := (\<lambda>sid' . if sid' \<in> s_live s then h else s_hist s sid')
      \<rparr>)))
    else Bool True)"

abbreviation m3b_sync where
  "m3b_sync T i s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if case v of sInt2 pri op h \<Rightarrow> 
          i \<in> s_live s \<and> pri \<in> s_live s \<and> is_head (m1_Sync_req op h) (s_ssibuf s pri)
        | _ \<Rightarrow> False
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio (IN B2_B_sync) T v X T' \<star>
      m3s_iospec_ord T' i 
      (case v of sInt2 pri op h \<Rightarrow> 
    s\<lparr>
      s_live := {sid' . sid' \<ge> pri \<and> sid' \<in> s_live s},
      s_hist := (s_hist s)(pri := h, i := h),
      s_ssibuf := (s_ssibuf s)(pri := tl (s_ssibuf s pri)),
      s_ssobuf := (s_ssobuf s)(pri := s_ssobuf s pri @ [m1_Sync_res op h]),
      s_pend := h
      \<rparr>)))
    else Bool True)"

abbreviation m3s_purge where
  "m3s_purge T i s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if case v of sInt3 sid \<Rightarrow> 
          \<exists> m . is_head m (s_ssibuf s sid)
        | _ \<Rightarrow> False
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio (IN B2_S_purge) T v X T' \<star>
      m3s_iospec_ord T' i 
      (case v of sInt3 sid \<Rightarrow> s_ssibuf_rm s sid)))
    else Bool True)"

abbreviation m3s_detect_failure where
  "m3s_detect_failure T i s \<equiv>  \<forall>\<^sup>\<star> (\<lambda>v. 
    if case v of sInt3 sid \<Rightarrow> True | _ \<Rightarrow> False
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio (IO B2_S_Detect_failure) T v X T' \<star>
      m3s_iospec_ord T' i 
      (case v of sInt3 sid \<Rightarrow> s\<lparr> s_live := (s_live s) - {sid}\<rparr> )))
    else Bool True)"

abbreviation m3s_send where
  "m3s_send T i s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if case v of sUpdate adr m \<Rightarrow> (case (inv addr) adr of Client cid \<Rightarrow> 
              is_head m (s_scobuf s cid) | _ \<Rightarrow> False)
            | sSync adr m \<Rightarrow> (case (inv addr) adr of Server sid \<Rightarrow> is_head m (s_ssobuf s sid) | _ \<Rightarrow> False)
            | _ \<Rightarrow> False
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio (IO B2_S_Send) T v X T' \<star>
      m3s_iospec_ord T' i 
      (case v of sUpdate adr m \<Rightarrow> (case (inv addr) adr of Client cid \<Rightarrow> s_scobuf_rm s cid)
            | sSync adr m \<Rightarrow> (case (inv addr) adr of Server sid \<Rightarrow> s_ssobuf_rm s sid))))
    else Bool True)"

abbreviation m3s_receive where
  "m3s_receive T i s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if v = sUnit
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio (IO B2_S_Recv) T v X T' \<star>
      m3s_iospec_ord T' i 
      (case X of sUpdate adr m \<Rightarrow> (case (inv addr) adr of Client cid \<Rightarrow> 
                s\<lparr>s_csibuf := (s_csibuf s)(cid := s_csibuf s cid @ [m])\<rparr>)
            | sSync adr m \<Rightarrow> (case (inv addr) adr of Server sid \<Rightarrow> 
                (if sid \<in> s_live s then 
                  s\<lparr>s_ssibuf := (s_ssibuf s)(sid := s_ssibuf s sid @ [m])\<rparr>
                 else s)))))
    else Bool True)"

abbreviation m3s_skip where
  "m3s_skip T i s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if True
    then ExT (\<lambda>T'. ExV (\<lambda>X. CBio Skip T v X T' \<star> m3s_iospec_ord T' i s))
    else Bool True)"

abbreviation m3s_stop where
  "m3s_stop T i s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if False
    then ExT (\<lambda>T'. ExV (\<lambda>X. CBio Stop T v X T' \<star> m3s_iospec_ord T' i s))
    else Bool True)"

lemma m3s_iospec_ord:
  "m3s_iospec_ord T i s = 
     m3p_req T i s \<star>
    (m3p_res T i s \<star>
    (m3b_sync T i s \<star>
    (m3s_purge T i s \<star>
    (m3s_detect_failure T i s \<star>
    (m3s_send T i s \<star>
    (m3s_receive T i s \<star>
    (m3s_skip T i s \<star> 
    (m3s_stop T i s \<star> 
    Bool True))))))))"

  \<comment> \<open>Note first method works on LHS only\<close>
  by(simp add: m3s_iospec_ord_def[where T=T] m3s_proc_ord_defs lPr.code[where s="s"])
    (auto simp add: m3s_iospec_ord_def m3s_proc_ord_defs m2s_trans_defs iospec_simps live2_geq_def remove_def)


text \<open>Correctness of the unfolding of the I/O spec.\<close>

abbreviation server_iospec_traces where
  "server_iospec_traces i \<equiv> server.traces_assn (ExT (\<lambda>t. CTok t \<star> m3s_iospec_ord t i m2s_init))"

lemma m3s_IOGES_trace_equiv_iospec:
    "server_iospec_traces i = traces (m2s_fES_base i)"
  by(simp add: m2s_fES_base_def m2s_ioges_trace_equiv_iospec_m3s[symmetric] m3s_iospec_ord_def 
               m3s_iospec_def server.trace_equivalences[symmetric] m3s_proc_opsem_equiv_m3s_proc_ord)

lemma m3s_IOGES_trace_equiv_iospec_\<beta>:
  "server_iospec_traces i \<lceil>\<beta>\<rceil> = traces (m2s_fES i)"
  by(simp add: m2s_fES_def traces_relabel_eq m3s_IOGES_trace_equiv_iospec)

end \<comment> \<open>context server\<close>


(******************************************************************************)
subsection \<open>Property preservation\<close>
(******************************************************************************)

context loc2 begin
definition traces_m3sys' where
  "traces_m3sys' = ((\<parallel>\<parallel> (\<lambda>i. client_iospec_traces i \<lceil>\<rho>\<rceil>)) || (\<parallel>\<parallel> (\<lambda>i. server_iospec_traces i \<lceil>\<beta>\<rceil>)))"

lemma traces_m3sys'_m2_sys'[simp]: "traces_m3sys' = traces m2sys'"
  by (auto simp add: traces_m3sys'_def m2c_def m2s_def m3s_IOGES_trace_equiv_iospec_\<beta> 
        m3c_IOGES_trace_equiv_iospec_\<rho> binterleave_composition interleaving_composition 
        traces_relabel_eq comp_def)

definition traces_m3sys where
  "traces_m3sys = (\<lambda>\<tau> . map ievt_comb \<tau>) ` traces_m3sys'"

definition traces_m3 where
  "traces_m3 = traces m2e \<parallel>\<chi> traces_m3sys"

lemma traces_m3_m2: "traces_m3 = traces m2"
proof-
  have m2_some_skip[intro]: "\<And>s . m2s: s\<midarrow>(SOME i. True, Skip)\<rightarrow> s" "\<And>c . m2c: c\<midarrow>(SOME i. True, Skip)\<rightarrow> c"
    by (fastforce simp add: m2_defs)+
  have traces_m3sys_simp: "traces_m3sys = traces (ievent_dist m2sys')" 
    apply(auto simp add: traces_m3sys_def traces_def image_def intro!: equalityI)
    subgoal by(drule ES_ievent_comb, auto simp add: m2_defs)
    by(drule ES_ievent_dist, fastforce simp add: m2_defs, auto intro!: exI simp add: ievent_dist_def)
  show ?thesis
    by(auto simp add: traces_m3_def m2_def trace_composition traces_m3sys_simp)
qed

lemma m3_backup_consistency: "traces_m3 \<subseteq> Collect backup_consistent"
  using m2_backup_consistency by(auto simp add: traces_m3_m2)

text \<open>Quod erat demonstrandum. This concludes our Primary-Backup case study.\<close> 

end
end
