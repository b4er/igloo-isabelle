(*******************************************************************************

  Igloo Case Study: One-Way authentication protocols

  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
  Version: Isabelle/HOL 2020
  Date:    2019
  ID:      $Id: m6_sig.thy 152662 2020-08-06 09:54:41Z tklenze $
  
*******************************************************************************)

section \<open>Refinement 6: Derivation of the Protocol Roles' I/O Specification\<close>

theory m6_sig
  imports 
    m5_sig
    "../../Event_Systems_into_IO_Processes"
    "../../IO_Processes_into_IO_Separation_Logic"
    "../../IO_Behavior"
begin

text \<open>Set up some useful simplification and congruence rules for simplifying the 
translation of event systems into I/O specs.\<close>

lemma ival_case_const: 
  "(case ival of iv_Unit \<Rightarrow> c | iv_M1 _ _ \<Rightarrow> c | iv_M2 _ _ _ \<Rightarrow> c | iv_IO _ _ \<Rightarrow> c) = c"
  by (simp split: ival.splits)

lemma rval_case_const:
  "(case rval of rv_Unit \<Rightarrow> c | rv_Int _ _ _ _ _ \<Rightarrow> c | rv_IO _ _ \<Rightarrow> c) = c"
  by (simp split: rval.splits)

lemma ival_case_distribR: 
  "(case ival of iv_Unit \<Rightarrow> f1 | iv_M1 x1 x2 \<Rightarrow> f2 x1 x2 | iv_M2 x1 x2 x3 \<Rightarrow> f3 x1 x2 x3 | iv_IO x1 x2 \<Rightarrow> f4 x1 x2) z =
   (case ival of iv_Unit \<Rightarrow> f1 z | iv_M1 x1 x2 \<Rightarrow> f2 x1 x2 z | iv_M2 x1 x2 x3 \<Rightarrow> f3 x1 x2 x3 z | iv_IO x1 x2 \<Rightarrow> f4 x1 x2 z)"
  by (simp split: ival.splits)

lemma rval_case_distribR:
  "(case rval of rv_Unit \<Rightarrow> f1 | rv_Int x1 x2 x3 x4 x5 \<Rightarrow> f2 x1 x2 x3 x4 x5 | rv_IO x1 x2 \<Rightarrow> f3 x1 x2) z =
   (case rval of rv_Unit \<Rightarrow> f1 z | rv_Int x1 x2 x3 x4 x5 \<Rightarrow> f2 x1 x2 x3 x4 x5 z | rv_IO x1 x2 \<Rightarrow> f3 x1 x2 z)"
  by (simp split: rval.splits)

lemmas val_case_distrib_simps = 
  ival.case_distrib[where h=embedp] 
  ival.case_distrib[where h=guard] ival.case_distrib[where h=update] 
  ival_case_distribR ival_case_const
  rval.case_distrib[where h=embedp] 
  rval.case_distrib[where h=guard] rval.case_distrib[where h=update] 
  rval_case_distribR rval_case_const

lemmas if_distrib_simps = 
  if_distrib[where f=embedp] if_distrib[where f=guard] if_distrib[where f=update] 
  if_distribR 

lemmas iospec_simps =
  lBChoice.simps embedp_VChoice_is_AllStar 
  if_distrib_simps val_case_distrib_simps

lemmas iospec_congs [cong] = 
  arg_cong[where f="\<forall>\<^sup>\<star>"] if_cong ival.case_cong rval.case_cong 

declare if_split [split del]


(******************************************************************************)
subsection \<open>Initiator's I/O specification\<close>
(******************************************************************************)

context initiator begin

definition m6i_proc :: "('a, 'b) m5i_state \<Rightarrow> (bio5i, ('a, 'b) ival) process" where
  "m6i_proc s = pr m5i_ioges s"    

text \<open>Embedding of the process into I/O spec.\<close>

definition m6i_iospec :: "place \<Rightarrow> ('a, 'b) m5i_state \<Rightarrow> (bio5i, ('a, 'b) ival) cassn" where 
  "m6i_iospec t s = embedp (m6i_proc s) t"


text \<open>Correctness of the translation to the I/O spec.\<close>

lemma m5i_ioges_trace_equiv_iospec_m5i:
    "bio5i.traces_assn (ExT (\<lambda>t. CTok t \<star> m6i_iospec t s))
   = traces (bio5i.IOGES_to_ES m5i_ioges ((=) s))" (is "?L = ?R")
proof-
  have "?L = bio5i.traces_opsem (m6i_proc s)" 
    by(simp add: m6i_iospec_def bio5i.trace_equivalences)
  also have "... = ?R" 
    by (simp add: m6i_proc_def bio5i.emb_opsem_equiv)
  finally show ?thesis by simp
qed


subsubsection \<open>Unfolding of the I/O specification\<close>
(******************************************************************************)

definition bio5i_list :: "bio5i list" where
  "bio5i_list = [
     B_m5i_init_start, B_m5i_init_put_M1, B_m5i_init_get_M2, B_m5i_recv, B_m5i_send, B_m5i_skip
   ]"

lemma bio5i_list_UNIV: "set bio5i_list = (UNIV::bio5i set)" 
  by (auto simp add: bio5i_list_def intro: bio5i.exhaust)

text \<open>Here, including parameters.\<close>

definition m6i_proc_ord where
  "m6i_proc_ord s \<equiv> lPr bio5i_list m5i_ioges s"

lemmas m6i_proc_ord_defs = m6i_proc_ord_def bio5i_list_def

lemma m6i_proc_opsem_equiv_m6i_proc_ord: 
  "bio5i.traces_opsem (m6i_proc s) = bio5i.traces_opsem (m6i_proc_ord s)"
by (simp add: m6i_proc_def m6i_proc_ord_def bio5i.bisim_lPr_pr bio5i_list_UNIV)


text \<open>Redefine the I/O spec and prove a fixed point equation.\<close>

term "embedp (m6i_proc_ord s) T"

definition m6i_iospec_ord :: 
  "place \<Rightarrow> ('a, 'b) m5i_state \<Rightarrow> (bio5i, ('a, 'b) ival) cassn" 
where 
  "m6i_iospec_ord T s = embedp (m6i_proc_ord s) T"

lemmas m6i_iospec_ord_defs = m6i_iospec_ord_def m6i_proc_ord_defs


text \<open>Prove a fixed point equation. This form can be translated to the input language of 
a program verifier (Nagini, VeriFast).\<close>

abbreviation m6i_init_start where
  "m6i_init_start T s \<equiv>  \<forall>\<^sup>\<star> (\<lambda>v. 
    if s = None \<and> v = iv_Unit
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio B_m5i_init_start T iv_Unit X T' \<star>
      m6i_iospec_ord T' (Some \<lparr>agts = [A, B], store = [], ibuf = {}, obuf = None\<rparr>)))
    else Bool True)"

abbreviation m6i_init_put_M1 where
  "m6i_init_put_M1 T s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if case v of
        iv_M1 bs Na \<Rightarrow> (\<exists>ib. s = Some \<lparr>agts = [A, B], store = [], ibuf = ib, obuf = None\<rparr>) \<and> 
                          Na = #[Init,Ra,0] \<and> \<lbrace> Agent A, Agent B, Nonce Na \<rbrace> = \<alpha> bs
      | _ \<Rightarrow> False
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio B_m5i_init_put_M1 T v X T' \<star>
      m6i_iospec_ord T' 
        (case v of iv_M1 bs Na \<Rightarrow> Some (the s\<lparr>obuf := Some bs \<rparr>) | _ \<Rightarrow> s))) 
    else Bool True)"

abbreviation m6i_init_get_M2 where
  "m6i_init_get_M2 T s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if case v of
      iv_M2 bs Na Nb \<Rightarrow> 
        (\<exists>ib ob ad. 
          s = Some \<lparr>agts = [A, B], store = [], ibuf = ib, obuf = ob\<rparr> \<and>
          (ad, bs) \<in> ib \<and> Crypt (priK B) \<lbrace>Nonce Nb, Nonce Na, Agent A\<rbrace> = \<alpha> bs) \<and> 
        Na = #[Init,Ra,0]
      | _ \<Rightarrow> False
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio B_m5i_init_get_M2 T v X T' \<star>
      m6i_iospec_ord T'
        (case v of iv_M2 bs Na Nb \<Rightarrow> Some (obuf_update Map.empty (the s\<lparr>store := [aNon Nb]\<rparr>)) | _ \<Rightarrow> s)))
    else Bool True)"

abbreviation m6i_recv where
  "m6i_recv T s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if (s \<noteq> None) \<and> v = iv_Unit
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio B_m5i_recv T iv_Unit X T' \<star>
      m6i_iospec_ord T'
        (case X of iv_IO ad bs \<Rightarrow> Some (the s\<lparr>ibuf := insert (ad, bs) (ibuf (the s))\<rparr>) | _ \<Rightarrow> s)))
    else Bool True)"

abbreviation m6i_send where
  "m6i_send T s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if case v of iv_IO x1 x2 \<Rightarrow> (\<exists>y. s = Some y) \<and> obuf (the s) = Some x2 \<and> x1 = addrB | _ \<Rightarrow> False
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio B_m5i_send T v X T' \<star> m6i_iospec_ord T' s))
    else Bool True)"

abbreviation m6i_skip where
  "m6i_skip T s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. ExT (\<lambda>T'. ExV (\<lambda>X. 
     CBio B_m5i_skip T v X T' \<star> m6i_iospec_ord T' s)))"

lemma m6i_iospec_ord:
  "m6i_iospec_ord T s = 
     m6i_init_start T s \<star>
    (m6i_init_put_M1 T s \<star>
    (m6i_init_get_M2 T s \<star>
    (m6i_recv T s \<star>
    (m6i_send T s \<star>
    (m6i_skip T s \<star> 
    Bool True)))))"

  \<comment> \<open>Note first method works on LHS only\<close>
  by (simp add: m6i_iospec_ord_def[where T=T] m6i_proc_ord_defs lPr.code[where s="s"])
     (auto simp add: m6i_iospec_ord_def m6i_proc_ord_defs m5i_trans_defs iospec_simps)
  

text \<open>This lemma proves the equivalence between the original, unordered IO-spec, and the unfolded,
      ordered IO-spec.\<close>

lemma translation_iospec_m6i:
  "bio5i.traces_assn (ExT (\<lambda>T. CTok T \<star> m6i_iospec T s)) = 
   bio5i.traces_assn (ExT (\<lambda>T. CTok T \<star> m6i_iospec_ord T s))"
  by (auto simp add: m6i_iospec_def m6i_iospec_ord_def m6i_proc_ord_def 
                     m6i_proc_opsem_equiv_m6i_proc_ord
           intro: bio5i.traces_assn_embedI del: equalityI)

text \<open>Correctness of the unfolding of the I/O spec.\<close>

abbreviation initiator_iospec_traces where
  "initiator_iospec_traces \<equiv> bio5i.traces_assn (ExT (\<lambda>t. CTok t \<star> m6i_iospec_ord t None))"

lemma m6i_IOGES_trace_equiv_iospec:
    "initiator_iospec_traces = traces m5i_base"
  by(simp add: m5i_init_def m5i_ioges_trace_equiv_iospec_m5i[symmetric] m6i_iospec_ord_def 
               m6i_iospec_def bio5i.trace_equivalences[symmetric] m6i_proc_opsem_equiv_m6i_proc_ord)

lemma m6i_IOGES_trace_equiv_iospec_\<rho>:
  "initiator_iospec_traces \<lceil>\<rho>\<rceil> = traces m5i"
  by(simp add: m5i_def traces_relabel_eq m6i_IOGES_trace_equiv_iospec)


end \<comment> \<open>context initiator\<close>

thm initiator.m6i_iospec_ord


(******************************************************************************)
subsection \<open>Responder's I/O specification\<close>
(******************************************************************************)

context responder begin

definition m6r_proc :: "('a, 'b) m5r_state \<Rightarrow> (bio5r, ('a::countable, 'b) rval) process" where
  "m6r_proc s = pr m5r_ioges s" 

text \<open>Embedding of the process into I/O spec.\<close>

definition m6r_iospec :: "place \<Rightarrow> ('a, 'b) m5r_state \<Rightarrow> (bio5r, ('a::countable, 'b) rval) cassn" where 
  "m6r_iospec t s = embedp (m6r_proc s) t"


text \<open>Correctness of the translation to the I/O spec.\<close>

lemma m5r_ioges_trace_equiv_iospec_m6r:
    "bio5r.traces_assn (ExT (\<lambda>t. CTok t \<star> m6r_iospec t s))
   = traces (bio5r.IOGES_to_ES m5r_ioges ((=) s))" (is "?L = ?R")
proof-
  have "?L = bio5r.traces_opsem (m6r_proc s)" 
    by(simp add: m6r_iospec_def bio5r.trace_equivalences)
  also have "... = ?R" 
    by (simp add: m6r_proc_def bio5r.emb_opsem_equiv)
  finally show ?thesis by simp
qed


subsubsection \<open>Unfolding of the I/O specification\<close>
(******************************************************************************)

definition bio5r_list :: "bio5r list" where
  "bio5r_list = [
     B_m5r_resp_start, B_m5r_resp_get_M1, B_m5r_resp_put_M2, B_m5r_recv, B_m5r_send, B_m5r_skip
   ]"

lemma bio5r_list_UNIV: "set bio5r_list = (UNIV::bio5r set)" 
  by (auto simp add: bio5r_list_def intro: bio5r.exhaust)

text \<open>Here, including parameters.\<close>

definition m6r_proc_ord where
  "m6r_proc_ord s \<equiv> lPr bio5r_list m5r_ioges s"

lemmas m6r_proc_ord_defs = m6r_proc_ord_def bio5r_list_def

lemma m6r_proc_opsem_equiv_m6r_proc_ord: 
  "bio5r.traces_opsem (m6r_proc s) = bio5r.traces_opsem (m6r_proc_ord s)"
by (simp add: m6r_proc_def m6r_proc_ord_def bio5r.bisim_lPr_pr bio5r_list_UNIV)


text \<open>Redefine the I/O spec and prove a fixed point equation.\<close>

definition m6r_iospec_ord :: 
  "place \<Rightarrow> ('a, 'b) m5r_state \<Rightarrow> (bio5r, ('a::countable, 'b) rval) cassn" 
where 
  "m6r_iospec_ord T s = embedp (m6r_proc_ord s) T"

lemmas m6r_iospec_ord_defs = m6r_iospec_ord_def m6r_proc_ord_defs


text \<open>Prove a fixed point equation. This form can be translated to the input language of 
a program verifier (Nagini, VeriFast).\<close>

abbreviation m6r_resp_start where
  "m6r_resp_start T s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if s = None \<and> v = rv_Unit
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio B_m5r_resp_start T rv_Unit X T' \<star>
      m6r_iospec_ord T' (Some \<lparr>agts = [B], store = [], ibuf = {}, obuf = None, addrA = None\<rparr>)))
    else Bool True)"

abbreviation m6r_resp_get_M1 where
  "m6r_resp_get_M1 T s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v.
    if case v of
      rv_Int ad bs A Nb Na \<Rightarrow>
        (\<exists>ob ib. s = Some \<lparr>agts = [B], store = [], ibuf = ib, obuf = ob, addrA = None\<rparr> \<and>
                 (ad, bs) \<in> ib \<and> \<lbrace>Agent A, Agent B, Nonce Na\<rbrace> = \<alpha> bs) \<and> 
        Nb = #[Resp,Rb,0]
      | _ \<Rightarrow> False
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio B_m5r_resp_get_M1 T v X T' \<star>
      m6r_iospec_ord T'
        (case v of
          rv_Int ad bs A Nb Na \<Rightarrow>
            Some (the s\<lparr>agts := [B, A], store := [aNon Na], obuf := None, addrA := Some ad\<rparr>)
          | _ \<Rightarrow> s)))
    else Bool True)"

abbreviation m6r_resp_put_M2 where
  "m6r_resp_put_M2 T s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v.
    if case v of
      rv_Int ad bs A Nb Na \<Rightarrow> 
        (\<exists>ib. s = Some \<lparr>agts = [B, A], store = [aNon Na], ibuf = ib, obuf = None, addrA = Some ad\<rparr>) \<and> 
              Nb = #[Resp,Rb,0] \<and> Crypt (priK B) \<lbrace>Nonce Nb, Nonce Na, Agent A\<rbrace> = \<alpha> bs
      | _ \<Rightarrow> False
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio B_m5r_resp_put_M2 T v X T' \<star>
      m6r_iospec_ord T'
        (case v of
          rv_Int ad bs A Nb Na \<Rightarrow>
            Some (the s\<lparr>obuf := Some bs\<rparr>)
          | _ \<Rightarrow> s)))
    else Bool True)"

abbreviation m6r_recv where
  "m6r_recv T s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if (\<exists>y. s = Some y) \<and> v = rv_Unit
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio B_m5r_recv T rv_Unit X T' \<star>
      m6r_iospec_ord T' 
        (case X of rv_IO ad bs \<Rightarrow> Some (the s\<lparr>ibuf := insert (ad, bs) (ibuf (the s))\<rparr>) | _ \<Rightarrow> s)))
    else Bool True)"

abbreviation m6r_send where
  "m6r_send T s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. 
    if case v of 
         rv_IO ad bs \<Rightarrow> s \<noteq> None \<and> addrA (the s) = Some ad \<and> obuf (the s) = Some bs | _ \<Rightarrow> False
    then ExT (\<lambda>T'. ExV (\<lambda>X. 
      CBio B_m5r_send T v X T' \<star> m6r_iospec_ord T' s))
    else Bool True)"

abbreviation m6r_skip where
  "m6r_skip T s \<equiv> \<forall>\<^sup>\<star> (\<lambda>v. ExT (\<lambda>T'. ExV (\<lambda>X. 
    CBio B_m5r_skip T v X T' \<star> m6r_iospec_ord T' s)))"

lemma m6r_iospec_ord:
  "m6r_iospec_ord T s = 
     m6r_resp_start T s \<star>
    (m6r_resp_get_M1 T s \<star>
    (m6r_resp_put_M2 T s \<star>
    (m6r_recv T s \<star>
    (m6r_send T s \<star>
    (m6r_skip T s \<star> 
    Bool True)))))"

  \<comment> \<open>Note first method works on LHS only\<close>
  by (simp add: m6r_iospec_ord_def[where T=T] m6r_proc_ord_defs lPr.code[where s="s"])
     (auto simp add: m6r_iospec_ord_def m6r_proc_ord_defs m5r_trans_defs iospec_simps)

text \<open>Correctness of the unfolding of the I/O spec.\<close>

abbreviation responder_iospec_traces where
  "responder_iospec_traces \<equiv> bio5r.traces_assn (ExT (\<lambda>t. CTok t \<star> m6r_iospec_ord t None))"

lemma m6r_IOGES_trace_equiv_iospec:
    "responder_iospec_traces = traces m5r_base"
  by(simp add: m5r_init_def m5r_ioges_trace_equiv_iospec_m6r[symmetric] m6r_iospec_ord_def 
               m6r_iospec_def bio5r.trace_equivalences[symmetric] m6r_proc_opsem_equiv_m6r_proc_ord)

lemma m6r_IOGES_trace_equiv_iospec_\<beta>:
  "responder_iospec_traces \<lceil>\<beta>\<rceil> = traces m5r"
  by(simp add: m5r_def traces_relabel_eq m6r_IOGES_trace_equiv_iospec)


end \<comment> \<open>context responder\<close>


(******************************************************************************)
subsection \<open>Property preservation\<close>
(******************************************************************************)

context complete_system
begin
definition traces_m6s where 
  "traces_m6s \<equiv> (\<parallel>\<parallel> (\<lambda>i . (ini.initiator_iospec_traces i) \<lceil>\<rho>\<rceil>)) || (\<parallel>\<parallel> (\<lambda>i . (rsp.responder_iospec_traces i) \<lceil>\<beta>\<rceil>))"

lemma traces_m6s_m5s: "traces_m6s = traces m5s"
  by(simp add: traces_m6s_def ini.m6i_IOGES_trace_equiv_iospec rsp.m6r_IOGES_trace_equiv_iospec 
      ini.m5i_def rsp.m5r_def binterleave_composition interleaving_composition traces_relabel_eq)

definition traces_m6 where 
  "traces_m6 \<equiv> (traces m5e) \<parallel>\<chi> (traces_m6s)"

lemma m5_equiv_m6: "traces_m6 = traces m5"
  by(simp add: traces_m6s_m5s traces_m6_def trace_composition)

corollary traces_m6_a0i: "map \<pi>\<^sub>1`map \<pi>\<^sub>2`map \<pi>\<^sub>4` traces_m6 \<subseteq> Collect a0i_inv3t_iagree" 
proof-
  have "map \<pi>\<^sub>1 ` traces m1 \<subseteq> Collect a0i_inv3t_iagree"
    using m1_trace_included_a0i a0i_inv2t_iagree trace_propertyE by auto 
  then show ?thesis
  apply(simp add: m4_equiv_m5[symmetric] m5_equiv_m6)
    using m2_trace_included_m1 m3_traced_included_m2 m4_traced_included_m3 
    by (meson order.trans subset_image_iff)
qed

text \<open>Quod erat demonstrandum. This concludes our Security case study.\<close> 

end
end