(*
  Title:  Interleaving composition of a family of event systems
  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
           Tobias Klenze (tobias.klenze@inf.ethz.ch)
  Version: Isabelle/HOL 2020
  Date:    2019-2020
  ID:      $Id: Interleaving.thy 152662 2020-08-06 09:54:41Z tklenze $
*)

section \<open>Interleaving Composition\<close> 

theory Interleaving
  imports 
    Event_Systems 
    "HOL-Library.Adhoc_Overloading"
begin

consts 
  INTERLEAVE :: "'a \<Rightarrow> 'b"  ("\<parallel>\<parallel>")
  BINTERLEAVE :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"  (infixr "||" 60)


(********************************************************************************)
subsection \<open>Binary interleaving composition\<close> 
(********************************************************************************)

subsubsection \<open>Binary interleaving of event systems\<close> 
(********************************************************************************)

definition binterleave_ES :: "('e, 's) ES \<Rightarrow> ('f, 't) ES \<Rightarrow> ('e + 'f, 's \<times> 't) ES" where
  "binterleave_ES E F \<equiv> \<lparr>
    init = \<lambda>(s, t). init E s \<and> init F t,
    trans = \<lambda>(s, t). \<lambda>g. \<lambda>(s', t').
      (\<exists>e. g = Inl e \<and> (E: s \<midarrow>e\<rightarrow> s') \<and> t = t') \<or> 
      (\<exists>f. g = Inr f \<and> (F: t \<midarrow>f\<rightarrow> t') \<and> s = s')
  \<rparr>"

adhoc_overloading BINTERLEAVE binterleave_ES

lemma binterleave_ES_init [simp]: 
  "init (E || F) = (\<lambda>(s, t). init E s \<and> init F t)"
  by (simp add: binterleave_ES_def)

lemma binterleave_E_trans [simp]: 
  "trans (E || F) = (\<lambda>(s, t) g (s', t'). 
    (\<exists>e. g = Inl e \<and> (E: s \<midarrow>e\<rightarrow> s') \<and> t = t') \<or> 
    (\<exists>f. g = Inr f \<and> (F: t \<midarrow>f\<rightarrow> t') \<and> s = s'))"
  by (simp add: binterleave_ES_def)


subsubsection \<open>Binary interleaving of traces and trace properties\<close> 
(********************************************************************************)

inductive 
  binterl :: "'e trace \<Rightarrow> 'f trace \<Rightarrow> ('e + 'f) trace \<Rightarrow> bool" 
where
  binterl_nil [simp, intro!]:  "binterl [] [] []"
| binterl_left_snoc [intro]: 
    "\<lbrakk> binterl \<tau>\<^sub>1 \<tau>\<^sub>2 \<tau>; \<tau>\<^sub>1' = \<tau>\<^sub>1 @ [e]; \<tau>' = \<tau> @ [Inl e] \<rbrakk> \<Longrightarrow> binterl \<tau>\<^sub>1' \<tau>\<^sub>2 \<tau>'"
| binterl_right_snoc [intro]: 
    "\<lbrakk> binterl \<tau>\<^sub>1 \<tau>\<^sub>2 \<tau>; \<tau>\<^sub>2' = \<tau>\<^sub>2 @ [f]; \<tau>' = \<tau> @ [Inr f] \<rbrakk> \<Longrightarrow> binterl \<tau>\<^sub>1 \<tau>\<^sub>2' \<tau>'"

definition binterleave_ts :: "'e trace set \<Rightarrow> 'f trace set \<Rightarrow> (('e + 'f) trace set)" where
  "binterleave_ts ts1 ts2 = {\<tau>. \<exists>\<tau>\<^sub>1 \<tau>\<^sub>2. \<tau>\<^sub>1 \<in> ts1 \<and> \<tau>\<^sub>2 \<in> ts2 \<and> binterl \<tau>\<^sub>1 \<tau>\<^sub>2 \<tau>}"

adhoc_overloading BINTERLEAVE binterleave_ts


subsubsection \<open>Composition theorem for binary interleaving \<close>
(********************************************************************************)

lemma binterleave_trace_decomp:
  "((E || F): (s, t) \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> (s', t')) \<longleftrightarrow> 
   (\<exists>\<tau>\<^sub>1 \<tau>\<^sub>2. (E: s \<midarrow>\<langle>\<tau>\<^sub>1\<rangle>\<rightarrow> s') \<and> (F: t \<midarrow>\<langle>\<tau>\<^sub>2\<rangle>\<rightarrow> t') \<and> binterl \<tau>\<^sub>1 \<tau>\<^sub>2 \<tau>)"  (is "?A \<longleftrightarrow> ?B")
proof 
  assume "?A"
  then show "?B"
  proof (induction \<tau> "(s', t')" arbitrary: s' t' rule: trace.induct)
    case trace_nil
    then show ?case by auto
  next
    case (trace_snoc \<tau> u g)
    then show ?case 
      by (atomize) (auto split: prod.splits)    \<comment> \<open>would need one-point rule in Pure...\<close>
  qed
next
  assume "?B"
  then obtain \<tau>\<^sub>1 \<tau>\<^sub>2 where 
     il: "binterl \<tau>\<^sub>1 \<tau>\<^sub>2 \<tau>" and 
     tr: "E: s \<midarrow>\<langle>\<tau>\<^sub>1\<rangle>\<rightarrow> s'" "F: t \<midarrow>\<langle>\<tau>\<^sub>2\<rangle>\<rightarrow> t'"  
    by blast
  then show "?A"
    by (induction \<tau>\<^sub>1 \<tau>\<^sub>2 \<tau> arbitrary: s' t' rule: binterl.induct) 
       (fastforce)+
qed

theorem binterleave_composition: "traces (E || F) = traces (E) || traces(F)" 
  by (fastforce simp add: traces_def binterleave_ts_def binterleave_trace_decomp)


(********************************************************************************)
subsection \<open>Indexed Interleaving Composition of Event System Families\<close> 
(********************************************************************************)

subsubsection \<open>Indexed interleaving of event system families\<close>
(********************************************************************************)

type_synonym ('e, 'l, 'i) fES = "'i \<Rightarrow> ('e, 'l) ES"

definition interleave_fES :: "('e, 'l, 'i) fES \<Rightarrow> ('i \<times> 'e, 'i \<Rightarrow> 'l) ES" where
  "interleave_fES fes \<equiv> \<lparr>
    init = \<lambda>s. (\<forall>i. init (fes i) (s i)),
    trans = \<lambda>s. \<lambda>(i, e). \<lambda>s'.
      (fes i: s i \<midarrow>e\<rightarrow> s' i) \<and> (\<forall>i' . i' \<noteq> i \<longrightarrow> s' i' = s i')
  \<rparr>"

adhoc_overloading INTERLEAVE interleave_fES

lemma interleave_fES_init [simp]: 
  "init (\<parallel>\<parallel> fes) = (\<lambda>s. (\<forall>i. init (fes i) (s i)))"
  by (simp add: interleave_fES_def)

lemma interleave_fES [simp]: 
  "trans (\<parallel>\<parallel> fes) = (\<lambda>s. \<lambda>(i, e). \<lambda>s'. 
    (fes i: s i \<midarrow>e\<rightarrow> s' i) \<and> (\<forall>i' . i' \<noteq> i \<longrightarrow> s' i' = s i'))"
  by (simp add: interleave_fES_def)


subsubsection \<open>Indexed interleaving of traces and trace properties\<close> 
(********************************************************************************)

inductive 
  interl :: "('i \<Rightarrow> 'e trace) \<Rightarrow> ('i \<times> 'e) trace \<Rightarrow> bool" 
where
  interl_nil [simp, intro!]:  "interl (\<lambda>_. []) []"
| interl_snoc [intro]: 
    "\<lbrakk> interl tf \<tau>; tf' = tf(i := tf i @ [e]); \<tau>' = \<tau> @ [(i, e)] \<rbrakk> \<Longrightarrow> interl tf' \<tau>'"

definition interleave_tsf :: "('i \<Rightarrow> 'e trace set) \<Rightarrow> (('i \<times> 'e) trace set)" where
  "interleave_tsf tsf = { \<tau> | \<tau> tf. \<forall>i. tf i \<in> tsf i \<and> interl tf \<tau>}"

adhoc_overloading INTERLEAVE interleave_tsf


subsubsection \<open>Composition theorem for indexed interleaving\<close>
(********************************************************************************)

lemma interleave_trace_decomp: 
  "(\<parallel>\<parallel> fes: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s') \<longleftrightarrow> (\<exists>tf. (\<forall>i. fes i: s i \<midarrow>\<langle>tf i\<rangle>\<rightarrow> s' i) \<and> interl tf \<tau>)"  (is "?A \<longleftrightarrow> ?B")
proof (intro iffI)
  assume "?A"
  then show "?B"
  proof (induction \<tau> s' rule: trace.induct)
    case trace_nil
    then show ?case by auto
  next
    case (trace_snoc \<tau> s' e s'')
    obtain j f where e: "e = (j, f)" by fastforce
    with trace_snoc(2) have *: "fes j: s' j \<midarrow>f\<rightarrow> s'' j" "\<forall>i' . i' \<noteq> j \<longrightarrow> s'' i' = s' i'"
      by (auto)
    from trace_snoc(3) obtain tf where "\<forall>i. fes i: s i \<midarrow>\<langle>tf i\<rangle>\<rightarrow> s' i" and "interl tf \<tau>" by blast
    then show ?case using trace_snoc(1) e *
      by (fastforce intro: exI[of _ "tf(j := tf j @ [f])"])
  qed
next
  assume "?B"
  then obtain tf where "interl tf \<tau>" and "\<forall>i. fes i: s i \<midarrow>\<langle>tf i\<rangle>\<rightarrow> s' i" by blast
  then show "?A"
  proof (induction tf \<tau> arbitrary: s' rule: interl.induct)
    case interl_nil
    then have "s' = s" by auto
    then show ?case by (auto) 
  next
    case (interl_snoc tf \<tau> tf' j e \<tau>')
    from interl_snoc.prems have "fes j: s j \<midarrow>\<langle>tf' j\<rangle>\<rightarrow> s' j" by (fastforce)
    with interl_snoc(2) have "fes j: s j \<midarrow>\<langle>tf j @ [e]\<rangle>\<rightarrow> s' j" by auto
    then obtain sj'' where "fes j: s j \<midarrow>\<langle>tf j\<rangle>\<rightarrow> sj''" and "fes j: sj'' \<midarrow>e\<rightarrow> s' j" by auto
    from interl_snoc.prems have "\<forall>i. i \<noteq> j \<longrightarrow> fes i: s i \<midarrow>\<langle>tf' i\<rangle>\<rightarrow> s' i" by (fastforce)
    with interl_snoc(2) have "\<forall>i. i \<noteq> j \<longrightarrow> fes i: s i \<midarrow>\<langle>tf i\<rangle>\<rightarrow> s' i" by auto
    with \<open>fes j: s j \<midarrow>\<langle>tf j\<rangle>\<rightarrow> sj''\<close> 
    have tau: "interleave_fES fes: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'(j := sj'')" using interl_snoc.IH by auto
    have "interleave_fES fes: s'(j := sj'') \<midarrow>(j, e)\<rightarrow> s'" using \<open>fes j: sj'' \<midarrow>e\<rightarrow> s' j\<close> by auto
    then show ?case using tau \<open>\<tau>' = \<tau> @ [(j, e)]\<close> by auto
  qed
qed

thm choice

theorem interleaving_composition: 
  "traces (\<parallel>\<parallel> fes) = \<parallel>\<parallel> (traces o fes)" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
    by (fastforce simp add: traces_def interleave_tsf_def interleave_trace_decomp)
next
  show "?B \<subseteq> ?A"
    by (auto 4 5 simp add: traces_def interleave_tsf_def interleave_trace_decomp all_conj_distrib 
                 dest!: choice)
qed


text \<open>The following lemma is useful in decomposition proofs.\<close>

lemma fun_point_equiv [dest]: "\<lbrakk>\<forall>j. j \<noteq> i \<longrightarrow> s j = s' j; s i = s' i\<rbrakk> \<Longrightarrow> s = s'"
  by auto


end