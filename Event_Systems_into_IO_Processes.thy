(*
  Title:   Embedding Event Systems into I/O Processes
  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
           Tobias Klenze (tobias.klenze@inf.ethz.ch)
  Version: Isabelle/HOL 2020
  Date:    2018-2020
  ID:      $Id: Event_Systems_into_IO_Processes.thy 152662 2020-08-06 09:54:41Z tklenze $
*)

section \<open>Embedding Event Systems into I/O Processes\<close>

theory Event_Systems_into_IO_Processes
  imports IO_Processes
begin

subsection \<open>(I/O-)guarded event systems (IOGES)\<close>
(*************************************************************************************************)

text \<open>First, we construct a special type of event that consist of a guard predicate (which can only
       read the state s, and the output v), and an update function (from state s, output v and
       input w to a successor state s1).\<close> 
text \<open>@{text "if G(s, v) then e(v).\<lambda>w.pr E (U s v w)"} where @{text e} is the label.\<close>

record ('s, 'v) gd_upd = 
  guard :: "bool"
  update :: "'v \<Rightarrow> 's"

type_synonym ('s, 'v) guarded_update = 
  "'s \<Rightarrow> 'v \<Rightarrow> ('s, 'v) gd_upd"

abbreviation gSkip :: "('s, 'v) guarded_update" where
  "gSkip s v \<equiv> \<lparr> guard = True, update = \<lambda>_. s \<rparr>"

abbreviation gNull :: "('s, 'v) guarded_update" where
  "gNull s v \<equiv> \<lparr> guard = False, update = \<lambda>_. s \<rparr>"


text \<open>An IOGES (I/O Guarded Event System) maps bio labels to guarded updates.\<close> 

type_synonym ('s, 'b, 'v) IOGES = "'b \<Rightarrow> ('s, 'v) guarded_update"


text \<open>Turns a family of guarded updates into a labelled transition relation 
@{text "state \<times> action \<times> state"}.\<close>

abbreviation (in Typing) 
  IOGES_trans :: "('s, 'b, 'v) IOGES \<Rightarrow> ('s \<Rightarrow> ('b, 'v) action \<Rightarrow> 's \<Rightarrow> bool)" where
  "IOGES_trans ges s e s1 \<equiv> \<exists>bio v w. guard (ges bio s v)  \<and> w \<in> Ty bio v \<and>
                                   s1 = update (ges bio s v) w \<and> e = ActBio bio v w"

text \<open>Turns a set of guarded updates with some given initial states into an event system.\<close>

definition (in Typing) 
  IOGES_to_ES :: "('s, 'b, 'v) IOGES \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> (('b, 'v) action, 's) ES" where
  "IOGES_to_ES GAs initial \<equiv> \<lparr>init = initial, trans = IOGES_trans GAs\<rparr>"

lemma (in Typing) IOGES_to_ES_init_single [simp]: "init (IOGES_to_ES E ((=) s)) t \<longleftrightarrow> t = s"
  by (auto simp add: IOGES_to_ES_def)

lemma (in Typing) IOGES_to_ES_trans: "trans (IOGES_to_ES GAs initial) = IOGES_trans GAs"
  by (simp add: IOGES_to_ES_def)

subsection \<open>Embdding (I/O-)GES into processes.\<close>
(*************************************************************************************************)

corec bPr :: "'b set \<Rightarrow> ('s, 'b::finite, 'v::countable) IOGES \<Rightarrow> 's \<Rightarrow> ('b, 'v) process" where
  "bPr B IOGES s = \<Oplus>\<^sup>b\<^sub>b\<^sub>i\<^sub>o B (\<lambda>bio. \<Oplus> (\<lambda>v. 
                if guard (IOGES bio s v) 
                then bio[v]. (\<lambda>w. bPr B IOGES (update (IOGES bio s v) w))
                else Null))"

definition pr :: "('s, 'b::finite, 'v::countable) IOGES \<Rightarrow> 's \<Rightarrow> ('b, 'v) process" where
  "pr \<equiv> bPr UNIV"

text \<open>We also define a trace-equivalent embedding that has a deterministic unfolding using lBChoice.\<close> 

corec lPr :: "'b list \<Rightarrow> ('s, 'b::finite, 'v::countable) IOGES \<Rightarrow> 's \<Rightarrow> ('b, 'v) process" where
  "lPr l IOGES s = \<Oplus>\<^sup>l\<^sub>b\<^sub>i\<^sub>o l (\<lambda>bio. \<Oplus> (\<lambda>v. 
                if guard (IOGES bio s v) 
                then bio[v]. (\<lambda>w. lPr l IOGES (update (IOGES bio s v) w))
                else Null))"

lemma lPr_Null[simp]: "lPr [] IOGES s = Null" by (simp add: lPr.code)
lemma bPr_Null[simp]: "bPr {} IOGES s = Null" by (simp add: bPr.code)


subsection \<open>Soundness of embedding @{text "bPr"}\<close>
(*************************************************************************************************)

text \<open>Main lemma is @{text "emb_soundness"}. Reverse inclusion shown in the next section,
       @{text "opsem_executability"}.\<close>  

text \<open>We prove something slightly stronger / more specific than needed for @{term "emb_soundness"}\<close>

lemma (in Typing) emb_soundness_step: 
  assumes "opsem (pr E t) (ActBio bio v w) P'" 
  shows "(IOGES_to_ES E ((=) s): t \<midarrow>ActBio bio v w\<rightarrow> (update (E bio t v) w)) 
        \<and> P' = pr E (update (E bio t v) w)"
  using assms
  by (auto simp add: pr_def bPr.code[of _ _ t] IOGES_to_ES_trans 
           dest!: opsem_bBChoice_invert opsem_bVChoice_invert split: if_split_asm)

text \<open>Soundness of the embedding. Notice that in I/O processes, we only have a single initial 
       state s, (unlike in our definition of event systems).\<close> 

lemma (in Typing) emb_soundness: "traces_opsem (pr E s) \<subseteq> traces (IOGES_to_ES E ((=) s))"
proof (rule simulation_rule_id[where R="\<lambda>s t. s = pr E t"])
  fix s1 t1 a s2
  assume "s1 = pr E t1" and "opsem_ES (pr E s): s1\<midarrow>a\<rightarrow> s2"
  moreover obtain bio v w where "a = ActBio bio v w" using \<open>opsem_ES (pr E s): s1\<midarrow>a\<rightarrow> s2\<close>
    by (fastforce simp add: IOGES_to_ES_trans dest!: opsem_bio_only)   (* auto does weird stuff *)
  ultimately show "\<exists>t2. (IOGES_to_ES E ((=) s): t1\<midarrow>a\<rightarrow> t2) \<and> s2 = pr E t2"
    by (auto dest: emb_soundness_step)
qed simp


subsection \<open>Executability (reverse direction of @{text "emb_soundness"})\<close> 
(*************************************************************************************************)

lemma (in Typing) opsem_executability_step:
  assumes "guard (E bio s v)" "w \<in> Ty bio v" 
  shows "opsem (pr E s) (ActBio bio v w) (pr E (update (E bio s v) w))"
  using assms
  by (auto simp add: pr_def bPr.code[of _ _ s] intro!: opsem_bBChoice opsem_bVChoice op_prefix)

lemma (in Typing) opsem_executability: 
  "traces (IOGES_to_ES E ((=) s)) \<subseteq> traces_opsem (pr E s)"
proof (rule simulation_rule_id[where R="\<lambda>s t. t = pr E s"])
  fix s1 t1 a s2
  assume "t1 = pr E s1" "IOGES_to_ES E ((=) s): s1\<midarrow>a\<rightarrow> s2"
  then show "\<exists>t2. (opsem_ES (pr E s): t1\<midarrow>a\<rightarrow> t2) \<and> t2 = pr E s2"
    by (auto simp add: IOGES_to_ES_trans intro!: opsem_executability_step)
qed simp


subsection \<open>Trace equivalence of embedding @{text "bPr"} with Event System\<close> 
(*************************************************************************************************)

lemma (in Typing) emb_opsem_equiv: "traces_opsem (pr E s) = traces (IOGES_to_ES E ((=) s))"
  by (intro equalityI emb_soundness opsem_executability)


subsection \<open>Trace equivalence between @{text "bPr"} and @{text "lPr"} embeddings\<close> 
(*************************************************************************************************)

text \<open>Show bisimulation between lPr and bPr.\<close> 

lemma (in Typing) bisim_lPr_bPr: 
  "traces_opsem (bPr (set l) IOGES s) = traces_opsem (lPr l IOGES s)" (is "?A = ?B")
proof
  define R where "R \<equiv> (\<lambda>L R. \<exists>s'. L = bPr (set l) IOGES s' \<and> R = lPr l IOGES s')"
  show "?A \<subseteq> ?B"
  proof (rule simulation_rule_id[where R=R])
    fix s1 t1 a s2
    assume "R s1 t1" "opsem_ES (bPr (set l) IOGES s): s1 \<midarrow>a\<rightarrow> s2"
    then show "\<exists>t2. (opsem_ES (lPr l IOGES s): t1\<midarrow>a\<rightarrow> t2) \<and> R s2 t2"
      by (auto simp add: bPr.code R_def dest!: opsem_bBChoice_invert opsem_bVChoice_invert 
               split: if_split_asm)
         (auto simp add: lPr.code intro!: exI opsem_lBChoice opsem_VChoice opsem.intros)
  qed (auto simp add: R_def)
next 
  define R where "R \<equiv> (\<lambda>L R. \<exists>s' . R = bPr (set l) IOGES s' \<and> L = lPr l IOGES s')"
  show "?B \<subseteq> ?A"
  proof (rule simulation_rule_id[where R=R])
    fix s1 t1 a s2
    assume "R s1 t1" "opsem_ES (lPr l IOGES s): s1 \<midarrow>a\<rightarrow> s2"
    then show "\<exists>t2. (opsem_ES (bPr (set l) IOGES s): t1\<midarrow>a\<rightarrow> t2) \<and> R s2 t2"
      by (auto simp add: lPr.code R_def dest!: opsem_lBChoice_invert opsem_bVChoice_invert 
               split: if_split_asm)
         (auto simp add: bPr.code intro!: exI opsem_bBChoice opsem_VChoice opsem.intros)
  qed (auto simp add: R_def)
qed

lemma (in Typing) bisim_lPr_pr: 
  assumes "set l = UNIV" 
  shows "traces_opsem (pr IOGES s) = traces_opsem (lPr l IOGES s)"
  using assms 
  by(simp add: bisim_lPr_bPr[symmetric] pr_def assms)

end

