(*
  Title:   I/O Processes
  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
           Tobias Klenze (tobias.klenze@inf.ethz.ch)
  Version: Isabelle/HOL 2020
  Date:    2019-2020
  ID:      $Id: IO_Processes.thy 152662 2020-08-06 09:54:41Z tklenze $
*)

section \<open>I/O Processes\<close>

theory IO_Processes         
  imports 
    Preliminaries
    "HOL-Library.BNF_Corec" 
begin

text \<open>We define (currently sequential) processes and embed them into the separation logic. 
We then construct a "canonical" model for each process and input schedule and show that 
is indeed a model.\<close>


subsection \<open>Process syntax\<close>
(********************************************************************************)

text \<open>A processes is either a null process (doing nothing), a prefixed process (executing
a basic I/O operation), or a choice process (choosing between two processes). Note that
for concrete process specifications, we can borrow co-recursive process definitions and 
conditionals from the meta-logic (i.e., HOL).\<close>

codatatype ('b, 'v) process = 
    Null 
  | Pref 'b 'v "'v \<Rightarrow> ('b, 'v) process "       ("(3_[_]._)" [90, 90, 90] 90)
  | Choice "('b, 'v) process" "('b, 'v) process"      (infixl "\<oplus>" 70)

thm process.coinduct
thm process.sel
thm process.disc


term "bio[x].(\<lambda>_.Null)"
term "bio[x].aP x"

subsection \<open>Countable choice operators\<close>
(********************************************************************************)
text \<open>We define various countable choice operator on values by corecursion:
     - VChoice, which chooses from the countable universe of values 'v,
     - BChoice, which chooses from the finite universe of basic I/O operations 'b, and
     - lBChoice, which chooses from elements of a list.\<close>

subsubsection \<open>Countable choice on Values\<close>

primcorec 
  bVChoice_from :: "nat \<Rightarrow> 'v::countable set \<Rightarrow> ('v \<Rightarrow> ('b, 'v) process) \<Rightarrow> ('b, 'v) process" 
where
  "bVChoice_from k S aP = 
     (if finite S \<and> card S \<le> k then Null
      else aP (from_nat_into S k) \<oplus> (bVChoice_from (Suc k) S aP))" 

abbreviation bVChoice ("\<Oplus>\<^sup>b") where "\<Oplus>\<^sup>b \<equiv> bVChoice_from 0"
abbreviation VChoice ("\<Oplus>")   where "\<Oplus> \<equiv> \<Oplus>\<^sup>b UNIV"

lemma Pref_not_bVChoice_from [simp]: "bio[x].P \<noteq> bVChoice_from k S aP"
  by (metis bVChoice_from.disc_iff(3) process.disc(2))

term "\<Oplus> (\<lambda>x. bio[x].aP x)"

(*
  trying to generalize index type to 'a fails here with message: 
  "Cannot have type variable "'x" in the argument types when it does not occur 
   as an immediate argument of the result type constructor".
   This could be a restriction of Isabelle.
*)
friend_of_corec 
  bVChoice_from :: "nat \<Rightarrow> 'v::countable set \<Rightarrow> ('v \<Rightarrow> ('b, 'v) process) \<Rightarrow> ('b, 'v) process" 
where
  "bVChoice_from k S aP = 
     (if finite S \<and> card S \<le> k then Null
      else aP (from_nat_into S k) \<oplus> (bVChoice_from (Suc k) S aP))"
  by (subst bVChoice_from.code, simp) transfer_prover


subsubsection \<open>Countable choice on Basic I/O Operations\<close>

function
  bBChoice :: "'b::finite set \<Rightarrow> ('b \<Rightarrow> ('b, 'v) process) \<Rightarrow> ('b, 'v) process" ("\<Oplus>\<^sup>b\<^sub>b\<^sub>i\<^sub>o")
where
  "\<Oplus>\<^sup>b\<^sub>b\<^sub>i\<^sub>o B aP = (if B = {} then Null else aP (pick B) \<oplus> (\<Oplus>\<^sup>b\<^sub>b\<^sub>i\<^sub>o (B - {pick B}) aP))" 
  by pat_completeness auto
termination 
  by (relation "measure (\<lambda>(B, aP). card B)") 
     (auto, metis card_gt_0_iff diff_Suc_less empty_iff finite)

abbreviation BChoice ("\<Oplus>\<^sub>b\<^sub>i\<^sub>o") where "\<Oplus>\<^sub>b\<^sub>i\<^sub>o \<equiv> \<Oplus>\<^sup>b\<^sub>b\<^sub>i\<^sub>o UNIV"

declare bBChoice.simps [simp del]      (* makes simplifier loop in some cases *)

term "\<Oplus>\<^sub>b\<^sub>i\<^sub>o (\<lambda>bio. \<Oplus> (\<lambda>x. bio[x].aP bio x))"

lemma bBChoice_empty [simp]: "\<Oplus>\<^sup>b\<^sub>b\<^sub>i\<^sub>o {} aP = Null" by (simp add: bBChoice.simps)

lemma Pref_not_bBChoice [simp]: "bio[x].P \<noteq> \<Oplus>\<^sup>b\<^sub>b\<^sub>i\<^sub>o B aP" by (simp add: bBChoice.simps)

friend_of_corec 
  bBChoice :: "'b::finite set \<Rightarrow> ('b \<Rightarrow> ('b, 'v) process) \<Rightarrow> ('b, 'v) process" 
where
  "\<Oplus>\<^sup>b\<^sub>b\<^sub>i\<^sub>o B aP = 
     (if B = {} then Null
      else aP (pick B) \<oplus> (\<Oplus>\<^sup>b\<^sub>b\<^sub>i\<^sub>o (B - {pick B}) aP))" 
  by (simp add: bBChoice.simps) transfer_prover


subsubsection \<open>Countable choice on lists with deterministic unfolding\<close>
text\<open>Here we define an operator @{text "\<Oplus>\<^sup>l\<^sub>b\<^sub>i\<^sub>o"} which is trace-equivalent to @{text "\<Oplus>\<^sub>b\<^sub>i\<^sub>o"} 
     when @{text "set l = UNIV"}, but has a clearly defined order. This allows us to unfold the
     operator syntactically for a given l. \<close>

fun
  lBChoice :: "'b list \<Rightarrow> ('b \<Rightarrow> ('b, 'v) process) \<Rightarrow> ('b, 'v) process" ("\<Oplus>\<^sup>l\<^sub>b\<^sub>i\<^sub>o")
where
  "\<Oplus>\<^sup>l\<^sub>b\<^sub>i\<^sub>o B aP = (case B of [] \<Rightarrow> Null | x#xs \<Rightarrow> aP x \<oplus> (\<Oplus>\<^sup>l\<^sub>b\<^sub>i\<^sub>o xs aP))"  (*define via fold*)

friend_of_corec
  lBChoice :: "'b list \<Rightarrow> ('b \<Rightarrow> ('b, 'v) process) \<Rightarrow> ('b, 'v) process" 
where  "\<Oplus>\<^sup>l\<^sub>b\<^sub>i\<^sub>o B aP = (case B of [] \<Rightarrow> Null | x#xs \<Rightarrow> aP x \<oplus> (\<Oplus>\<^sup>l\<^sub>b\<^sub>i\<^sub>o xs aP))" 
  apply (simp)
  apply transfer_prover
  done (*takes a few seconds*)

lemma lBChoice_Null[simp]: "\<Oplus>\<^sup>l\<^sub>b\<^sub>i\<^sub>o [] aP = Null" by simp

declare lBChoice.simps [simp del]      (* sometimes annoying *)


subsection \<open>Operational semantics\<close>
(********************************************************************************)

context Typing begin

inductive opsem :: "('b, 'v) process \<Rightarrow> ('b, 'v) action \<Rightarrow> ('b, 'v) process \<Rightarrow> bool" where
    op_prefix: "w \<in> Ty bio v \<Longrightarrow> opsem (bio[v].P) (ActBio bio v w) (P w)"
  | op_choice1: "opsem P a P' \<Longrightarrow> opsem (P \<oplus> Q) a P'"
  | op_choice2: "opsem Q a Q' \<Longrightarrow> opsem (P \<oplus> Q) a Q'"

inductive_cases opsem_null_invert [elim!]: "opsem Null a P"
inductive_cases opsem_prefix_invert [elim!]: "opsem (bio[v].P) a Q"
inductive_cases opsem_choice_invert [elim!]: "opsem (P \<oplus> Q) a R"

lemma opsem_well_typed_act: 
  "opsem P a P' \<Longrightarrow> well_typed_act a"
  by (induction rule: opsem.induct) auto 

lemma opsem_bio_only:           \<comment> \<open>there are only bio transitions (for now)\<close>
  assumes "opsem P a P'"
  obtains bio v w where "a = ActBio bio v w" "w \<in> Ty bio v"
  using assms
  by (induction P a P' rule: opsem.induct) auto


abbreviation opsem_ES :: "('b, 'v) process \<Rightarrow> (('b, 'v) action , ('b, 'v) process) ES" where
  "opsem_ES P \<equiv> \<lparr> init = \<lambda>Q. Q = P, trans = opsem \<rparr>"

abbreviation traces_opsem where
  "traces_opsem P \<equiv> traces (opsem_ES P)"


text \<open>Properties of indexed value choice\<close>

lemma opsem_bVChoice_from_leq:
  assumes "opsem (bVChoice_from k S aP) a P'" "n \<le> k" 
  shows "opsem (bVChoice_from n S aP) a P'"
  using assms
proof (induction k)
  case 0
  then show ?case
    by (auto simp add: bVChoice_from.code[of 0] intro: opsem.intros)
next
  case (Suc m)
  then show ?case 
  proof (cases "n = Suc m")
    case False
    from \<open>opsem (bVChoice_from (Suc m) S aP) a P'\<close> have "opsem (bVChoice_from m S aP) a P'" 
      by (auto simp add: bVChoice_from.code[of m] bVChoice_from.code[of "Suc m"]
               intro: opsem.intros)
    then show ?thesis using Suc \<open>n \<noteq> Suc m\<close> by auto
  qed simp
qed

lemma opsem_bVChoice: 
  assumes "opsem (aP v) a P'" "v \<in> S" (* requires "countable S" *)
  shows   "opsem (\<Oplus>\<^sup>b S aP) a P'"
proof -
  have "\<lbrakk> finite S; v \<in> S \<rbrakk> \<Longrightarrow> \<not> card S \<le> to_nat_on S v"
    by (auto dest!: to_nat_on_finite[THEN bij_betwE])
  with assms have "opsem (bVChoice_from (to_nat_on S v) S aP ) a P'"
    by (auto simp add: bVChoice_from.code[of "to_nat_on S v"] intro: opsem.intros)
  then show ?thesis 
    by (auto intro: opsem_bVChoice_from_leq)
qed

lemma opsem_VChoice: "opsem (aP v) a P' \<Longrightarrow> opsem (\<Oplus> aP) a P'"
  by (simp add: opsem_bVChoice)

lemma opsem_bVChoice_from_invert:
  assumes "opsem (bVChoice_from k S aP) a P'" (* requires "countable S" *)
  shows "\<exists>v\<in>S. opsem (aP v) a P'"
  using assms
proof(induction "bVChoice_from k S aP" a P' arbitrary: k S rule: opsem.induct) 
  case (op_prefix bio v P w)    
  then show ?case by simp   (* by contradiction *)
next
  case (op_choice1 P a P' Q) 
  show ?case 
  proof (cases "(finite S \<and> card S \<le> k)")
    case True
    then show ?thesis using op_choice1(3) by (auto simp add: bVChoice_from.code[of k])
  next
    case False
    then show ?thesis using op_choice1
      by (auto simp add: bVChoice_from.code[of k] intro: from_nat_into
               intro!: bexI[where x="from_nat_into S k"] split: if_split_asm)
  qed
next
  case (op_choice2 Q a Q' P) 
  then show ?case by (simp add: bVChoice_from.code[of k] split: if_split_asm)
qed

lemma opsem_bVChoice_invert: "opsem (\<Oplus>\<^sup>b S aP) a P' \<Longrightarrow> \<exists>v\<in>S. opsem (aP v) a P'"
  by (rule opsem_bVChoice_from_invert)

lemma opsem_VChoice_invert: "opsem (\<Oplus> aP) a P' \<Longrightarrow> \<exists>v. opsem (aP v) a P'"
  by (auto dest: opsem_bVChoice_invert)


text \<open>Properties of indexed basic I/O choice\<close>

lemma opsem_bBChoice:   
  assumes "opsem (aP b) a P'" "b \<in> B" 
  shows   "opsem (\<Oplus>\<^sup>b\<^sub>b\<^sub>i\<^sub>o B aP) a P'"
  using assms
proof -
  have "finite B" by simp
  then show ?thesis using assms 
  proof (induction B rule: finite_psubset_induct)
    case (psubset A)
    have "opsem (aP (pick A) \<oplus> \<Oplus>\<^sup>b\<^sub>b\<^sub>i\<^sub>o (A - {pick A}) aP) a P'" 
    proof (cases "b = pick A")
      case True
      then show ?thesis using \<open>opsem (aP b) a P'\<close> by (blast intro: opsem.intros)
    next
      case False
      have "A - {pick A} \<subset> A" using \<open>b \<in> A\<close> by fastforce
      moreover 
      have "b \<in> A - {pick A}" using \<open>b \<in> A\<close> \<open>b \<noteq> pick A\<close> by simp
      ultimately show ?thesis using psubset.IH[of "A - {pick A}"] \<open>opsem (aP b) a P'\<close> 
        by (auto intro: opsem.intros)
    qed
    then show ?case using \<open>b \<in> A\<close> 
      by (auto simp add: bBChoice.simps[where B=A])
  qed
qed

lemma opsem_bBChoice_invert: "opsem (\<Oplus>\<^sup>b\<^sub>b\<^sub>i\<^sub>o B aP) a P' \<Longrightarrow> \<exists>b\<in>B. opsem (aP b) a P'"
proof(induction "bBChoice B aP" a P' arbitrary: B rule: opsem.induct) 
  case (op_prefix bio v P w)    
  then show ?case by simp   (* by contradiction *)
next
  case (op_choice1 P a P' Q) 
  then show ?case by (auto simp add: bBChoice.simps[where B=B] split: if_split_asm)
next
  case (op_choice2 Q a Q' P) 
  then show ?case by (auto simp add: bBChoice.simps[where B=B] split: if_split_asm)
qed

lemma opsem_lBChoice:   
  assumes "opsem (aP b) a P'" "b \<in> set B" 
  shows   "opsem (\<Oplus>\<^sup>l\<^sub>b\<^sub>i\<^sub>o B aP) a P'"
  using assms
  by(induction B rule: list.induct)
    (auto simp add: lBChoice.code intro: op_choice1 op_choice2)

lemma opsem_lBChoice_invert:
  assumes "opsem (\<Oplus>\<^sup>l\<^sub>b\<^sub>i\<^sub>o B aP) a P'"
  shows   "\<exists> b \<in> set B . opsem (aP b) a P'"
  using assms
  by(induction B rule: list.induct)
    (fastforce simp add: lBChoice.simps[where B="_#_"] lBChoice.simps)+

lemma opsem_bBChoice_monotone: 
  assumes "opsem (\<Oplus>\<^sup>b\<^sub>b\<^sub>i\<^sub>o A aP) a P'" "A \<subseteq> B"
  shows   "opsem (\<Oplus>\<^sup>b\<^sub>b\<^sub>i\<^sub>o B aP) a P'"
  using assms
by (auto intro: opsem_bBChoice dest: opsem_bBChoice_invert)


subsection \<open>Trace properties of processes\<close>
(********************************************************************************)

text \<open>We first prove characterizations of the trace sets generated by each type of process.\<close>

lemma trace_Null: "(opsem_ES P: Null \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> Q) \<Longrightarrow> \<tau> = [] \<and> Q = Null"
  by (induct rule: trace.induct) auto

lemma traces_Null_eq[simp]: "traces_opsem Null = {[]}"
  by (fastforce dest: trace_Null)

lemma traces_Prefix_eq: 
  "traces_opsem (bio[v].P) = 
     insert [] {ActBio bio v w # \<tau>' | w \<tau>'. \<tau>' \<in> traces_opsem (P w) \<and> w \<in> Ty bio v}"
  by (fastforce intro: trace_consI opsem.intros elim: trace_cases_cons[where s="bio[v].P"])

lemma traces_Choice_eq: "traces_opsem (P \<oplus> Q) = traces_opsem P \<union> traces_opsem Q"
  by (fastforce intro: trace_consI opsem.intros
                elim: trace_cases_cons[where s="P"] trace_cases_cons[where s="Q"] 
                      trace_cases_cons[where s="P \<oplus> Q"])

text \<open>Next, we establish some algebraic laws about processes.\<close> 

lemma traces_Choice_Null[simp]: "traces_opsem (P \<oplus> Null) = traces_opsem P"
  by (auto simp add: traces_Choice_eq)

lemma traces_Choice_commute: "traces_opsem (P \<oplus> Q) = traces_opsem (Q \<oplus> P)"
  by (auto simp add: traces_Choice_eq)

lemma traces_Choice_Prefix: 
  "traces_opsem (bio[v].P \<oplus> bio[v].Q) = traces_opsem (bio[v].(\<lambda>w. (P w \<oplus> Q w)))"
  by (auto simp add: traces_Prefix_eq traces_Choice_eq)

lemma opsem_ES_init: "init (opsem_ES x) s \<Longrightarrow> s = x" by auto

lemma opsem_insert_bBChoice: "opsem (\<Oplus>\<^sup>b\<^sub>b\<^sub>i\<^sub>o (insert x F) aP) a Q \<longleftrightarrow> opsem (\<Oplus>\<^sup>b\<^sub>b\<^sub>i\<^sub>o F aP) a Q \<or> opsem (aP x) a Q"
  by (metis insert_iff opsem_bBChoice opsem_bBChoice_invert)+

lemma bBChoice_singleton[simp]: "\<Oplus>\<^sup>b\<^sub>b\<^sub>i\<^sub>o {x} aP = aP x \<oplus> Null" 
  using bBChoice.simps
  by (metis Diff_insert_absorb empty_not_insert insert_Diff pick_non_empty singleton_insert_inj_eq)

lemma opsem_ES_Choice_Null_init: 
  "(opsem_ES (P \<oplus> Null): s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s') \<Longrightarrow> (opsem_ES P: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s')"
  by auto

lemma traces_bBChoice:  "traces_opsem (\<Oplus>\<^sup>b\<^sub>b\<^sub>i\<^sub>o B aP) = insert [] (\<Union> {traces_opsem (aP b) | b. b \<in> B})"
proof(induction B aP rule: bBChoice.induct)
  case (1 B aP)
  have "B \<noteq> {} \<Longrightarrow> \<Union>{traces_opsem (aP b) |b. b \<in> B} = 
                    traces_opsem (aP (pick B)) \<union> \<Union>{traces_opsem (aP b) |b. b \<in> B \<and> b \<noteq> (pick B)}"
    by (auto 3 4 intro!: exI[of _ "traces_opsem (aP (pick B))"])
  then show ?case using 1 by (auto del: equalityI simp add: traces_Choice_eq bBChoice.simps[of B aP])
qed

text \<open>This is the main result about BChoice that we want to show.\<close>  

lemma traces_BChoice: "traces_opsem (\<Oplus>\<^sub>b\<^sub>i\<^sub>o aP) = \<Union> {traces_opsem (aP b) | b. True}"
  by(fastforce simp add: traces_bBChoice)

text \<open>We now show a lemma that shows trace equivalence between the non-deterministic unfolding of 
      BChoice and the deterministic unfolding of lBChoice.\<close>

lemma traces_lBChoice: "traces_opsem (\<Oplus>\<^sup>b\<^sub>b\<^sub>i\<^sub>o (set l) aP) = traces_opsem (\<Oplus>\<^sup>l\<^sub>b\<^sub>i\<^sub>o l aP)"
  by(induction rule: list.induct)
    (auto simp add: traces_Choice_eq traces_bBChoice lBChoice.simps)

end

end

