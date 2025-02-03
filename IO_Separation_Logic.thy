(*
  Title:   Separation Logic for I/O Specifications
           (see Penninckx, Jacobs and Piessens, ESOP 2015)
  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
  Version: Isabelle/HOL 2020
  Date:    2019
  ID:      $Id: IO_Separation_Logic.thy 152662 2020-08-06 09:54:41Z tklenze $
*)

section \<open>I/O Separation Logic\<close>

theory IO_Separation_Logic
  imports 
    EMultiset Preliminaries
    "HOL-Library.Stream"
begin

text \<open>We define a separation logic for I/O specifications similar to the one proposed 
by Penninckx, Jacobs and Piessens (ESOP 2015). The semantics is given in terms of 
heaps of basic I/O operations.\<close>


subsection \<open>Syntax\<close> 
(********************************************************************************)

text \<open>Define heap chunks first. We could use a type variable for places, but this will not
buy us much. We use @{typ "nat list"} here, which will be more useful later than just 
@{typ "nat"}.\<close>

type_synonym place = "nat list" 

datatype ('b, 'v) chunk =           (* ADD (dead 'b) as attempted BUG workaround *)
    Tok place 
  | Bio 'b place 'v 'v place       

text \<open>Source places of basic I/O operations\<close>

fun src_place :: "('b, 'v) chunk \<Rightarrow> place set" where
  "src_place (Tok t) = {}" |
  "src_place (Bio bio t v w t') = {t}"

text \<open>Assertions, encoded in higher-order abstract syntax.\<close> 

codatatype ('b, 'v) assn =
    Bool bool
  | Chunk "'b"                       (* here 'b abstracts ('b, 'v) chunk, instantiated later *)
  | Star "('b, 'v) assn" "('b, 'v) assn"  (infixl "\<star>" 70)
  | ExV "'v \<Rightarrow> ('b, 'v) assn"            
  | ExT "place \<Rightarrow> ('b, 'v) assn"

thm assn.coinduct

abbreviation CTok where
  "CTok t \<equiv> Chunk (Tok t)"

abbreviation CBio where
  "CBio bio t v w t' \<equiv> Chunk (Bio bio t v w t')"


text \<open>Define disjunction from existential quantification. To make sense semantically, this 
requires at least two distinct elements in universe of value.\<close> 

definition Disj :: "('b, 'v) assn \<Rightarrow> ('b, 'v) assn \<Rightarrow> ('b, 'v) assn"  (infix "OR" 65) where
  "A1 OR A2 = ExT (\<lambda>t. if t \<noteq> [] then A1 else A2)"      


text \<open>Define the AllStar quantifier corecursively.\<close>

(* NOTE: we cannot use pick to define this, since we do not know whether we will
   pick all elements of an infinite set S. *)

primcorec
  bAllStar_from :: "nat \<Rightarrow> 'v set \<Rightarrow> ('v \<Rightarrow> ('b, 'v) assn) \<Rightarrow> ('b, 'v) assn"  
where
  "bAllStar_from k S aP = 
     (if finite S \<and> k \<ge> card S 
      then Bool True 
      else aP (from_nat_into S k) \<star> (bAllStar_from (Suc k) S aP ))" 

abbreviation bAllStar ("\<forall>\<^sup>\<star>\<^sup>b") where "\<forall>\<^sup>\<star>\<^sup>b \<equiv> bAllStar_from 0" 
abbreviation AllStar ("\<forall>\<^sup>\<star>") where "\<forall>\<^sup>\<star> \<equiv> \<forall>\<^sup>\<star>\<^sup>b UNIV"

(* DO NOT WORK with "'b chunk" in ('b, 'v) assn definition due to an Isabelle 2018/9 bug. *)

friend_of_corec 
  bAllStar_from :: "nat \<Rightarrow> 'v set \<Rightarrow> ('v \<Rightarrow> ('b, 'v) assn) \<Rightarrow> ('b, 'v) assn" 
where
  "bAllStar_from k S aP = 
     (if finite S \<and> k \<ge> card S 
      then Bool True 
      else aP (from_nat_into S k) \<star> (bAllStar_from (Suc k) S aP ))" 
  apply (subst bAllStar_from.code, simp) 
  apply transfer_prover
  done


subsection \<open>Coinductive semantics\<close> 
(********************************************************************************)

type_synonym ('b, 'v) heap = "('b, 'v) chunk emultiset"
type_synonym ('b, 'v) cassn = "(('b, 'v) chunk, 'v) assn"


text \<open>Define the set of source places of heaps.\<close>

definition src_places :: "('b, 'v) heap \<Rightarrow> place set" where
  "src_places h \<equiv>  (\<Union>c \<in> msupport h. src_place c)"

lemma src_places_empty [simp, intro!]: "src_places 0 = {}"
  by (simp add: src_places_def)

lemma src_places_plus [simp]: "src_places (g + h) = src_places g \<union> src_places h"
  by (simp add: src_places_def)

lemma src_places_bio [dest]: "Bio bio t v w t' #\<in># g \<Longrightarrow> t \<in> src_places g" 
  by(auto simp add: src_places_def msupport_def melem_def)


context Typing
begin

fun well_typed_chunk :: "('b, 'v) chunk \<Rightarrow> bool" where
  "well_typed_chunk (Bio bio _ v w _) \<longleftrightarrow>  w \<in> Ty bio v" |
  "well_typed_chunk _ \<longleftrightarrow> True"


text \<open>Semantics of I/O separation logic.\<close>

coinductive sem :: "('b, 'v) heap \<Rightarrow> ('b, 'v) cassn \<Rightarrow> bool"  (infix "\<Turnstile>" 50) where
    sem_True: "h \<Turnstile> Bool True"
  | sem_Chunk: "well_typed_chunk c \<Longrightarrow> {# c #} + h \<Turnstile> Chunk c"  
  | sem_Star: "\<lbrakk> h1 \<Turnstile> A1; h2 \<Turnstile> A2; h = h1 + h2 \<rbrakk> \<Longrightarrow> h \<Turnstile> A1 \<star> A2"
  | sem_ExV: "h \<Turnstile> aA v \<Longrightarrow> h \<Turnstile> ExV aA"
  | sem_ExT: "h \<Turnstile> aA t \<Longrightarrow> h \<Turnstile> ExT aA"     

declare 
  sem_True [simp, intro!]
  sem.intros(2-5) [intro]

lemmas sem_Chunk_non_leaking [simp, intro!] = sem_Chunk[of _ 0, simplified]

(* CAUTION: [elim!] might be too agressive. *)
inductive_cases sem_Chunk_elim: "h \<Turnstile> Chunk c"
inductive_cases sem_Star_elim: "h \<Turnstile> A1 \<star> A2"
inductive_cases sem_ExV_elim: "h \<Turnstile> ExV aA"
inductive_cases sem_ExT_elim: "h \<Turnstile> ExT aA"

lemmas sem_elims = sem_Chunk_elim sem_Star_elim sem_ExV_elim sem_ExT_elim

subsubsection \<open>Coinduction up-to for semantics\<close>

thm sem.coinduct

text \<open>Derive a coinduction-upto rule for the assertion semantics. First define a closure
for cooinduction relations depending on a heap and an assertion.\<close>

inductive cl for R where
  cl_base: "R h A \<Longrightarrow> cl R h A"
| cl_sem: "h \<Turnstile> A \<Longrightarrow> cl R h A"
| cl_Star: "cl R h1 A1 \<Longrightarrow> cl R h2 A2 \<Longrightarrow> h = h1 + h2 \<Longrightarrow> cl R h (A1 \<star> A2)"
| cl_ExV: "cl R h (aA v) \<Longrightarrow> cl R h (ExV aA)"
| cl_ExT: "cl R h (aA t) \<Longrightarrow> cl R h (ExT aA)"

declare cl.intros [intro]

theorem sem_coinduct_upto[consumes 1, case_names sem]:
  assumes X: "X heap assertion"
  and CIH: "\<And>heap assertion.
      X heap assertion \<Longrightarrow>
      (\<exists>h. heap = h \<and> assertion = Bool True) \<or>
      (\<exists>c h. heap = {#c#} + h \<and> assertion = Chunk c \<and> well_typed_chunk c) \<or>
      (\<exists>h1 A1 h2 A2 h. heap = h \<and> assertion = A1 \<star> A2 \<and> cl X h1 A1 \<and> cl X h2 A2 \<and> h = h1 + h2) \<or>
      (\<exists>h aA v. heap = h \<and> assertion = ExV aA \<and> cl X h (aA v)) \<or>
      (\<exists>h aA t. heap = h \<and> assertion = ExT aA \<and> cl X h (aA t))"
  shows "heap \<Turnstile> assertion"
  apply (rule sem.coinduct[where X = "cl X"])
   apply (rule cl.intros, rule X)
  subgoal for h P
    apply (induct P rule: cl.induct)
        apply (drule CIH; force)
       apply (auto 4 0)
    subgoal for h P
      apply (cases h P rule: sem.cases)
           apply auto
      done
    done
  done

thm sem.coinduct[of X heap assertion] sem_coinduct_upto[of X heap assertion]


subsubsection \<open>Basic properties of the semantics\<close>

lemma sem_leaking_left: "h \<Turnstile> A \<Longrightarrow> g + h \<Turnstile> A"
proof (coinduction arbitrary: h A rule: sem.coinduct)
  case sem
  then show ?case
  proof (cases rule: sem.cases)
    case (sem_Chunk c h)
    then show ?thesis
      by (auto simp add: Groups.ac_simps intro: exI[of _ "g + h"]) 
  next
    case (sem_Star h1 A1 h2 A2)
    then show ?thesis
      by (auto 0 3 simp: add.assoc intro: exI[of _ "g + h1"] exI[of _ "h2"])
  qed auto
qed

lemma sem_leaking_right: "h \<Turnstile> A \<Longrightarrow> h + g \<Turnstile> A"
  by (auto simp add: sem_leaking_left add.commute) 

lemmas sem_leaking = sem_leaking_left sem_leaking_right


lemma sem_Bool [simp]: "h \<Turnstile> Bool b \<longleftrightarrow> b"
  by (auto) (erule sem.cases, auto)


lemma sem_Disj1: "h \<Turnstile> A1 \<Longrightarrow> h \<Turnstile> A1 OR A2"
  by (auto simp add: Disj_def)

lemma sem_Disj2: "h \<Turnstile> A2 \<Longrightarrow> h \<Turnstile> A1 OR A2"
  by (auto simp add: Disj_def)

end


subsection \<open>Heap transitions\<close>
(********************************************************************************)

context Typing 
begin

inductive hact :: "('b, 'v) heap option \<Rightarrow> ('b, 'v) action \<Rightarrow> ('b, 'v) heap option \<Rightarrow> bool" where
  ha_bio: 
    "\<lbrakk> h = {# Bio bio t v w t' #} + h''; h' = {# Tok t' #} + h''; w \<in> Ty bio v \<rbrakk> \<Longrightarrow>
       hact (Some ({# Tok t #} + h)) 
            (ActBio bio v w) 
            (Some h')" |
  ha_contradict: 
    "\<lbrakk> h = {# Bio bio t v w t' #} + h'; w \<noteq> w'; w \<in> Ty bio v; w' \<in> Ty bio v \<rbrakk> \<Longrightarrow>
       hact (Some ({# Tok t #} + h)) 
            (ActBio bio v w') 
            None" |
  ha_chaos: 
    "\<lbrakk> well_typed_act a \<rbrakk> \<Longrightarrow>
       hact None a None"    

inductive_cases hact_empty [elim!]: "hact (Some 0) a ho"


text \<open>Frame properties.\<close>

lemma hact_frame: 
  "hact (Some h) a (Some h') \<Longrightarrow> hact (Some (h + g)) a (Some (h' + g))"
  by (auto simp add: add.assoc intro!: hact.intros elim!: hact.cases)

lemma hact_frame_None:
  "hact (Some h) a None \<Longrightarrow> hact (Some (h + g)) a None"
  by (auto simp add: add.assoc intro: ha_contradict elim!: hact.cases)


text \<open>There can only be a transition to state @{term None} if there is also a regular 
transition with a different input value.\<close>

lemma hact_None_alternative_Some:
  assumes "hact (Some ({# Tok t #} + h)) (ActBio bio v w') None" "\<And>tk. Tok tk #\<notin># h"
  shows "\<exists>t' h' w. w \<noteq> w' \<and> 
           hact (Some ({# Tok t #} + h)) (ActBio bio v w) (Some ({# Tok t' #} + h'))"
  using assms
  by (cases rule: hact.cases) (auto dest: minsert_match intro: ha_bio)
 

subsubsection \<open>Event systems and trace properties\<close>

definition heap_ES :: "('b, 'v) heap option \<Rightarrow> (('b, 'v) action, ('b, 'v) heap option) ES" where
  "heap_ES ho \<equiv> \<lparr> init = \<lambda>ho'. ho' = ho, trans = hact \<rparr>"

lemma heap_ES_init [simp]: "init (heap_ES ho) ho' \<longleftrightarrow> ho' = ho" 
  by (simp add: heap_ES_def)

lemma heap_ES_trans: "trans (heap_ES ho) = hact"
  by (simp add: heap_ES_def)


lemma well_typed_act_heap_ES_trans [simp, dest]: 
  "\<lbrakk> heap_ES ho: s \<midarrow>e\<rightarrow> s' \<rbrakk> \<Longrightarrow> well_typed_act e"
  by (auto simp add: heap_ES_trans elim: hact.cases)


text \<open>Trace properties of heap sets and heap maps and their equivalence.\<close>

definition traces_heap_set :: "('b, 'v) heap set \<Rightarrow> ('b, 'v) atrace set" where
  "traces_heap_set H = {\<tau>. \<forall>h \<in> H. \<tau> \<in> traces (heap_ES (Some h))}"

lemma traces_heap_set_empty_trace [simp, intro!]: "[] \<in> traces_heap_set H"
  by (simp add: traces_heap_set_def)

lemma traces_heap_set_empty [simp]: "traces_heap_set {} = UNIV"
  by (auto simp add: traces_heap_set_def)

lemma well_typed_traces_heap_ES [simp, dest]:
  assumes "\<tau> \<in> traces (heap_ES ho)"
  shows "well_typed_atrace \<tau>"
  using assms
proof
  fix s s'
  assume "heap_ES ho: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'"
  then show ?thesis by (induction rule: trace.induct) simp_all
qed

lemma well_typed_traces_heap_set [simp, dest]:
  "\<lbrakk> \<tau> \<in> traces_heap_set H; H \<noteq> {} \<rbrakk> \<Longrightarrow> well_typed_atrace \<tau>"
  by (auto simp add: traces_heap_set_def)


text \<open>Trace properties of assertions.\<close>

abbreviation traces_assn :: "('b, 'v) cassn \<Rightarrow> ('b, 'v) atrace set" where
  "traces_assn A \<equiv> traces_heap_set {h. h \<Turnstile> A}"

lemmas traces_assn_def = traces_heap_set_def

end

end