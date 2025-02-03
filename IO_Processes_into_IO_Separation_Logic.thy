(*
  Title:   I/O Processes and their Embedding into I/O Separation Logic
  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
  Version: Isabelle/HOL 2020
  Date:    September 2018
  ID:      $Id: IO_Processes_into_IO_Separation_Logic.thy 152662 2020-08-06 09:54:41Z tklenze $
*)

section \<open>Embedding I/O Processes into I/O Separation Logic\<close>

theory IO_Processes_into_IO_Separation_Logic         
  imports 
    IO_Processes IO_Separation_Logic
    "HOL-Library.Simps_Case_Conv"              (* for simps_of_case *)
    "HOL-Library.Nat_Bijection"
    "HOL-Library.Prefix_Order"
begin

text \<open>We embed processes into the I/O separation logic. We then construct a canonical model 
for each process and input schedule and show that is indeed a model.\<close>


subsection \<open>Embedding processes into assertions\<close>
(********************************************************************************)

corec embedp :: "('b, 'v) process \<Rightarrow> place \<Rightarrow> ('b, 'v) cassn" where
  "embedp P T = (case P of
       Null \<Rightarrow> Bool True
     | bio[v].aP \<Rightarrow> ExT (\<lambda>T'. ExV (\<lambda>X. CBio bio T v X T' \<star> embedp (aP X) T')) 
     | P1 \<oplus> P2 \<Rightarrow> embedp P1 T \<star> embedp P2 T
  )"

abbreviation addtok :: "(place \<Rightarrow> ('b, 'v) cassn) \<Rightarrow> ('b, 'v) cassn" where
  "addtok aA \<equiv> ExT (\<lambda>t. CTok t \<star> aA t)"

abbreviation proc_assn :: "('b, 'v) process \<Rightarrow> ('b, 'v) cassn"  where
  "proc_assn P \<equiv> addtok (embedp P)"

thm embedp.code 

simps_of_case embedp_simps [simp]: embedp.code
thm embedp_simps

thm process.splits

thm assn.coinduct_strong 
thm assn.coinduct_upto assn.cong_intros  \<comment> \<open>NOTE: These get updated with each friend declaration.\<close>
thm embedp.coinduct
thm bVChoice_from.code


lemma embedp_bVChoice_from_is_bAllStar_from: 
  "embedp (bVChoice_from k S aP) T = bAllStar_from k S (\<lambda>v. embedp (aP v) T)"
proof (coinduction arbitrary: k S rule: assn.coinduct_strong)   (* does not work: embedp.coinduct*)
  case Eq_assn
  then show ?case by (auto simp add: bVChoice_from.code[where k=k and S=S])
qed

lemma embedp_bVChoice_is_bAllStar: 
  "embedp (\<Oplus>\<^sup>b S aP) T = \<forall>\<^sup>\<star>\<^sup>b S (\<lambda>v. embedp (aP v) T)"
  by (rule embedp_bVChoice_from_is_bAllStar_from)

lemma embedp_VChoice_is_AllStar: 
  "embedp (\<Oplus> aP) T = \<forall>\<^sup>\<star> (\<lambda>v. embedp (aP v) T)"
  by (rule embedp_bVChoice_is_bAllStar)


subsection \<open>"Canonical" models\<close>  
(********************************************************************************)

text \<open>We construct a "canonical" model for a given process and input schedule.
This model has the following properties:
\begin{itemize}
\item It never reuses a place, i.e., each target place of a basic I/O operation is
unique. Or, in other words, its token graph is a tree.
\item It is indeed a model of the assertion derived from the process and input 
schedule (proved below).
\item It is minimal in the simulation preorder among all models of the given process 
and input schedule (shown later).
\end{itemize}
We start by defining the types of tree positions and input schedules. As this is the same 
type as @{typ place}, we can use tree positions as places of our canonical models.\<close>

type_synonym pos = "nat list"

text \<open>Input Schedule: It takes an entire trace, a BIO and the output value and returns the 
input value.\<close>  

type_synonym ('b, 'v) isched = "('b, 'v) atrace \<Rightarrow> 'b \<Rightarrow> 'v \<Rightarrow> 'v"

definition (in Typing) well_typed_isched :: "('b, 'v) isched \<Rightarrow> bool" where
  "well_typed_isched \<rho> = (\<forall>\<tau> bio v. \<rho> \<tau> bio v \<in> Ty bio v)"

lemma (in Typing) well_typed_ischedD [simp, dest]:
  "well_typed_isched \<rho> \<Longrightarrow> \<rho> \<tau> bio v \<in> Ty bio v"
  by (simp add: well_typed_isched_def)

lemma (in Typing) well_typed_isched_exists: "\<exists>\<rho>. well_typed_isched \<rho>"
  by (auto simp add: well_typed_isched_def Ty_non_empty some_in_eq  
           intro: exI[where x="\<lambda>\<tau> bio v. SOME w. w \<in> Ty bio v"])


text \<open>The following function returns the heap chunk (if any) of a given process and input schedule
at a given tree position (last position argument). It has three additional position arguments:
@{term "\<tau>"} stores the trace of the traversed I/O operations, which is needed for the input schedule.
@{term "ppos"} denotes the position of the previous anchestor heap chunk and @{term cpos}
keeps track of the current, already traversed position in the tree. If there is
a prefixing operator at the visited position (first equation) then the function returns
the corresponding heap chunk, using the input schedule @{term "\<rho>"} to determine the input value 
and @{term ppos} and @{term cpos} to derive the source and target places. 
When traversing a prefix operator (second equation), its position is memorized in the 
position argument @{term ppos}. Choices are traversed recursively.
If the visited position does not designate a prefixing operator we return @{term None}.\<close>

fun premodel :: "('b, 'v) process \<Rightarrow> ('b, 'v) isched \<Rightarrow> ('b, 'v) atrace \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> pos 
                    \<Rightarrow> ('b, 'v) chunk option" 
  where
    "premodel (bio[v].aP) \<rho> \<tau> ppos cpos [] = Some (Bio bio ppos v (\<rho> \<tau> bio v) (cpos @ [0]))" 
  | "premodel (bio[v].aP) \<rho> \<tau> ppos cpos (0 # pos) 
     = premodel (aP (\<rho> \<tau> bio v)) \<rho> (\<tau> @ [ActBio bio v (\<rho> \<tau> bio v)]) (cpos @ [0]) (cpos @ [0]) pos" 
  | "premodel (P1 \<oplus> P2) \<rho> \<tau> ppos cpos (0 # pos) = premodel P1 \<rho> \<tau> ppos (cpos @ [0]) pos" 
  | "premodel (P1 \<oplus> P2) \<rho> \<tau>  ppos cpos (Suc 0 # pos) = premodel P2 \<rho> \<tau> ppos (cpos @ [Suc 0]) pos" 
  | "premodel _ _ _ _ _ _ = None" 

thm premodel.cases premodel.elims

text \<open>Our model is then constructed by taking the multiset range of @{term "premodel P"} and 
filtering out the uninteresting @{term None}'s.\<close>

definition 
  gmodel :: "('b, 'v) process \<Rightarrow> ('b, 'v) isched \<Rightarrow> ('b, 'v) atrace \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> ('b, 'v) heap" 
where
  "gmodel P \<rho> \<tau> ppos cpos \<equiv> mmrange (premodel P \<rho> \<tau> ppos cpos)" 

abbreviation model :: "('b, 'v) process \<Rightarrow> ('b, 'v) isched \<Rightarrow> ('b, 'v) heap" where
  "model P \<rho> \<equiv> gmodel P \<rho> [] [] []" 


subsubsection \<open>Trace properties of canonical models\<close>

text \<open>Each individual heap only works on a specific input schedule @{term "\<rho>"}. For instance, 
assume that the heap expecting a certain schedule @{term "\<rho>"} produces a trace @{term "\<tau>"} when 
run with this @{term "\<rho>"}. Then all other heaps in @{term "gmodels_heaps"} can also re-produce 
this trace @{term "\<tau>"}, since they at some point will encounter an unexpected input and can use 
hact rule @{term "ha_contradict"} from that point to complete the trace.\<close> 

abbreviation (in Typing) gmodels_heaps :: "('b, 'v) process \<Rightarrow> ('b, 'v) heap set" where
  "gmodels_heaps P \<equiv> \<Union>\<rho>. {h. h = {# Tok [] #} + model P \<rho> \<and> well_typed_isched \<rho>}" 

definition (in Typing) traces_gmodels :: "('b, 'v) process \<Rightarrow> ('b, 'v) atrace set" where
  "traces_gmodels P = traces_heap_set (gmodels_heaps P)"

lemma (in Typing) well_typed_traces_gmodels: 
  "\<tau> \<in> traces_gmodels P \<Longrightarrow> well_typed_atrace \<tau>"
  by (auto simp add: traces_gmodels_def well_typed_isched_exists
           elim: well_typed_traces_heap_set)


subsection \<open>Basic lemmas about canonical models\<close>
(********************************************************************************)

text \<open>Basic lemmas about @{term premodel}.\<close>

lemma premodel_null [simp]: "premodel Null \<rho> \<tau> ppos cpos = Map.empty"
  by (rule ext) simp

lemma premodel_prefix:
  "premodel (bio[v].aP) \<rho> \<tau> ppos cpos = (\<lambda>pos. 
     if pos = [] 
     then Some (Bio bio ppos v (\<rho> \<tau> bio v) (cpos @ [0])) 
     else if hd pos = 0 
     then premodel (aP (\<rho> \<tau> bio v)) \<rho> (\<tau> @ [ActBio bio v (\<rho> \<tau> bio v)]) (cpos @ [0]) (cpos @ [0]) (tl pos)
     else None)"  (is "?L = (\<lambda>pos. ?R pos)")
proof (rule ext) 
  fix pos
  show "?L pos = ?R pos"
    by (cases "(bio[v].aP, \<rho>, \<tau>, ppos, cpos, pos)" rule: premodel.cases) simp_all
qed

lemma premodel_choice:
  "premodel (P1 \<oplus> P2) \<rho> \<tau> ppos cpos 
      = (\<lambda>pos. (if pos = [] then None
                else if hd pos = 0 then premodel P1 \<rho> \<tau> ppos (cpos @ [0]) (tl pos)
                else if hd pos = Suc 0 then premodel P2 \<rho> \<tau> ppos (cpos @ [Suc 0]) (tl pos)
                else None))"  (is "?L = (\<lambda>pos. ?R pos)")
proof (rule ext) 
  fix pos
  show "?L pos = ?R pos"
    by (cases "(P1 \<oplus> P2, \<rho>, \<tau>, ppos, cpos, pos)" rule: premodel.cases; simp)
qed

lemma premodel_Some_Bio_places:
  assumes "premodel P \<rho> \<tau> ppos cpos pos = Some (Bio bio t v w t')" "t = ppos'"
          "ppos \<le> cpos"        
  shows "ppos \<le> ppos' \<and> t' = cpos @ pos @ [0]" 
  using assms
proof (induction P \<rho> \<tau> ppos cpos pos rule: premodel.induct)
  case (1 bio v aP \<rho> ppos cpos)
  then show ?case by (auto)
next
  case (2 bio v aP \<rho> \<tau> cpos pos posa)
  have "cpos \<le> cpos @ [0]" by simp
  then show ?case using 2 by (force elim: dual_order.trans)
qed auto

(******)

text \<open>Two technical lemmas.\<close>

lemma mmimage_tree_tl_pos:  
  assumes "A = (- {[]} \<inter> {x. hd x = a})"
  shows "mmimage (\<lambda>pos. tree (tl pos)) A = mmrange (tree)"
proof -
  { 
    fix y
    have "(\<lambda>pos. tree (tl pos)) -` {y} \<inter> (- {[]} \<inter> {x. hd x = a}) = Cons a`(tree -` {y})"
      by (auto simp add: vimage_def image_def)
  }
  with assms show ?thesis by (simp add: mmimage_def ecard_inj_image)
qed

lemma technical:
  "(- {[]} \<inter> - {x. hd x = 0} \<inter> {x. hd x = Suc 0}) = (- {[]} \<inter> {x. hd x = Suc 0})"
  by auto

(******)

text \<open>Basic lemmas about @{term gmodel}.\<close>

lemma gmodel_eq_Bio_plus_invert:
  assumes "gmodel P \<rho> \<tau> ppos cpos = {# Bio bio t v w t' #} + h"
  shows "\<exists>pos. premodel P \<rho> \<tau> ppos cpos pos = Some (Bio bio t v w t')" 
  using assms
  by (auto dest!: minsert_implies_elem) (auto simp add: gmodel_def mmimage_elem_eq)

lemma gmodel_token_free: "Tok t #\<notin># gmodel P \<rho> \<tau> ppos cpos"
proof 
  assume "Tok t #\<in># gmodel P \<rho> \<tau> ppos cpos"
  then obtain pos where "premodel P \<rho> \<tau> ppos cpos pos = Some (Tok t)"
    by (auto simp add: gmodel_def mmimage_elem_eq)
  then show False 
    by (induction P \<rho> \<tau> ppos cpos pos rule: premodel.induct) auto
qed

lemma gmodel_bio_only: 
  assumes "c #\<in># gmodel P \<rho> \<tau> ppos cpos"
  obtains bio t v w t' where "c = Bio bio t v w t'"
  using assms
  by (cases c) (simp_all add: gmodel_token_free)


lemma gmodel_null [simp]: "gmodel Null \<rho> \<tau> ppos cpos = 0"
  by (simp add: gmodel_def)

lemma gmodel_prefix:
  "gmodel (bio[v].aP) \<rho> \<tau> ppos cpos 
   = {# Bio bio ppos v (\<rho> \<tau> bio v) (cpos @ [0]) #} 
      + gmodel (aP (\<rho> \<tau> bio v)) \<rho> (\<tau> @ [ActBio bio v (\<rho> \<tau> bio v)]) (cpos @ [0]) (cpos @ [0])"
  apply (simp add: gmodel_def)
  apply (subst premodel_prefix)
  apply (subst mrange_if mimage_if)+
  apply (simp add: mmimage_tree_tl_pos mmimage_const_single)
  done

lemma gmodel_choice: 
  "gmodel (Q1 \<oplus> Q2) \<rho> \<tau> ppos cpos = gmodel Q1 \<rho> \<tau> ppos (cpos @ [0])  
                                  + gmodel Q2 \<rho> \<tau> ppos (cpos @ [Suc 0])"
  apply (simp add: gmodel_def)
  apply (subst premodel_choice)
  apply (subst mrange_if mimage_if)+
  apply (auto simp add: mmimage_tree_tl_pos technical) 
  done


subsection \<open>The canonical model theorem\<close> 
(********************************************************************************)

text \<open>We show that canonical models are indeed models of the process assertion.\<close>

context Typing
begin


theorem canonical_model_general: 
  assumes "well_typed_isched \<rho>"
  shows "gmodel P \<rho> \<tau> ppos cpos \<Turnstile> embedp P ppos"
(* 
  bisimulation relation: X h A \<equiv> \<exists>P \<tau> ppos cpos. h = gmodel P \<rho> \<tau> ppos cpos \<and> A = embedp P ppos) 
*)
proof (coinduction arbitrary: P \<tau> ppos cpos rule: sem_coinduct_upto)       
  case sem
  then show ?case
  proof (cases P)
    case (Pref bio v aP)
    then show ?thesis
(*
      by (fastforce simp add: gmodel_prefix \<open>well_typed_isched \<rho>\<close>
                    intro: exI[of _ "cpos @ [0]"] cl_ExV[of _ _ _ "\<rho> \<tau> bio v"]
                           cl_Star cl_sem sem_Chunk[of _ 0] exI[of _ "aP (\<rho> \<tau> bio v)"] cl_base)
*)
      apply simp
      apply (rule exI[of _ "cpos @ [0]"])
      apply (rule cl_ExV[of _ _ _ "\<rho> \<tau> bio v"])
      apply (rule cl_Star)
        apply (rule cl_sem)
        apply (rule sem_Chunk[of _ 0], simp add: \<open>well_typed_isched \<rho>\<close>)
       apply (rule cl_base)
       apply (rule exI[of _ "aP (\<rho> \<tau> bio v)"]; auto) 
      apply (simp add: gmodel_prefix)
      done
  next
    case (Choice Q1 Q2)
    then show ?thesis
(*
      by (fastforce simp add: gmodel_choice 
                    intro: exI [of _ "gmodel Q1 \<rho> \<tau> ppos (cpos @ [0])"] 
                           exI [of _ "gmodel Q2 \<rho> \<tau> ppos (cpos @ [Suc 0])"] cl_base)
*)
      apply simp
      apply (rule exI [of _ "gmodel Q1 \<rho> \<tau> ppos (cpos @ [0])"])
      apply rule
       apply (rule cl_base)
       apply (rule exI [of _ "Q1"]; auto)
      apply (rule exI [of _ "gmodel Q2 \<rho> \<tau> ppos (cpos @ [Suc 0])"])
      apply rule
       apply (rule cl_base) 
       apply (rule exI [of _ "Q2"]; auto)
      apply (simp add: gmodel_choice)
      done      
  qed simp
qed

corollary canonical_model: 
  assumes "well_typed_isched \<rho>"
  shows "model P \<rho> \<Turnstile> embedp P []"
  using assms 
  by (fact canonical_model_general)

corollary canonical_model_with_token: 
  assumes "well_typed_isched \<rho>"
  shows "{# Tok [] #} + model P \<rho> \<Turnstile> CTok [] \<star> embedp P []"
  using assms 
  by (fastforce intro: canonical_model)


text \<open>It is instructive to compare the proof above with the following failed proof, which uses the 
standard coinduction scheme for the semantics predicate. (This proof is commented out.)\<close>
(* 
t h e o r e m canonical_model_general_FAILED: 
  assumes "well_typed_isched \<rho>"
  shows "gmodel P \<rho> \<tau> ppos cpos \<Turnstile> embedp P ppos"
  bisimulation relation: X h A \<equiv> \<exists>P ppos cops. h = model P \<rho> ppos cpos \<and> A = embedp P ppos)  
*)
(*
proof (coinduction arbitrary: P \<tau> ppos cpos rule: sem.coinduct)       
  case sem
  then show ?case
  proof (cases P)
    case (Pref bio v aP)
    then show ?thesis
      apply simp
      apply (rule exI[of _ "cpos"])
      apply (rule disjI1)
      apply (rule exI[of _ "bio[v].aP"])
      apply (rule exI conjI refl)+ 
      apply (subst embedp_simps)
(* MISMATCH indicating that we need coinduction "up to":
              ExV (\<lambda>X. CBio bio ppos v X cpos \<star> embedp (aP X) cpos) 
  = ExT (\<lambda>T'. ExV (\<lambda>X. CBio bio ppos v X T' \<star> embedp (aP X) T'))
*)
      apply simp  (* argh! *)
      s o r r y
  next
    case (Choice Q1 Q2)
    then show ?thesis
      apply simp
      apply (rule exI [of _ "gmodel Q1 \<rho> \<tau> ppos (cpos @ [0])"])
      apply (rule conjI, rule disjI1)
      subgoal
        apply (rule exI[of _ "Q1"])
        apply (rule exI conjI refl)+
        done
      subgoal
        apply (rule exI [of _ "gmodel Q2 \<rho> \<tau> ppos (cpos @ [1])"])
        apply (rule conjI, rule disjI1)
         apply (rule exI [of _ "Q2"])
         apply (rule exI conjI refl)+
        apply (simp add: gmodel_choice)
        done      
      done
  qed simp
oops
*)

end \<comment> \<open>context Typing\<close>


subsection \<open>Model decomposition\<close> 
(********************************************************************************)

text \<open>Decompose process along a path. Goes as far as possible into path, but stops at 
prefix processes, null processes, and invalid positions. Returns the process found
along with its position as well as all alternative choices along the path with their
positions.\<close>

fun decompose :: "('b, 'v) process \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> (pos \<times> ('b, 'v) process) list" where
  "decompose P cpos [] = [(cpos, P)]" |
  "decompose Null cpos pos = [(cpos, Null)]" | 
  "decompose (bio[v].aP) cpos pos = [(cpos, bio[v].aP)]" | 
  "decompose (P1 \<oplus> P2) cpos (0 # pos) = decompose P1 (cpos @ [0]) pos @ [(cpos @ [1], P2)]" |
  "decompose (P1 \<oplus> P2) cpos (Suc 0 # pos) = decompose P2 (cpos @ [1]) pos @ [(cpos @ [0], P1)]" |
  "decompose (P1 \<oplus> P2) cpos _  = [(cpos, P1 \<oplus> P2)]"

text \<open>Some reality checks:\<close>

value "decompose Null cpos (k # pos)"
value "decompose (bio[v].aP) cpos (k # pos)"
value "decompose (bio1[v1].aP1 \<oplus> (bio2[v2].aP2 \<oplus> Null) \<oplus> P3) [] [0]"
value "decompose (bio1[v1].aP1 \<oplus> (bio2[v2].aP2 \<oplus> Null) \<oplus> P3) [] [0,1]"
value "decompose (bio1[v1].aP1 \<oplus> (bio2[v2].aP2 \<oplus> Null) \<oplus> P3) [] [0,1,0]"
value "decompose (bio1[v1].aP1 \<oplus> (bio2[v2].aP2 \<oplus> Null) \<oplus> P3) [] [0,1,2]" 


lemma decompose_not_Nil [simp]: "decompose P cpos pos \<noteq> []"
  by (rule, erule decompose.elims) auto

text \<open>The operator used on the right hand side is defined in the "Groups List" theory.
   It sums a function over a list. The list is @{term "decompose P cpos pos"}
   and we take the multiset sum of the values resulting from applying gmodel
   on the list elements.\<close> 

(*   An example, using natural numbers is as follows:
\<Sum>x\<leftarrow>[1,3,7]. Suc x = 14*)
lemma gmodel_decomposition:
  "gmodel P \<rho> \<tau> ppos cpos = (\<Sum>(pos', P')\<leftarrow>decompose P cpos pos. gmodel P' \<rho> \<tau> ppos pos')"
proof (induction rule: decompose.induct)
  case (3 bio v aP cpos va vb)
  then show ?case by (simp add: gmodel_prefix) 
next
  case (4 P1 P2 cpos pos)
  then show ?case by (simp add: gmodel_choice) 
next
  case (5 P1 P2 cpos pos)
  then show ?case by (simp add: gmodel_choice add.commute) 
qed auto

lemma gmodel_Bio_plus_hd_decompose:
  assumes 
    "gmodel P \<rho> \<tau> ppos cpos = {# Bio bio t v w t' #} + h" 
    "t = ppos" "ppos \<le> cpos"
  shows "\<exists>pos aP. 
     hd (decompose P cpos pos) = (cpos @ pos, bio[v].aP) \<and>
     w = \<rho> \<tau> bio v \<and> t' = cpos @ pos @ [0]" 
proof -
  from assms(1-2) obtain pos where 
    "premodel P \<rho> \<tau> ppos cpos pos = Some (Bio bio ppos v w t')" 
    by (auto dest: gmodel_eq_Bio_plus_invert)
  then show ?thesis using \<open>ppos \<le> cpos\<close>
  proof (induction P \<rho> \<tau> ppos cpos pos rule: premodel.induct)
    case (1 bio v aP \<rho> \<tau> ppos cpos)
    then show ?case 
      by (auto simp add: gmodel_prefix intro!: exI[of _ "[]"])
  next
    case (2 bio v aP \<rho> \<tau> cpos pos posa)
    then show ?case 
      by (auto simp add: premodel_prefix dest: premodel_Some_Bio_places order_trans)
  next
    case (3 P1 P2 \<rho> \<tau> ppos cpos pos')
    then show ?case 
      by (force simp add: premodel_choice intro: exI[of _ "0 # pos" for pos]) 
  next
    case (4 P1 P2 \<rho> \<tau> ppos cpos pos)
    then show ?case 
      by (force simp add: premodel_choice intro: exI[of _ "1 # pos" for pos]) 
  qed auto
qed

lemma gmodel_Bio_plus_decomposition:
  assumes 
    "gmodel P \<rho> \<tau> ppos cpos = {# Bio bio t v w t' #} + h" 
    "t = ppos"
    "ppos \<le> cpos"
  shows "\<exists>pos aP. 
    w = \<rho> \<tau> bio v \<and>
    t' = cpos @ pos @ [0] \<and>
    hd (decompose P cpos pos) = (cpos @ pos, bio[v].aP) \<and>
    h = gmodel (aP w) \<rho> (\<tau> @ [ActBio bio v (\<rho> \<tau> bio v)]) (cpos @ pos @ [0]) (cpos @ pos @ [0]) + 
        (\<Sum>(pos', P')\<leftarrow>tl (decompose P cpos pos). gmodel P' \<rho> \<tau> ppos pos')"
proof -
  from assms obtain pos aP where
    H: "hd (decompose P cpos pos) = (cpos @ pos, bio[v].aP)" 
       "w = \<rho> \<tau> bio v" "t' = cpos @ pos @ [0]" 
    by (auto dest: gmodel_Bio_plus_hd_decompose)
  have "gmodel P \<rho> \<tau> ppos cpos = (\<Sum>(pos', P')\<leftarrow>decompose P cpos pos. gmodel P' \<rho> \<tau> ppos pos')"
    by (fact gmodel_decomposition)
  also have "... = (\<Sum>(pos', P')\<leftarrow> hd (decompose P cpos pos) # tl (decompose P cpos pos). 
                      gmodel P' \<rho> \<tau> ppos pos')"
    by (simp)
  also have "... = {#Bio bio ppos v w (cpos @ pos @ [0])#} 
                   + gmodel (aP w) \<rho> (\<tau> @ [ActBio bio v (\<rho> \<tau> bio v)]) (cpos @ pos @ [0]) (cpos @ pos @ [0])
                   +  (\<Sum>(pos', P')\<leftarrow>tl (decompose P cpos pos). gmodel P' \<rho> \<tau> ppos pos')" 
            (is "_ = ?R") 
    by (simp add: H(1-2) gmodel_prefix)
  finally have "gmodel P \<rho> \<tau> ppos cpos = ?R" .
  with assms(1,2) H(2,3) 
  have "h = gmodel (aP w) \<rho> (\<tau> @ [ActBio bio v (\<rho> \<tau> bio v)]) (cpos @ pos @ [0]) (cpos @ pos @ [0]) 
            + (\<Sum>(pos', P')\<leftarrow>tl (decompose P cpos pos). gmodel P' \<rho> \<tau> ppos pos')"
    by (auto simp add: add.assoc dest: minsert_cancel_left)
  with H show ?thesis by (auto)
qed

text \<open>Basic lemma relating process decomposition to operational semantics.\<close>

lemma (in Typing) hd_decompose_opsem:
  assumes
    "hd (decompose P cpos pos) = (cpos @ pos, bio[v].aP)" "w \<in> Ty bio v"
  shows 
    "opsem P (ActBio bio v w) (aP w)"
  using assms
  by (induction P cpos pos rule: decompose.induct) (auto intro: opsem.intros)


end
