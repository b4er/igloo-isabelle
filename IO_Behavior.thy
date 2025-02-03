(*
  Title:   Behavior of I/O Specifications and Processes and their Equivalence
  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
           Tobias Klenze (tobias.klenze@inf.ethz.ch)
  Version: Isabelle/HOL 2020
  Date:    2018-2020
  ID:      $Id: IO_Behavior.thy 152662 2020-08-06 09:54:41Z tklenze $
*)

section \<open>Behavior of I/O Specifications and Processes\<close>

theory IO_Behavior
  imports IO_Processes_into_IO_Separation_Logic
begin

text \<open>We prove that the equivalence of the following trace properties:
\begin{itemize}
\item heap traces of embedded process assertions,
\item heap traces of canonical process model,
\item process traces (according to operational semantics).
\end{itemize}
We show this by establishing three set inclusions.\<close>


subsubsection \<open>Heap trace properties of processes.\<close>
(********************************************************************************)

context Typing
begin

abbreviation traces_process_assn :: "('b, 'v) process \<Rightarrow> ('b, 'v) atrace set" where
  "traces_process_assn P \<equiv> traces_assn (proc_assn P)"

lemmas traces_process_assn_defs = traces_assn_def


text \<open>This lemma simply shows the above abbreviations collapsed into one equivalence. It only serves
  as illustration and is not used below.\<close>

lemma traces_process_assn_unfolded:
  "traces_process_assn P = {\<tau>. \<forall>h. h \<Turnstile> proc_assn P \<longrightarrow> \<tau> \<in> traces (heap_ES (Some h))}"
by (simp add: traces_heap_set_def)

end


subsection \<open>Dead heap parts\<close>
(********************************************************************************)

text \<open>These are I/O permissions that can not be used now, or in the future, since we do not have
      and never will have, the source token for the I/O permission.\<close>

definition dead :: "('b, 'v) heap \<Rightarrow> place \<Rightarrow> bool" where 
  "dead h tpos \<longleftrightarrow> src_places h \<inter> upset tpos = {} \<and> (\<forall>t . Tok t #\<notin># h)"

lemma deadI:
  "\<lbrakk>src_places h \<inter> upset tpos = {}; \<forall>t. Tok t #\<notin># h\<rbrakk> \<Longrightarrow> dead h tpos"
  by (auto simp add: dead_def)

lemma deadE [elim]:
  "\<lbrakk>dead h tpos; \<lbrakk> src_places h \<inter> upset tpos = {}; (\<forall>t . Tok t #\<notin># h)\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto simp add: dead_def)

lemma dead_token_free: "dead h tpos \<Longrightarrow> Tok t #\<notin># h"
  by (auto simp add: dead_def)

lemma dead_no_ready_bio: "dead h tpos \<Longrightarrow> Bio bio tpos v w t' #\<notin># h" 
  by (auto simp add: dead_def)


lemma dead_empty [simp, intro!]: "dead 0 pos"
  by (auto simp add: dead_def)

lemma dead_plus [simp]: "dead (g + h) pos \<longleftrightarrow> dead g pos \<and> dead h pos"
  by (auto simp add: dead_def)

lemma dead_suffix [simp]: "\<lbrakk> dead h pos; pos \<le> pos' \<rbrakk> \<Longrightarrow>  dead h pos'"
  by (auto simp add: dead_def dest: upset_antitone [THEN [2] rev_subsetD])


subsection \<open>Residual models are dead\<close>
lemma dead_elem: "dead g pos \<longleftrightarrow> (\<forall>x . x #\<in># g \<longrightarrow> dead {#x#} pos)"
  by (auto simp add: dead_def melem_def upset_def src_places_def msupport_def)

lemma dead_elemI: "\<lbrakk>\<And>x. x #\<in># g \<Longrightarrow> dead {#x#} pos\<rbrakk> \<Longrightarrow> dead g pos"
  using dead_elem by blast

(* If x is an element of the multiset sum of lists, then it must occur somewhere in the list.*)
lemma sum_list_elem:
 "x #\<in># (\<Sum>param\<leftarrow>l. f param) \<Longrightarrow> \<exists> param . x #\<in># f param \<and> param \<in> set l"
  by (induction l) auto

text \<open>Reason about the source positions of bios allowed by @{term "gmodel"}\<close>

lemma src_place_gmodels:
  assumes "Bio bio t v w t' #\<in># gmodel P \<rho> \<tau> ppos cpos" "ppos \<le> cpos" 
  shows "\<exists> pos. t = pos \<and> ppos \<le> pos"   (* add: \<and> w = \<rho> ppos ?! *)
proof -
  obtain p where "premodel P \<rho> \<tau> ppos cpos p = Some (Bio bio t v w t')" using assms(1)
    by(auto dest!: gmodel_eq_Bio_plus_invert simp add: elem_minsert_eq)
  moreover obtain tpos where "t = tpos" using bij_list_encode by(auto simp add: bij_def)
  finally have "ppos \<le> tpos"
    using assms(2) premodel_Some_Bio_places by fastforce
  then show ?thesis using \<open>t = tpos\<close> by blast
qed

text \<open>A position returned by decompose is prefixed by @{term cpos}.\<close> 

lemma decompose_sub_positions:
  "(pos', P') \<in> set (decompose P cpos pos) \<Longrightarrow> cpos \<le> pos'"
by(induction  P cpos pos rule: decompose.induct)
  (auto intro: prefixI dual_order.trans)

text \<open>The positions returned by decompose are not related by @{text "\<le>"}.\<close>

lemma decompose_distinct_pos:
  assumes "(pos1, P1) \<in> set (decompose P cpos pos)" 
          "(pos2, P2) \<in> set (decompose P cpos pos)"
          "pos1 \<noteq> pos2"
    shows "\<not> pos1 \<le> pos2"
proof -
  have helper: "\<And>p c . c @ [Suc 0] \<le> p \<Longrightarrow> c @ [0] \<le> p \<Longrightarrow> False"
    by (erule prefixE, simp)
  show ?thesis using assms apply auto 
    apply(induction  P cpos pos rule: decompose.induct)
      (* actually this should work just by case analysis, no induction hypothesis is required *)
    by (auto dest: decompose_sub_positions helper dual_order.trans)+
qed

text \<open>The position marker (cpos @ pos) is not a prefix (parent) of any position
   returned by an element of tl decompose (or vice versa). (Actually, we could generalize this:
   no two elements of (set decompose) are related by prefixing.)

   (cpos @ pos), the first element of hd decompose, is the position at which we continue after 
   executing a @{term hact_reg}.
   tl decompose contains all the things that are dead. Showing that they are not
   related to hd decompose by prefixing is a way of proving that these things are dead. \<close>

lemma decompose_hd_vs_tl:
  assumes 
    "(pos', P') \<in> set (tl (decompose P cpos pos))"
    "ppos \<le> cpos"
    "hd (decompose P cpos pos) = (cpos @ pos, bio[v].aP)"
  shows "\<not> (cpos @ pos) \<le> pos' \<and> \<not> pos' \<le> (cpos @ pos)" 
proof -
  have "(pos', P') \<in> set (decompose P cpos pos)" 
    using assms(1) by (simp add: list.set_sel(2))
  moreover have "(cpos @ pos, bio[v].aP) \<in> set (decompose P cpos pos)"
    using assms(3) decompose_not_Nil list.set_sel(1) by metis
  moreover have "pos' \<noteq> cpos @ pos" using assms(1,3)
    by (induction P cpos pos rule: decompose.induct) auto
  ultimately show ?thesis by (auto dest: decompose_distinct_pos)
qed

text \<open>If a bio is produced by premodel of some ppos and some cpos = pos', then the source token of this
 bio is either at position of ppos (shallow bio), or at a position deeper than pos'.\<close>

lemma premodel_tpos:
  assumes "Some (Bio bio tpos v w t') = premodel P' \<rho> \<tau> ppos pos' p" 
          "ppos \<le> pos'"
          "tpos \<noteq> ppos"
  shows "pos' \<le> tpos"
  using assms
by(induction P' \<rho> \<tau> ppos pos' p rule: premodel.induct)
  (auto intro: prefixI dual_order.trans)


text \<open>tl (decompose P cpos pos) is what we are left with when we execute the action 
      corresponding to hd (decompose P cpos pos).
      In this lemma we show that everything in that heap is dead.\<close>

lemma dead_residual_gmodels:
  assumes "g = (\<Sum>(pos', P')\<leftarrow>tl (decompose P cpos pos). gmodel P' \<rho> \<tau> ppos pos')"
          "ppos \<le> cpos"
          "hd (decompose P cpos pos) = (cpos @ pos, bio[v].aP)"
  shows "dead g (cpos @ pos @ [0])"
proof (rule dead_elemI)
  fix x
  assume "x #\<in># g"
  then have x_def: "x #\<in># (\<Sum>(pos', P')\<leftarrow>tl (decompose P cpos pos). gmodel P' \<rho> \<tau> ppos pos')" 
    using assms by blast
  then obtain pos' P' where pos'_def: "x #\<in># gmodel P' \<rho> \<tau> ppos pos'" 
                                      "(pos', P') \<in> set (tl (decompose P cpos pos))"
    by (metis (mono_tags, lifting) case_prodE2 sum_list_elem)
  have pos'_elem: "(pos', P') \<in> set (decompose P cpos pos)" using pos'_def(2)
    by (simp add: list.set_sel(2))
  from \<open>x #\<in># gmodel P' \<rho> \<tau> ppos pos'\<close> obtain bio t v w t' where bio_def: "x = Bio bio t v w t'"
    using gmodel_bio_only by blast
  from bio_def have src_x: "src_places {#x#} = {t}" by (simp add: src_places_def msupport_def)
  have "cpos \<le> pos'"  using decompose_sub_positions pos'_elem by blast
  then have "ppos \<le> pos'" using assms(2) by auto
  then obtain tpos where tpos_def: "t = tpos" "ppos \<le> tpos" 
    using src_place_gmodels bio_def pos'_def(1) assms(2) by metis
  from pos'_def(1) 
  obtain p where p_def: "Some (Bio bio (tpos) v w t') = premodel P' \<rho> \<tau> ppos pos' p" 
    using gmodel_eq_Bio_plus_invert  bio_def elem_minsert_eq tpos_def(1)
    by (metis)
  have "\<not> (cpos @ pos @ [0]) \<le> tpos"
  proof (cases "tpos = ppos")
    case True (* x is a first-level bio that has ppos as source token *)
    then show ?thesis using assms(2) dual_order.trans by blast
  next
    case False (* x is a >1st level bio that has some source token which to which pos' is a prefix
                  use premodel_tpos here *)
    have "\<not> cpos @ pos \<le> pos'" "\<not> pos' \<le> cpos @ pos" 
      using pos'_def(2) assms(2,3) by(auto dest!: decompose_hd_vs_tl)
    then have "\<not> pos' \<le> cpos @ pos @ [0]"
      using Prefix_Order.prefix_snoc append.assoc eq_iff by metis
    have "pos' \<le> tpos" using p_def \<open>ppos \<le> pos'\<close>  \<open>tpos \<noteq> ppos\<close> by(auto elim: premodel_tpos)
    then obtain ys where "tpos = pos' @ ys" by(erule prefixE)
    show ?thesis 
    proof 
      assume "cpos @ pos @ [0] \<le> tpos"
      then obtain zs where "tpos = (cpos @ pos @ [0]) @ zs" by(auto elim!: prefixE)
      then have "pos' @ ys = (cpos @ pos @ [0]) @ zs" using \<open>tpos = pos' @ ys\<close> by simp
      then show "False" 
        using \<open>\<not> pos' \<le> cpos @ pos @ [0]\<close> \<open>\<not> cpos @ pos \<le> pos'\<close> 
        by(auto simp add: append_eq_append_conv2) 
    qed
  qed
  then have "src_places {#x#}  \<inter> upset (cpos @ pos @ [0]) = {}"
    by (simp add: upset_def inj_image_mem_iff inj_list_encode src_x tpos_def)
  then show "dead {#x#} (cpos @ pos @ [0])"
    by (auto intro: deadI simp add: melem_def bio_def)
qed

subsection \<open>Lemmas about heap transitions of canonical process models\<close>
(********************************************************************************)

text \<open>Two lemmas about heap transitions of the canonical models plus some dead heap part.\<close>

context Typing
begin

lemma hact_gmodel_and_dead_has_bio_trans_only:
  assumes
    "hact (Some ({# Tok t #} + gmodel P \<rho> \<tau> ppos cpos + g)) a ho'"
    "t = ppos" "dead g ppos" 
  shows "\<exists>bio v w w' t' h''. 
    a = ActBio bio v w \<and> w \<in> Ty bio v \<and> w' \<in> Ty bio v \<and>
    gmodel P \<rho> \<tau> ppos cpos = {#Bio bio t v w' t'#} + h'' \<and>
    (w = w' \<and> ho' = Some ({# Tok t' #} + h'' + g) \<or> w \<noteq> w' \<and> ho' = None)"
  using assms
proof (cases rule: hact.cases)
  case (ha_bio h bio ta v w t' ha' h')
  from \<open>{#Tok t#} + gmodel P \<rho> \<tau> ppos cpos + g = {#Tok ta#} + h\<close> \<open>dead g ppos\<close>
  have "ta = t" "h = gmodel P \<rho> \<tau> ppos cpos + g"
    by (auto simp add: add.assoc  dead_token_free gmodel_token_free dest!: minsert_match )  
  from \<open>h = {#Bio bio ta v w t'#} + ha'\<close> \<open>h = gmodel P \<rho> \<tau> ppos cpos + g\<close> 
  have "Bio bio ta v w t' #\<in># gmodel P \<rho> \<tau> ppos cpos \<or> Bio bio ta v w t' #\<in># g" 
    by (auto dest: minsert_implies_elem)
  then show ?thesis 
  proof
    assume "Bio bio ta v w t' #\<in># gmodel P \<rho> \<tau> ppos cpos"
    then obtain hb' where "gmodel P \<rho> \<tau> ppos cpos = {#Bio bio ta v w t'#} + hb'" 
      by (auto simp add: elem_minsert_eq)
    with \<open>h = {#Bio bio ta v w t'#} + ha'\<close> \<open>h = gmodel P \<rho> \<tau> ppos cpos + g\<close>
    have "ha' = hb' + g"
      by (auto simp add: add.assoc intro: minsert_cancel_left sym)
    with \<open>gmodel P \<rho> \<tau> ppos cpos = {#Bio bio ta v w t'#} + hb'\<close> 
    show ?thesis 
      using \<open>ta = t\<close> \<open>a = ActBio bio v w\<close> \<open>h' = {#Tok t'#} + ha'\<close> \<open>ho' = Some h'\<close> \<open>w \<in> Ty bio v\<close>
      by (auto simp add: add.assoc)
  next
    assume "Bio bio ta v w t' #\<in># g"
    then show ?thesis using \<open>dead g ppos\<close> \<open>ta = t\<close> \<open>t = ppos\<close> 
      by (auto dest: dead_no_ready_bio)
  qed
next
  case (ha_contradict h bio ta v w ta' ha' w')
  from \<open>{#Tok t#} + gmodel P \<rho> \<tau> ppos cpos + g = {#Tok ta#} + h\<close> \<open>dead g ppos\<close>
  have "ta = t" "h = gmodel P \<rho> \<tau> ppos cpos + g"
    by (auto simp add: add.assoc  dead_token_free gmodel_token_free dest!: minsert_match )  
  from \<open>h = {#Bio bio ta v w ta'#} + ha'\<close> \<open>h = gmodel P \<rho> \<tau> ppos cpos + g\<close> 
  have "Bio bio ta v w ta' #\<in># gmodel P \<rho> \<tau> ppos cpos \<or> Bio bio ta v w ta' #\<in># g" 
    by (auto dest: minsert_implies_elem)
  then show ?thesis 
  proof 
    assume "Bio bio ta v w ta' #\<in># gmodel P \<rho> \<tau> ppos cpos"
    then obtain hb' where "gmodel P \<rho> \<tau> ppos cpos = {#Bio bio ta v w ta'#} + hb'" 
      by (auto simp add: elem_minsert_eq)
    then show ?thesis
      using \<open>ta = t\<close> \<open>ho' = None\<close> \<open>a = ActBio bio v w'\<close> \<open>w' \<in> Ty bio v\<close> \<open>w \<in> Ty bio v\<close> \<open>w \<noteq> w'\<close>
      by (auto simp add: add.assoc)
  next
    assume "Bio bio ta v w ta' #\<in># g"
    then show ?thesis using \<open>dead g ppos\<close> \<open>ta = t\<close> \<open>t = ppos\<close> 
      by (auto dest: dead_no_ready_bio)
  qed
qed

lemma hact_remove_dead_heap_part: 
  assumes
    "hact (Some ({# Tok t #} + gmodel P \<rho> \<tau> ppos cpos + g)) a (Some h')"
    "t = ppos" "dead g ppos" 
  shows
    "\<exists>h''. h' = h'' + g \<and>
      hact (Some ({# Tok ppos #} + gmodel P \<rho> \<tau> ppos cpos)) a (Some h'')"
proof - 
  from assms obtain bio v w t' h'' where 
    "a = ActBio bio v w" and "w \<in> Ty bio v" and
    "gmodel P \<rho> \<tau> ppos cpos = {#Bio bio t v w t'#} + h''" and
    "h' = {# Tok t' #} + h'' + g"
    by (blast dest: hact_gmodel_and_dead_has_bio_trans_only)
  with assms show ?thesis  
    by (auto intro: exI[where x="{#Tok t'#} + h''"] hact.intros)
qed


subsection \<open>From embedded process assertions to canonical process models\<close>
(********************************************************************************)

text \<open>This property immediately follows from the definitions and the canonical
model theorem. Note that this requires the restriction to well-typed input schedule in @{term "traces_gmodels P"}\<close> 

lemma traces_process_assn_subset_gmodels: "traces_process_assn P \<subseteq> traces_gmodels P"
  by (auto simp add: traces_process_assn_defs traces_gmodels_def 
           intro: canonical_model_with_token)


subsection \<open>From canonical process model to operational semantics\<close>  
(********************************************************************************)

text \<open>Main transition-level lemma relating canonical process model transitions to 
operational semantics. The basic version does not take into account dead heap parts,
while the full version does.\<close>

lemma opsem_simulates_process_gmodel_basic: 
  assumes "hact (Some ({# Tok t #} + gmodel P \<rho> \<tau> ppos cpos))
                (ActBio bio v w) 
                (Some h')" 
          "t = ppos" and "ppos \<le> cpos" 
          "w \<in> Ty bio v" 
  shows "\<exists>aP pos ppos'. 
           opsem P (ActBio bio v w) (aP w) \<and>
           w = \<rho> \<tau> bio v \<and>
           ppos' = cpos @ pos @ [0] \<and> 
           h' = {# Tok ppos' #} 
                + gmodel (aP w) \<rho> (\<tau> @ [ActBio bio v w]) ppos' ppos'
                + (\<Sum>(posx, Px)\<leftarrow>tl (decompose P cpos pos). gmodel Px \<rho> \<tau> ppos posx) \<and>
           hd (decompose P cpos pos) = (cpos @ pos, bio[v].aP)"
proof -
  from assms(1) obtain ta t' g where
     "{# Tok t #} + gmodel P \<rho> \<tau> ppos cpos = {# Tok ta #} + ({#Bio bio ta v w t'#} + g)"
     "h' = {#Tok t'#} + g"
    by (cases rule: hact.cases, auto)
  then have "gmodel P \<rho> \<tau> ppos cpos = {#Bio bio t v w t'#} + g" using \<open>t = ppos\<close> 
    by (auto simp add: gmodel_token_free dest!: minsert_match)
  with assms(2,3) obtain pos aP where 
    "w = \<rho> \<tau> bio v"
    "t' = cpos @ pos @ [0]"
    "hd (decompose P cpos pos) = (cpos @ pos, bio[v].aP)"
    "g = gmodel (aP w) \<rho> (\<tau> @ [ActBio bio v w]) (cpos @ pos @ [0]) (cpos @ pos @ [0]) 
         + (\<Sum>(pos', P')\<leftarrow>tl (decompose P cpos pos). gmodel P' \<rho> \<tau> ppos pos')"
    by (auto dest: gmodel_Bio_plus_decomposition)
  then show ?thesis using \<open>h' = {#Tok t'#} + g\<close> \<open>w \<in> Ty bio v\<close> 
    by (fastforce simp add: add.assoc dest: hd_decompose_opsem) 
qed


lemma opsem_simulates_process_gmodel: 
  assumes "hact (Some ({# Tok t #} + gmodel P \<rho> \<tau> ppos cpos + g)) a (Some h')" 
          "a = ActBio bio v w" and "w \<in> Ty bio v" 
          "t = ppos" and "ppos \<le> cpos" and "dead g ppos"  
  shows "\<exists>aP pos ppos' g'. 
           opsem P (ActBio bio v w) (aP w) \<and> 
           w = \<rho> \<tau> bio v \<and>
           h' = {# Tok ppos' #} 
                + gmodel (aP w) \<rho> (\<tau> @ [ActBio bio v w]) ppos' ppos' + g' \<and>
           ppos' = cpos @ pos @ [0] \<and>
           dead g' ppos'" 
proof - 
  obtain h'' where 
    "hact (Some ({# Tok t #} + gmodel P \<rho> \<tau> ppos cpos)) a (Some h'')" "h' = h'' + g"
    using assms(1) \<open>t = ppos\<close> \<open>dead g ppos\<close>
    by (auto dest: hact_remove_dead_heap_part)
  then show ?thesis using assms(2-)
    (* SLOW: 15s *)
    by (force simp add: add.assoc dest!: opsem_simulates_process_gmodel_basic
              intro: dead_residual_gmodels
              intro!: exI[of _ "(\<Sum>(posx, Px)\<leftarrow>tl (decompose P cpos pos). 
                                   gmodel Px \<rho> \<tau> ppos posx) + g" for pos])
       
qed

text \<open>Transitions using scheduled input always go to a heap.\<close>

lemma hact_gmodel_scheduled_input: 
  assumes "hact (Some ({# Tok t #} + gmodel P \<rho> \<tau> ppos cpos + g))
                (ActBio bio v w) 
                ho"                
          "t = ppos" and "ppos \<le> cpos" and 
          "dead g ppos" and "w = \<rho> \<tau> bio v" 
  shows "ho \<noteq> None"        (* could be strengthened: w = \<rho> ppos \<longleftrightarrow> ho \<noteq> None *)
  using assms
proof (cases rule: hact.cases)
  case (ha_contradict h t0 w' t' h')
  from \<open>{#Tok t#} + gmodel P \<rho> \<tau> ppos cpos + g = {#Tok t0#} + h\<close> \<open>dead g ppos\<close>
  have "t0 = t" "h = gmodel P \<rho> \<tau> ppos cpos + g"
    by (auto simp add: gmodel_token_free add.assoc dest!: minsert_match)
  hence "Bio bio t v w' t' #\<in># gmodel P \<rho> \<tau> ppos cpos + g" using \<open>h = {#Bio bio t0 v w' t'#} + h'\<close> 
    by (auto dest: minsert_implies_elem [OF sym])
  hence "Bio bio t v w' t' #\<in># gmodel P \<rho> \<tau> ppos cpos" using \<open>t = ppos\<close> \<open>dead g ppos\<close>  
    by (auto)
  with \<open>t = ppos\<close> \<open>ppos \<le> cpos\<close> have "w' = \<rho> \<tau> bio v"
    by (auto simp add: elem_minsert_eq dest!: gmodel_Bio_plus_hd_decompose)     (* ugly! *)
  then show ?thesis using \<open>w = \<rho> \<tau> bio v\<close> \<open>w' \<noteq> w\<close> by simp
qed auto

thm gmodel_Bio_plus_hd_decompose
thm minsert_cancel_left minsert_match
thm minsert_implies_elem elem_minsert_eq

thm opsem_simulates_process_gmodel


lemma opsem_simulates_process_gmodel_scheduled_input:
  assumes 
    "hact (Some ({# Tok t #} + gmodel P \<rho> \<tau> ppos cpos + g)) a ho'"
    "a = ActBio bio v w" "w = \<rho> \<tau> bio v" 
    "t = ppos" "ppos \<le> cpos" "dead g ppos" "w \<in> Ty bio v"
  shows
    "\<exists>aP ppos' pos g'. 
        opsem P a (aP w) 
      \<and> ho' = Some ({#Tok ppos'#} + gmodel (aP w) \<rho> (\<tau> @ [a]) ppos' ppos' + g')
      \<and> dead g' ppos'
      \<and> ppos' = cpos @ pos @ [0]" 
proof -
  from assms obtain h'' where "ho' = Some h''"   
    by (auto dest!: hact_gmodel_scheduled_input)
  then show ?thesis using assms \<open>ho' = Some h''\<close>
    by (auto dest!: opsem_simulates_process_gmodel)
qed


text \<open>Define a witnessing schedule for a given trace. This schedule is defined for proper
prefixes of the given trace for which it returns the input ``predicted'' by that trace. 
It is undefined on all other traces.\<close>

fun \<rho>_wit :: "('b, 'v) atrace \<Rightarrow> ('b, 'v) isched" where
  "\<rho>_wit (ActBio bio' v' w # \<tau>) [] bio v = (if bio' = bio \<and> v' = v then w else pick (Ty bio v))" |
  "\<rho>_wit (a # \<tau>) (b # \<sigma>) bio v = (if a = b then \<rho>_wit \<tau> \<sigma> bio v else pick (Ty bio v))" |
  "\<rho>_wit _ _ bio v = pick (Ty bio v)"

lemma well_typed_\<rho>_wit:
  assumes "well_typed_atrace \<sigma>" 
  shows "well_typed_isched (\<rho>_wit \<sigma>)" 
proof (unfold well_typed_isched_def, intro allI)
  fix \<tau> bio v
  show "\<rho>_wit \<sigma> \<tau> bio v \<in> Ty bio v" using \<open>well_typed_atrace \<sigma>\<close>
    by (induction \<sigma> \<tau> bio v rule: \<rho>_wit.induct) (auto simp add: Ty_non_empty some_in_eq) 
qed

lemma \<rho>_wit_next: 
  assumes "\<tau> @ [ActBio bio v w] \<le> \<sigma>"
  shows "w = \<rho>_wit \<sigma> \<tau> bio v" 
  using assms
  by (induction \<sigma> \<tau> bio v rule: \<rho>_wit.induct) auto


text \<open>Lift relation between canonical process model and operational semantics from 
transitions to traces.\<close>

lemma opsem_simulates_process_gmodel_trace:  
  assumes 
    "heap_ES (Some ({# Tok t #} + gmodel P \<rho> \<tau>' ppos cpos + g)): 
       (Some ({# Tok t #} + gmodel P \<rho> \<tau>' ppos cpos + g)) \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> ho'"
    "\<rho> = \<rho>_wit \<sigma>" "\<tau>' @ \<tau> \<le> \<sigma>" "well_typed_atrace \<sigma>" 
    "t = ppos" "ppos \<le> cpos" "dead g ppos"
  shows 
    "\<exists>P' t' ppos' cpos' g'. 
        (opsem_ES P: P \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> P') 
      \<and> ho' = Some ({# Tok t' #} + gmodel P' \<rho> (\<tau>' @ \<tau>) ppos' cpos' + g')
      \<and> t' = ppos' \<and> ppos' \<le> cpos' \<and> dead g' ppos'"
  using assms
proof (induction \<tau> ho' rule: trace.induct)
  case trace_nil
  then show ?case by (auto simp add: \<rho>_wit_next)
next
  case (trace_snoc \<tau> ho' a ho'')
  from \<open>\<tau>' @ \<tau> @ [a] \<le> \<sigma>\<close> have "\<tau>' @ \<tau> \<le> \<sigma>"
    by (metis Prefix_Order.prefixE Sublist.prefixI append_assoc less_eq_list_def)
  then obtain P' t' ppos' cpos' g' where H:
    "opsem_ES P: P \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> P'" 
    "ho' = Some ({#Tok t'#} + gmodel P' \<rho> (\<tau>' @ \<tau>) ppos' cpos' + g')"
    "t' = ppos'" "ppos' \<le> cpos'" "dead g' ppos'" 
    using trace_snoc.IH \<open>\<rho> = \<rho>_wit \<sigma>\<close> \<open>\<tau>' @ \<tau> \<le> \<sigma>\<close> \<open>well_typed_atrace \<sigma>\<close> 
          \<open>t = ppos\<close> \<open>ppos \<le> cpos\<close> \<open>dead g ppos\<close> 
    by auto
  from H(2) trace_snoc.hyps(2) 
  have hact: "hact (Some ({#Tok t'#} + gmodel P' \<rho> (\<tau>' @ \<tau>) ppos' cpos' + g')) a ho''" 
    by (simp add: heap_ES_def)
  then obtain bio v w where "a = ActBio bio v w" and "w \<in> Ty bio v" 
    using \<open>t' = ppos'\<close> \<open>dead g' ppos'\<close> 
    by (blast dest: hact_gmodel_and_dead_has_bio_trans_only)
  then have "w = \<rho> (\<tau>' @ \<tau>) bio v" using \<open>\<rho> = \<rho>_wit \<sigma>\<close> and \<open>\<tau>' @ \<tau> @ [a] \<le> \<sigma>\<close> 
    by (auto simp add: \<rho>_wit_next)
  then obtain P'' t'' ppos'' g'' where H':
    "opsem_ES P: P' \<midarrow>a\<rightarrow> P''" 
    "ho'' = Some ({#Tok t''#} + gmodel P'' \<rho> (\<tau>' @ \<tau> @ [a]) ppos'' ppos'' + g'')"
    "t'' = ppos''" "dead g'' ppos''" 
    using hact H(3-) \<open>a = ActBio bio v w\<close> \<open>w \<in> Ty bio v\<close>
    by (auto dest: opsem_simulates_process_gmodel_scheduled_input)
  have "opsem_ES P: P \<midarrow>\<langle>\<tau> @ [a]\<rangle>\<rightarrow> P''" 
    using \<open>opsem_ES P: P \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> P'\<close> \<open>opsem_ES P: P' \<midarrow>a\<rightarrow> P''\<close> 
    by auto
  then show ?case 
    using \<open>ho'' = Some ({#Tok t''#} + gmodel P'' \<rho> (\<tau>' @ \<tau> @ [a]) ppos'' ppos'' + g'')\<close> 
          \<open>t'' = ppos''\<close> \<open>dead g'' ppos''\<close> H'
    by (auto intro!: exI [of _ P''] exI [of _ t''] exI [of _ ppos''] exI [of _ g''])
qed


text \<open>Here is the second trace inclusion.\<close>

lemma traces_gmodels_subset_opsem: "traces_gmodels P \<subseteq> traces_opsem P"
proof
  fix \<tau>
  assume A: "\<tau> \<in> traces_gmodels P"
  then have "well_typed_atrace \<tau>" by (fact well_typed_traces_gmodels)
  with A have "\<tau> \<in> traces (heap_ES (Some ({#Tok []#} + model P (\<rho>_wit \<tau>))))"
    by (auto simp add: traces_gmodels_def traces_heap_set_def well_typed_\<rho>_wit)
  then obtain ho' where 
    Tr: "heap_ES (Some ({#Tok []#} + model P (\<rho>_wit \<tau>))): 
           Some ({#Tok []#} + model P (\<rho>_wit \<tau>)) \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> ho'"
    by (auto simp add: heap_ES_def)
  then obtain P' where "opsem_ES P: P \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> P'" using \<open>well_typed_atrace \<tau>\<close>
    by (auto dest: opsem_simulates_process_gmodel_trace [where g="0", simplified])
  then show "\<tau> \<in> traces_opsem P" by auto
qed



subsection \<open>From operational semantics to embedded process assertions\<close> 
(********************************************************************************)

text \<open>Define the simulation relation between processes and heap options.\<close>

abbreviation R_proc_ho where 
  "R_proc_ho P ho \<equiv> (\<exists>t h. ho = Some ({# Tok t #} + h) \<and> h \<Turnstile> embedp P t) \<or> ho = None"


text \<open>Actions of operational semantics can be simulated by any heap model of a process.\<close>

lemma any_process_model_simulates_opsem: 
  assumes "opsem P a P'" "a = ActBio bio v w" "h \<Turnstile> embedp P t" 
  shows "\<exists>ho. hact (Some ({# Tok t #} + h)) a ho \<and> R_proc_ho P' ho"
  using assms
proof (induction rule: opsem.induct)
  case (op_prefix w bio v P)
  then obtain w' t' h1 where
    H: "h = {# Bio bio t v w' t' #} + h1" "h1 \<Turnstile> embedp (P w') t'" "w' \<in> Ty bio v"
    by (fastforce simp add: add.assoc intro: sem_leaking_left elim: sem_elims)
  show ?case
  proof (cases "w = w'")
    case True
    then show ?thesis using H \<open>w \<in> Ty bio v\<close> by (auto intro: ha_bio)
  next
    case False
    then show ?thesis using H \<open>w \<in> Ty bio v\<close> by (auto intro: ha_contradict)  
  qed
next
  case (op_choice1 P a P' Q)
  then obtain ho where
    H1: "hact (Some ({#Tok t#} + h)) a ho" and
    H2: "R_proc_ho P' ho"
    by (auto elim: sem.cases intro: sem_leaking)
  show ?case 
  proof (cases "ho \<noteq> None")
    case True
    with H2 obtain t' h' where "ho = Some ({#Tok t'#} + h')" "h' \<Turnstile> embedp P' t'" by clarsimp
    with H1 show ?thesis by auto
  next
    case False
    with H1 show ?thesis by auto
  qed
next
  case (op_choice2 Q a Q' P)
  then obtain ho where
    H1: "hact (Some ({#Tok t#} + h)) a ho" and
    H2: "R_proc_ho Q' ho"
    by (auto elim: sem.cases intro: sem_leaking)
  show ?case 
  proof (cases "ho \<noteq> None")
    case True
    with H2 obtain t' h' where "ho = Some ({#Tok t'#} + h')" "h' \<Turnstile> embedp Q' t'" by clarsimp
    with H1 show ?thesis by auto
  next
    case False
    with H1 show ?thesis by auto
  qed
qed


lemma traces_opsem_subset_heap_option:     (* with generalized simulation relation *)
  assumes "R_proc_ho P ho"
  shows "traces_opsem P \<subseteq> traces (heap_ES ho)"
proof (rule simulation_rule_id[where R=R_proc_ho])
  fix P0
  assume "init (opsem_ES P) P0"
  then show "\<exists>ho0. init (heap_ES ho) ho0 \<and> R_proc_ho P0 ho0" by (simp add: heap_ES_def assms)
next
  fix P1 ho1 a P2
  assume "R_proc_ho P1 ho1" and "opsem_ES P: P1 \<midarrow>a\<rightarrow> P2"
  then show "\<exists>ho2. (heap_ES ho: ho1\<midarrow>a\<rightarrow> ho2) \<and> R_proc_ho P2 ho2"
  proof (cases a)
    case (ActBio bio v w)
    from \<open>R_proc_ho P1 ho1\<close> 
    consider t h where "ho1 = Some ({# Tok t #} + h)" "h \<Turnstile> embedp P1 t" | "ho1 = None" by auto
    then show ?thesis 
    proof cases
      case 1
      then show ?thesis using \<open>opsem_ES P: P1 \<midarrow>a\<rightarrow> P2\<close> \<open>a = ActBio bio v w\<close>
        by (auto simp add: heap_ES_trans intro: any_process_model_simulates_opsem)
    next
      case 2
      then show ?thesis using \<open>opsem_ES P: P1 \<midarrow>a\<rightarrow> P2\<close> \<open>a = ActBio bio v w\<close>
        by (auto simp add: heap_ES_trans intro: exI[of _ None] ha_chaos opsem_well_typed_act)
    qed
  next
    case Epsilon 
    then show ?thesis using \<open>opsem_ES P: P1 \<midarrow>a\<rightarrow> P2\<close>
      by (auto simp add: heap_ES_trans dest: opsem_bio_only)
  qed
qed

lemma traces_opsem_subset_process: "traces_opsem P \<subseteq> traces_process_assn P" 
  by (fastforce simp add: traces_process_assn_defs add.assoc intro: sem_leaking
                elim!: traces_opsem_subset_heap_option [THEN [2] rev_subsetD] elim: sem_elims)


subsection \<open>Main result\<close>
(********************************************************************************)

theorem trace_equivalences:
  "traces_opsem P = traces_gmodels P" "traces_gmodels P = traces_process_assn P"
  by (auto intro: traces_opsem_subset_process traces_process_assn_subset_gmodels
                  traces_gmodels_subset_opsem subset_trans
             del: subsetI)


text \<open>This intro rule provides a convenient way of proving trace equivalence of the embedding of 
       two trace-equivalent processes.\<close>

lemma traces_assn_embedI:
  assumes "traces_opsem P1 = traces_opsem P2"
  shows "traces_process_assn P1 = traces_process_assn P2"
  using assms
  by (simp add: trace_equivalences)

end

end