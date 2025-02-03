(*
  Title:   Composition of event systems for Butler-style compositional refinement
  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
  Version: Isabelle/HOL 2020
  Date:    2019-2020
  ID:      $Id: Composition.thy 152662 2020-08-06 09:54:41Z tklenze $
*)

section \<open>Event System Composition\<close>

text\<open>In this theory, we define the composition of two event systems (and of two traces). We use a
construction similar to the shared-event decomposition of Silva and Butler, but generalize their 
results and prove them sound.

We construct composition from product, restriction and relabeling operations.

Reference:
Renato Silva and Michael J. Butler. 2010. Shared Event Composition/Decomposition in Event-B. In Formal Methods for
Components and Objects - 9th International Symposium, FMCO 2010, Graz, Austria, November 29 - December 1, 2010. Revised
Papers (Lecture Notes in Computer Science), Bernhard K. Aichernig, Frank S. de Boer, and Marcello M. Bonsangue (Eds.),
Vol. 6957. Springer, 122–141.\<close>

theory Composition
  imports 
    Main Event_Systems "HOL-Library.Adhoc_Overloading"
begin

consts 
  COMP :: "'a \<Rightarrow> ('f \<rightharpoonup> 'g) \<Rightarrow> 'b \<Rightarrow> 'c"  ("(3_ \<parallel>_ _)" [90, 90, 90] 90)
  PROD :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"  ("(2_ \<Otimes> _)" [90, 90] 90)
  RESTR :: "'a \<Rightarrow> 'e set \<Rightarrow> 'a"   ("(2_\<restriction>_)" [100, 100] 100)
  RELABEL :: "'a \<Rightarrow> ('f \<Rightarrow> 'g) \<Rightarrow> 'b"   ("(2_\<lceil>_\<rceil>)" [95, 95] 95)


subsection \<open>Product\<close>
(******************************************************************************)

subsubsection \<open>Product on trace properties\<close>
(******************************************************************************)

definition traces_prod where
  "traces_prod T U \<equiv> {zip \<tau> \<sigma> | \<tau> \<sigma>. \<tau> \<in> T \<and> \<sigma> \<in> U \<and> length \<tau> = length \<sigma>}"

adhoc_overloading PROD traces_prod

lemma traces_prodI [intro]: 
  "\<lbrakk>\<tau> \<in> T; \<sigma> \<in> U; length \<tau> = length \<sigma>; \<xi> = zip \<tau> \<sigma> \<rbrakk> \<Longrightarrow> \<xi> \<in> T \<Otimes> U"
by (auto simp add: traces_prod_def)

lemma traces_prodE [elim]: 
  "\<lbrakk> \<xi> \<in> T \<Otimes> U;
     \<And> \<tau> \<sigma> . \<lbrakk> \<tau> \<in> T; \<sigma> \<in> U; length \<tau> = length \<sigma>; \<xi> = zip \<tau> \<sigma> \<rbrakk> \<Longrightarrow> P \<rbrakk> 
 \<Longrightarrow> P"
  by (auto simp add: traces_prod_def)

subsubsection \<open>Product on event systems\<close> 
(******************************************************************************)

definition ES_prod :: "('e, 's) ES \<Rightarrow> ('f, 't) ES \<Rightarrow> ('e * 'f, 's * 't) ES" where
  "ES_prod E F = \<lparr> 
     init = (\<lambda>(s, t). init E s \<and> init F t), 
     trans = (\<lambda>(s, t) g (s', t'). \<exists>e f. (e, f) = g \<and> (E: s \<midarrow>e\<rightarrow> s') \<and> (F: t \<midarrow>f\<rightarrow> t'))
  \<rparr>"

adhoc_overloading PROD ES_prod

lemma ES_prod_init_eq [simp]: "init (E \<Otimes> F) (s, t) \<longleftrightarrow> init E s \<and> init F t"
  by (simp add: ES_prod_def)

lemma ES_prod_trans_eq [simp]: 
  "((E \<Otimes> F): (s, t) \<midarrow>(e, f)\<rightarrow> (s', t')) \<longleftrightarrow> (E: s \<midarrow>e\<rightarrow> s') \<and> (F: t \<midarrow>f\<rightarrow> t')"
  by (auto simp add: ES_prod_def)

lemma traces_from_deprod:
  "((E \<Otimes> F): (s, t) \<midarrow>\<langle>\<xi>\<rangle>\<rightarrow> u) \<longleftrightarrow> 
      (\<exists>\<tau> \<sigma> s' t'. (E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s') \<and> (F: t \<midarrow>\<langle>\<sigma>\<rangle>\<rightarrow> t') \<and>
                   length \<tau> = length \<sigma> \<and> u = (s', t') \<and> \<xi> = zip \<tau> \<sigma>)"   (is "?A \<longleftrightarrow> ?B")
proof
  assume "?A" thus "?B"
    by (induction \<xi> u rule: trace.induct)
       (fastforce simp add: prod_def intro: exI[of _ "\<tau> @ [e]" for \<tau> e])+ 
next
  assume "?B" then obtain \<tau> \<sigma> s'' t'' where
    prem: "E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s''" "F: t \<midarrow>\<langle>\<sigma>\<rangle>\<rightarrow> t''" "length \<tau> = length \<sigma>" 
          "u = (s'', t'')" "\<xi> = zip \<tau> \<sigma>"
    by auto
  from prem(1-3) have "\<lbrakk>E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s''; F: t \<midarrow>\<langle>\<sigma>\<rangle>\<rightarrow> t''; length \<tau> = length \<sigma>\<rbrakk> 
                        \<Longrightarrow> E \<Otimes> F: (s, t) \<midarrow>\<langle>zip \<tau> \<sigma>\<rangle>\<rightarrow> (s'', t'')"
    by (induct \<tau> s'' \<sigma> t'' rule: trace_induct2) (auto simp add: prem)
  thus "?A" by(simp add: prem)
qed

theorem traces_prod_eq: "traces (E \<Otimes> F) = (traces E) \<Otimes> (traces F)"
  by(fastforce simp add: traces_def traces_from_deprod)


(******************************************************************************)
subsection \<open>Relabeling\<close>
(******************************************************************************)

subsubsection \<open>Relabeling on trace properties\<close>
(******************************************************************************)

definition traces_relabel where
  "traces_relabel T f \<equiv> { map f \<tau> | \<tau> . \<tau> \<in> T}"

adhoc_overloading RELABEL traces_relabel

lemma traces_relabelI [intro]: 
  "\<lbrakk>\<tau> \<in> T; \<xi> = map f \<tau> \<rbrakk> \<Longrightarrow> \<xi> \<in> T\<lceil>f\<rceil>"
  by (auto simp add: traces_relabel_def)

lemma traces_relabelE [elim]:
  "\<lbrakk>\<xi> \<in> T\<lceil>f\<rceil>; \<And> \<tau> . \<lbrakk>\<tau> \<in> T; \<xi> = map f \<tau> \<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp add: traces_relabel_def)

subsubsection \<open>Relabeling on event systems\<close> 
(******************************************************************************)

definition ES_relabel :: "('e, 's) ES \<Rightarrow> ('e \<Rightarrow> 'f) \<Rightarrow> ('f, 's) ES"
where
  "ES_relabel E f = \<lparr> 
     init = init E, 
     trans = (\<lambda>s e s'. \<exists> e' . (E: s \<midarrow>e'\<rightarrow> s') \<and> f e' = e)
  \<rparr>"

adhoc_overloading RELABEL ES_relabel

lemma ES_relabel_init_eq [simp]: "init (E\<lceil>f\<rceil>) s \<longleftrightarrow> init E s"
  by (simp add: ES_relabel_def)

lemma ES_relabel_trans_eq [simp]: 
  "(E\<lceil>f\<rceil>: s \<midarrow>g\<rightarrow> s') \<longleftrightarrow> (\<exists>e. f e = g \<and> E: s \<midarrow>e\<rightarrow> s')"
  by (auto simp add: ES_relabel_def)

lemma ES_relabel_trace: "(E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s') \<Longrightarrow> (E\<lceil>f\<rceil>: s \<midarrow>\<langle>map f \<tau>\<rangle>\<rightarrow> s')"
  by (induct \<tau> s' rule: trace.induct)
     (auto simp add: ES_relabel_def intro!: trace_snoc)

lemma ES_relabel_trace_reverse: 
  assumes "E\<lceil>f\<rceil>: s \<midarrow>\<langle>\<tau>'\<rangle>\<rightarrow> s'"
  shows "\<exists> \<tau> . \<tau>' = map f \<tau> \<and> E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'"
  using assms
proof (induct \<tau>' s' rule: trace.induct)
  case (trace_snoc \<tau> s' e s'')
  then show ?case by (auto intro: exI [of _ "\<tau>' @ [e]" for \<tau>' e])
qed simp

theorem traces_relabel_eq: "traces (E\<lceil>f\<rceil>) = (traces E)\<lceil>f\<rceil>"
  by(fastforce simp add: traces_def intro: ES_relabel_trace dest!: ES_relabel_trace_reverse)


(******************************************************************************)
subsection \<open>Restriction\<close>
(******************************************************************************)

subsubsection \<open>Restriction on trace properties\<close> 
(******************************************************************************)

abbreviation trace_restr :: "'e trace \<Rightarrow> 'e set \<Rightarrow> 'e trace" where
  "trace_restr \<tau> S \<equiv> takeWhile (\<lambda>e. e \<in> S) \<tau>"

adhoc_overloading RESTR trace_restr 

value "[''a'', ''b'', ''a'', ''c''] \<restriction> {''a'', ''c''}"

lemma trace_restr_unrestricted [simp]: "set \<tau> \<subseteq> S \<Longrightarrow> \<tau>\<restriction>S = \<tau>"
  by (auto)

lemma trace_restr_snoc_eq: 
  "(\<sigma> @ [e])\<restriction>S = (if set \<sigma> \<subseteq> S then (if e \<in> S then \<sigma> @ [e] else \<sigma>) else \<sigma>\<restriction>S)"
by (induction \<sigma>) simp_all


definition traces_restr :: "'e trace set \<Rightarrow> 'e set \<Rightarrow> 'e trace set" where
  "traces_restr T S = (\<lambda>\<tau>. \<tau>\<restriction>S)`T"

lemmas traces_restr_defs = traces_restr_def image_def

adhoc_overloading RESTR traces_restr

text \<open>The following lemmas make use of both @{term "trace_restr"} and @{term "traces_restr"}.\<close>

lemma traces_restrI [intro]: "\<lbrakk> \<sigma> \<in> T; \<tau> = \<sigma>\<restriction>S \<rbrakk> \<Longrightarrow> \<tau> \<in> T\<restriction>S"
  by (auto simp add: traces_restr_defs)

lemma traces_restrE [elim]: "\<lbrakk> \<tau> \<in> T\<restriction>S; \<And>\<sigma>. \<lbrakk> \<sigma> \<in> T; \<tau> = \<sigma>\<restriction>S \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto simp add: traces_restr_defs)

lemma traces_restr_Nil [simp, intro!]: "[] \<in> T \<Longrightarrow> [] \<in> T\<restriction>S"
  by (force simp add: traces_restr_defs)


subsubsection \<open>Restriction on event systems\<close> 
(******************************************************************************)

definition ES_restrict :: "('e, 's) ES \<Rightarrow> 'e set \<Rightarrow> ('e, 's) ES" where
  "ES_restrict E S = \<lparr> 
     init = init E, 
     trans = \<lambda>s e s'. (E: s \<midarrow>e\<rightarrow> s') \<and> e \<in> S 
  \<rparr>"

adhoc_overloading RESTR ES_restrict

lemma ES_restrict_init_eq [simp]: "init (E\<restriction>S) s \<longleftrightarrow> init E s"
  by (auto simp add: ES_restrict_def)

lemma ES_restrict_trans_eq [simp]: "((E\<restriction>S): t \<midarrow>e\<rightarrow> u) \<longleftrightarrow> (E: t \<midarrow>e\<rightarrow> u) \<and> e \<in> S"
  by (auto simp add: ES_restrict_def)

lemma traces_from_restr_eq [simp]: 
  "((E\<restriction>S): s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> t) \<longleftrightarrow> (E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> t) \<and> set \<tau> \<subseteq> S"  
proof (intro iffI; (elim conjE)?)
  assume "(E\<restriction>S): s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> t"
  then show "(E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> t) \<and> set \<tau> \<subseteq> S"
    by (induction \<tau> t rule: trace.induct) auto
next
  assume "(E: s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> t)" "set \<tau> \<subseteq> S"
  then show "(E\<restriction>S): s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> t"
    by (induction \<tau> t rule: trace.induct) auto 
qed

lemma traces_restriction_eq: "traces (E\<restriction>S) = (traces E)\<restriction>S"
proof (intro equalityI subsetI; elim tracesE traces_restrE)
  fix \<tau> s s'
  assume "(E\<restriction>S): s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'" "init (E\<restriction>S) s"
  thus "\<tau> \<in> (traces E)\<restriction>S"
  proof (induct \<tau> s' rule: trace.induct)
    case (trace_snoc \<tau> s' e s'') 
    from \<open>(E\<restriction>S): s \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> s'\<close> \<open>(E\<restriction>S): s' \<midarrow>e\<rightarrow> s''\<close>
    have "E: s \<midarrow>\<langle>\<tau> @ [e]\<rangle>\<rightarrow> s''" and "e \<in> S"  and "set \<tau> \<subseteq> S" 
      by (auto simp add: traces_from_restr_eq)
    then show ?case using \<open>init (E\<restriction>S) s\<close> 
      by (auto intro!: traces_restrI [where \<sigma>="\<tau> @ [e]"])
  qed simp
next
  fix \<tau> \<sigma> s s'
  assume "E: s \<midarrow>\<langle>\<sigma>\<rangle>\<rightarrow> s'" "init E s" "\<tau> = \<sigma>\<restriction>S" 
  thus "\<tau> \<in> traces (E\<restriction>S)"
  proof (induction \<sigma> s' arbitrary: \<tau> rule: trace.induct)
    case (trace_snoc \<sigma> s' e s'') 
    then show ?case 
      by (fastforce simp add: trace_restr_snoc_eq)
  qed simp
qed


(******************************************************************************)
subsection \<open>Parallel composition\<close>
(******************************************************************************)

subsubsection \<open>Parallel composition on trace properties\<close> 
(******************************************************************************)

definition 
   traces_comp :: "'e trace set \<Rightarrow> ('e * 'f \<rightharpoonup> 'g) \<Rightarrow> 'f trace set \<Rightarrow> 'g trace set" 
where
  "traces_comp T \<chi> U \<equiv> ((T \<Otimes> U) \<restriction> (dom \<chi>)) \<lceil> (the o \<chi>) \<rceil>"

adhoc_overloading COMP traces_comp

lemma traces_compI [intro]:
  "\<lbrakk> \<tau> \<in> T; \<sigma> \<in> U; length \<tau> = length \<sigma>; \<xi>'' = zip \<tau> \<sigma>; \<xi>' = takeWhile (\<lambda>x . x \<in> (dom \<chi>)) \<xi>'';
     \<xi> = map (the o \<chi>) \<xi>' \<rbrakk> 
    \<Longrightarrow> \<xi> \<in> T \<parallel>\<chi> U"
by (auto simp add: traces_comp_def)

lemma traces_compE [elim]:
  "\<lbrakk> \<xi> \<in> T \<parallel>\<chi> U;
     \<And>\<tau> \<sigma> \<xi>'' \<xi>'. 
       \<lbrakk> \<tau> \<in> T; \<sigma> \<in> U; length \<tau> = length \<sigma>; \<xi>'' = zip \<tau> \<sigma>; \<xi>' = takeWhile (\<lambda>x . x \<in> (dom \<chi>)) \<xi>'';
         \<xi> = map (the o \<chi>) \<xi>'\<rbrakk> 
   \<Longrightarrow> P \<rbrakk> 
 \<Longrightarrow> P"
  by (fastforce simp add: traces_comp_def)

lemma traces_comp_Nil: 
  assumes  "[] \<in> T" "[] \<in> U"
  shows "[] \<in> T \<parallel>\<chi> U" 
  using assms by (auto)

lemma traces_comp_monotone: 
  assumes "T' \<subseteq> T" and "U' \<subseteq> U"
  shows "T' \<parallel>\<chi> U' \<subseteq> T \<parallel>\<chi> U" using assms
by (fastforce)


subsubsection \<open>Composition of event systems\<close> 
(******************************************************************************)

text \<open>Define composed system.\<close> 

definition 
   ES_compose :: "('e, 's) ES \<Rightarrow> ('e * 'f \<rightharpoonup> 'g) \<Rightarrow> ('f, 't) ES \<Rightarrow> ('g, 's * 't) ES"
where
  "ES_compose E \<chi> F \<equiv> ((E \<Otimes> F) \<restriction> (dom \<chi>)) \<lceil> (the o \<chi>) \<rceil>"

adhoc_overloading COMP ES_compose

lemma ES_compose_init_eq [simp]: 
  "init (E \<parallel>\<chi> F) (s, t) \<longleftrightarrow> init E s \<and> init F t"
  by (auto simp add: ES_compose_def)

lemma ES_compose_trans_eq [simp]: 
  "((E \<parallel>\<chi> F): (s, t) \<midarrow>g\<rightarrow> (s', t')) \<longleftrightarrow> 
   (\<exists>e f. \<chi> (e, f) = Some g \<and> (E: s \<midarrow>e\<rightarrow> s') \<and> (F: t \<midarrow>f\<rightarrow> t'))"
  by (force simp add: ES_compose_def)

text \<open>The following theorem together with the monotonicity of trace property composition
enables compositional refinement.\<close> 

theorem trace_composition: "traces (E \<parallel>\<chi> F) = (traces E) \<parallel>\<chi> (traces F)"
  by (simp add: ES_compose_def traces_comp_def traces_prod_eq traces_relabel_eq 
                traces_restriction_eq o_def)

corollary compositional_refinement: 
  "\<lbrakk>traces(E') \<subseteq> traces(E); traces(F') \<subseteq> traces(F)\<rbrakk> \<Longrightarrow> traces(E'\<parallel>\<chi> F') \<subseteq> traces(E \<parallel>\<chi> F)"
  by(auto simp add: traces_comp_monotone trace_composition)

end



