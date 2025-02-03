(*
  Title:   Decomposition
  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
           Tobias Klenze (tobias.klenze@inf.ethz.ch)
  Version: Isabelle/HOL 2020
  Date:    2019-2020
  ID:      $Id: Decomposition.thy 152662 2020-08-06 09:54:41Z tklenze $
*)

section \<open>Decomposition\<close>
text \<open>In this section we provide rules for decomposing an event system into a system and an environment part.\<close>

theory Decomposition
  imports 
    Composition Interleaving  
begin

lemma bij_inv_self: "bij \<rho> \<Longrightarrow> inv \<rho> (\<rho> x) = x"
  by (simp add: bij_betw_def)

lemma decomposition_env_system_equiv_upto [consumes 0, case_names surj bij init trans]:

fixes \<S> :: "('g, 'u) ES"               \<comment> \<open>monolithic system\<close>
  and \<E> :: "('e, 's) ES"               \<comment> \<open>environment\<close>
  and \<C> :: "('f, 't) ES"               \<comment> \<open>component(s)\<close>
  and \<chi> :: "'e \<times> 'f \<rightharpoonup> 'g"             \<comment> \<open>synchronization map\<close>
  and \<rho> :: "'s \<times> 't \<Rightarrow> 'u"             \<comment> \<open>bijection between state spaces\<close>

assumes \<chi>_surj_on_trans: "\<And>u g u'.
          \<lbrakk> \<S>: u \<midarrow>g\<rightarrow> u'; reach \<S> u \<rbrakk> \<Longrightarrow> \<exists>e f. \<chi> (e, f) = Some g"
    and \<rho>_bij: "bij \<rho>"
    and init: "\<And>s t u. \<rho> (s, t) = u \<Longrightarrow> init \<S> u \<longleftrightarrow> init \<E> s \<and> init \<C> t"
    and trans: "\<And>e f g s t s' t'. 
          \<lbrakk> \<chi> (e, f) = Some g \<rbrakk> \<Longrightarrow>
            (\<S>: \<rho> (s, t) \<midarrow>g\<rightarrow> \<rho> (s', t')) \<longleftrightarrow> (\<E>: s \<midarrow>e\<rightarrow> s') \<and> (\<C>: t \<midarrow>f\<rightarrow> t')"
shows 
  "traces \<S> = traces (\<E> \<parallel>\<chi> \<C>)" 

proof (intro equalityI simulation_soundness_id)
  show "\<S> \<sqsubseteq>\<^sub>id (\<E> \<parallel>\<chi> \<C>)"
  proof (rule simulate_ES_fun[where h="inv \<rho>" and \<pi>=id, simplified])
    fix u0
    assume "init \<S> u0"
    then show "init (\<E> \<parallel>\<chi> \<C>) (inv \<rho> u0)"       
      by (cases "inv \<rho> u0") (metis ES_compose_init_eq \<rho>_bij bij_inv_eq_iff init) 
  next
    fix u g u'
    assume "\<S>: u\<midarrow>g\<rightarrow> u'" and "reach \<S> u" (* and "reach (\<E> \<parallel>\<chi> \<C>) u" *)
    with \<chi>_surj_on_trans obtain e f where "\<chi> (e, f) = Some g" 
      by fastforce
    moreover obtain l r l' r' where u_def: "u = \<rho> (l, r)" "u' = \<rho> (l', r')"
      using \<open>bij \<rho>\<close> old.prod.exhaust bij_pointE by metis
    ultimately have "(\<E> \<parallel>\<chi> \<C>): (l, r)\<midarrow>g\<rightarrow>(l', r')" 
      using \<open>\<S>: u\<midarrow>g\<rightarrow> u'\<close> by(auto simp add: trans) 
    then show "\<E> \<parallel>\<chi> \<C>: inv \<rho> u\<midarrow>g\<rightarrow> inv \<rho> u'"
      using \<open>bij \<rho>\<close> by (auto simp add: u_def bij_inv_self) 
  qed
next
  show "(\<E> \<parallel>\<chi> \<C>) \<sqsubseteq>\<^sub>id \<S>"
  proof (rule simulate_ES_fun[where h=\<rho> and \<pi>=id, simplified])
    fix u0
    assume "init (\<E> \<parallel>\<chi> \<C>) u0"
    then show "init \<S> (\<rho> u0)"
      by (cases u0) (auto simp add: init)
  next
    fix u g u'
    assume "(\<E> \<parallel>\<chi> \<C>): u\<midarrow>g\<rightarrow> u'" and "reach (\<E> \<parallel>\<chi> \<C>) u" and "reach \<S> (\<rho> u)"
    then show "\<S>: \<rho> u\<midarrow>g\<rightarrow> \<rho> u'"
      by (cases u, cases u') (auto simp add: trans)
  qed
qed


lemma decomposition_env_system_equiv [consumes 0, case_names surj init trans]:

fixes \<S> :: "('g, 's \<times> 't) ES"         \<comment> \<open>monolithic system\<close>
  and \<E> :: "('e, 's) ES"               \<comment> \<open>environment\<close>
  and \<C> :: "('f, 't) ES"               \<comment> \<open>family of components\<close>
  and \<chi> :: "'e \<times> 'f \<rightharpoonup> 'g"            \<comment> \<open>synchronization map\<close>

assumes \<chi>_surj_on_trans: "\<And>u g u'. 
          \<lbrakk> \<S>: u \<midarrow>g\<rightarrow> u'; reach \<S> u \<rbrakk> \<Longrightarrow> \<exists>e f. \<chi> (e, f) = Some g"
    and init: "\<And>s t. 
           init \<S> (s, t) \<longleftrightarrow> init \<E> s \<and> init \<C> t"
    and trans: "\<And>e f g s t s' t'. 
          \<chi> (e, f) = Some g \<Longrightarrow>
            (\<S>: (s, t) \<midarrow>g\<rightarrow> (s', t')) \<longleftrightarrow> (\<E>: s \<midarrow>e\<rightarrow> s') \<and> (\<C>: t \<midarrow>f\<rightarrow> t')"
shows 
  "traces \<S> = traces (\<E> \<parallel>\<chi> \<C>)" 
  using assms by(elim decomposition_env_system_equiv_upto[where \<rho>=id]) auto


text \<open>Decompose an event system into an environment and a family of components.\<close>

text \<open>FIXME: order of env and system should probably be swapped, as this is the preferred
order also if there are several component types.\<close>

lemma decomposition_comp_family_env_equiv:

fixes \<S> :: "('g, ('i \<Rightarrow> 'l) \<times> 's) ES"         \<comment> \<open>monolithic system\<close>
  and \<E> :: "('f, 's) ES"                      \<comment> \<open>environment\<close>
  and \<C> :: "'i \<Rightarrow> ('e, 'l) ES"                \<comment> \<open>family of components\<close>
  and \<chi> :: "('i \<times> 'e) \<times> 'f \<rightharpoonup> 'g"            \<comment> \<open>synchronization map\<close>

assumes \<chi>_surj_on_trans: "\<And>u g u'. 
          \<lbrakk> \<S>: u \<midarrow>g\<rightarrow> u'; reach \<S> u \<rbrakk> \<Longrightarrow> \<exists>i e f. \<chi> ((i, e), f) = Some g"
    and init: "\<And>s t. 
           init \<S> (s, t) \<longleftrightarrow> (\<forall>i. init (\<C> i) (s i)) \<and> init \<E> t"
    and trans: "\<And>i e f g s t s' t'. 
          \<chi> ((i, e), f) = Some g \<Longrightarrow>
            (\<S>: (s, t) \<midarrow>g\<rightarrow> (s', t')) \<longleftrightarrow> 
            (\<C> i: s i \<midarrow>e\<rightarrow> s' i) \<and> (\<E>: t \<midarrow>f\<rightarrow> t') \<and> (\<forall>j. j \<noteq> i \<longrightarrow> s' j = s j)"
shows 
  "traces \<S> = traces ((\<parallel>\<parallel> \<C>) \<parallel>\<chi> \<E>)" 

proof (intro equalityI simulation_soundness_id)
  show "\<S> \<sqsubseteq>\<^sub>id (\<parallel>\<parallel> \<C> \<parallel>\<chi> \<E>)"
  proof (rule simulate_ES_fun[where h=id and \<pi>=id, simplified])
    fix u0
    assume "init \<S> u0"
    then show "init (\<parallel>\<parallel> \<C> \<parallel>\<chi> \<E>) u0"
      by (cases u0) (auto simp add: init)
  next
    fix u g u'
    assume "\<S>: u\<midarrow>g\<rightarrow> u'" and "reach \<S> u" (* and "reach (\<parallel>\<parallel> \<C> \<parallel>\<chi> \<E>) u" *)
    with \<chi>_surj_on_trans obtain i e f where "\<chi> ((i, e), f) = Some g" 
      by fastforce
    then show "(\<parallel>\<parallel> \<C> \<parallel>\<chi> \<E>): u\<midarrow>g\<rightarrow> u'" using \<open>\<S>: u\<midarrow>g\<rightarrow> u'\<close>
      by (cases u, cases u') (auto simp add: trans)
  qed
next
  show "(\<parallel>\<parallel> \<C> \<parallel>\<chi> \<E>) \<sqsubseteq>\<^sub>id \<S>"
  proof (rule simulate_ES_fun[where h=id and \<pi>=id, simplified])
    fix u0
    assume "init (\<parallel>\<parallel> \<C> \<parallel>\<chi> \<E>) u0"
    then show "init \<S> u0"
      by (cases u0) (auto simp add: init)
  next
    fix u g u'
    assume "(\<parallel>\<parallel> \<C> \<parallel>\<chi> \<E>): u\<midarrow>g\<rightarrow> u'" and "reach (\<parallel>\<parallel> \<C> \<parallel>\<chi> \<E>) u" and "reach \<S> u"
    then show "\<S>: u\<midarrow>g\<rightarrow> u'"
      by (cases u, cases u') (auto simp add: trans)
  qed
qed


end