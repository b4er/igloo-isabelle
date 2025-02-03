(*
  Title:  Preliminaries
  Author:  Christoph Sprenger (sprenger@inf.ethz.ch)
           Tobias Klenze (tobias.klenze@inf.ethz.ch)
  Version: Isabelle/HOL 2020
  Date:    2019-2020
  ID:      $Id: Preliminaries.thy 152662 2020-08-06 09:54:41Z tklenze $
*)
chapter \<open>Igloo Theory: Linking Separation Logic, Processes, and Event Systems\<close>
text\<open>
This chapter presents our main theoretical contribution and the core part of our methodology:
the sound linking of Event Systems and Separation Logic, via the intermediate formalism of Processes.

The starting point of the translation of an Event System into an I/O specification in Separation
Logic is a system decomposed into several components, or component families, and the environment.
Each component type is separately converted into a trace-equivalent I/O spec.

After some short preliminary definitions we begin the main part by formally defining I/O Processes 
and linking them with Event Systems. Then we define our I/O Separation Logic and a translation from
I/O Processes. In a final step we prove the trace equivalence of Event Systems and their embedding
into Separation Logic.

In some places, the Isabelle formalization deviates slightly from the paper. These differences are 
technical in nature and should not have any impact on the general methodology or the soundness results. 
\begin{itemize}
\item In our Isabelle formalization, Event Systems consist of an initial state predicate, and a 
transition function. In the paper, the initial state predicate is omitted. Instead, the initial 
states are passed to functions working with Event Systems explicitly. For instance, @{text "traces(E, I)"} 
where @{text I} is a set of initial states.
\item In the Isabelle formalization, we define all but the most concrete model directly as event 
systems. Only the most concrete system model is defined as an I/O guarded event system. By contrast, 
the paper uses the uniform syntax of guarded event systems for presentation reasons.
\item In our formalization, both output and input parameters of events are over some shared type 
@{text "'v"} which is countable. In the leadership election example, we instantiate @{text "'v"} 
with a datatype val which can represent three different types: Unit (used when the parameter is 
not applicable, e.g., when no output or no input is performed), Msg (a single node identifier) and 
AddrMsg (a node identifier and an address). In the paper, we use tuples and leave out the Unit 
parameter. The other case studies are similar.
\item As shortly sketched out in the paper, we enforce a typing discipline on inputs by using a 
typing function. In our formalization this is implemented via a Typing context. This context gives 
for every combination of bio and output value the type of the input values that are expected. Note 
that this Typing context does not appear in the predicate of the generated I/O spec; it is, however, 
an assumption on the library and thus part of the environment assumptions. A user of our framework 
should ensure that the I/O library does indeed always return a well-typed input.
\end{itemize}
\<close>
(********************************************************************************)
section \<open>Preliminaries\<close>
(********************************************************************************)
theory Preliminaries
  imports 
    Event_Systems
    "HOL-Library.Countable_Set"
begin


subsection \<open>Pick an element from a set\<close> 
(********************************************************************************)

definition pick :: "'a set \<Rightarrow> 'a" where
  "pick A \<equiv> SOME x. x \<in> A"

lemma pick_mem [simp]: "x \<in> A \<Longrightarrow> pick A \<in> A"
  by (auto simp add: pick_def intro: someI)

lemma pick_non_empty [simp]: "A \<noteq> {} \<Longrightarrow> pick A \<in> A"
  by (auto simp add: pick_def intro: someI)


subsection \<open>Upwards-closed sets.\<close>
(********************************************************************************)

definition upset :: "'a::order \<Rightarrow> 'a set" where
  "upset x = {y. x \<le> y}"

lemma upset_elem [simp, intro]: "x \<in> upset x"
  by (simp add: upset_def)

lemma upset_antitone: "x \<le> y \<Longrightarrow> upset y \<subseteq> upset x"
by (auto simp add: upset_def)


subsection \<open>Actions and typing\<close>
(********************************************************************************)

text \<open>Type of actions. These will label transitions.\<close>

datatype ('b, 'v) action = 
  ActBio 'b 'v 'v | 
  Epsilon

type_synonym ('b, 'v) atrace = "('b, 'v) action trace"


text \<open>The typing restricts the possible input values for each basic I/O operation and output 
value. It can also be read as specifying and I/O relation for each basic I/O operation.\<close>

locale Typing = 
  fixes Ty :: "'b::finite \<Rightarrow> 'v::countable \<Rightarrow> 'v set" 
  assumes Ty_non_empty: "Ty bio v \<noteq> {}"
begin

fun well_typed_act :: "('b, 'v) action \<Rightarrow> bool" where
  "well_typed_act (ActBio bio v w) \<longleftrightarrow> (w \<in> Ty bio v)" |
  "well_typed_act Epsilon \<longleftrightarrow> True"

definition well_typed_atrace :: "('b, 'v) atrace \<Rightarrow> bool" where
  "well_typed_atrace \<tau> = (\<forall>a \<in> set \<tau>. well_typed_act a)"

lemma well_typed_atrace_empty [simp, intro!]: "well_typed_atrace []"
  by (simp add: well_typed_atrace_def)

lemma well_typed_atrace_snoc [simp]:
  "well_typed_atrace (\<tau> @ [e]) \<longleftrightarrow> well_typed_atrace \<tau> \<and> well_typed_act e"
  by (auto simp add: well_typed_atrace_def)

lemma well_typed_atrace_cons [simp]:
  "well_typed_atrace (e # \<tau>) \<longleftrightarrow> well_typed_atrace \<tau> \<and> well_typed_act e"
  by (auto simp add: well_typed_atrace_def)

end

end