(*
  Title:   Event Composition uses a generic event datatype to distinguish internal and "real" IO events.
  Author:  Tobias Klenze (tobias.klenze@inf.ethz.ch)
  Version: Isabelle/HOL 2020
  Date:    2020
  ID:      $Id: Decomposition.thy 152658 2020-08-06 08:13:12Z tklenze $
*)

section \<open>Event Composition\<close>
text\<open>In this theory, we define a datatype events, which distinguishes two types of events:
into internal events and "real" IO events. Only the latter will then be allowed to interact with 
the environment, while the former have no effect on the environment.
This is primarily a conceptual distinction of the different types of events present in a system, 
but the use of this theory in applying the Igloo methodology is optional. 
A beneficial side effect in practice is that the relevant lemmas for a concrete composition 
function @{term "\<chi>"} can be computed faster if using this theory, as it only needs to be defined over
real I/O events, rather than all (including internal) events. While the Igloo methodology can be 
applied by defining a single concrete datatype of all events, the concrete composition function 
definition might take a long time to be accepted by Isabelle, since Isabelle creates simp rules for
lots of different patterns. The number of possible patterns is greatly reduced when using this theory's
events type.

The @{text "Primary_Backup_2"} theory provides an example on how to use this theory. In particular, it 
explained how @{term "\<chi>"} is defined for a composition of an environment, and two indexed component families 
called Clients and Servers.\<close>

theory Event_Composition
  imports
    "Interleaving"
    "Composition"
    "Decomposition"
begin

text\<open>Events are either internal operations, real IO operations, Skip (which does nothing) or Stop
(which should never occur on a trace). The distinction of internal and real IO only becomes relevant
when we combine the events of a component with those of the environment. Only real IO events can
synchronize with actual environment events, all internal events as well as Skip synchronize with the 
environment's Skip event, and Stop does not combine with the environment at all.\<close>
datatype ('a, 'b) events = IN 'a | IO 'b | Skip | Stop

text\<open>The rest of this theory is concerned with how event systems using the "events" datatype as event
labels can be combined. When combining them naively using the Composition theory, the resulting 
event system is defined over the sum type of to instances of "events", rather than a directly an 
instance of the "events" type as well. Thus, we define an appropriate mapping.\<close>

text \<open>Lifts mapping of events to mapping of event systems. f maps new events to old events. For Skip
and for Stop, this function ignores function f, and directly defines the appropriate transition 
relation.\<close>
fun map_ES :: "(('a, 'b) events \<Rightarrow> 'c) \<Rightarrow> ('c, 'd) ES \<Rightarrow> (('a, 'b) events, 'd) ES"  where
  "map_ES f E = \<lparr>init = init E, trans = (\<lambda> s e s' . (case e of 
    IN _ \<Rightarrow> trans E s (f e) s'
  | IO _ \<Rightarrow> trans E s (f e) s'
  | Skip \<Rightarrow> s' = s
  | Stop \<Rightarrow> False))\<rparr>"

subsection\<open>Combining two event systems\<close>

text \<open>Distribute the events type over the sum type.\<close>
fun evt_dist :: "('in1 + 'in2, 'io1 + 'io2) events \<Rightarrow>
            (('in1, 'io1) events + ('in2, 'io2) events)" where
  "evt_dist (IN (Inl x)) = Inl (IN x)"
| "evt_dist (IN (Inr y)) = Inr (IN y)"
| "evt_dist (IO (Inl x)) = Inl (IO x)"
| "evt_dist (IO (Inr y)) = Inr (IO y)"
| "evt_dist Skip = Inr Skip"
| "evt_dist Stop = Inr Stop"

text \<open>Combine the sum of two events into one event.\<close>
fun evt_comb :: "(('in1, 'io1) events + ('in2, 'io2) events) \<Rightarrow>
           ('in1 + 'in2, 'io1 + 'io2) events" where
  "evt_comb (Inl (IN x)) = IN (Inl x)"
| "evt_comb (Inr (IN y)) = IN (Inr y)"
| "evt_comb (Inl (IO x)) = IO (Inl x)"
| "evt_comb (Inr (IO y)) = IO (Inr y)"
| "evt_comb (Inl Skip) = Skip"
| "evt_comb (Inr Skip) = Skip"
| "evt_comb (Inl Stop) = Stop"
| "evt_comb (Inr Stop) = Stop"

fun event_dist :: "((('in1, 'io1) events + ('in2, 'io2) events), 's) ES \<Rightarrow>
                   (('in1 + 'in2, 'io1 + 'io2) events, 's) ES" where
  "event_dist E = map_ES evt_dist E"

text\<open>Note that the inverse, @{term "evt_dist (evt_comb e) = e"}, does not hold, because of the mapping of 
Skip and Stop to a Skip and Stop of *some* component (but not necessarily the right one). This is
not a problem, since we already set up @{term map_ES} to handle the special cases Skip and Stop.\<close>
lemma evt_comb_dist: "evt_comb (evt_dist e) = e"
  apply (cases e, auto)
  subgoal for x1 by(cases x1, auto)
  subgoal for x1 by(cases x1, auto)
  done
lemma evt_comb_dist_trace: "map (evt_comb \<circ> evt_dist) \<tau> = \<tau>"
  by (induction \<tau>, auto simp add: evt_comb_dist)


subsection\<open>Combining two families of event systems\<close>


text \<open>Distribute the events type over the sum type (?). The above definition without indices mapped
@{text "(in1 + in2, io1 + io2) events"} to @{text "(in1, io1) events + (in2, io2) events"}. 
Here, we consider families and add the parameters i and j to the events, since this function is used 
on two parametrized event systems.\<close>
fun ievt_dist :: "('i \<times> 'in1 + 'j \<times> 'in2, 'i \<times> 'io1 + 'j \<times> 'io2) events \<Rightarrow>
            ('i \<times> ('in1, 'io1) events + 'j \<times> ('in2, 'io2) events)" where
  "ievt_dist (IN (Inl (i, x))) = Inl (i, IN x)"
| "ievt_dist (IN (Inr (j, y))) = Inr (j, IN y)"
| "ievt_dist (IO (Inl (i, x))) = Inl (i, IO x)"
| "ievt_dist (IO (Inr (j, y))) = Inr (j, IO y)"
| "ievt_dist Skip = Inr ((SOME i. True), Skip)"
| "ievt_dist Stop = Inr ((SOME i. True), Stop)"

text \<open>Combine the sum of two events into one event.\<close>
fun ievt_comb :: "('i \<times> ('in1, 'io1) events + 'j \<times> ('in2, 'io2) events) \<Rightarrow>
           ('i \<times> 'in1 + 'j \<times> 'in2, 'i \<times> 'io1 + 'j \<times> 'io2) events" where
  "ievt_comb (Inl (i, IN x)) = IN (Inl (i, x))"
| "ievt_comb (Inr (j, IN y)) = IN (Inr (j, y))"
| "ievt_comb (Inl (i, IO x)) = IO (Inl (i, x))"
| "ievt_comb (Inr (j, IO y)) = IO (Inr (j, y))"
| "ievt_comb (Inl (i, Skip)) = Skip"
| "ievt_comb (Inr (i, Skip)) = Skip"
| "ievt_comb (Inl (j, Stop)) = Stop"
| "ievt_comb (Inr (j, Stop)) = Stop"

definition ievent_dist :: "(('i \<times> ('in1, 'io1) events + 'j \<times> ('in2, 'io2) events), 's) ES \<Rightarrow>
                   (('i \<times> 'in1 + 'j \<times> 'in2, 'i \<times> 'io1 + 'j \<times> 'io2) events, 's) ES" where
  "ievent_dist E = map_ES ievt_dist E"

text\<open>Note that the inverse, @{term "ievt_dist (ievt_comb e) = e"}, does not hold, because of the mapping of 
Skip and Stop to a Skip and Stop of *some* component (but not necessarily the right one). This is
not a problem, since we already set up @{term map_ES} to handle the special cases Skip and Stop.\<close>
lemma ievt_comb_dist[simp]: "ievt_comb (ievt_dist e) = e"
  apply (cases e, auto)
  subgoal for x1 by(cases x1, auto)
  subgoal for x1 by(cases x1, auto)
  done

lemma ievt_comb_dist_trace[simp]: "map (ievt_comb \<circ> ievt_dist) \<tau> = \<tau>"
  by (induction \<tau>, auto)

lemma ES_ievent_dist: 
  "\<lbrakk>ievent_dist m2sys': (c, s) \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> (c', s'); \<And>c s. m2sys': (c, s)\<midarrow>Inr (SOME i. True, Skip)\<rightarrow> (c, s)\<rbrakk> 
\<Longrightarrow> m2sys': (c, s) \<midarrow>\<langle>map ievt_dist \<tau>\<rangle>\<rightarrow> (c', s')"
  apply(erule trace.induct[of _ "(c, s)" "\<tau>" "(c', s')"], auto simp add: ievent_dist_def)
  subgoal for \<tau> c s e c' s' by(erule trace_snoc, cases e, auto elim: allE[of _ Skip])
  done

lemma ES_ievent_comb: 
  "\<lbrakk>m1 || m2: (c, s) \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> (c', s'); 
  \<And>c i c'. m1: c\<midarrow>(i, Skip)\<rightarrow> c' \<Longrightarrow> c' = c; \<And>c i c'. m1: c\<midarrow>(i, Stop)\<rightarrow> c' \<Longrightarrow> False;
   \<And>s j s'. m2: s\<midarrow>(j, Skip)\<rightarrow> s' \<Longrightarrow> s' = s; \<And>s j s'. m2: s\<midarrow>(j, Stop)\<rightarrow> s' \<Longrightarrow> False\<rbrakk> 
  \<Longrightarrow> ievent_dist (m1 || m2): (c, s) \<midarrow>\<langle>map ievt_comb \<tau>\<rangle>\<rightarrow> (c', s')"
  apply(erule trace.induct[of _ "(c, s)" "\<tau>" "(c', s')"], auto simp add: ievent_dist_def)
  subgoal for \<tau> c c' s i e apply(erule trace_snoc) apply(cases e) by (auto) 
  subgoal for \<tau> c c' s i e apply(erule trace_snoc) apply(cases e) by (auto) 
  done

(* We also formulated a combined lemma, but don't use it: *)
(*l e m m a ES_ievent: 
  assumes "\<tau>' = map ievt_dist \<tau>" "\<And>c s. m1 || m2: (c, s)\<midarrow>Inr (SOME i. True, Skip)\<rightarrow> (c, s)"
  "\<And>c i c'. m1: c\<midarrow>(i, Skip)\<rightarrow> c' \<Longrightarrow> c' = c" "\<And>c i c'. m1: c\<midarrow>(i, Stop)\<rightarrow> c' \<Longrightarrow> False"
   "\<And>s j s'. m2: s\<midarrow>(j, Skip)\<rightarrow> s' \<Longrightarrow> s' = s" "\<And>s j s'. m2: s\<midarrow>(j, Stop)\<rightarrow> s' \<Longrightarrow> False" 
 shows "ievent_dist (m1 || m2): (c, s) \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> (c', s') \<longleftrightarrow> m1 || m2: (c, s) \<midarrow>\<langle>\<tau>'\<rangle>\<rightarrow> (c', s')"
proof(rule iffI)
  assume "ievent_dist (m1 || m2): (c, s) \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> (c', s')" 
  then show "m1 || m2: (c, s) \<midarrow>\<langle>\<tau>'\<rangle>\<rightarrow> (c', s')" apply(simp only: assms(1) evt_comb_dist_trace ievent_dist_def)
 using assms(2) apply -
  apply(erule trace.induct[of _ "(c, s)" "\<tau>" "(c', s')"], auto)
  subgoal for \<tau> c s e c' s' by(erule trace_snoc, cases e, auto elim: allE[of _ Skip])
  done
next
  have \<tau>_def: "\<tau> = map ievt_comb \<tau>'" using assms(1) evt_comb_dist_trace by simp
  assume "m1 || m2: (c, s) \<midarrow>\<langle>\<tau>'\<rangle>\<rightarrow> (c', s')"
  then show "ievent_dist (m1 || m2): (c, s) \<midarrow>\<langle>\<tau>\<rangle>\<rightarrow> (c', s')" apply(simp only: \<tau>_def ievent_dist_def)
  apply(erule trace.induct[of _ "(c, s)" "\<tau>'" "(c', s')"], auto)
  subgoal for \<tau> c c' s i e apply(erule trace_snoc) apply(cases e) using assms by (auto) 
  subgoal for \<tau> c c' s i e apply(erule trace_snoc) apply(cases e) using assms by (auto) 
  done
qed
*)

end
