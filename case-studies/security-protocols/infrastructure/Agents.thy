(*******************************************************************************

  Project: Development of Security Protocols by Refinement
  Agents and nonces (partly based on Paulson's Message.thy)

*******************************************************************************)

section \<open>Atomic messages\<close>

theory Agents imports 
  Main 
  "HOL-Library.Countable_Set"
begin

text \<open>The definitions below are moved here from the message theory, since
the higher levels of protocol abstraction do not know about cryptographic 
messages.\<close>


(******************************************************************************)
subsection \<open>Agents\<close>
(******************************************************************************)

datatype  \<comment> \<open>We allow any number of agents.\<close>
  agent = Agt nat

instance agent :: countable
  by countable_datatype

consts 
  bad :: "agent set"			      \<comment> \<open>compromised agents\<close>

abbreviation 
  good :: "agent set"
where
  "good \<equiv> -bad"


(******************************************************************************)
subsection \<open>Roles\<close>
(******************************************************************************)

text \<open>Define some typical roles.\<close>

datatype role = Init | Resp | Serv

instance role :: countable
  by countable_datatype


(******************************************************************************)
subsection \<open>Fresh values and nonces\<close>
(******************************************************************************)

text \<open>Assuming each role has its own space of fresh values we tag these with the role.\<close>

datatype uid = 
  Uid "nat"

instance uid :: countable
  by countable_datatype

datatype fresh = 
  Fresh "role" "uid" "nat"   ("(#[_,_,_])" [50, 50, 50] 65)  

instance fresh :: countable
  by countable_datatype

type_synonym nonce = fresh


end
