(*******************************************************************************

  Project: Development of Security Protocols by Refinement
  
  Protocol runs: local state of executing protocol roles

*******************************************************************************)

section \<open>Protocol runs\<close>

theory Runs imports Atoms
begin


(******************************************************************************)
subsection \<open>Runs\<close>
(******************************************************************************)

text \<open>The type of runs is a partial function from run identifiers to 
a triple consisting of a role, a list of agents, and a list of atomic messages 
recorded during the run's execution. 

The type of roles could be made a parameter for more flexibility.\<close>

type_synonym rid = "uid"
type_synonym run_store = "atom list"

record run_state = 
  agts :: "agent list"        \<comment> \<open>run owner first by convention\<close>
  store :: "run_store"

type_synonym runs = "rid \<rightharpoonup> run_state"



end
