section\<open>Matching theorems from paper to the formalization\<close>

theory Igloo
  imports Composition Interleaving Event_Systems_into_IO_Processes IO_Behavior
begin

context Typing
begin

text\<open> The following lists matches theorems, lemmas, propositions and corollaries with lemmas in the paper.
\begin{itemize}
\item Theorem 2.1, p. 4 (Refinement soundness): @{text "Event_Systems.simulation_soundness"}
\item Theorem 2.2, p. 4 (Property preservation): @{text "Event_Systems.property_preservation"}
\item Theorem 3.1, p. 9 (Composition theorem): @{text "Composition.trace_composition"}
\item Theorem 3.2, p. 9 (Compositional refinement): @{text "Composition.compositional_refinement"}
\item Theorem 5.1, p. 17 (Monotonicity): @{text "IO_Separation_Logic.Typing.sem_leaking_left"}
\item Theorem 5.5, p. 19 (Trace equivalence of I/O-GES and their embedding into Processes): 
  @{text "Event_Systems_into_IO_Processes.Typing.emb_opsem_equiv"}
\item Theorem 5.6, p. 19 (Countable choice translation): \\
  @{text "IO_Processes_into_IO_Separation_Logic.embedp_VChoice_is_AllStar"}
\item Theorem 5.7, p. 19 (Traces of processes are equivalent to their embedding into I/O specifications): 
  @{text "IO_Behavior.Typing.trace_equivalences"}
\item Theorem 5.8, p. 19 (Traces of processes are contained in their embedding into I/O specifications): 
  @{text "IO_Behavior.Typing.traces_opsem_subset_process"}
\item Theorem 5.10, p. 22 (Canonical model property): \\
  @{text "IO_Processes_into_IO_Separation_Logic.Typing.canonical_model_with_token"}
\item Theorem 5.11, p. 22 (Traces of embedding of P are contained in traces of canonical models of P): 
  @{text "IO_Behavior.Typing.traces_process_assn_subset_gmodels"}
\item Theorem 5.12, p. 23 (Traces of canonical models of P are contained in those of P): 
  @{text "IO_Behavior.Typing.traces_gmodels_subset_opsem"}
\item Theorem B.2, p. 22 (Canonical model as fixed-point): \\
  @{text "IO_Processes_into_IO_Separation_Logic.gmodel_null"} \\
  @{text "IO_Processes_into_IO_Separation_Logic.gmodel_prefix"} \\
  @{text "IO_Processes_into_IO_Separation_Logic.gmodel_choice"}
\item (Canonical heap transitions): \\
  @{text "IO_Behavior.Typing.opsem_simulates_process_gmodel"}
\item Theorem B.6, p. 23 (Canonical heap traces): \\
  @{text "IO_Behavior.Typing.opsem_simulates_process_gmodel_trace"}
\end{itemize}\<close>

thm Event_Systems.simulation_soundness 
thm Event_Systems.property_preservation
thm Composition.trace_composition
thm Composition.compositional_refinement
thm IO_Separation_Logic.Typing.sem_leaking_left
thm Event_Systems_into_IO_Processes.Typing.emb_opsem_equiv
thm IO_Processes_into_IO_Separation_Logic.embedp_VChoice_is_AllStar
thm IO_Behavior.Typing.trace_equivalences
thm IO_Behavior.Typing.traces_opsem_subset_process
thm IO_Processes_into_IO_Separation_Logic.Typing.canonical_model_with_token
thm IO_Behavior.Typing.traces_process_assn_subset_gmodels
thm IO_Behavior.Typing.traces_gmodels_subset_opsem
thm IO_Processes_into_IO_Separation_Logic.gmodel_null 
thm IO_Processes_into_IO_Separation_Logic.gmodel_prefix 
thm IO_Processes_into_IO_Separation_Logic.gmodel_choice
thm IO_Behavior.Typing.opsem_simulates_process_gmodel
thm IO_Behavior.Typing.opsem_simulates_process_gmodel_trace

end
end

