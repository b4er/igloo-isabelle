section \<open>Implementation of Cryptographic Messages\<close>
(*
   Module:  Security Protocol Infrastructure / Crypto Algebra (Isabelle/HOL 2020)
   ID:      $Id: Crypto_Algebra.thy 152658 2020-08-06 08:13:12Z tklenze $
   Author:  Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
*)
theory Crypto_Algebra
  imports 
    Message 
    "HOL-Library.Countable_Set"
begin

locale crypto_algebra = 
  fixes \<alpha> :: "('b :: countable) \<Rightarrow> msg"     \<comment> \<open>abstraction: abstract ``bitstrings'' to messages\<close>
  assumes surj_alpha: "surj \<alpha>"
begin

lemma inv_alpha_gamma: "image \<alpha> o vimage \<alpha> = id"
  by (auto simp add: surj_alpha)

lemma inv_alpha_gamma_pointed: "\<alpha>`(\<alpha>-`H) = H"
  by (auto simp add: surj_alpha)


text \<open>Collect some useful simplification rules connected to injectivity.\<close>


subsection \<open>A Dolev-Yao attacker on bitstrings\<close>

text \<open>Define bitstring versions of analz and synth, simply by transferring the bitstrings
to messages and back.\<close>

definition canalz :: "'b set \<Rightarrow> 'b set" where
  "canalz Bs = \<alpha>-`analz (\<alpha>`Bs)"

definition csynth :: "'b set \<Rightarrow> 'b set" where
  "csynth Bs = \<alpha>-`synth (\<alpha>`Bs)"


text \<open>This lemma is all that is needed to simulate the term-based DY attacker.\<close>

lemma csynth_canalz_eq: "csynth (canalz Bs) = \<alpha>-`synth (analz (\<alpha>`Bs))"
  by (simp add: canalz_def csynth_def surj_alpha)


text \<open>Injection lemmas for concrete analz and synth.\<close>

lemma canalz_inject: "bs \<in> Bs \<Longrightarrow> bs \<in> canalz Bs"
 by (simp add: canalz_def)

lemma csynth_inject: "bs \<in> Bs \<Longrightarrow> bs \<in> csynth Bs"
  by (simp add: csynth_def synth.Inj)

lemmas canalz_csynth_inject = canalz_inject csynth_inject


end


text \<open>Witnessing interpretation given by term messages themselves.\<close>

instance ltkey :: countable
  by countable_datatype

instance key :: countable
  by countable_datatype

instance msg :: countable
  by countable_datatype

interpretation msg: crypto_algebra "id :: msg \<Rightarrow> msg" 
  by unfold_locales auto


end