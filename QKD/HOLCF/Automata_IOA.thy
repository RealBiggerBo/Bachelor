theory Automata_IOA
  imports Automata
begin

locale IOA =
  fixes ioa' :: "('a, 's) ioa"
  assumes is_asig_of: "is_asig_of ioa'"
      and is_starts_of: "is_starts_of ioa'"
      and is_trans_of: "is_trans_of ioa'"
      and input_enabled: "input_enabled ioa'"
begin

(*abbreviation asig where
  \<open>asig \<equiv> asig_of ioa'\<close>

abbreviation starts where
  \<open>starts \<equiv> starts_of ioa'\<close>

abbreviation trans where
  \<open>trans \<equiv> trans_of ioa'\<close>

abbreviation wfair where
  \<open>wfair \<equiv> wfair_of ioa'\<close>

abbreviation sfair where
  \<open>sfair \<equiv> sfair_of ioa'\<close>*)

abbreviation ioa where
  \<open>ioa \<equiv> ioa'\<close>

lemma is_ioa: "Automata.IOA ioa'"
  unfolding Automata.IOA_def 
  using is_asig_of is_starts_of is_trans_of input_enabled by simp

end

end