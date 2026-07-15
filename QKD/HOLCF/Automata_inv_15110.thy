theory Automata_inv_15110
  imports Automata_inv_def
begin

lemma invariants15110:
  shows "invariant (System t (UNIV - {0}) r) (\<lambda>s. (inv15 s) \<and> (inv110 s))"
  sorry

end