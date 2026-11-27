theory Automata_inv_111314
  imports Automata_inv_def
begin

lemma invariants111314:
  shows "invariant (System t (UNIV - {0}) r) (\<lambda>s. (inv11 UNIV s) \<and> (inv13 UNIV s) \<and> (inv14 UNIV s))"
  sorry

end