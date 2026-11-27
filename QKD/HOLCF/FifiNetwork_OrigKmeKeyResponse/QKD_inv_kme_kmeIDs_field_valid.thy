theory QKD_inv_kme_kmeIDs_field_valid
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
begin

context QKD_Network
begin

lemma inv_kme_kmeIDs_field_valid:
  shows "invariant System.ioa (kme_kmeIDs_field_valid nodes kmeID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 tn qkd net)
    then show ?thesis
      unfolding kme_kmeIDs_field_valid_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    have "\<And>m. kme_get_kmeIDs_field (IoaState appState msgs) = kme_get_kmeIDs_field (IoaState appState (msgs - {m}))"
      using kme_get_kmeIDs_field.simps kme_state.exhaust by (smt (verit, best))
    then show ?case
      using Kme_Send(2,3,9,10) 2(2) unfolding kme_kmeIDs_field_valid_def by auto
  qed
  (use 2(2) in \<open>auto simp: kme_kmeIDs_field_valid_def\<close>)
qed

end

end