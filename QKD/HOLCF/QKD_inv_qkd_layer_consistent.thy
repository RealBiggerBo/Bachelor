theory QKD_inv_qkd_layer_consistent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
begin

context QKD_Network
begin

lemma "invariant System.ioa qkd_layer_consistent"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 tn qkd net)
    then show ?thesis
      unfolding qkd_layer_consistent_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof(induction rule: TEST)
    unfolding trans_of_def
    sorry
qed

end

end