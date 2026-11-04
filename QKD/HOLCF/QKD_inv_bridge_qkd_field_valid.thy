theory QKD_inv_bridge_qkd_field_valid
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
begin

context QKD_Network
begin

lemma inv_bridge_qkd_field_valid:
  shows "invariant System.ioa (bridge_qkd_field_valid nodes bridgeIDs qkdID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 tn qkd net)
    then show ?thesis
      unfolding bridge_qkd_field_valid_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (Bridge_Tick_GetKey apps kmes bridges qkds net bridges' net' n b slaveBridge otherKme qkd kme msgs)
    then show ?case
      using 2(2) unfolding bridge_qkd_field_valid_def apply simp by fast
  next
    case (Bridge_Master_KeyResponse apps kmes bridges qkds net bridges' net' n b slaveBridge otherKme qkd kme msgs keyID keyVal)
    then show ?case
      using 2(2) unfolding bridge_qkd_field_valid_def apply simp by fast
  next
    case (Bridge_Slave_GetKeyWithID apps kmes bridges qkds net bridges' net' n b masterBridge otherKme qkd kme msgs sender keyID)
    then show ?case
      using 2(2) unfolding bridge_qkd_field_valid_def apply simp by fast
  next
    case (Bridge_Slave_KeyResponse apps kmes bridges qkds net bridges' net' n b masterBridge otherKme qkd kme msgs keyID keyVal)
    then show ?case 
      using 2(2) unfolding bridge_qkd_field_valid_def apply simp by fast
  next
    case (Bridge_Send apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState)
    then show ?case 
      using 2(2) unfolding bridge_qkd_field_valid_def apply simp by fast
  qed
  (use 2(2) in \<open>auto simp: bridge_qkd_field_valid_def\<close>)
qed

end

end