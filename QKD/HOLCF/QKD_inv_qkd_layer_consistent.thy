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
  proof (induction rule: test2)
    case (App_Master_GetKey apps kmes bridges qkd net apps' pid n sae kme keys msgs)
    then show ?case sorry
  next
    case (App_Master_KeyResponse apps kmes bridges qkd net apps' pid n sae kme keys msgs sender keyID keyVal)
    then show ?case sorry
  next
    case (App_Slave_GetKey apps kmes bridges qkd net apps' pid n sae kme keys msgs sender keyID)
    then show ?case sorry
  next
    case (App_Slave_KeyResponse apps kmes bridges qkd net apps' pid n sae kme keys msgs sender keyID keyVal)
    then show ?case sorry
  next
    case (App_Send apps kmes bridges qkd net apps' net' pid n msgs rcpt msg appState)
    then show ?case sorry
  qed
qed

end

end