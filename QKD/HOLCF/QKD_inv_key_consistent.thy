theory QKD_inv_key_consistent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
begin

context QKD_Network
begin

lemma "invariant System.ioa (key_consistent nodes)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 tn qkd net)
    then show ?thesis
      unfolding key_consistent_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (App_Master_RequestKey apps kmes bridges qkd net apps' n sae kme keys msgs)
    then have "\<And>n state msgs state' msgs'. \<lbrakk>n \<in> nodes; app s n = IoaState state msgs; app t n = IoaState state' msgs'\<rbrakk> \<Longrightarrow> state = state'"
      sorry
    then show ?case 
      unfolding key_consistent_def apply auto
      sorry
  next
    case (App_Master_KeyResponse apps kmes bridges qkd net apps' n sae kme keys msgs sender keyID keyVal)
    then show ?case sorry
  next
    case (App_Slave_AppIDRelay apps kmes bridges qkd net apps' n sae kme keys msgs sender keyID)
    then show ?case sorry
  next
    case (App_Slave_KeyResponse apps kmes bridges qkd net apps' n sae kme keys msgs sender keyID keyVal)
    then show ?case sorry
  next
    case (App_Send apps kmes bridges qkd net apps' net' n msgs rcpt msg appState)
    then show ?case sorry
  qed
  (use 2(2) in \<open>simp_all add: key_consistent_def\<close>)
qed

end

end