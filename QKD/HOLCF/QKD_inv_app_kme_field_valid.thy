theory QKD_inv_app_kme_field_valid
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
begin

context QKD_Network
begin

lemma inv_app_kme_field_valid:
  shows "invariant System.ioa (app_kme_field_valid nodes kmeID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 tn qkd net)
    then show ?thesis
      unfolding app_kme_field_valid_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (App_Master_RequestKey apps kmes bridges qkd net apps' net' n sae kme keys msgs)
    then show ?case
      using 2(2)
      unfolding app_kme_field_valid_def apply simp by fast
  next
    case (App_Master_KeyResponse apps kmes bridges qkd net apps' net' n sae kme keys msgs keyID keyVal)
    then show ?case
      using 2(2)
      unfolding app_kme_field_valid_def apply simp by fast
  next
    case (App_Slave_AppIDRelay apps kmes bridges qkd net apps' net'  sae kme keys msgs sender keyID)
    then show ?case
      using 2(2)
      unfolding app_kme_field_valid_def apply simp by fast
  next
    case (App_Slave_KeyResponse apps kmes bridges qkd net apps' net' n sae kme keys msgs keyID keyVal)
    then show ?case
      using 2(2)
      unfolding app_kme_field_valid_def apply simp by fast
  next
    case (App_Send apps kmes bridges qkd net apps' net' n msgs rcpt msg appState)
    then show ?case
      using 2(2)
      unfolding app_kme_field_valid_def apply simp by fast
  qed
  (use 2(2) in \<open>simp_all add: app_kme_field_valid_def\<close>)
qed

end

end