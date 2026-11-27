theory QKD_inv_qkd_layer_consistent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
begin

context QKD_Network
begin

lemma inv_qkd_layer_consistent:
  shows "invariant System.ioa qkd_layer_consistent"
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
  proof (induction rule: System_step_induct)
    case (Qkd_GetKey_Gen apps kmes bridges qkd net qkd' pid gen sent sender target keyID keyVal)
    then show ?case
      using 2(2) unfolding qkd_layer_consistent_def
      by (smt (verit, best) Un_empty_right Un_iff Un_insert_right image_insert insertCI insertE
          insert_image qkd_layer_state.inject split_pairs)
  next
    case (Qkd_GetKeyWithID_Reserve apps kmes bridges qkd net qkd' pid gen sent sender target keyID keyVal)
    then show ?case
      using 2(2) unfolding qkd_layer_consistent_def by auto
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    then show ?case
      using 2(2) unfolding qkd_layer_consistent_def
      by (smt (verit, ccfv_SIG) Un_empty_right Un_insert_right Un_left_commute image_insert
          insert_Diff qkd_layer_state.inject split_pairs)
  qed 
  (use 2(2) in \<open>simp_all add: qkd_layer_consistent_def\<close>)
qed

end

end