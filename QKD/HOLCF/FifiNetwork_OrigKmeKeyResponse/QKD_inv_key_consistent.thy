theory QKD_inv_key_consistent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
          QKD_inv_app_kme_field_valid
          QKD_inv_app_key_sent
          QKD_inv_kme_app_send_consistent
begin

context QKD_Network
begin

lemma inv_key_consistent:
  shows "invariant System.ioa (key_consistent nodes)"
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
      by (metis (no_types, opaque_lifting) fstI fun_upd_def ioa_state.inject)
    then have "key_consistent nodes s \<longleftrightarrow> key_consistent nodes t"
      unfolding key_consistent_def apply auto
      by (metis ioa_state.exhaust)+
    then show ?case 
      using 2(2) by presburger
  next
    case (App_Master_KeyResponse apps kmes bridges qkd net apps' n sae kme keys msgs keyID keyVal)
    have reach:"reachable System.ioa t"
      using App_Master_KeyResponse(1) 2(1) reachable_n by fast
    have "app_key_sent nodes appID t"
      using reach inv_app_key_sent unfolding invariant_def by fast
    moreover have "app_kme_field_valid nodes kmeID t"
      using reach inv_app_kme_field_valid unfolding invariant_def by fast
    moreover have "kme_app_send_consistent nodes appID kmeID t"
      using reach inv_kme_app_send_consistent unfolding invariant_def by fast
    moreover have "appID n \<in> appID ` nodes"
      using App_Master_KeyResponse(4) by blast
    ultimately show ?case 
      unfolding key_consistent_def app_key_sent_def kme_app_send_consistent_def app_kme_field_valid_def 
      by (meson imageI)
  next
    case (App_Slave_AppIDRelay apps kmes bridges qkd net apps' n sae kme keys msgs sender keyID)
    then have "\<And>n state msgs state' msgs'. \<lbrakk>n \<in> nodes; app s n = IoaState state msgs; app t n = IoaState state' msgs'\<rbrakk> \<Longrightarrow> state = state'"
      by (metis (no_types, opaque_lifting) fstI fun_upd_def ioa_state.inject)
    then have "key_consistent nodes s \<longleftrightarrow> key_consistent nodes t"
      unfolding key_consistent_def apply auto
      by (metis ioa_state.exhaust)+
    then show ?case 
      using 2(2) by presburger
  next
    case (App_Slave_KeyResponse apps kmes bridges qkd net apps' n sae kme keys msgs keyID keyVal)
    have reach:"reachable System.ioa t"
      using App_Slave_KeyResponse(1) 2(1) reachable_n by fast
    have "app_key_sent nodes appID t"
      using reach inv_app_key_sent unfolding invariant_def by fast
    moreover have "app_kme_field_valid nodes kmeID t"
      using reach inv_app_kme_field_valid unfolding invariant_def by fast
    moreover have "kme_app_send_consistent nodes appID kmeID t"
      using reach inv_kme_app_send_consistent unfolding invariant_def by fast
    moreover have "appID n \<in> appID ` nodes"
      using App_Slave_KeyResponse(4) by blast
    ultimately show ?case 
      unfolding key_consistent_def app_key_sent_def kme_app_send_consistent_def app_kme_field_valid_def 
      by (meson imageI)
  next
    case (App_Send apps kmes bridges qkd net apps' net' n msgs rcpt msg appState)
    then have "\<And>n state msgs state' msgs'. \<lbrakk>n \<in> nodes; app s n = IoaState state msgs; app t n = IoaState state' msgs'\<rbrakk> \<Longrightarrow> state = state'"
      by (metis (no_types, opaque_lifting) fstI fun_upd_def ioa_state.inject)
    then have "key_consistent nodes s \<longleftrightarrow> key_consistent nodes t"
      unfolding key_consistent_def apply auto
      by (metis ioa_state.exhaust)+
    then show ?case 
      using 2(2) by presburger
  qed
  (use 2(2) in \<open>simp_all add: key_consistent_def\<close>)
qed

end

end