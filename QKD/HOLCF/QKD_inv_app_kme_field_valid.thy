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
    case (App_Master_RequestKey apps kmes bridges qkd net apps' n sae kme keys msgs)
    then have "(\<forall>na master oSae kme store msgs. na \<in> nodes - {n} \<and> app t na = IoaState (App master oSae kme store) msgs \<longrightarrow> kme \<in> kmeID ` nodes)"
      using 2(2) unfolding app_kme_field_valid_def by simp
    moreover have "(\<forall>na master oSae kme store msgs. na \<in> {n} \<and> app t na = IoaState (App master oSae kme store) msgs \<longrightarrow> kme \<in> kmeID ` nodes)"
      using 2(2) App_Master_RequestKey(2-4,7,8) unfolding app_kme_field_valid_def by fastforce
    ultimately show ?case
      unfolding app_kme_field_valid_def by blast
  next
    case (App_Master_KeyResponse apps kmes bridges qkd net apps' n sae kme keys msgs keyID keyVal)
    then have "(\<forall>na master oSae kme store msgs. na \<in> nodes - {n} \<and> app t na = IoaState (App master oSae kme store) msgs \<longrightarrow> kme \<in> kmeID ` nodes)"
      using 2(2) unfolding app_kme_field_valid_def by simp
    moreover have "(\<forall>na master oSae kme store msgs. na \<in> {n} \<and> app t na = IoaState (App master oSae kme store) msgs \<longrightarrow> kme \<in> kmeID ` nodes)"
      using 2(2) App_Master_KeyResponse(2-4,8,9) unfolding app_kme_field_valid_def by fastforce
    ultimately show ?case
      unfolding app_kme_field_valid_def by blast
  next
    case (App_Slave_AppIDRelay apps kmes bridges qkd net apps' n sae kme keys msgs sender keyID)
    then have "(\<forall>na master oSae kme store msgs. na \<in> nodes - {n} \<and> app t na = IoaState (App master oSae kme store) msgs \<longrightarrow> kme \<in> kmeID ` nodes)"
      using 2(2) unfolding app_kme_field_valid_def by simp
    moreover have "(\<forall>na master oSae kme store msgs. na \<in> {n} \<and> app t na = IoaState (App master oSae kme store) msgs \<longrightarrow> kme \<in> kmeID ` nodes)"
      using 2(2) App_Slave_AppIDRelay(2-4,8,9) unfolding app_kme_field_valid_def by fastforce
    ultimately show ?case
      unfolding app_kme_field_valid_def by blast
  next
    case (App_Slave_KeyResponse apps kmes bridges qkd net apps' n sae kme keys msgs keyID keyVal)
    then have "(\<forall>na master oSae kme store msgs. na \<in> nodes - {n} \<and> app t na = IoaState (App master oSae kme store) msgs \<longrightarrow> kme \<in> kmeID ` nodes)"
      using 2(2) unfolding app_kme_field_valid_def by simp
    moreover have "(\<forall>na master oSae kme store msgs. na \<in> {n} \<and> app t na = IoaState (App master oSae kme store) msgs \<longrightarrow> kme \<in> kmeID ` nodes)"
      using 2(2) App_Slave_KeyResponse(2-4,8,9) unfolding app_kme_field_valid_def by fastforce
    ultimately show ?case
      unfolding app_kme_field_valid_def by blast
  next
    case (App_Send apps kmes bridges qkd net apps' net' n msgs rcpt msg appState)
    then have "(\<forall>na master oSae kme store msgs. na \<in> nodes - {n} \<and> app t na = IoaState (App master oSae kme store) msgs \<longrightarrow> kme \<in> kmeID ` nodes)"
      using 2(2) unfolding app_kme_field_valid_def by simp
    moreover have "(\<forall>na master oSae kme store msgs. na \<in> {n} \<and> app t na = IoaState (App master oSae kme store) msgs \<longrightarrow> kme \<in> kmeID ` nodes)"
      using 2(2) App_Send(2-4,9,10) unfolding app_kme_field_valid_def by fastforce
    ultimately show ?case
      unfolding app_kme_field_valid_def by blast
  qed
  (use 2(2) in \<open>simp_all add: app_kme_field_valid_def\<close>)
qed

end

end