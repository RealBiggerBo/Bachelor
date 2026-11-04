theory QKD_inv_bridge_kme_msg_sent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
          QKD_inv_bridge_kme_buffer_sent
begin

context QKD_Network
begin

lemma bridge_kme_msg_sent_helper:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps', kmes', bridges, qkd, net')"
    and "net' = rmv_msg net sender rcpt m"
    and "can_send net sender rcpt m"
    and "bridge_kme_msg_sent nodes kmeID bridgeIDs s"
  shows "bridge_kme_msg_sent nodes kmeID bridgeIDs t"
  using assms unfolding bridge_kme_msg_sent_def apply simp apply auto
  by (metis image_eqI list.set_sel(2))

lemma inv_bridge_kme_msg_sent:
  shows "invariant System.ioa (bridge_kme_msg_sent nodes kmeID bridgeIDs)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 tn qkd net)
    then show ?thesis
      unfolding bridge_kme_msg_sent_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (App_Master_RequestKey apps kmes bridges qkd net apps' net' n sae kme keys msgs)
    then show ?case 
      using 2(2) by (auto simp: bridge_kme_msg_sent_def)
  next
    case (App_Send apps kmes bridges qkd net apps' net' n msgs rcpt msg appState)
    then have "appID n \<notin> \<Union>(bridgeIDs ` nodes)"
      using disjoint_ids app_neq_bridge by auto
    then have "bridge_kme_msg_sent nodes kmeID bridgeIDs s \<longrightarrow> bridge_kme_msg_sent nodes kmeID bridgeIDs t"
      using App_Send(2,3,7) unfolding bridge_kme_msg_sent_def by simp
    then show ?case 
      using 2(2) by argo
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    then have "kmeID n \<notin> \<Union>(bridgeIDs ` nodes)"
      using disjoint_ids kme_neq_bridge by auto
    then have "bridge_kme_msg_sent nodes kmeID bridgeIDs s \<longrightarrow> bridge_kme_msg_sent nodes kmeID bridgeIDs t"
      using Kme_Send(2,3,7) unfolding bridge_kme_msg_sent_def by simp
    then show ?case 
      using 2(2) by argo
  next
    case (Bridge_Tick_GetKey apps kmes bridges qkds net bridges' net' n b slaveBridge otherKme qkd kme msgs)
    then show ?case
      using 2(2) by (auto simp: bridge_kme_msg_sent_def)
  next
    case (Bridge_Master_KeyResponse apps kmes bridges qkds net bridges' net' n b slaveBridge otherKme qkd kme msgs keyID keyVal)
    have "\<forall>s1 r1 otherKme keyID keyVal. network_has_msg t s1 r1 (KMPost otherKme keyID keyVal) \<longrightarrow> network_has_msg s s1 r1 (KMPost otherKme keyID keyVal)"
      unfolding bridge_kme_msg_sent_def using Bridge_Master_KeyResponse(2,3,8,9) apply simp apply auto
      by (metis list.set_sel(2))
    moreover have "\<forall>keyID keyVal. qkd_has_key s keyID keyVal \<longrightarrow> qkd_has_key t keyID keyVal"
      unfolding bridge_kme_msg_sent_def using Bridge_Master_KeyResponse(2,3) by force
    ultimately show ?case
      using 2(2) unfolding bridge_kme_msg_sent_def by meson
  next
    case (Bridge_Slave_GetKeyWithID apps kmes bridges qkds net bridges' net' n b masterBridge otherKme qkd kme msgs sender keyID)
    have "\<forall>s1 r1 otherKme keyID keyVal. network_has_msg t s1 r1 (KMPost otherKme keyID keyVal) \<longrightarrow> network_has_msg s s1 r1 (KMPost otherKme keyID keyVal)"
      unfolding bridge_kme_msg_sent_def using Bridge_Slave_GetKeyWithID(2,3,8,9) apply simp apply auto
      by (metis list.set_sel(2))
    moreover have "\<forall>keyID keyVal. qkd_has_key s keyID keyVal \<longrightarrow> qkd_has_key t keyID keyVal"
      unfolding bridge_kme_msg_sent_def using Bridge_Slave_GetKeyWithID(2,3) by force
    ultimately show ?case
      using 2(2) unfolding bridge_kme_msg_sent_def by meson
  next
    case (Bridge_Slave_KeyResponse apps kmes bridges qkds net bridges' net' n b masterBridge otherKme qkd kme msgs keyID keyVal)
    have "\<forall>s1 r1 otherKme keyID keyVal. network_has_msg t s1 r1 (KMPost otherKme keyID keyVal) \<longrightarrow> network_has_msg s s1 r1 (KMPost otherKme keyID keyVal)"
      unfolding bridge_kme_msg_sent_def using Bridge_Slave_KeyResponse(2,3,8,9) apply simp apply auto
      by (metis list.set_sel(2))
    moreover have "\<forall>keyID keyVal. qkd_has_key s keyID keyVal \<longrightarrow> qkd_has_key t keyID keyVal"
      unfolding bridge_kme_msg_sent_def using Bridge_Slave_KeyResponse(2,3) by force
    ultimately show ?case
      using 2(2) unfolding bridge_kme_msg_sent_def by meson
  next
    case (Bridge_ReceiveStutter apps kmes bridges qkds net net' n b sender msg)
    have "\<forall>s1 r1 otherKme keyID keyVal. network_has_msg t s1 r1 (KMPost otherKme keyID keyVal) \<longrightarrow> network_has_msg s s1 r1 (KMPost otherKme keyID keyVal)"
      unfolding bridge_kme_msg_sent_def using Bridge_ReceiveStutter(2,3,8,9) apply simp apply auto
      by (metis list.set_sel(2))
    moreover have "\<forall>keyID keyVal. qkd_has_key s keyID keyVal \<longrightarrow> qkd_has_key t keyID keyVal"
      unfolding bridge_kme_msg_sent_def using Bridge_ReceiveStutter(2,3) by force
    ultimately show ?case
      using 2(2) unfolding bridge_kme_msg_sent_def by meson
  next
    case (Bridge_Send apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState)
    have "bridge_kme_buffer_sent nodes bridgeIDs s"
      using inv_bridge_kme_buffer_sent 2(1) unfolding invariant_def by fast
    then show ?case
      using 2(2) Bridge_Send(2-5,8-10) unfolding bridge_kme_msg_sent_def bridge_kme_buffer_sent_def 
      apply simp apply auto by blast
  next
    case (Qkd_GetKey_Gen apps kmes bridges qkd net qkd' net' pid gen sent sender target keyID keyVal)
    then show ?case
      using 2(2) unfolding bridge_kme_msg_sent_def 
      apply simp apply auto by (meson image_eqI list.set_sel(2))+
  next
    case (Qkd_GetKeyWithID_Reserve apps kmes bridges qkd net qkd' net' pid gen sent sender target keyID keyVal)
    then show ?case
      using 2(2) unfolding bridge_kme_msg_sent_def 
      apply simp apply auto by (meson image_eqI list.set_sel(2))+
  next
    case (Qkd_ReceiveStutter apps kmes bridges qkd net qkd' net' pid sender msg)
    then show ?case
      using 2(2) unfolding bridge_kme_msg_sent_def 
      apply simp apply auto by (meson image_eqI list.set_sel(2))+
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    then have "pid \<notin> \<Union>(bridgeIDs ` nodes)"
      using disjoint_ids unfolding disjnt_def by blast
    then have "bridge_kme_msg_sent nodes kmeID bridgeIDs s \<longrightarrow> bridge_kme_msg_sent nodes kmeID bridgeIDs t"
      using Qkd_Send(2,3,7-10) unfolding bridge_kme_msg_sent_def apply simp apply auto by fastforce+
    then show ?case 
      using 2(2) by argo
  next
    case (Network_Ext_Receive apps kmes bridges qkd net net' sender rcpt msg all)
    then show ?case
      using 2(2) by (auto simp: bridge_kme_msg_sent_def)
  next
    case (Network_Ext_Send apps kmes bridges qkd net net' sender rcpt msg all)
    then show ?case
      using 2(2) by (auto simp: bridge_kme_msg_sent_def)
  qed 
    (use 2(2) in \<open>auto simp: bridge_kme_msg_sent_helper\<close>)
qed

end

end