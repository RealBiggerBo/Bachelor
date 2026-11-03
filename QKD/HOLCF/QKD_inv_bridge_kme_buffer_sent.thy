theory QKD_inv_bridge_kme_buffer_sent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
          QKD_inv_qkd_bridge_msg_sent
begin

context QKD_Network
begin

lemma inv_bridge_kme_buffer_sent:
  shows "invariant System.ioa (bridge_kme_buffer_sent nodes bridgeIDs)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 apps kmes bridges qkd net)
    then show ?thesis
      unfolding bridge_kme_buffer_sent_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (Bridge_Master_KeyResponse apps kmes bridges qkds net bridges' net' n b slaveBridge otherKme qkd kme msgs keyID keyVal)
    have "qkd \<in> qkdID ` \<Union> (bridgeIDs ` nodes)"
      sorry
    moreover have "network_has_msg s qkd b (KeyResponse keyID keyVal)"
      using Bridge_Master_KeyResponse(2,9) by (metis list.set_sel(1) split_pairs2)
    ultimately have "qkd_has_key s keyID keyVal"
      using Bridge_Master_KeyResponse(4,5) inv_qkd_bridge_msg_sent 2(1) 
      unfolding invariant_def qkd_bridge_msg_sent_def by blast
    then have "qkd_has_key t keyID keyVal"
      using Bridge_Master_KeyResponse(2,3) by simp
    then show ?case 
      using 2(2) Bridge_Master_KeyResponse(2,3,10,11)
      unfolding bridge_kme_buffer_sent_def by auto
  next
    case (Bridge_Slave_KeyResponse apps kmes bridges qkds net bridges' net' n b masterBridge otherKme qkd kme msgs keyID keyVal)
    have "qkd \<in> qkdID ` \<Union> (bridgeIDs ` nodes)"
      sorry
    moreover have "network_has_msg s qkd b (KeyResponse keyID keyVal)"
      using Bridge_Slave_KeyResponse(2,9) by (metis list.set_sel(1) split_pairs2)
    ultimately have "qkd_has_key s keyID keyVal"
      using Bridge_Slave_KeyResponse(4,5) inv_qkd_bridge_msg_sent 2(1) 
      unfolding invariant_def qkd_bridge_msg_sent_def by blast
    then have "qkd_has_key t keyID keyVal"
      using Bridge_Slave_KeyResponse(2,3) by simp
    then show ?case 
      using 2(2) Bridge_Slave_KeyResponse(2,3,10,11)
      unfolding bridge_kme_buffer_sent_def by auto
  next
    case (Qkd_GetKeyWithID_Reserve apps kmes bridges qkd net qkd' net' pid gen sent sender target keyID keyVal)
    have "\<And>keyID keyVal. qkd_has_key s keyID keyVal \<longleftrightarrow> qkd_has_key t keyID keyVal"
      using Qkd_GetKeyWithID_Reserve(2,3,7,10,11) by force
    then show ?case 
      using 2(2) Qkd_GetKeyWithID_Reserve(2,3) unfolding bridge_kme_buffer_sent_def by simp
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    have "\<And>keyID keyVal. qkd_has_key s keyID keyVal \<longleftrightarrow> qkd_has_key t keyID keyVal"
      using Qkd_Send(2,3,7,9,10) by force
    then show ?case 
      using 2(2) Qkd_Send(2,3) unfolding bridge_kme_buffer_sent_def by simp
  qed
  (use 2(2) in \<open>auto simp: bridge_kme_buffer_sent_def\<close>)
qed

end

end