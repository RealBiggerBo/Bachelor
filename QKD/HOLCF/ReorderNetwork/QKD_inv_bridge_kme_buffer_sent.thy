theory QKD_inv_bridge_kme_buffer_sent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
begin

context QKD_Network
begin

lemma inv_bridge_kme_buffer_sent:
  shows "invariant System.ioa (bridge_kme_buffer_sent nodes kmeID bridgeIDs qkdID)"
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
    case (App_Send apps kmes bridges qkd net apps' net' n msgs rcpt msg appState)
    then show ?case
      using 2(2) unfolding bridge_kme_buffer_sent_def apply simp
      by blast
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    then show ?case
      using 2(2) unfolding bridge_kme_buffer_sent_def apply simp
      by blast
  next
    case (Bridge_Master_KeyResponse apps kmes bridges qkds net bridges' n b slaveBridge otherKme qkd kme msgs keyID keyVal)
    have "qkd \<in> qkdID ` \<Union> (bridgeIDs ` nodes)"
      sorry
    then show ?case
      using 2(2) Bridge_Master_KeyResponse(2-10) unfolding bridge_kme_buffer_sent_def apply simp
      by blast
  next
    case (Bridge_Slave_KeyResponse apps kmes bridges qkds net bridges' n b masterBridge otherKme qkd kme msgs keyID keyVal)
    have "qkd \<in> qkdID ` \<Union> (bridgeIDs ` nodes)"
      sorry
    then show ?case
      using 2(2) Bridge_Slave_KeyResponse(2-10) unfolding bridge_kme_buffer_sent_def apply simp
      by blast
  next
    case (Bridge_Send apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState)
    then show ?case
      using 2(2) unfolding bridge_kme_buffer_sent_def apply simp
      by blast
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    then show ?case
      using 2(2) unfolding bridge_kme_buffer_sent_def apply simp
      by blast
  next
    case (Network_Ext_Send apps kmes bridges qkd net net' sender rcpt msg all)
    then show ?case
      using 2(2) unfolding bridge_kme_buffer_sent_def apply simp 
      by meson
  qed
  (use 2(2) in \<open>auto simp: bridge_kme_buffer_sent_def\<close>)
qed

end

end