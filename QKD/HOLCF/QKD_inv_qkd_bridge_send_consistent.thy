theory QKD_inv_qkd_bridge_send_consistent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
          QKD_inv_qkd_bridge_msg_sent
          QKD_inv_qkd_layer_consistent
begin

context QKD_Network
begin

lemma inv_qkd_bridge_send_consistent:
  shows "invariant System.ioa (qkd_bridge_send_consistent nodes bridgeIDs qkdID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 tn qkd net)
    then show ?thesis
      unfolding qkd_bridge_send_consistent_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (App_Send apps kmes bridges qkd net apps' net' n msgs rcpt msg appState)
    then have "appID n \<notin> qkdID ` \<Union>(bridgeIDs ` nodes)"
      using disjoint_ids
      by (metis (no_types, opaque_lifting) disjnt_iff image_iff rangeI)
    then have "qkd_bridge_send_consistent nodes bridgeIDs qkdID s \<longleftrightarrow> qkd_bridge_send_consistent nodes bridgeIDs qkdID t"
      using App_Send(2,3,7) unfolding qkd_bridge_send_consistent_def
      by (metis (mono_tags, lifting) Un_iff prod.inject singletonD sndI)
    then show ?case 
      using 2(2) by argo
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    then have "kmeID n \<notin> qkdID ` \<Union>(bridgeIDs ` nodes)"
      using disjoint_ids
      by (metis (no_types, opaque_lifting) disjnt_iff image_iff rangeI)
    then have "qkd_bridge_send_consistent nodes bridgeIDs qkdID s \<longleftrightarrow> qkd_bridge_send_consistent nodes bridgeIDs qkdID t"
      using Kme_Send(2,3,7) unfolding qkd_bridge_send_consistent_def
      by (metis (mono_tags, lifting) Un_iff prod.inject singletonD sndI)
    then show ?case 
      using 2(2) by argo
  next
    case (Bridge_Send apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState)
    then have "b \<notin> qkdID ` \<Union>(bridgeIDs ` nodes)"
      using disjoint_ids unfolding disjnt_def by blast
    then have "qkd_bridge_send_consistent nodes bridgeIDs qkdID s \<longleftrightarrow> qkd_bridge_send_consistent nodes bridgeIDs qkdID t"
      using Bridge_Send(2,3,8) unfolding qkd_bridge_send_consistent_def
      by (metis (mono_tags, lifting) Un_iff prod.inject singletonD sndI)
    then show ?case 
      using 2(2) by argo
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    then have "qkd_bridge_msg_sent nodes bridgeIDs qkdID t"
      using inv_qkd_bridge_msg_sent 2(1) Qkd_Send(1) reachable_n unfolding invariant_def by fast
    moreover have "qkd_layer_consistent t"
      using inv_qkd_layer_consistent 2(1) Qkd_Send(1) reachable_n unfolding invariant_def by fast
    ultimately show ?case
      unfolding qkd_bridge_msg_sent_def qkd_layer_consistent_def qkd_bridge_send_consistent_def
      by (metis qkd_layer_state.inject)
  next
    case (Network_Ext_Send apps kmes bridges qkd net net' sender rcpt msg all)
    then have "sender \<notin> qkdID ` \<Union>(bridgeIDs ` nodes)"
      by fast
    then have "qkd_bridge_send_consistent nodes bridgeIDs qkdID s \<longleftrightarrow> qkd_bridge_send_consistent nodes bridgeIDs qkdID t"
      using Network_Ext_Send(2,3,12) unfolding qkd_bridge_send_consistent_def
      by (metis (no_types, lifting) Un_iff fstI singleton_iff snd_conv)
    then show ?case 
      using 2(2) by argo
  qed
  (use 2(2) in \<open>auto simp: qkd_bridge_send_consistent_def\<close>)
qed

end

end