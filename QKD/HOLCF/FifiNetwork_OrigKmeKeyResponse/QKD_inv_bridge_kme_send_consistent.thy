theory QKD_inv_bridge_kme_send_consistent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
          QKD_inv_bridge_kme_msg_sent
          QKD_inv_qkd_bridge_send_consistent
begin

context QKD_Network
begin

lemma inv_bridge_kme_send_consistent:
  shows "invariant System.ioa (bridge_kme_send_consistent nodes kmeID bridgeIDs)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 tn qkd net)
    then show ?thesis
      unfolding bridge_kme_send_consistent_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (App_Send apps kmes bridges qkd net apps' net' n msgs rcpt msg appState)
    then have "appID n \<notin> \<Union>(bridgeIDs ` nodes)"
      using disjoint_ids
      by (meson UnionE app_neq_bridge bex_imageD)
    then have "bridge_kme_send_consistent nodes kmeID bridgeIDs s \<longleftrightarrow> bridge_kme_send_consistent nodes kmeID bridgeIDs t"
      using App_Send(2,3,7) unfolding bridge_kme_send_consistent_def
      by (metis (mono_tags, lifting) Un_iff prod.inject singletonD sndI)
    then show ?case 
      using 2(2) by argo
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    then have "kmeID n \<notin> \<Union>(bridgeIDs ` nodes)"
      using disjoint_ids
      by (meson UnionE kme_neq_bridge bex_imageD)
    then have "bridge_kme_send_consistent nodes kmeID bridgeIDs s \<longleftrightarrow> bridge_kme_send_consistent nodes kmeID bridgeIDs t"
      using Kme_Send(2,3,7) unfolding bridge_kme_send_consistent_def
      by (metis (mono_tags, lifting) Un_iff prod.inject singletonD sndI)
    then show ?case 
      using 2(2) by argo
  next
    case (Bridge_Send apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState)
    then have "bridge_kme_msg_sent nodes kmeID bridgeIDs qkdID t"
      using inv_bridge_kme_msg_sent 2(1) Bridge_Send(1) reachable_n unfolding invariant_def by fast
    moreover have "qkd_bridge_send_consistent nodes bridgeIDs qkdID t"
      using inv_qkd_bridge_send_consistent 2(1) Bridge_Send(1) reachable_n unfolding invariant_def by fast
    ultimately show ?case
      using Bridge_Send(2,3,7,8,9,10)
      unfolding bridge_kme_msg_sent_def qkd_bridge_send_consistent_def bridge_kme_send_consistent_def
      by metis
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    then have "pid \<notin> \<Union>(bridgeIDs ` nodes)"
      using disjoint_ids unfolding disjnt_def by blast
    then have "bridge_kme_send_consistent nodes kmeID bridgeIDs s \<longleftrightarrow> bridge_kme_send_consistent nodes kmeID bridgeIDs t"
      using Qkd_Send(2,3,7) unfolding bridge_kme_send_consistent_def
      by (simp add: Qkd_Send.hyps(2))
    then show ?case 
      using 2(2) by argo
  next
    case (Network_Ext_Send apps kmes bridges qkd net net' sender rcpt msg all)
    then have "sender \<notin> \<Union>(bridgeIDs ` nodes)"
      by fast
    then have "bridge_kme_send_consistent nodes kmeID bridgeIDs s \<longleftrightarrow> bridge_kme_send_consistent nodes kmeID bridgeIDs t"
      using Network_Ext_Send(2,3,12) unfolding bridge_kme_send_consistent_def
      by (metis (no_types, lifting) Un_iff fstI singleton_iff snd_conv)
    then show ?case 
      using 2(2) by argo
  qed
  (use 2(2) in \<open>auto simp: bridge_kme_send_consistent_def\<close>)
qed

end

end