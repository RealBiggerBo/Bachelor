theory QKD_inv_bridge_kme_msg_sent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
          QKD_inv_bridge_kme_buffer_sent
begin

context QKD_Network
begin

lemma inv_bridge_kme_msg_sent:
  shows "invariant System.ioa (bridge_kme_msg_sent nodes kmeID bridgeIDs qkdID)"
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
    case (App_Send apps kmes bridges qkd net apps' net' n msgs rcpt msg appState)
    then have "appID n \<notin> \<Union>(bridgeIDs ` nodes)"
      using disjoint_ids
      by (meson UnionE app_neq_bridge bex_imageD)
    then have "bridge_kme_msg_sent nodes kmeID bridgeIDs qkdID s \<longrightarrow> bridge_kme_msg_sent nodes kmeID bridgeIDs qkdID t"
      using App_Send(2,3,7) unfolding bridge_kme_msg_sent_def
      apply simp by blast
    then show ?case
      using 2(2) by argo
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    then have "kmeID n \<notin> \<Union>(bridgeIDs ` nodes)"
      using disjoint_ids
      by (meson UnionE kme_neq_bridge bex_imageD)
    then have "bridge_kme_msg_sent nodes kmeID bridgeIDs qkdID s \<longrightarrow> bridge_kme_msg_sent nodes kmeID bridgeIDs qkdID t"
      using Kme_Send(2,3,7) unfolding bridge_kme_msg_sent_def
      apply simp by blast
    then show ?case 
      using 2(2) by argo
  next
    case (Bridge_Send apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState)
    then have "bridge_kme_buffer_sent nodes kmeID bridgeIDs qkdID s"
      using inv_bridge_kme_buffer_sent 2(1) reachable_n unfolding invariant_def by fast
    then show ?case
      using Bridge_Send(2,3,4,5,8,9,10,11) 2(2)
      unfolding bridge_kme_buffer_sent_def bridge_kme_msg_sent_def apply simp apply auto
      by blast+
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    then have "pid \<notin> \<Union>(bridgeIDs ` nodes)"
      using disjoint_ids unfolding disjnt_def by blast
    then have "bridge_kme_msg_sent nodes kmeID bridgeIDs qkdID s \<longrightarrow> bridge_kme_msg_sent nodes kmeID bridgeIDs qkdID t"
      using Qkd_Send(2,3,7) Qkd_Send.hyps(2) unfolding bridge_kme_msg_sent_def
      apply simp apply auto by blast      
    then show ?case 
      using 2(2) by argo
  next
    case (Network_Ext_Send apps kmes bridges qkd net net' sender rcpt msg all)
    then have "sender \<notin> \<Union>(bridgeIDs ` nodes)"
      by fast
    then have "bridge_kme_msg_sent nodes kmeID bridgeIDs qkdID s \<longrightarrow> bridge_kme_msg_sent nodes kmeID bridgeIDs qkdID t"
      using Network_Ext_Send(2,3,12) unfolding bridge_kme_msg_sent_def
      apply simp by blast
    then show ?case
      using 2(2) by argo
  qed
  (use 2(2) in \<open>auto simp: bridge_kme_msg_sent_def\<close>)
qed

end

end