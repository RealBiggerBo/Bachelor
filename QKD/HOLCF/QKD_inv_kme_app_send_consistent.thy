theory QKD_inv_kme_app_send_consistent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
          (*QKD_inv_kme_app_msg_sent*)
          QKD_inv_bridge_kme_send_consistent
begin

context QKD_Network
begin

lemma inv_kme_app_send_consistent:
  shows "invariant System.ioa (kme_app_send_consistent nodes appID kmeID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 tn qkd net)
    then show ?thesis
      unfolding kme_app_send_consistent_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (App_Send apps kmes bridges qkd net apps' net' n msgs rcpt msg appState)
    then have "appID n \<notin> kmeID ` nodes"
      using disjoint_ids
      by (metis (no_types, opaque_lifting) disjnt_iff image_iff range_eqI)
    then have "kme_app_send_consistent nodes appID kmeID s \<longleftrightarrow> kme_app_send_consistent nodes appID kmeID t"
      using App_Send(2,3,7) unfolding kme_app_send_consistent_def
      by (metis (mono_tags, lifting) Un_iff prod.inject singletonD sndI)
    then show ?case 
      using 2(2) by argo
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    then have "kme_app_msg_sent nodes appID kmeID bridgeIDs t"
      sorry
    moreover have "bridge_kme_send_consistent nodes kmeID bridgeIDs t"
      using inv_bridge_kme_send_consistent 2(1) Kme_Send(1) reachable_n unfolding invariant_def by fast
    ultimately show ?case
      using Kme_Send(2,3,7,8,9,10)
      unfolding kme_app_msg_sent_def bridge_kme_send_consistent_def kme_app_send_consistent_def
      by metis
  next
    case (Bridge_Send apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState)
    then have "b \<notin> kmeID ` nodes"
      using disjoint_ids
      by (smt (verit, ccfv_threshold) UNIV_I Union_iff disjnt_insert2 image_iff insert_absorb)
    then have "kme_app_send_consistent nodes appID kmeID s \<longleftrightarrow> kme_app_send_consistent nodes appID kmeID t"
      using Bridge_Send(2,3,8) unfolding kme_app_send_consistent_def
      by (metis (mono_tags, lifting) Un_iff prod.inject singletonD sndI)
    then show ?case 
      using 2(2) by argo
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    then have "pid \<notin> kmeID ` nodes"
      using disjoint_ids
      by (metis (no_types, opaque_lifting) disjnt_iff image_iff insertCI insert_UNIV)
    then have "kme_app_send_consistent nodes appID kmeID s \<longleftrightarrow> kme_app_send_consistent nodes appID kmeID t"
      using Qkd_Send(2,3,8) unfolding kme_app_send_consistent_def
      by (metis (mono_tags, lifting) Un_iff prod.inject singletonD sndI)
    then show ?case 
      using 2(2) by argo
  next
    case (Network_Ext_Send apps kmes bridges qkd net net' sender rcpt msg all)
    then have "sender \<notin> kmeID ` nodes"
      by fast
    then have "kme_app_send_consistent nodes appID kmeID s \<longleftrightarrow> kme_app_send_consistent nodes appID kmeID t"
      using Network_Ext_Send(2,3,12) unfolding kme_app_send_consistent_def
      by (metis (mono_tags, lifting) Un_iff prod.inject singletonD sndI)
    then show ?case 
      using 2(2) by argo
  qed
  (use 2(2) in \<open>auto simp: kme_app_send_consistent_def\<close>)
qed

end

end