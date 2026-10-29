theory QKD_inv_qkd_bridge_msg_sent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
begin

context QKD_Network
begin

term qkd_bridge_msg_sent

lemma inv_qkd_bridge_msg_sent:
  shows "invariant System.ioa (qkd_bridge_msg_sent nodes bridgeIDs qkdID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 tn qkd net)
    then show ?thesis
      unfolding qkd_bridge_msg_sent_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (App_Send apps kmes bridges qkd net apps' net' n msgs rcpt msg appState)
    then have "appID n \<notin> qkdID ` \<Union>(bridgeIDs ` nodes)"
      using disjoint_ids
      by (metis (no_types, opaque_lifting) disjnt_iff image_iff rangeI)
    then have "qkd_bridge_msg_sent nodes bridgeIDs qkdID s \<longrightarrow> qkd_bridge_msg_sent nodes bridgeIDs qkdID t"
      using App_Send(2,3,7) unfolding qkd_bridge_msg_sent_def by simp
    then show ?case 
      using 2(2) by argo
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    then have "kmeID n \<notin> qkdID ` \<Union>(bridgeIDs ` nodes)"
      using disjoint_ids
      by (metis (no_types, opaque_lifting) disjnt_iff image_iff rangeI)
    then have "qkd_bridge_msg_sent nodes bridgeIDs qkdID s \<longrightarrow> qkd_bridge_msg_sent nodes bridgeIDs qkdID t"
      using Kme_Send(2,3,7) unfolding qkd_bridge_msg_sent_def by simp
    then show ?case 
      using 2(2) by argo
  next
    case (Bridge_Send apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState)
    then have "b \<notin> qkdID ` \<Union>(bridgeIDs ` nodes)"
      using disjoint_ids unfolding disjnt_def by blast
    then have "qkd_bridge_msg_sent nodes bridgeIDs qkdID s \<longrightarrow> qkd_bridge_msg_sent nodes bridgeIDs qkdID t"
      using Bridge_Send(2,3,8) unfolding qkd_bridge_msg_sent_def by simp
    then show ?case
      using 2(2) by argo
  next
    case (Qkd_GetKey_Gen apps kmes bridges qkd net qkd' net' pid gen sent sender target keyID keyVal)
    show ?case
      using 2(2) Qkd_GetKey_Gen(2-11)
      unfolding qkd_bridge_msg_sent_def apply simp apply auto
       apply (metis SUP_absorb Un_iff insert_iff insert_image list.set_sel(2))
      by (metis UN_absorb UnI1 insertI1 insert_image list.set_sel(2))
  next
    case (Qkd_GetKeyWithID_Reserve apps kmes bridges qkd net qkd' pid gen sent sender target keyID keyVal)
    show ?case
      using 2(2) Qkd_GetKeyWithID_Reserve(2,3,8-11)
      unfolding qkd_bridge_msg_sent_def apply simp apply auto
           apply (metis UN_I image_eqI list.set_sel(2))
          apply (metis UN_I image_eqI list.set_sel(2))
      by blast+
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    then have "qkd_has_key t keyID keyVal"
      by auto
    have "\<forall>s1 r1 keyID keyVal.
       s1 \<in> qkdID ` \<Union> (bridgeIDs ` nodes) \<and>
       r1 \<in> \<Union> (bridgeIDs ` nodes) \<and> network_has_msg t s1 r1 (KeyResponse keyID keyVal)
       \<longrightarrow>
       s1 \<in> qkdID ` \<Union> (bridgeIDs ` nodes) \<and>
       r1 \<in> \<Union> (bridgeIDs ` nodes) \<and> network_has_msg s s1 r1 (KeyResponse keyID keyVal)"
      using Qkd_Send(2-10) apply simp (*Wrongggg! ! ! ! ! ! !*)
      sorry
    moreover have "\<forall>keyID keyVal. qkd_has_key s keyID keyVal \<longleftrightarrow> qkd_has_key t keyID keyVal"
      using Qkd_Send(2,3,7,9,10) apply simp by force
    ultimately show ?case
      using 2(2) Qkd_Send(2,3-10)
      unfolding qkd_bridge_msg_sent_def by meson
  next
    case (Network_Ext_Receive apps kmes bridges qkd net net' sender rcpt msg all)
    then show ?case sorry
  next
    case (Network_Ext_Send apps kmes bridges qkd net net' sender rcpt msg all)
    then have "sender \<notin> qkdID ` \<Union>(bridgeIDs ` nodes)"
      by fast
    then have "qkd_bridge_msg_sent nodes bridgeIDs qkdID s \<longleftrightarrow> qkd_bridge_msg_sent nodes bridgeIDs qkdID t"
      using Network_Ext_Send(2,3,12) unfolding qkd_bridge_msg_sent_def apply simp apply auto
        apply blast+
      by (smt (verit) UN_I image_eqI)
    then show ?case 
      using 2(2) by argo
  qed
  (use 2(2) in \<open>auto simp: qkd_bridge_msg_sent_def\<close>)
qed

end

end