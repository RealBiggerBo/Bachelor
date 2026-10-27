theory QKD_inv_qkd_bridge_msg_sent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
begin

context QKD_Network
begin

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
    then have "qkd_bridge_msg_sent nodes bridgeIDs qkdID s \<longleftrightarrow> qkd_bridge_msg_sent nodes bridgeIDs qkdID t"
      using App_Send(2,3,7) unfolding qkd_bridge_msg_sent_def
      by (smt (verit) Un_empty_right Un_insert_right insert_iff split_pairs2)
    then show ?case 
      using 2(2) by argo
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    then have "kmeID n \<notin> qkdID ` \<Union>(bridgeIDs ` nodes)"
      using disjoint_ids
      by (metis (no_types, opaque_lifting) disjnt_iff image_iff rangeI)
    then have "qkd_bridge_msg_sent nodes bridgeIDs qkdID s \<longleftrightarrow> qkd_bridge_msg_sent nodes bridgeIDs qkdID t"
      using Kme_Send(2,3,7) unfolding qkd_bridge_msg_sent_def
      by (smt (verit) Un_empty_right Un_insert_right insert_iff split_pairs2)
    then show ?case 
      using 2(2) by argo
  next
    case (Bridge_Send apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState)
    then have "b \<notin> qkdID ` \<Union>(bridgeIDs ` nodes)"
      using disjoint_ids unfolding disjnt_def by blast
    then have "qkd_bridge_msg_sent nodes bridgeIDs qkdID s \<longleftrightarrow> qkd_bridge_msg_sent nodes bridgeIDs qkdID t"
      using Bridge_Send(2,3,8) unfolding qkd_bridge_msg_sent_def
      by (smt (verit) Un_empty_right Un_insert_right insert_iff split_pairs2)
    then show ?case
      using 2(2) by argo
  next
    case (Qkd_GetKey_Gen apps kmes bridges qkd net qkd' pid gen sent sender target keyID keyVal)
    show ?case
      using 2(2) Qkd_GetKey_Gen(2-9)
      unfolding qkd_bridge_msg_sent_def by simp
  next
    case (Qkd_GetKeyWithID_Reserve apps kmes bridges qkd net qkd' pid gen sent sender target keyID keyVal)
    show ?case
      using 2(2) Qkd_GetKeyWithID_Reserve(2-9)
      unfolding qkd_bridge_msg_sent_def apply simp apply auto
      by blast+
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    have "\<forall>keyID' keyVal'. 
            (\<exists>gen sent. qkd_layer t = QKD gen sent \<and> (keyID', keyVal') \<in> snd ` gen \<union> sent) 
            \<longleftrightarrow> (\<exists>gen sent. qkd_layer s = QKD gen sent \<and> (keyID', keyVal') \<in> snd ` gen \<union> sent)"
      using Qkd_Send(2,3,8,9,10) apply simp
      by (smt (verit, best) Diff_subset Pair_inject Qkd_Send.hyps(1) image_insert image_mono 
                            insertE insert_Diff rev_image_eqI snd_conv subsetD)
    moreover have "network t - {(pid, rcpt, KeyResponse keyID keyVal)} \<subseteq> network s"
      using Qkd_Send(2,3,8,9,10) by simp
    ultimately have "\<forall>s1 r1 keyID' keyVal'. 
                        s1 \<in> qkdID ` \<Union> (bridgeIDs ` nodes) \<and> 
                        r1 \<in> \<Union> (bridgeIDs ` nodes) \<and> 
                        (s1, r1, KeyResponse keyID' keyVal') \<in> (network t - {(pid, rcpt, KeyResponse keyID keyVal)}) 
                        \<longrightarrow> (\<exists>gen sent. 
                                qkd_layer t = QKD gen sent \<and> 
                                (keyID', keyVal') \<in> snd ` gen \<union> sent)"
      using 2(2) Qkd_Send(2-10) unfolding qkd_bridge_msg_sent_def
      apply simp apply auto
         apply blast
        apply blast
       apply blast
      by (metis UN_I image_eqI)
    moreover have "\<forall>s1 r1 keyID' keyVal'. s1 \<in> qkdID ` \<Union> (bridgeIDs ` nodes) \<and> r1 \<in> \<Union> (bridgeIDs ` nodes) \<and> (s1, r1, KeyResponse keyID' keyVal') \<in> ({(pid, rcpt, KeyResponse keyID keyVal)}) \<longrightarrow>
       (\<exists>gen sent. qkd_layer t = QKD gen sent \<and> (keyID', keyVal') \<in> snd ` gen \<union> sent)"
      using Qkd_Send by simp
    ultimately show ?case
      unfolding qkd_bridge_msg_sent_def 
      by (metis DiffI)
  next
    case (Network_Ext_Send apps kmes bridges qkd net net' sender rcpt msg all)
    then have "sender \<notin> qkdID ` \<Union>(bridgeIDs ` nodes)"
      by fast
    then have "qkd_bridge_msg_sent nodes bridgeIDs qkdID s \<longleftrightarrow> qkd_bridge_msg_sent nodes bridgeIDs qkdID t"
      using Network_Ext_Send(2,3,12) unfolding qkd_bridge_msg_sent_def
      by (metis (no_types, lifting) Un_iff fstI singleton_iff snd_conv)
    then show ?case 
      using 2(2) by argo
  qed
  (use 2(2) in \<open>auto simp: qkd_bridge_msg_sent_def\<close>)
qed

end

end