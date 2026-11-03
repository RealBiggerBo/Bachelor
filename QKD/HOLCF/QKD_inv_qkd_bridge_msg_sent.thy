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
    case (App_Master_RequestKey apps kmes bridges qkd net apps' net' n sae kme keys msgs)
    then show ?case
using 2(2) by (auto simp: qkd_bridge_msg_sent_def)
  next
    case (App_Master_KeyResponse apps kmes bridges qkd net apps' net' n sae kme keys msgs keyID keyVal)
    then show ?case
      sorry
  next
    case (App_Slave_AppIDRelay apps kmes bridges qkd net apps' net' n sae kme keys msgs sender keyID)
    then show ?case
using 2(2) unfolding qkd_bridge_msg_sent_def
  by (auto simp: qkd_bridge_msg_sent_def fun_upd_apply list.set_sel(2) split_pairs2)
  next
    case (App_Slave_KeyResponse apps kmes bridges qkd net apps' net' n sae kme keys msgs keyID keyVal)
    then show ?case sorry
  next
    case (App_ReceiveStutter apps kmes bridges qkd net net' n sender msg)
    then show ?case sorry
  next
    case (App_Send apps kmes bridges qkd net apps' net' n msgs rcpt msg appState)
    then show ?case sorry
  next
    case (Kme_KMPost_NewKeyVal apps kmes bridges qkd net kmes' net' n sender otherKme keyID keyVal store route saeToKme bridgeIDs msgs)
    then show ?case sorry
  next
    case (Kme_KMPut_Confirm apps kmes bridges qkd net kmes' net' n sender otherKme keyID store route saeToKme bridgeIDs msgs)
    then show ?case sorry
  next
    case (Kme_GetKey apps kmes bridges qkd net kmes' net' n sender host slaveSae store route saeToKme bridgeIDs msgs keyID val)
    then show ?case sorry
  next
    case (Kme_KMPut_Reserve apps kmes bridges qkd net kmes' net' n sender otherKme slaveSae store route saeToKme bridgeIDs msgs keyID)
    then show ?case sorry
  next
    case (Kme_GetKey_Reserved apps kmes bridges qkd net kmes' net' n sender store keyID val conf res saeID route saeToKme bridgeIDs msgs)
    then show ?case sorry
  next
    case (Kme_GetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n sender host store keyID val saeToKme bridgeIDs masterSae route msgs)
    then show ?case sorry
  next
    case (Kme_GetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' net' n sender host masterSae keyID store route nextKme keyID2 val2 saeToKme bridgeIDs msgs)
    then show ?case sorry
  next
    case (Kme_GetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' net' n nextKme masterSae slaveSae keyID keyID2 store route saeToKme bridgeIDs msgs)
    then show ?case sorry
  next
    case (Kme_KMGetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n nextKme masterSae keyID keyID2 slaveSae store route saeToKme bridgeIDs msgs sender val val2)
    then show ?case sorry
  next
    case (Kme_KMGetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' net' n nextKme masterSae keyID keyID2 slaveSae store val2 sender route keyID3 val3 saeToKme bridgeIDs msgs)
    then show ?case sorry
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' net' n nextKme prevKme masterSae keyID keyID2 slaveSae store route keyID3 saeToKme bridgeIDs msgs)
    then show ?case sorry
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme prevKme keyID keyVal' store keyID2 val2 sender keyID3 val3 masterSae route saeToKme bridgeIDs msgs slaveSae)
    then show ?case sorry
  next
    case (Kme_GetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme keyID keyVal' store keyID2 val2 masterSae sender route saeToKme bridgeIDs msgs)
    then show ?case sorry
  next
    case (Kme_ReceiveStutter apps kmes bridges qkd net net' n sender msg)
    then show ?case sorry
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    then show ?case sorry
  next
    case (Bridge_Tick_GetKey apps kmes bridges qkds net bridges' net' n b slaveBridge otherKme qkd kme msgs)
    then show ?case sorry
  next
    case (Bridge_Master_KeyResponse apps kmes bridges qkds net bridges' net' n b slaveBridge otherKme qkd kme msgs keyID keyVal)
    then show ?case sorry
  next
    case (Bridge_Slave_GetKeyWithID apps kmes bridges qkds net bridges' net' n b masterBridge otherKme qkd kme msgs sender keyID)
    then show ?case sorry
  next
    case (Bridge_Slave_KeyResponse apps kmes bridges qkds net bridges' net' n b masterBridge otherKme qkd kme msgs keyID keyVal)
    then show ?case sorry
  next
    case (Bridge_ReceiveStutter apps kmes bridges qkds net net' n b sender msg)
    then show ?case sorry
  next
    case (Bridge_Send apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState)
    then show ?case sorry
  next
    case (Qkd_GetKey_Gen apps kmes bridges qkd net qkd' net' pid gen sent sender target keyID keyVal)
    then show ?case sorry
  next
    case (Qkd_GetKeyWithID_Reserve apps kmes bridges qkd net qkd' net' pid gen sent sender target keyID keyVal)
    then show ?case sorry
  next
    case (Qkd_ReceiveStutter apps kmes bridges qkd net qkd' net' pid sender msg)
    then show ?case sorry
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    then show ?case sorry
  next
    case (Network_Ext_Receive apps kmes bridges qkd net net' sender rcpt msg all)
    then show ?case sorry
  next
    case (Network_Ext_Send apps kmes bridges qkd net net' sender rcpt msg all)
    then show ?case sorry
  qed
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
    have "\<forall>s1 r1 keyID' keyVal'.
            (keyID' \<noteq> keyID \<or> keyVal' \<noteq> keyVal) 
            \<longrightarrow> (
              s1 \<in> qkdID ` \<Union> (bridgeIDs ` nodes) \<and>
              r1 \<in> \<Union> (bridgeIDs ` nodes) \<and> 
              network_has_msg s s1 r1 (KeyResponse keyID' keyVal') 
              \<longleftrightarrow> 
              s1 \<in> qkdID ` \<Union> (bridgeIDs ` nodes) \<and>
              r1 \<in> \<Union> (bridgeIDs ` nodes) \<and> 
              network_has_msg t s1 r1 (KeyResponse keyID' keyVal'))"
      using Qkd_Send(2,3,8) by auto
    moreover have "\<forall>s1 r1 keyID' keyVal'.
                    (keyID' \<noteq> keyID \<or> keyVal' \<noteq> keyVal) 
                    \<longrightarrow> (
                      qkd_has_key s keyID' keyVal' 
                      \<longleftrightarrow> 
                      qkd_has_key t keyID' keyVal')"
      using Qkd_Send(2,3,9,10) by force
    ultimately have "\<forall>s1 r1 keyID' keyVal'.
                      (keyID' \<noteq> keyID \<or> keyVal' \<noteq> keyVal) \<and>
                      s1 \<in> qkdID ` \<Union>(bridgeIDs `  nodes) \<and>
                      r1 \<in> \<Union>(bridgeIDs ` nodes) \<and> 
                      network_has_msg t s1 r1 (KeyResponse keyID' keyVal') 
                      \<longrightarrow>
                        qkd_has_key t keyID' keyVal'"
      using 2(2) unfolding qkd_bridge_msg_sent_def by metis
    moreover have "\<forall>s1 r1.
                    s1 \<in> qkdID ` \<Union>(bridgeIDs `  nodes) \<and>
                    r1 \<in> \<Union>(bridgeIDs ` nodes) \<and> 
                    network_has_msg t s1 r1 (KeyResponse keyID keyVal) 
                    \<longrightarrow>
                      qkd_has_key t keyID keyVal"
      using 2(2) Qkd_Send(3,10) unfolding qkd_bridge_msg_sent_def by simp
    ultimately show ?case
      using 2(2)
      unfolding qkd_bridge_msg_sent_def by metis
  next
    case (Network_Ext_Receive apps kmes bridges qkd net net' sender rcpt msg all)
    then have "rcpt \<notin> \<Union>(bridgeIDs ` nodes)"
      by fast
    then have "qkd_bridge_msg_sent nodes bridgeIDs qkdID s \<longleftrightarrow> qkd_bridge_msg_sent nodes bridgeIDs qkdID t"
      using Network_Ext_Receive(2,3,11) unfolding qkd_bridge_msg_sent_def apply simp apply auto
        apply blast+
      by (smt (verit) UN_I image_eqI)
    then show ?case 
      using 2(2) by argo
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