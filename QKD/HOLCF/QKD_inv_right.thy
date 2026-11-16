theory QKD_inv_right
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
begin

context QKD_Network
begin

lemma inv1_helper:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps', kmes, bridges', qkd', net')"
    and "net' = rmv_msg net sender rcpt msg"
    and "can_send net sender rcpt msg"
    and "\<forall>slaveSae keyID encKeyID masterSae. msg \<noteq> KMGet slaveSae keyID encKeyID masterSae"
    and "inv1 nodes kmeID s"
  shows "inv1 nodes kmeID t"
  using assms unfolding inv1_def
  apply simp apply auto
  by (meson list.set_sel(2))+

lemma inv1_helper_stutter:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes, bridges, qkd, net')"
    and "net' = rmv_msg net sender rcpt msg"
    and "can_send net sender rcpt msg"
    and "inv1 nodes kmeID s"
  shows "inv1 nodes kmeID t"
  using assms unfolding inv1_def
  apply simp apply auto
  by (meson list.set_sel(2))+
  

lemma inv_kme_msg_field_valid:
  shows "invariant System.ioa (inv1 nodes kmeID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 apps kmes bridges qkd net)
    then show ?thesis
      unfolding inv1_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (App_Master_RequestKey apps kmes bridges qkd net apps' net' n sae kme keys msgs)
    then have "inv1 nodes kmeID t"
      using 2(2) unfolding inv1_def by auto
    then show ?case 
      by simp
  next
    case (App_Master_KeyResponse apps kmes bridges qkd net apps' net' n sae kme keys msgs keyID keyVal)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper by fastforce
    then show ?case 
      by simp
  next
    case (App_Slave_AppIDRelay apps kmes bridges qkd net apps' net' n sae kme keys msgs sender keyID)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper by fastforce
    then show ?case 
      by simp
  next
    case (App_Slave_KeyResponse apps kmes bridges qkd net apps' net' n sae kme keys msgs keyID keyVal)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper by fastforce
    then show ?case 
      by simp
  next
    case (App_ReceiveStutter apps kmes bridges qkd net net' n sender msg)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper_stutter by fastforce
    then show ?case 
      by simp
  next
    case (App_Send apps kmes bridges qkd net apps' net' n msgs rcpt msg appState)
    then have "inv1 nodes kmeID t"
    proof -
      have "inv1 nodes kmeID s \<longrightarrow> inv1 nodes kmeID t"
        using App_Send(2-10) disjoint_ids unfolding inv1_def disjnt_def apply simp
        by (metis (lifting) IntI UNIV_I empty_iff image_eqI)
      then show ?thesis
        using 2(2) by linarith
    qed
    then show ?case 
      by simp
  next
    case (Kme_KMPost_NewKeyVal apps kmes bridges qkd net kmes' net' n sender otherKme keyID keyVal store route saeToKme bridgeIDs kmeIDs msgs)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper sorry
    then show ?case 
      by simp
  next
    case (Kme_KMPut_Confirm apps kmes bridges qkd net kmes' net' n sender otherKme keyID store route saeToKme bridgeIDs kmeIDs msgs)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper sorry
    then show ?case 
      by simp
  next
    case (Kme_GetKey apps kmes bridges qkd net kmes' net' n sender host slaveSae store route saeToKme bridgeIDs kmeIDs msgs keyID val)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper sorry
    then show ?case 
      by simp
  next
    case (Kme_KMPut_Reserve apps kmes bridges qkd net kmes' net' n sender otherKme slaveSae store route saeToKme bridgeIDs kmeIDs msgs keyID)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper sorry
    then show ?case 
      by simp
  next
    case (Kme_GetKey_Reserved apps kmes bridges qkd net kmes' net' n sender store keyID val conf res saeID route saeToKme bridgeIDs kmeIDs msgs)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper sorry
    then show ?case 
      by simp
  next
    case (Kme_GetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n sender host store keyID val saeToKme bridgeIDs kmeIDs masterSae route msgs)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper sorry
    then show ?case 
      by simp
  next
    case (Kme_GetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' net' n sender host masterSae keyID store route nextKme keyID2 val2 saeToKme bridgeIDs kmeIDs msgs)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper sorry
    then show ?case 
      by simp
  next
    case (Kme_GetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' net' n nextKme masterSae slaveSae keyID keyID2 store route saeToKme bridgeIDs kmeIDs msgs)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper sorry
    then show ?case 
      by simp
  next
    case (Kme_KMGetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n masterSae keyID keyID2 slaveSae store route saeToKme bridgeIDs kmeIDs msgs sender val val2)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper sorry
    then show ?case 
      by simp
  next
    case (Kme_KMGetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' net' n nextKme masterSae keyID keyID2 slaveSae store val2 sender route keyID3 val3 saeToKme bridgeIDs kmeIDs msgs)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper sorry
    then show ?case 
      by simp
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' net' n nextKme prevKme masterSae keyID keyID2 slaveSae store route keyID3 saeToKme bridgeIDs kmeIDs msgs)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper sorry
    then show ?case 
      by simp
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme prevKme keyID keyVal' store keyID2 val2 keyID3 val3 masterSae route saeToKme bridgeIDs kmeIDs msgs slaveSae)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper sorry
    then show ?case 
      by simp
  next
    case (Kme_GetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme keyID keyVal' store keyID2 val2 masterSae sender route saeToKme bridgeIDs kmeIDs msgs)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper sorry
    then show ?case 
      by simp
  next
    case (Kme_ReceiveStutter apps kmes bridges qkd net net' n sender msg)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper_stutter by fastforce
    then show ?case 
      by simp
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    then have "inv1 nodes kmeID t"
    proof -
      have "\<forall>nA nB slaveSae keyID encKeyID masterSae.
              nA \<in> nodes - {n} \<and>
              kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae)
              \<longrightarrow> kme_network_has_msg kmeID s nA nB (KMGet slaveSae keyID encKeyID masterSae)"
        using Kme_Send(2-10) apply auto
        apply (cases msg)
                apply fastforce+
        sorry
      moreover have "\<forall>nB slaveSae keyID encKeyID masterSae.
              kme_network_has_msg kmeID t n nB (KMGet slaveSae keyID encKeyID masterSae)
              \<longrightarrow> kme_network_has_msg kmeID s n nB (KMGet slaveSae keyID encKeyID masterSae)"
        using Kme_Send(2-10) by simp 
      moreover have "\<forall>nA encKeyID. 
                      nA \<in> nodes - {n} \<and>
                      kme_has_decryptionKeyID (kme s nA) = Some encKeyID
                      \<longrightarrow> kme_has_decryptionKeyID (kme t nA) = Some encKeyID"
        using Kme_Send(2-10) by simp
      moreover have "\<forall>encKeyID.
                      kme_has_decryptionKeyID (kme s n) = Some encKeyID
                      \<longrightarrow> kme_has_decryptionKeyID (kme t n) = Some encKeyID"
        using Kme_Send(2-10) kme_has_decryptionKeyID.elims by force
      ultimately have "inv1 nodes kmeID s \<longrightarrow> inv1 nodes kmeID t"
        unfolding inv1_def apply auto by blast+
      then show ?thesis
        using 2(2) by linarith
    qed
    then show ?case 
      by simp
  next
    case (Bridge_Tick_GetKey apps kmes bridges qkds net bridges' net' n b slaveBridge otherKme qkd kme msgs)
    then have "inv1 nodes kmeID t"
      using 2(2) unfolding inv1_def by auto
    then show ?case 
      by simp
  next
    case (Bridge_Master_KeyResponse apps kmes bridges qkds net bridges' net' n b slaveBridge otherKme qkd kme msgs keyID keyVal)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper by fastforce
    then show ?case 
      by simp
  next
    case (Bridge_Slave_GetKeyWithID apps kmes bridges qkds net bridges' net' n b masterBridge otherKme qkd kme msgs keyID)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper by fastforce
    then show ?case 
      by simp
  next
    case (Bridge_Slave_KeyResponse apps kmes bridges qkds net bridges' net' n b masterBridge otherKme qkd kme msgs keyID keyVal)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper by fastforce
    then show ?case 
      by simp
  next
    case (Bridge_ReceiveStutter apps kmes bridges qkds net net' n b sender msg)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper_stutter by fastforce
    then show ?case 
      by simp
  next
    case (Bridge_Send apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper sorry
    then show ?case 
      by simp
  next
    case (Qkd_GetKey_Gen apps kmes bridges qkd net qkd' net' pid gen sent sender target keyID keyVal)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper by fastforce
    then show ?case 
      by simp
  next
    case (Qkd_GetKeyWithID_Reserve apps kmes bridges qkd net qkd' net' pid gen sent sender target keyID keyVal)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper by fastforce
    then show ?case 
      by simp
  next
    case (Qkd_ReceiveStutter apps kmes bridges qkd net qkd' net' pid sender msg)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper_stutter by fastforce
    then show ?case 
      by simp
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    then have "inv1 nodes kmeID t"
    proof -
      have "inv1 nodes kmeID s \<longrightarrow> inv1 nodes kmeID t"
        using Qkd_Send(2-10) disjoint_ids unfolding inv1_def disjnt_def apply simp
        by metis
      then show ?thesis
        using 2(2) by linarith
    qed
    then show ?case 
      by simp
  next
    case (Network_Ext_Receive apps kmes bridges qkd net net' sender rcpt msg all)
    then have "inv1 nodes kmeID t"
      using 2(2) inv1_helper sorry
    then show ?case 
      by simp
  next
    case (Network_Ext_Send apps kmes bridges qkd net net' sender rcpt msg all)
    then have "inv1 nodes kmeID s \<longrightarrow> inv1 nodes kmeID t"
      unfolding inv1_def 
    then have "inv1 nodes kmeID t"
    proof -
      have "\<forall>n. kme_has_decryptionKeyID (kme s n) = kme_has_decryptionKeyID (kme t n)"
        using Network_Ext_Send(2,3) by simp
      moreover have "(\<forall>nA nB slaveSae keyID encKeyID masterSae.
        nA \<in> nodes \<and> nB \<in> nodes \<and> kme_network_has_msg kmeID s nA nB (KMGet slaveSae keyID encKeyID masterSae) = kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae))"
        using Network_Ext_Send(2,3-12)
    then show ?case 
      by simp
  qed
qed

end

end