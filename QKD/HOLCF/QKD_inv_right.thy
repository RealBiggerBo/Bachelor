theory QKD_inv_right
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
begin

context QKD_Network
begin

lemma kme_network_has_msg_no_kme_change:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps', kmes, bridges', qkd', net')"
    and "(net' = rmv_msg net sender rcpt msg \<and> can_send net sender rcpt msg) \<or> net' = net"
  shows "\<And>msg. kme_network_has_msg kmeID t nA nB msg \<Longrightarrow> kme_network_has_msg kmeID s nA nB msg"
  using assms apply (auto split: if_splits)
  apply(cases "net (kmeID nA, kmeID nB)")
  apply meson by simp

lemma 
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps', kmes', bridges', qkd', net')"
    and "kmes n = IoaState state msgs"
    and "kmes' = kmes(n := IoaState state' (msgs \<union> newMsgs))"
    and "net' = rmv_msg net sender rcpt msg"
    and "can_send net sender rcpt msg"
  shows "\<And>msg. \<lbrakk>(kmeID nA, kmeID nB, msg) \<notin> newMsgs; kme_network_has_msg kmeID t nA nB msg\<rbrakk> \<Longrightarrow> kme_network_has_msg kmeID s nA nB msg"
  using assms apply (auto split: if_splits)
  apply(cases "net (kmeID nA, kmeID nB)")
    apply meson apply simp
  apply(cases "net (kmeID nA, kmeID nB)") apply fast by simp

lemma right_helper_receive_no_kme_change:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps', kmes, bridges', qkd', net')"
    and "(net' = rmv_msg net sender rcpt msg \<and> can_send net sender rcpt msg) \<or> net' = net"
    and "right nodes kmeID s"
  shows "right nodes kmeID t"
proof -
  have "inv1 nodes kmeID t"
    using assms unfolding inv1_def
    apply simp
    apply(cases "net' = net")
     apply metis
    apply auto
    by (meson list.set_sel(2))+
  moreover have "inv2 nodes kmeID t"
    unfolding inv2_def
  proof (intro allI impI)
    fix nA nB slaveSae keyID' keyVal' keyID encKeyID masterSae
    assume assm:"nA \<in> nodes \<and> nB \<in> nodes \<and> kme_network_has_msg kmeID t nB nA (KeyResponse keyID' keyVal')"
    then have "kme_network_has_msg kmeID s nB nA (KeyResponse keyID' keyVal')"
      using kme_network_has_msg_no_kme_change[OF assms(1,2,3)] by simp
    then have "\<not> kme_network_has_msg kmeID s nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      using assms(4) assm unfolding inv2_def by blast
    then show "\<not> kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      using kme_network_has_msg_no_kme_change[OF assms(1,2,3)] by auto
  qed
  moreover have "inv3 nodes kmeID t"
    unfolding inv3_def
  proof (intro allI impI)
    fix nA nB
    assume assm:"nA \<in> nodes \<and> nB \<in> nodes"
    have "card (kme_get_buffer_msg kmeID s nA nB is_KMGet) = card (kme_get_buffer_msg kmeID t nA nB is_KMGet)"
      using assms(1,2) by simp
    moreover have "length (filter is_KMGet (network t (kmeID nA, kmeID nB))) \<le> length (filter is_KMGet (network s (kmeID nA, kmeID nB)))"
      using assms(1,2,3) apply auto
      apply (cases "net (kmeID nA, kmeID nB)") by simp_all
    ultimately have "kme_get_msg_count kmeID t nA nB QKD_inv_def.is_KMGet \<le> kme_get_msg_count kmeID s nA nB QKD_inv_def.is_KMGet"
      by simp
    moreover have "kme_get_msg_count kmeID s nA nB QKD_inv_def.is_KMGet \<le> 1"
      using assm assms(4) unfolding inv3_def by simp
    ultimately show "kme_get_msg_count kmeID t nA nB QKD_inv_def.is_KMGet \<le> 1"
      by simp
  qed
  moreover have "inv4 nodes kmeID t"
    unfolding inv4_def
  proof (intro allI impI)
    fix nA nB slaveSae keyID encKeyID masterSae
    assume assm:"nA \<in> nodes \<and> nB \<in> nodes \<and> kme_network_has_msg kmeID t nB nA OK"
    then have "kme_network_has_msg kmeID s nB nA OK"
      using kme_network_has_msg_no_kme_change[OF assms(1,2,3)] by simp
    then have "\<not> kme_network_has_msg kmeID s nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      using assms(4) assm unfolding inv4_def by blast
    then show "\<not> kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      using kme_network_has_msg_no_kme_change[OF assms(1,2,3)] by auto
  qed
  moreover have "inv5 nodes kmeID t"
    unfolding inv5_def
  proof (intro allI impI)
    fix nA nB kmID keyID' reserveOption slaveSae keyID encKeyID masterSae
    assume assm:"nA \<in> nodes \<and> nB \<in> nodes \<and> kme_network_has_msg kmeID t nA nB (KMPut kmID keyID' reserveOption)"
    then have "kme_network_has_msg kmeID s nA nB (KMPut kmID keyID' reserveOption)"
      using kme_network_has_msg_no_kme_change[OF assms(1,2,3)] by simp
    then have "\<not> kme_network_has_msg kmeID s nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      using assms(4) assm unfolding inv5_def by blast
    then show "\<not> kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      using kme_network_has_msg_no_kme_change[OF assms(1,2,3)] by auto
  qed
  moreover have "inv6 nodes kmeID t"
    unfolding inv6_def
  proof (intro allI impI)
    fix nA nB slaveSae keyID encKeyID masterSae
    assume assm:"nA \<in> nodes \<and> nB \<in> nodes \<and> kme_has_decryptionKeyID (kme t nA) = None"
    then have "kme_has_decryptionKeyID (kme s nA) = None"
      using assms(1,2) by simp
    then have "\<not> kme_network_has_msg kmeID s nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      using assms(4) assm unfolding inv6_def by blast
    then show "\<not> kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      using kme_network_has_msg_no_kme_change[OF assms(1,2,3)] by auto
  qed
  ultimately show ?thesis
    by simp
qed

lemma right_helper_send:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps', kmes', bridges', qkd', net')"
    and "net' = add_msg net sender rcpt msg"
    and "right nodes kmeID s"
  shows "right nodes kmeID t"
  sorry
  

lemma inv_kme_msg_field_valid:
  shows "invariant System.ioa (right nodes kmeID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 apps kmes bridges qkd net)
    then show ?thesis
      unfolding inv1_def inv2_def inv3_def inv4_def inv5_def inv6_def by force
  qed
next
  case (2 s t a)
  note invs = inv1_def inv2_def inv3_def inv4_def inv5_def inv6_def
  show ?case
    using 2 
  proof (induction rule: System_step_induct)
    case (App_Send apps kmes bridges qkd net apps' net' n msgs rcpt msg appState)
    show ?case sorry
  next
    case (Kme_KMPost_NewKeyVal apps kmes bridges qkd net kmes' net' n sender otherKme keyID keyVal store route saeToKme bridgeIDs kmeIDs msgs)
    show ?case sorry
  next
    case (Kme_KMPut_Confirm apps kmes bridges qkd net kmes' net' n sender otherKme keyID store route saeToKme bridgeIDs kmeIDs msgs)
    show ?case sorry
  next
    case (Kme_GetKey apps kmes bridges qkd net kmes' net' n sender host slaveSae store route saeToKme bridgeIDs kmeIDs msgs keyID val)
    show ?case sorry
  next
    case (Kme_KMPut_Reserve apps kmes bridges qkd net kmes' net' n sender otherKme slaveSae store route saeToKme bridgeIDs kmeIDs msgs keyID)
    show ?case sorry
  next
    case (Kme_GetKey_Reserved apps kmes bridges qkd net kmes' net' n sender store keyID val conf res saeID route saeToKme bridgeIDs kmeIDs msgs)
    show ?case sorry
  next
    case (Kme_GetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n sender host store keyID val saeToKme bridgeIDs kmeIDs masterSae route msgs)
    show ?case sorry
  next
    case (Kme_GetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' net' n sender host masterSae keyID store route nextKme keyID2 val2 saeToKme bridgeIDs kmeIDs msgs)
    show ?case sorry
  next
    case (Kme_GetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' net' n nextKme masterSae slaveSae keyID keyID2 store route saeToKme bridgeIDs kmeIDs msgs)
    show ?case sorry
  next
    case (Kme_KMGetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n masterSae keyID keyID2 slaveSae store route saeToKme bridgeIDs kmeIDs msgs sender val val2)
    show ?case sorry
  next
    case (Kme_KMGetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' net' n nextKme masterSae keyID keyID2 slaveSae store val2 sender route keyID3 val3 saeToKme bridgeIDs kmeIDs msgs)
    show ?case sorry
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' net' n nextKme prevKme masterSae keyID keyID2 slaveSae store route keyID3 saeToKme bridgeIDs kmeIDs msgs)
    show ?case sorry
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme prevKme keyID keyVal' store keyID2 val2 keyID3 val3 masterSae route saeToKme bridgeIDs kmeIDs msgs slaveSae)
    show ?case sorry
  next
    case (Kme_GetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme keyID keyVal' store keyID2 val2 masterSae sender route saeToKme bridgeIDs kmeIDs msgs)
    show ?case sorry
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    show ?case sorry
  next
    case (Bridge_Send apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState)
    show ?case sorry
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    show ?case sorry
  next
    case (Network_Ext_Send apps kmes bridges qkd net net' sender rcpt msg all)
    show ?case sorry
  qed (use 2(2) right_helper_receive_no_kme_change in \<open>meson+\<close>)
qed

end

end