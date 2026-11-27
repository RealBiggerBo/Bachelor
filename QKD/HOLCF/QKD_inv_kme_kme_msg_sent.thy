theory QKD_inv_kme_kme_msg_sent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
begin

context QKD_Network
begin

lemma kme_kme_msg_sent_helper_receive:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps', kmes, bridges', qkd, net')"
    and "net' = rmv_msg net sender rcpt msg"
    and "can_send net sender rcpt msg"
    and "kme_kme_msg_sent nodes kmeID dec s"
  shows "kme_kme_msg_sent nodes kmeID dec t"
  unfolding kme_kme_msg_sent_def
proof(intro allI impI)
  fix s1 r1 encKeyID keyID keyVal' encKeyVal
  assume assm:"s1 \<in> kmeID ` nodes \<and>
          r1 \<in> kmeID ` nodes \<and>
          network_has_msg t s1 r1 (KMKeyResponse encKeyID keyID keyVal') \<and> 
          qkd_has_key t encKeyID encKeyVal"
  then have "network_has_msg s s1 r1 (KMKeyResponse encKeyID keyID keyVal')"
    using assms(1-4) apply(auto split: if_splits)
    using image_eqI list.set_sel(2) by fast+
  moreover have "qkd_has_key s encKeyID encKeyVal"
    using assms(1,2) assm by simp
  ultimately have "qkd_has_key s keyID (dec keyVal' encKeyVal)"
    using assm assms(5) unfolding kme_kme_msg_sent_def by meson
  then show "qkd_has_key t keyID (dec keyVal' encKeyVal)"
    using assms(1,2) by force
qed

lemma kme_kme_msg_sent_helper_send:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps', kmes', bridges', qkd, net')"
    and "net' = add_msg net sender rcpt msg"
    and "sender \<notin> kmeID ` nodes"
    and "kme_kme_msg_sent nodes kmeID dec s"
  shows "kme_kme_msg_sent nodes kmeID dec t"
  unfolding kme_kme_msg_sent_def
proof(intro allI impI)
  fix s1 r1 encKeyID keyID keyVal' encKeyVal
  assume assm:"s1 \<in> kmeID ` nodes \<and>
          r1 \<in> kmeID ` nodes \<and>
          network_has_msg t s1 r1 (KMKeyResponse encKeyID keyID keyVal') \<and> 
          qkd_has_key t encKeyID encKeyVal"
  then have "network_has_msg s s1 r1 (KMKeyResponse encKeyID keyID keyVal')"
    using assms(1-4) by(auto split: if_splits)
  moreover have "qkd_has_key s encKeyID encKeyVal"
    using assms(1,2) assm by simp
  ultimately have "qkd_has_key s keyID (dec keyVal' encKeyVal)"
    using assm assms(5) unfolding kme_kme_msg_sent_def by meson
  then show "qkd_has_key t keyID (dec keyVal' encKeyVal)"
    using assms(1,2) by force
qed

lemma inv_kme_kme_msg_sent:
  shows "invariant System.ioa (kme_kme_msg_sent nodes kmeID dec)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 apps kmes bridges qkd net)
    then show ?thesis
      unfolding kme_kme_msg_sent_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (App_Master_RequestKey apps kmes bridges qkd net apps' net' n sae kme keys msgs)
    then show ?case
      using 2(2) by (auto simp: kme_kme_msg_sent_def)
  next
    case (App_Send apps kmes bridges qkd net apps' net' n msgs rcpt msg appState)
    have "appID n \<notin> kmeID ` nodes"
      using disjoint_ids unfolding disjnt_def by fast
    then show ?case
      using 2(2) App_Send by (auto simp: kme_kme_msg_sent_helper_send)
  next
    case (Kme_KMPost_NewKeyVal apps kmes bridges qkd net kmes' net' n sender otherKme keyID keyVal store route saeToKme bridgeIDs kmeIDs msgs)
    then show ?case
      using 2(2) sorry
  next
    case (Kme_KMPut_Confirm apps kmes bridges qkd net kmes' net' n sender otherKme keyID store route saeToKme bridgeIDs kmeIDs msgs)
    then show ?case
      using 2(2) sorry
  next
    case (Kme_GetKey apps kmes bridges qkd net kmes' net' n sender host slaveSae store route saeToKme bridgeIDs kmeIDs msgs keyID val)
    then show ?case
      using 2(2) sorry
  next
    case (Kme_KMPut_Reserve apps kmes bridges qkd net kmes' net' n sender otherKme slaveSae store route saeToKme bridgeIDs kmeIDs msgs keyID)
    then show ?case
      using 2(2) sorry
  next
    case (Kme_GetKey_Reserved apps kmes bridges qkd net kmes' net' n sender store keyID val conf res saeID route saeToKme bridgeIDs kmeIDs msgs)
    then show ?case
      using 2(2) sorry
  next
    case (Kme_GetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n sender host store keyID val saeToKme bridgeIDs kmeIDs masterSae route msgs)
    then show ?case
      using 2(2) sorry
  next
    case (Kme_GetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' net' n sender host masterSae keyID store route nextKme keyID2 val2 saeToKme bridgeIDs kmeIDs msgs)
    then show ?case
      using 2(2) sorry
  next
    case (Kme_GetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' net' n nextKme masterSae slaveSae keyID keyID2 store route saeToKme bridgeIDs kmeIDs msgs)
    then show ?case
      using 2(2) sorry
  next
    case (Kme_KMGetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n masterSae keyID keyID2 slaveSae store route saeToKme bridgeIDs kmeIDs msgs sender val val2)
    then show ?case
      using 2(2) sorry
  next
    case (Kme_KMGetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' net' n nextKme masterSae keyID keyID2 slaveSae store val2 sender route keyID3 val3 saeToKme bridgeIDs kmeIDs msgs)
    then show ?case
      using 2(2) sorry
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' net' n nextKme prevKme masterSae keyID keyID2 slaveSae store route keyID3 saeToKme bridgeIDs kmeIDs msgs)
    then show ?case
      using 2(2) sorry
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme prevKme keyID keyVal' store keyID2 val2 keyID3 val3 masterSae route saeToKme bridgeIDs kmeIDs msgs slaveSae)
    then show ?case
      using 2(2) sorry
  next
    case (Kme_GetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme keyID keyVal' store keyID2 val2 masterSae sender route saeToKme bridgeIDs kmeIDs msgs)
    then show ?case
      using 2(2) sorry
  next
    case (Kme_ReceiveStutter apps kmes bridges qkd net net' n sender msg)
    then show ?case
      using 2(2) sorry
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    then show ?case
      using 2(2) sorry
  next
    case (Bridge_Tick_GetKey apps kmes bridges qkds net bridges' net' n b slaveBridge otherKme qkd kme msgs)
    then show ?case
      using 2(2) by (auto simp: kme_kme_msg_sent_def)
  next
    case (Bridge_Send apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState)
    then have "b \<notin> kmeID ` nodes"
      using disjoint_ids unfolding disjnt_def by fast
    then show ?case
      using 2(2) Bridge_Send by (auto simp: kme_kme_msg_sent_helper_send)
  next
    case (Qkd_GetKey_Gen apps kmes bridges qkd net qkd' net' pid gen sent sender target keyID keyVal)
    then show ?case
      using 2(2) sorry
  next
    case (Qkd_GetKeyWithID_Reserve apps kmes bridges qkd net qkd' net' pid gen sent sender target keyID keyVal)
    then show ?case
      using 2(2) sorry
  next
    case (Qkd_ReceiveStutter apps kmes bridges qkd net qkd' net' pid sender msg)
    then show ?case
      using 2(2) sorry
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    then show ?case
      using 2(2) sorry
  next
    case (Network_Ext_Send apps kmes bridges qkd net net' sender rcpt msg all)
    then show ?case
      using 2(2) by (auto simp: kme_kme_msg_sent_def)
  qed
    (use 2(2) in \<open>auto simp: kme_kme_msg_sent_helper_receive\<close>)
qed

end

end