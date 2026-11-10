theory QKD_inv_kme_store_partnerField_valid
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
          QKD_inv_kme_bridgeIDs_field_valid
          QKD_inv_bridge_kme_msgField_valid
          QKD_inv_kme_msg_field_valid
          QKD_inv_kme_kmeIDs_field_valid
begin

lemma kme_get_store_ignores_msgs:
  "kme_get_store (IoaState state msgs) = kme_get_store (IoaState state msgs')"
  by (cases state) simp_all

context QKD_Network
begin

lemma inv_kme_store_partnerField_valid:
  shows "invariant System.ioa (kme_store_partnerField_valid nodes kmeID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 tn qkd net)
    then show ?thesis
      unfolding kme_store_partnerField_valid_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (Kme_KMPost_NewKeyVal apps kmes bridges qkd net kmes' net' n sender otherKme keyID keyVal store route saeToKme bridgeIDs' kmeIDs msgs)
    have "bridge_kme_msgField_valid nodes bridgeIDs kmeID s \<and> kme_bridgeIDs_field_valid nodes bridgeIDs s"
      using 2(1) inv_kme_bridgeIDs_field_valid inv_bridge_kme_msgField_valid
      unfolding invariant_def by fast
    moreover have "network_has_msg s sender (kmeID n) (KMPost otherKme keyID keyVal)"
      using Kme_KMPost_NewKeyVal(2,8) by (metis hd_in_set sndI)
    moreover have "sender \<in> \<Union> (bridgeIDs ` nodes)"
      using calculation(1) Kme_KMPost_NewKeyVal(2,4,9,10) unfolding kme_bridgeIDs_field_valid_def by force
    ultimately have "otherKme \<in> kmeID ` nodes"
      unfolding bridge_kme_msgField_valid_def by blast
    then have "\<forall>keyID keyVal partner conf res.
                  kme_get_store (kme t n) keyID = Some (Some keyVal, partner, conf, res)
                  \<longrightarrow> partner \<in> kmeID ` nodes"
      using 2(2) Kme_KMPost_NewKeyVal(2,3,4,10,11) 
      unfolding kme_store_partnerField_valid_def apply (auto split: option.split) by fastforce+
    moreover have "\<forall>n' keyID keyVal partner conf res.
                  n' \<in> nodes - {n} \<and>
                  kme_get_store (kme t n') keyID = Some (Some keyVal, partner, conf, res)
                  \<longrightarrow> partner \<in> kmeID ` nodes"
      using 2(2) Kme_KMPost_NewKeyVal(2,3,11) 
      unfolding kme_store_partnerField_valid_def by auto
    ultimately show ?case
      unfolding kme_store_partnerField_valid_def by blast
  next
    case (Kme_KMPut_Confirm apps kmes bridges qkd net kmes' net' n sender otherKme keyID store route saeToKme bridgeIDs' kmeIDs msgs)
    have "kme_msg_field_valid nodes kmeID s \<and> kme_kmeIDs_field_valid nodes kmeID s"
      using inv_kme_msg_field_valid inv_kme_kmeIDs_field_valid 2(1) unfolding invariant_def by fast
    moreover have "network_has_msg s sender (kmeID n) (KMPut otherKme keyID None)"
      using Kme_KMPut_Confirm(8) by (metis Kme_KMPut_Confirm.IH(2) hd_in_set snd_conv)
    moreover have "sender \<in> kmeID ` nodes"
      using Kme_KMPut_Confirm(2,4,9,10) calculation(1) unfolding kme_kmeIDs_field_valid_def by auto
    ultimately have "otherKme \<in> kmeID ` nodes"
      unfolding kme_msg_field_valid_def by blast
    then have "\<forall>keyID keyVal partner conf res.
                  kme_get_store (kme t n) keyID = Some (Some keyVal, partner, conf, res)
                  \<longrightarrow> partner \<in> kmeID ` nodes"
      using 2(2) Kme_KMPut_Confirm(2,3,4,10,11) 
      unfolding kme_store_partnerField_valid_def apply (auto split: option.split) by fastforce+
    moreover have "\<forall>n' keyID keyVal partner conf res.
                  n' \<in> nodes - {n} \<and>
                  kme_get_store (kme t n') keyID = Some (Some keyVal, partner, conf, res)
                  \<longrightarrow> partner \<in> kmeID ` nodes"
      using 2(2) Kme_KMPut_Confirm(2,3,11) 
      unfolding kme_store_partnerField_valid_def by auto
    ultimately show ?case
      unfolding kme_store_partnerField_valid_def by blast
  next
    case (Kme_GetKey apps kmes bridges qkd net kmes' net' n sender host slaveSae store route saeToKme bridgeIDs kmeIDs msgs keyID val)
    then have "\<forall>n keyID. kme_get_store (kme s n) keyID = kme_get_store (kme t n) keyID"
      by simp
    then show ?case
      using 2(2)
      unfolding kme_store_partnerField_valid_def by presburger
  next
    case (Kme_KMPut_Reserve apps kmes bridges qkd net kmes' net' n sender otherKme slaveSae store route saeToKme bridgeIDs kmeIDs msgs keyID)
    then have "\<forall>keyID keyVal partner conf res.
                  kme_get_store (kme t n) keyID = Some (Some keyVal, partner, conf, res)
                  \<longrightarrow> partner \<in> kmeID ` nodes"
      using 2(2) 
      unfolding kme_store_partnerField_valid_def apply (auto split: option.split) by fastforce+
    moreover have "\<forall>n' keyID keyVal partner conf res.
                  n' \<in> nodes - {n} \<and>
                  kme_get_store (kme t n') keyID = Some (Some keyVal, partner, conf, res)
                  \<longrightarrow> partner \<in> kmeID ` nodes"
      using 2(2) Kme_KMPut_Reserve(2,3,10) 
      unfolding kme_store_partnerField_valid_def by auto
    ultimately show ?case
      unfolding kme_store_partnerField_valid_def by blast
  next
    case (Kme_GetKey_Reserved apps kmes bridges qkd net kmes' net' n sender store keyID val conf res saeID route saeToKme bridgeIDs kmeIDs msgs)
    then have "\<forall>keyID keyVal partner conf res.
                  kme_get_store (kme t n) keyID = Some (Some keyVal, partner, conf, res)
                  \<longrightarrow> partner \<in> kmeID ` nodes"
      using 2(2) 
      unfolding kme_store_partnerField_valid_def apply (auto split: option.split) by fastforce+
    moreover have "\<forall>n' keyID keyVal partner conf res.
                  n' \<in> nodes - {n} \<and>
                  kme_get_store (kme t n') keyID = Some (Some keyVal, partner, conf, res)
                  \<longrightarrow> partner \<in> kmeID ` nodes"
      using 2(2) Kme_GetKey_Reserved(2,3,11) 
      unfolding kme_store_partnerField_valid_def by auto
    ultimately show ?case
      unfolding kme_store_partnerField_valid_def by blast
  next
    case (Kme_GetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n sender host store keyID val saeToKme bridgeIDs kmeIDs masterSae route msgs)
    then have "\<forall>keyID keyVal partner conf res.
                  kme_get_store (kme t n) keyID = Some (Some keyVal, partner, conf, res)
                  \<longrightarrow> partner \<in> kmeID ` nodes"
      using 2(2) 
      unfolding kme_store_partnerField_valid_def apply (auto split: option.split) by fastforce+
    moreover have "\<forall>n' keyID keyVal partner conf res.
                  n' \<in> nodes - {n} \<and>
                  kme_get_store (kme t n') keyID = Some (Some keyVal, partner, conf, res)
                  \<longrightarrow> partner \<in> kmeID ` nodes"
      using 2(2) Kme_GetKeyWithID_IDFound(2,3,11) 
      unfolding kme_store_partnerField_valid_def by auto
    ultimately show ?case
      unfolding kme_store_partnerField_valid_def by blast
  next
    case (Kme_GetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' net' n sender host masterSae keyID store route nextKme keyID2 val2 saeToKme bridgeIDs kmeIDs msgs)
    then have "\<forall>n keyID. kme_get_store (kme s n) keyID = kme_get_store (kme t n) keyID"
      by simp
    then show ?case
      using 2(2)
      unfolding kme_store_partnerField_valid_def by presburger
  next
    case (Kme_GetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' net' n nextKme masterSae slaveSae keyID keyID2 store route saeToKme bridgeIDs kmeIDs msgs)
    then have "\<forall>n keyID. kme_get_store (kme s n) keyID = kme_get_store (kme t n) keyID"
      by simp
    then show ?case
      using 2(2)
      unfolding kme_store_partnerField_valid_def by presburger
  next
    case (Kme_KMGetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n masterSae keyID keyID2 slaveSae store route saeToKme bridgeIDs kmeIDs msgs sender val val2)
    then have "\<forall>keyID keyVal partner conf res.
                  kme_get_store (kme t n) keyID = Some (Some keyVal, partner, conf, res)
                  \<longrightarrow> partner \<in> kmeID ` nodes"
      using 2(2) 
      unfolding kme_store_partnerField_valid_def apply (auto split: option.split) by fastforce+
    moreover have "\<forall>n' keyID keyVal partner conf res.
                  n' \<in> nodes - {n} \<and>
                  kme_get_store (kme t n') keyID = Some (Some keyVal, partner, conf, res)
                  \<longrightarrow> partner \<in> kmeID ` nodes"
      using 2(2) Kme_KMGetKeyWithID_IDFound(2,3,12) 
      unfolding kme_store_partnerField_valid_def by auto
    ultimately show ?case
      unfolding kme_store_partnerField_valid_def by blast
  next
    case (Kme_KMGetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' net' n nextKme masterSae keyID keyID2 slaveSae store val2 sender route keyID3 val3 saeToKme bridgeIDs kmeIDs msgs)
    then have "\<forall>n keyID. kme_get_store (kme s n) keyID = kme_get_store (kme t n) keyID"
      by simp
    then show ?case
      using 2(2)
      unfolding kme_store_partnerField_valid_def by presburger
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' net' n nextKme prevKme masterSae keyID keyID2 slaveSae store route keyID3 saeToKme bridgeIDs kmeIDs msgs)
    then have "\<forall>n keyID. kme_get_store (kme s n) keyID = kme_get_store (kme t n) keyID"
      by simp
    then show ?case
      using 2(2)
      unfolding kme_store_partnerField_valid_def by presburger
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme prevKme keyID keyVal' store keyID2 val2 keyID3 val3 masterSae route saeToKme bridgeIDs kmeIDs msgs slaveSae)
    then have "\<forall>keyID keyVal partner conf res.
                  kme_get_store (kme t n) keyID = Some (Some keyVal, partner, conf, res)
                  \<longrightarrow> partner \<in> kmeID ` nodes"
      using 2(2) 
      unfolding kme_store_partnerField_valid_def apply (auto split: option.split) by fastforce+
    moreover have "\<forall>n' keyID keyVal partner conf res.
                  n' \<in> nodes - {n} \<and>
                  kme_get_store (kme t n') keyID = Some (Some keyVal, partner, conf, res)
                  \<longrightarrow> partner \<in> kmeID ` nodes"
      using 2(2) Kme_KMGetKeyWithID_IDNotFound_Return(2,3,12) 
      unfolding kme_store_partnerField_valid_def by auto
    ultimately show ?case
      unfolding kme_store_partnerField_valid_def by blast
  next
    case (Kme_GetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme keyID keyVal' store keyID2 val2 masterSae sender route saeToKme bridgeIDs kmeIDs msgs)
    then have "\<forall>keyID keyVal partner conf res.
                  kme_get_store (kme t n) keyID = Some (Some keyVal, partner, conf, res)
                  \<longrightarrow> partner \<in> kmeID ` nodes"
      using 2(2) 
      unfolding kme_store_partnerField_valid_def apply (auto split: option.split) by fastforce+
    moreover have "\<forall>n' keyID keyVal partner conf res.
                  n' \<in> nodes - {n} \<and>
                  kme_get_store (kme t n') keyID = Some (Some keyVal, partner, conf, res)
                  \<longrightarrow> partner \<in> kmeID ` nodes"
      using 2(2) Kme_GetKeyWithID_IDNotFound_Return(2,3,11) 
      unfolding kme_store_partnerField_valid_def by auto
    ultimately show ?case
      unfolding kme_store_partnerField_valid_def by blast
  next
    case (Kme_ReceiveStutter apps kmes bridges qkd net net' n sender msg)
    then have "\<forall>n keyID. kme_get_store (kme s n) keyID = kme_get_store (kme t n) keyID"
      by simp
    then show ?case
      using 2(2)
      unfolding kme_store_partnerField_valid_def by presburger
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    then show ?case
      using kme_get_store_ignores_msgs 2(2) unfolding kme_store_partnerField_valid_def
      by (smt (verit, ccfv_threshold) fun_upd_other fun_upd_same split_pairs)
  qed
  (use 2(2) in \<open>auto simp: kme_store_partnerField_valid_def\<close>)
qed

end

end