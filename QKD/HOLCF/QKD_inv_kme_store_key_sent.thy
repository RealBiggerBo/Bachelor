theory QKD_inv_kme_store_key_sent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
          QKD_inv_bridge_kme_msg_sent
          QKD_inv_kme_bridgeIDs_field_valid
begin

context QKD_Network
begin

lemma keyStore_add_same:
  "\<exists>c r. keyStore_add store k kv p k = Some (kv, p, c, r)"
  by (cases "store k") (auto split: prod.splits)

lemma keyStore_add_other:
  "k' \<noteq> k \<Longrightarrow> keyStore_add store k kv p k' = store k'"
  by (cases "store k") (auto split: prod.splits)

lemma inv_kme_store_key_sent:
  shows "invariant System.ioa (kme_store_key_sent nodes kmeID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 apps kmes bridges qkd net)
    then show ?thesis
      unfolding kme_store_key_sent_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (Kme_KMPost_NewKeyVal apps kmes bridges qkd net kmes' net' n sender otherKme keyID keyVal store route saeToKme bridgeIDs' msgs)
    have "network_has_msg s sender (kmeID n) (KMPost otherKme keyID keyVal)"
      using Kme_KMPost_NewKeyVal(2,8) by (metis list.set_sel(1) snd_conv)
    moreover have "sender \<in> \<Union>(bridgeIDs ` nodes)"
      using Kme_KMPost_NewKeyVal(2,4,9,10) 2(1) inv_kme_bridgeIDs_field_valid 
      unfolding invariant_def kme_bridgeIDs_field_valid_def by fastforce
    ultimately have "qkd_has_key s keyID keyVal"
      using 2(1) inv_bridge_kme_msg_sent Kme_KMPost_NewKeyVal(4)
      unfolding invariant_def bridge_kme_msg_sent_def by blast
    then have "qkd_has_key t keyID keyVal"
      using Kme_KMPost_NewKeyVal(2,3) by simp
    then have "\<forall>keyID keyVal. kme_has_key (kme t n) keyID keyVal \<longrightarrow> qkd_has_key t keyID keyVal"
      using 2(2) Kme_KMPost_NewKeyVal(2,3,4,10,11) unfolding kme_store_key_sent_def  
       apply (auto split: option.splits if_splits) by force+
    moreover have "\<forall>n' keyID keyVal. n' \<in> nodes - {n} \<and> kme_has_key (kme t n') keyID keyVal \<longrightarrow> qkd_has_key t keyID keyVal"
      using 2(2) Kme_KMPost_NewKeyVal(2,3,11) unfolding kme_store_key_sent_def by auto
    ultimately show ?case
      unfolding kme_store_key_sent_def by blast
  next
    case (Kme_KMPut_Confirm apps kmes bridges qkd net kmes' net' n sender otherKme keyID store route saeToKme bridgeIDs msgs)
    have "\<And>keyID keyVal. qkd_has_key s keyID keyVal \<longleftrightarrow> qkd_has_key t keyID keyVal"
      using Kme_KMPut_Confirm(2,3) by force
    moreover have "\<And>keyID keyVal n. n \<in> nodes 
                      \<longrightarrow> (kme_has_key (kme s n) keyID keyVal \<longleftrightarrow> kme_has_key (kme t n) keyID keyVal)"
      using Kme_KMPut_Confirm(2,3,9,10) apply simp by (auto split: option.splits)
    ultimately show ?case 
      using 2(2) unfolding kme_store_key_sent_def by meson
  next
    case (Kme_GetKey apps kmes bridges qkd net kmes' net' n sender host slaveSae store route saeToKme bridgeIDs msgs keyID val)
    have "\<And>keyID keyVal. qkd_has_key s keyID keyVal \<longleftrightarrow> qkd_has_key t keyID keyVal"
      using Kme_GetKey(2,3) by force
    moreover have "\<And>keyID keyVal n. n \<in> nodes 
                      \<longrightarrow> (kme_has_key (kme s n) keyID keyVal \<longleftrightarrow> kme_has_key (kme t n) keyID keyVal)"
      using Kme_GetKey(2,3,10,11) by auto
    ultimately show ?case 
      using 2(2) unfolding kme_store_key_sent_def by meson
  next
    case (Kme_KMPut_Reserve apps kmes bridges qkd net kmes' net' n sender otherKme slaveSae store route saeToKme bridgeIDs msgs keyID)
    have "\<And>keyID keyVal. qkd_has_key s keyID keyVal \<longleftrightarrow> qkd_has_key t keyID keyVal"
      using Kme_KMPut_Reserve(2,3) by force
    moreover have "\<And>keyID keyVal n. n \<in> nodes 
                      \<longrightarrow> (kme_has_key (kme s n) keyID keyVal \<longleftrightarrow> kme_has_key (kme t n) keyID keyVal)"
      using Kme_KMPut_Reserve(2,3,9,10) apply simp by (auto split: option.splits)
    ultimately show ?case 
      using 2(2) unfolding kme_store_key_sent_def by meson
  next
    case (Kme_GetKey_Reserved apps kmes bridges qkd net kmes' net' n sender store keyID val conf res saeID route saeToKme bridgeIDs msgs)
    have "\<And>keyID keyVal n. kme_has_key (kme t n) keyID keyVal \<longrightarrow> kme_has_key (kme s n) keyID keyVal"
      using Kme_GetKey_Reserved(2,3,8,10,11) by auto
    moreover have "\<And>keyID keyVal. qkd_has_key s keyID keyVal \<longrightarrow> qkd_has_key t keyID keyVal"
      using Kme_GetKey_Reserved(2,3) by force
    ultimately show ?case
      using 2(2) unfolding kme_store_key_sent_def by meson
  next
    case (Kme_GetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n sender host store keyID val saeToKme bridgeIDs masterSae route msgs)
    have "\<And>keyID keyVal n. kme_has_key (kme t n) keyID keyVal \<longrightarrow> kme_has_key (kme s n) keyID keyVal"
      using Kme_GetKeyWithID_IDFound(2,3,8,10,11) by auto
    moreover have "\<And>keyID keyVal. qkd_has_key s keyID keyVal \<longrightarrow> qkd_has_key t keyID keyVal"
      using Kme_GetKeyWithID_IDFound(2,3) by force
    ultimately show ?case
      using 2(2) unfolding kme_store_key_sent_def by meson
  next
    case (Kme_GetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' net' n sender host masterSae keyID store route nextKme keyID2 val2 saeToKme bridgeIDs msgs)
    have "\<And>keyID keyVal. qkd_has_key s keyID keyVal \<longleftrightarrow> qkd_has_key t keyID keyVal"
      using Kme_GetKeyWithID_IDNotFound(2,3) by force
    moreover have "\<And>keyID keyVal n. n \<in> nodes 
                      \<longrightarrow> (kme_has_key (kme s n) keyID keyVal \<longleftrightarrow> kme_has_key (kme t n) keyID keyVal)"
      using Kme_GetKeyWithID_IDNotFound(2,3,12,13) by auto
    ultimately show ?case 
      using 2(2) unfolding kme_store_key_sent_def by meson
  next
    case (Kme_GetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' net' n nextKme masterSae slaveSae keyID keyID2 store route saeToKme bridgeIDs msgs)
    have "\<And>keyID keyVal. qkd_has_key s keyID keyVal \<longleftrightarrow> qkd_has_key t keyID keyVal"
      using Kme_GetKeyWithID_IDNotFound_Reserved(2,3) by force
    moreover have "\<And>keyID keyVal n. n \<in> nodes 
                      \<longrightarrow> (kme_has_key (kme s n) keyID keyVal \<longleftrightarrow> kme_has_key (kme t n) keyID keyVal)"
      using Kme_GetKeyWithID_IDNotFound_Reserved(2,3,9,10) by auto
    ultimately show ?case 
      using 2(2) unfolding kme_store_key_sent_def by meson
  next
    case (Kme_KMGetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n nextKme masterSae keyID keyID2 slaveSae store route saeToKme bridgeIDs msgs sender val val2)
    have "\<And>keyID keyVal n. kme_has_key (kme t n) keyID keyVal \<longrightarrow> kme_has_key (kme s n) keyID keyVal"
      using Kme_KMGetKeyWithID_IDFound(2,3,8,11,12) by auto
    moreover have "\<And>keyID keyVal. qkd_has_key s keyID keyVal \<longrightarrow> qkd_has_key t keyID keyVal"
      using Kme_KMGetKeyWithID_IDFound(2,3) by force
    ultimately show ?case
      using 2(2) unfolding kme_store_key_sent_def by meson
  next
    case (Kme_KMGetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' net' n nextKme masterSae keyID keyID2 slaveSae store val2 sender route keyID3 val3 saeToKme bridgeIDs msgs)
    have "\<And>keyID keyVal. qkd_has_key s keyID keyVal \<longleftrightarrow> qkd_has_key t keyID keyVal"
      using Kme_KMGetKeyWithID_IDNotFound(2,3) by force
    moreover have "\<And>keyID keyVal n. n \<in> nodes 
                      \<longrightarrow> (kme_has_key (kme s n) keyID keyVal \<longleftrightarrow> kme_has_key (kme t n) keyID keyVal)"
      using Kme_KMGetKeyWithID_IDNotFound(2,3,14,13) by auto
    ultimately show ?case 
      using 2(2) unfolding kme_store_key_sent_def by meson
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' net' n nextKme prevKme masterSae keyID keyID2 slaveSae store route keyID3 saeToKme bridgeIDs msgs)
    have "\<And>keyID keyVal. qkd_has_key s keyID keyVal \<longleftrightarrow> qkd_has_key t keyID keyVal"
      using Kme_KMGetKeyWithID_IDNotFound_Reserved(2,3) by force
    moreover have "\<And>keyID keyVal n. n \<in> nodes 
                      \<longrightarrow> (kme_has_key (kme s n) keyID keyVal \<longleftrightarrow> kme_has_key (kme t n) keyID keyVal)"
      using Kme_KMGetKeyWithID_IDNotFound_Reserved(2,3,9,10) by auto
    ultimately show ?case 
      using 2(2) unfolding kme_store_key_sent_def by meson
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme prevKme keyID keyVal' store keyID2 val2 sender keyID3 val3 masterSae route saeToKme bridgeIDs msgs slaveSae)
    have "\<And>keyID keyVal n. kme_has_key (kme t n) keyID keyVal \<longrightarrow> kme_has_key (kme s n) keyID keyVal"
      using Kme_KMGetKeyWithID_IDNotFound_Return(2,3,8,11,12) by auto
    moreover have "\<And>keyID keyVal. qkd_has_key s keyID keyVal \<longrightarrow> qkd_has_key t keyID keyVal"
      using Kme_KMGetKeyWithID_IDNotFound_Return(2,3) by force
    ultimately show ?case
      using 2(2) unfolding kme_store_key_sent_def by meson
  next
    case (Kme_GetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme keyID keyVal' store keyID2 val2 masterSae sender route saeToKme bridgeIDs msgs)
    have "\<And>keyID keyVal n. kme_has_key (kme t n) keyID keyVal \<longrightarrow> kme_has_key (kme s n) keyID keyVal"
      using Kme_GetKeyWithID_IDNotFound_Return(2,3,7,9,10,11) by auto
    moreover have "\<And>keyID keyVal. qkd_has_key s keyID keyVal \<longrightarrow> qkd_has_key t keyID keyVal"
      using Kme_GetKeyWithID_IDNotFound_Return(2,3) by force
    ultimately show ?case
      using 2(2) unfolding kme_store_key_sent_def by meson
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    have "\<And>keyID keyVal. qkd_has_key s keyID keyVal \<longleftrightarrow> qkd_has_key t keyID keyVal"
      using Kme_Send(2,3,7,9,10) by force
    moreover have "\<And>keyID keyVal n. n \<in> nodes 
                      \<longrightarrow> (kme_has_key (kme s n) keyID keyVal \<longleftrightarrow> kme_has_key (kme t n) keyID keyVal)"
      using Kme_Send(2,3,9,10) kme_has_key.elims(2) apply auto by force+
    ultimately show ?case 
      using 2(2) unfolding kme_store_key_sent_def by meson
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    have "\<And>keyID keyVal. qkd_has_key s keyID keyVal \<longleftrightarrow> qkd_has_key t keyID keyVal"
      using Qkd_Send(2,3,7,9,10) by force
    then show ?case 
      using 2(2) Qkd_Send(2,3) unfolding kme_store_key_sent_def by simp
  qed
  (use 2(2) in \<open>auto simp: kme_store_key_sent_def\<close>)
qed

end

end