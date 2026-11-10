theory QKD_inv_kme_buffer_msg_field_valid
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
          QKD_inv_bridge_otherKme_field_valid
begin

context QKD_Network
begin

lemma inv_kme_buffer_msg_field_valid:
  shows "invariant System.ioa (kme_buffer_msg_field_valid nodes kmeID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 apps kmes bridges qkd net)
    then show ?thesis
      unfolding kme_buffer_msg_field_valid_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (Kme_KMPost_NewKeyVal apps kmes bridges qkd net kmes' net' n sender otherKme keyID keyVal store route saeToKme bridgeIDs kmeIDs msgs)
    then have "kmeID n \<in> kmeID ` nodes"
      by fast
    then show ?case 
      using 2(2) Kme_KMPost_NewKeyVal(2,3,4,6,10,11) unfolding kme_buffer_msg_field_valid_def apply auto by fast
  next
    case (Kme_KMPut_Confirm apps kmes bridges qkd net kmes' net' n sender otherKme keyID store route saeToKme bridgeIDs kmeIDs msgs)
    then have "kmeID n \<in> kmeID ` nodes"
      by fast
    then show ?case 
      using 2(2) Kme_KMPut_Confirm(2,3,4,8-11) unfolding kme_buffer_msg_field_valid_def by auto
  next
    case (Kme_GetKey apps kmes bridges qkd net kmes' net' n sender host slaveSae store route saeToKme bridgeIDs kmeIDs msgs keyID val)
    then have "kmeID n \<in> kmeID ` nodes"
      by fast
    then show ?case 
      using 2(2) Kme_GetKey(2,3,4,6,10,11) unfolding kme_buffer_msg_field_valid_def apply auto by fast
  next
    case (Kme_KMPut_Reserve apps kmes bridges qkd net kmes' net' n sender otherKme slaveSae store route saeToKme bridgeIDs kmeIDs msgs keyID)
    then have "kmeID n \<in> kmeID ` nodes"
      by fast
    then show ?case 
      using 2(2) Kme_KMPut_Reserve(2,3,4,9,10) unfolding kme_buffer_msg_field_valid_def by auto
  next
    case (Kme_GetKey_Reserved apps kmes bridges qkd net kmes' net' n sender store keyID val conf res saeID route saeToKme bridgeIDs kmeIDs msgs)
    then have "kmeID n \<in> kmeID ` nodes"
      by fast
    then show ?case 
      using 2(2) Kme_GetKey_Reserved(2,3,4,6,10,11) unfolding kme_buffer_msg_field_valid_def by auto
  next
    case (Kme_GetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n sender host store keyID val saeToKme bridgeIDs kmeIDs masterSae route msgs)
    then have "kmeID n \<in> kmeID ` nodes"
      by fast
    then show ?case 
      using 2(2) Kme_GetKeyWithID_IDFound(2,3,4,6,10,11) unfolding kme_buffer_msg_field_valid_def by auto
  next
    case (Kme_GetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' net' n sender host masterSae keyID store route nextKme keyID2 val2 saeToKme bridgeIDs kmeIDs msgs)
    then have "kmeID n \<in> kmeID ` nodes"
      by fast
    then show ?case 
      using 2(2) Kme_GetKeyWithID_IDNotFound(2,3,4,12,13) unfolding kme_buffer_msg_field_valid_def apply auto by fast
  next
    case (Kme_GetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' net' n nextKme masterSae slaveSae keyID keyID2 store route saeToKme bridgeIDs kmeIDs msgs)
    then have "kmeID n \<in> kmeID ` nodes"
      by fast
    then show ?case 
      using 2(2) Kme_GetKeyWithID_IDNotFound_Reserved(2,3,4,9,10) unfolding kme_buffer_msg_field_valid_def by auto
  next
    case (Kme_KMGetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n masterSae keyID keyID2 slaveSae store route saeToKme bridgeIDs kmeIDs msgs sender val val2)
    then have "kmeID n \<in> kmeID ` nodes"
      by fast
    then show ?case 
      using 2(2) Kme_KMGetKeyWithID_IDFound(2,3,4,11,12) unfolding kme_buffer_msg_field_valid_def by auto
  next
    case (Kme_KMGetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' net' n nextKme masterSae keyID keyID2 slaveSae store val2 sender route keyID3 val3 saeToKme bridgeIDs kmeIDs msgs)
    then have "kmeID n \<in> kmeID ` nodes"
      by fast
    then show ?case 
      using 2(2) Kme_KMGetKeyWithID_IDNotFound(2,3,4,13,14) unfolding kme_buffer_msg_field_valid_def apply auto by fast
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' net' n nextKme prevKme masterSae keyID keyID2 slaveSae store route keyID3 saeToKme bridgeIDs kmeIDs msgs)
    then have "kmeID n \<in> kmeID ` nodes"
      by fast
    then show ?case 
      using 2(2) Kme_KMGetKeyWithID_IDNotFound_Reserved(2,3,4,6,9,10) unfolding kme_buffer_msg_field_valid_def by auto
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme prevKme keyID keyVal' store keyID2 val2 keyID3 val3 masterSae route saeToKme bridgeIDs kmeIDs msgs slaveSae)
    then have "kmeID n \<in> kmeID ` nodes"
      by fast
    then show ?case 
      using 2(2) Kme_KMGetKeyWithID_IDNotFound_Return(2,3,4,6,10,11,12) unfolding kme_buffer_msg_field_valid_def by auto
  next
    case (Kme_GetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme keyID keyVal' store keyID2 val2 masterSae sender route saeToKme bridgeIDs kmeIDs msgs)
    then have "kmeID n \<in> kmeID ` nodes"
      by fast
    then show ?case 
      using 2(2) Kme_GetKeyWithID_IDNotFound_Return(2,3,4,6,10,11) unfolding kme_buffer_msg_field_valid_def by auto
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    then have "\<And>n b state msgs rcpt kme' keyID res. 
                kme t n = IoaState state msgs \<and> (kmeID n, rcpt, KMPut kme' keyID res) \<in> msgs
                \<longrightarrow> (\<exists>msgs'. 
                      kme s n = IoaState state msgs' \<and> (kmeID n, rcpt, KMPut kme' keyID res) \<in> msgs')"
      by auto
    then show ?case
      using 2(2) unfolding kme_buffer_msg_field_valid_def by blast
  qed
  (use 2(2) in \<open>auto simp: kme_buffer_msg_field_valid_def\<close>)
qed

end

end