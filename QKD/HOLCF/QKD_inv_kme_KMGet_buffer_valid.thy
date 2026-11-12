theory QKD_inv_kme_KMGet_buffer_valid
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
begin

context QKD_Network
begin

lemma inv_kme_KMGet_buffer_valid:
  shows "invariant System.ioa (kme_KMGet_buffer_valid nodes kmeID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 apps kmes bridges qkd net)
    then show ?thesis
      unfolding kme_KMGet_buffer_valid_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (App_Master_RequestKey apps kmes bridges qkd net apps' net' n sae kme keys msgs)
    then show ?case 
      using 2(2) unfolding kme_KMGet_buffer_valid_def by auto
  next
    case (App_Master_KeyResponse apps kmes bridges qkd net apps' net' n sae kme keys msgs keyID keyVal)
    then show ?case 
      using 2(2) unfolding kme_KMGet_buffer_valid_def by auto
  next
    case (App_Slave_AppIDRelay apps kmes bridges qkd net apps' net' n sae kme keys msgs sender keyID)
    then show ?case 
      using 2(2) unfolding kme_KMGet_buffer_valid_def by auto
  next
    case (App_Slave_KeyResponse apps kmes bridges qkd net apps' net' n sae kme keys msgs keyID keyVal)
    then show ?case 
      using 2(2) unfolding kme_KMGet_buffer_valid_def by auto
  next
    case (App_ReceiveStutter apps kmes bridges qkd net net' n sender msg)
    then show ?case 
      using 2(2) unfolding kme_KMGet_buffer_valid_def by auto
  next
    case (App_Send apps kmes bridges qkd net apps' net' n msgs rcpt msg appState)
    then show ?case 
      using 2(2) unfolding kme_KMGet_buffer_valid_def by auto
  next
    case (Kme_KMPost_NewKeyVal apps kmes bridges qkd net kmes' net' n sender otherKme keyID keyVal store route saeToKme bridgeIDs kmeIDs msgs)
    then have "kme_KMGet_buffer_valid {n} kmeID s \<longrightarrow>  kme_KMGet_buffer_valid {n} kmeID t"
      unfolding kme_KMGet_buffer_valid_def by simp
    moreover have "kme_KMGet_buffer_valid (nodes - {n}) kmeID s \<longrightarrow>  kme_KMGet_buffer_valid (nodes - {n}) kmeID t"
      using Kme_KMPost_NewKeyVal
      unfolding kme_KMGet_buffer_valid_def by auto
    ultimately have "kme_KMGet_buffer_valid nodes kmeID s \<longrightarrow>  kme_KMGet_buffer_valid nodes kmeID t"
      unfolding kme_KMGet_buffer_valid_def by blast
    then show ?case 
      using 2(2) by simp
  next
    case (Kme_KMPut_Confirm apps kmes bridges qkd net kmes' net' n sender otherKme keyID store route saeToKme bridgeIDs kmeIDs msgs)
    then have "kme_KMGet_buffer_valid {n} kmeID s \<longrightarrow>  kme_KMGet_buffer_valid {n} kmeID t"
      unfolding kme_KMGet_buffer_valid_def by simp
    moreover have "kme_KMGet_buffer_valid (nodes - {n}) kmeID s \<longrightarrow>  kme_KMGet_buffer_valid (nodes - {n}) kmeID t"
      using Kme_KMPut_Confirm
      unfolding kme_KMGet_buffer_valid_def by auto
    ultimately have "kme_KMGet_buffer_valid nodes kmeID s \<longrightarrow>  kme_KMGet_buffer_valid nodes kmeID t"
      unfolding kme_KMGet_buffer_valid_def by blast
    then show ?case 
      using 2(2) by simp
  next
    case (Kme_GetKey apps kmes bridges qkd net kmes' net' n sender host slaveSae store route saeToKme bridgeIDs kmeIDs msgs keyID val)
    then have "kme_KMGet_buffer_valid {n} kmeID s \<longrightarrow>  kme_KMGet_buffer_valid {n} kmeID t"
      unfolding kme_KMGet_buffer_valid_def by simp
    moreover have "kme_KMGet_buffer_valid (nodes - {n}) kmeID s \<longrightarrow>  kme_KMGet_buffer_valid (nodes - {n}) kmeID t"
      using Kme_GetKey
      unfolding kme_KMGet_buffer_valid_def by auto
    ultimately have "kme_KMGet_buffer_valid nodes kmeID s \<longrightarrow>  kme_KMGet_buffer_valid nodes kmeID t"
      unfolding kme_KMGet_buffer_valid_def by blast
    then show ?case 
      using 2(2) by simp
  next
    case (Kme_KMPut_Reserve apps kmes bridges qkd net kmes' net' n sender otherKme slaveSae store route saeToKme bridgeIDs kmeIDs msgs keyID)
    then have "kme_KMGet_buffer_valid {n} kmeID s \<longrightarrow>  kme_KMGet_buffer_valid {n} kmeID t"
      unfolding kme_KMGet_buffer_valid_def by simp
    moreover have "kme_KMGet_buffer_valid (nodes - {n}) kmeID s \<longrightarrow>  kme_KMGet_buffer_valid (nodes - {n}) kmeID t"
      using Kme_KMPut_Reserve
      unfolding kme_KMGet_buffer_valid_def by auto
    ultimately have "kme_KMGet_buffer_valid nodes kmeID s \<longrightarrow>  kme_KMGet_buffer_valid nodes kmeID t"
      unfolding kme_KMGet_buffer_valid_def by blast
    then show ?case 
      using 2(2) by simp
  next
    case (Kme_GetKey_Reserved apps kmes bridges qkd net kmes' net' n sender store keyID val conf res saeID route saeToKme bridgeIDs kmeIDs msgs)
    then have "kme_KMGet_buffer_valid {n} kmeID s \<longrightarrow>  kme_KMGet_buffer_valid {n} kmeID t"
      unfolding kme_KMGet_buffer_valid_def by simp
    moreover have "kme_KMGet_buffer_valid (nodes - {n}) kmeID s \<longrightarrow>  kme_KMGet_buffer_valid (nodes - {n}) kmeID t"
      using Kme_GetKey_Reserved
      unfolding kme_KMGet_buffer_valid_def by auto
    ultimately have "kme_KMGet_buffer_valid nodes kmeID s \<longrightarrow>  kme_KMGet_buffer_valid nodes kmeID t"
      unfolding kme_KMGet_buffer_valid_def by blast
    then show ?case 
      using 2(2) by simp
  next
    case (Kme_GetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n sender host store keyID val saeToKme bridgeIDs kmeIDs masterSae route msgs)
    then have "kme_KMGet_buffer_valid {n} kmeID s \<longrightarrow>  kme_KMGet_buffer_valid {n} kmeID t"
      unfolding kme_KMGet_buffer_valid_def by simp
    moreover have "kme_KMGet_buffer_valid (nodes - {n}) kmeID s \<longrightarrow>  kme_KMGet_buffer_valid (nodes - {n}) kmeID t"
      using Kme_GetKeyWithID_IDFound
      unfolding kme_KMGet_buffer_valid_def by auto
    ultimately have "kme_KMGet_buffer_valid nodes kmeID s \<longrightarrow>  kme_KMGet_buffer_valid nodes kmeID t"
      unfolding kme_KMGet_buffer_valid_def by blast
    then show ?case 
      using 2(2) by simp
  next
    case (Kme_GetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' net' n sender host masterSae keyID store route nextKme keyID2 val2 saeToKme bridgeIDs kmeIDs msgs)
    then have "kme_KMGet_buffer_valid {n} kmeID s \<longrightarrow>  kme_KMGet_buffer_valid {n} kmeID t"
      unfolding kme_KMGet_buffer_valid_def by simp
    moreover have "kme_KMGet_buffer_valid (nodes - {n}) kmeID s \<longrightarrow>  kme_KMGet_buffer_valid (nodes - {n}) kmeID t"
      using Kme_GetKeyWithID_IDNotFound
      unfolding kme_KMGet_buffer_valid_def by auto
    ultimately have "kme_KMGet_buffer_valid nodes kmeID s \<longrightarrow>  kme_KMGet_buffer_valid nodes kmeID t"
      unfolding kme_KMGet_buffer_valid_def by blast
    then show ?case 
      using 2(2) by simp
  next
    case (Kme_GetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' net' n nextKme masterSae slaveSae keyID keyID2 store route saeToKme bridgeIDs kmeIDs msgs)
    then have "kme_KMGet_buffer_valid {n} kmeID s \<longrightarrow>  kme_KMGet_buffer_valid {n} kmeID t"
      unfolding kme_KMGet_buffer_valid_def by simp
    moreover have "kme_KMGet_buffer_valid (nodes - {n}) kmeID s \<longrightarrow>  kme_KMGet_buffer_valid (nodes - {n}) kmeID t"
      using Kme_GetKeyWithID_IDNotFound_Reserved
      unfolding kme_KMGet_buffer_valid_def by auto
    ultimately have "kme_KMGet_buffer_valid nodes kmeID s \<longrightarrow>  kme_KMGet_buffer_valid nodes kmeID t"
      unfolding kme_KMGet_buffer_valid_def by blast
    then show ?case 
      using 2(2) by simp
  next
    case (Kme_KMGetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n masterSae keyID keyID2 slaveSae store route saeToKme bridgeIDs kmeIDs msgs sender val val2)
    then have "kme_KMGet_buffer_valid {n} kmeID s \<longrightarrow>  kme_KMGet_buffer_valid {n} kmeID t"
      unfolding kme_KMGet_buffer_valid_def by simp
    moreover have "kme_KMGet_buffer_valid (nodes - {n}) kmeID s \<longrightarrow>  kme_KMGet_buffer_valid (nodes - {n}) kmeID t"
      using Kme_KMGetKeyWithID_IDFound
      unfolding kme_KMGet_buffer_valid_def by auto
    ultimately have "kme_KMGet_buffer_valid nodes kmeID s \<longrightarrow>  kme_KMGet_buffer_valid nodes kmeID t"
      unfolding kme_KMGet_buffer_valid_def by blast
    then show ?case 
      using 2(2) by simp
  next
    case (Kme_KMGetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' net' n nextKme masterSae keyID keyID2 slaveSae store val2 sender route keyID3 val3 saeToKme bridgeIDs kmeIDs msgs)
    then have "kme_KMGet_buffer_valid {n} kmeID s \<longrightarrow>  kme_KMGet_buffer_valid {n} kmeID t"
      unfolding kme_KMGet_buffer_valid_def by simp
    moreover have "kme_KMGet_buffer_valid (nodes - {n}) kmeID s \<longrightarrow>  kme_KMGet_buffer_valid (nodes - {n}) kmeID t"
      using Kme_KMGetKeyWithID_IDNotFound
      unfolding kme_KMGet_buffer_valid_def by auto
    ultimately have "kme_KMGet_buffer_valid nodes kmeID s \<longrightarrow>  kme_KMGet_buffer_valid nodes kmeID t"
      unfolding kme_KMGet_buffer_valid_def by blast
    then show ?case 
      using 2(2) by simp
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' net' n nextKme prevKme masterSae keyID keyID2 slaveSae store route keyID3 saeToKme bridgeIDs kmeIDs msgs)
    then have "kme_KMGet_buffer_valid {n} kmeID s \<longrightarrow>  kme_KMGet_buffer_valid {n} kmeID t"
      unfolding kme_KMGet_buffer_valid_def by simp
    moreover have "kme_KMGet_buffer_valid (nodes - {n}) kmeID s \<longrightarrow>  kme_KMGet_buffer_valid (nodes - {n}) kmeID t"
      using Kme_KMGetKeyWithID_IDNotFound_Reserved
      unfolding kme_KMGet_buffer_valid_def by auto
    ultimately have "kme_KMGet_buffer_valid nodes kmeID s \<longrightarrow>  kme_KMGet_buffer_valid nodes kmeID t"
      unfolding kme_KMGet_buffer_valid_def by blast
    then show ?case 
      using 2(2) by simp
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme prevKme keyID keyVal' store keyID2 val2 keyID3 val3 masterSae route saeToKme bridgeIDs kmeIDs msgs slaveSae)
    then have "kme_KMGet_buffer_valid {n} kmeID s \<longrightarrow>  kme_KMGet_buffer_valid {n} kmeID t"
      unfolding kme_KMGet_buffer_valid_def by simp
    moreover have "kme_KMGet_buffer_valid (nodes - {n}) kmeID s \<longrightarrow>  kme_KMGet_buffer_valid (nodes - {n}) kmeID t"
      using Kme_KMGetKeyWithID_IDNotFound_Return
      unfolding kme_KMGet_buffer_valid_def by auto
    ultimately have "kme_KMGet_buffer_valid nodes kmeID s \<longrightarrow>  kme_KMGet_buffer_valid nodes kmeID t"
      unfolding kme_KMGet_buffer_valid_def by blast
    then show ?case 
      using 2(2) by simp
  next
    case (Kme_GetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme keyID keyVal' store keyID2 val2 masterSae sender route saeToKme bridgeIDs kmeIDs msgs)
    then have "kme_KMGet_buffer_valid {n} kmeID s \<longrightarrow>  kme_KMGet_buffer_valid {n} kmeID t"
      unfolding kme_KMGet_buffer_valid_def by simp
    moreover have "kme_KMGet_buffer_valid (nodes - {n}) kmeID s \<longrightarrow>  kme_KMGet_buffer_valid (nodes - {n}) kmeID t"
      using Kme_GetKeyWithID_IDNotFound_Return
      unfolding kme_KMGet_buffer_valid_def by auto
    ultimately have "kme_KMGet_buffer_valid nodes kmeID s \<longrightarrow>  kme_KMGet_buffer_valid nodes kmeID t"
      unfolding kme_KMGet_buffer_valid_def by blast
    then show ?case 
      using 2(2) by simp
  next
    case (Kme_ReceiveStutter apps kmes bridges qkd net net' n sender msg)
    then show ?case 
      using 2(2) unfolding kme_KMGet_buffer_valid_def by auto
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    then have "kme_KMGet_buffer_valid {n} kmeID s \<longrightarrow>  kme_KMGet_buffer_valid {n} kmeID t"
      unfolding kme_KMGet_buffer_valid_def apply simp
      apply (cases msg) 
      sorry
    moreover have "kme_KMGet_buffer_valid (nodes - {n}) kmeID s \<longrightarrow>  kme_KMGet_buffer_valid (nodes - {n}) kmeID t"
      using Kme_Send
      unfolding kme_KMGet_buffer_valid_def by auto
    ultimately have "kme_KMGet_buffer_valid nodes kmeID s \<longrightarrow>  kme_KMGet_buffer_valid nodes kmeID t"
      unfolding kme_KMGet_buffer_valid_def by blast
    then show ?case 
      using 2(2) by simp
  next
    case (Bridge_Tick_GetKey apps kmes bridges qkds net bridges' net' n b slaveBridge otherKme qkd kme msgs)
    then show ?case 
      using 2(2) unfolding kme_KMGet_buffer_valid_def by auto
  next
    case (Bridge_Master_KeyResponse apps kmes bridges qkds net bridges' net' n b slaveBridge otherKme qkd kme msgs keyID keyVal)
    then show ?case 
      using 2(2) unfolding kme_KMGet_buffer_valid_def by auto
  next
    case (Bridge_Slave_GetKeyWithID apps kmes bridges qkds net bridges' net' n b masterBridge otherKme qkd kme msgs keyID)
    then show ?case 
      using 2(2) unfolding kme_KMGet_buffer_valid_def by auto
  next
    case (Bridge_Slave_KeyResponse apps kmes bridges qkds net bridges' net' n b masterBridge otherKme qkd kme msgs keyID keyVal)
    then show ?case 
      using 2(2) unfolding kme_KMGet_buffer_valid_def by auto
  next
    case (Bridge_ReceiveStutter apps kmes bridges qkds net net' n b sender msg)
    then show ?case 
      using 2(2) unfolding kme_KMGet_buffer_valid_def by auto
  next
    case (Bridge_Send apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState)
    then show ?case 
      using 2(2) unfolding kme_KMGet_buffer_valid_def by auto
  next
    case (Qkd_GetKey_Gen apps kmes bridges qkd net qkd' net' pid gen sent sender target keyID keyVal)
    then show ?case 
      using 2(2) unfolding kme_KMGet_buffer_valid_def by auto
  next
    case (Qkd_GetKeyWithID_Reserve apps kmes bridges qkd net qkd' net' pid gen sent sender target keyID keyVal)
    then show ?case 
      using 2(2) unfolding kme_KMGet_buffer_valid_def by auto
  next
    case (Qkd_ReceiveStutter apps kmes bridges qkd net qkd' net' pid sender msg)
    then show ?case 
      using 2(2) unfolding kme_KMGet_buffer_valid_def by auto
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    then show ?case 
      using 2(2) unfolding kme_KMGet_buffer_valid_def by auto
  next
    case (Network_Ext_Receive apps kmes bridges qkd net net' sender rcpt msg all)
    then show ?case 
      using 2(2) unfolding kme_KMGet_buffer_valid_def by auto
  next
    case (Network_Ext_Send apps kmes bridges qkd net net' sender rcpt msg all)
    then show ?case 
      using 2(2) unfolding kme_KMGet_buffer_valid_def by auto
  qed
  (use 2(2) in \<open>auto simp: kme_KMGet_buffer_valid_def\<close>)
qed

end

end