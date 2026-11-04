theory QKD_inv_kme_app_buffer_sent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
          QKD_inv_bridge_kme_msg_sent
begin

context QKD_Network
begin

lemma inv_kme_app_buffer_sent:
  shows "invariant System.ioa (kme_app_buffer_sent nodes kmeID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 apps kmes bridges qkd net)
    then show ?thesis
      unfolding kme_app_buffer_sent_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (Kme_GetKey_Reserved apps kmes bridges qkd net kmes' net' n sender store keyID val conf res saeID route saeToKme bridgeIDs msgs)
    then show ?case 
      sorry
  next
    case (Kme_GetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n sender host store keyID val saeToKme bridgeIDs masterSae route msgs)
    then show ?case 
      sorry
  next
    case (Kme_KMGetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n nextKme masterSae keyID keyID2 slaveSae store route saeToKme bridgeIDs msgs sender val val2)
    then show ?case 
      sorry
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme prevKme keyID keyVal' store keyID2 val2 sender keyID3 val3 masterSae route saeToKme bridgeIDs msgs slaveSae)
    then show ?case 
      sorry
  next
    case (Kme_GetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme keyID keyVal' store keyID2 val2 masterSae sender route saeToKme bridgeIDs msgs)
    then show ?case 
      sorry
  next
    case (Qkd_GetKeyWithID_Reserve apps kmes bridges qkd net qkd' net' pid gen sent sender target keyID keyVal)
    have "\<And>keyID keyVal. qkd_has_key s keyID keyVal \<longleftrightarrow> qkd_has_key t keyID keyVal"
      using Qkd_GetKeyWithID_Reserve(2,3,7,9,10,11) by force
    then show ?case 
      using 2(2) Qkd_GetKeyWithID_Reserve(2,3) unfolding kme_app_buffer_sent_def by simp
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    have "\<And>keyID keyVal. qkd_has_key s keyID keyVal \<longleftrightarrow> qkd_has_key t keyID keyVal"
      using Qkd_Send(2,3,7,9,10) by force
    then show ?case 
      using 2(2) Qkd_Send(2,3) unfolding kme_app_buffer_sent_def by simp
  qed
  (use 2(2) in \<open>auto simp: kme_app_buffer_sent_def\<close>)
qed

end

end