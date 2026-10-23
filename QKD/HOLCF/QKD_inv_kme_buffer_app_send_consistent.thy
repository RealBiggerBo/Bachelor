theory QKD_inv_kme_buffer_app_send_consistent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
begin

context QKD_Network
begin

lemma inv_kme_buffer_app_send_consistent:
  shows "invariant System.ioa (kme_buffer_app_send_consistent nodes appID kmeID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 tn qkd net)
    then show ?thesis
      unfolding kme_buffer_app_send_consistent_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (App_Send apps kmes bridges qkd net apps' net' n msgs rcpt msg appState)
    have "appID n \<notin> kmeID ` nodes"
      using disjoint_ids App_Send(4)
      by (metis disjoint_ids image_iff UNIV_I disjnt_iff)
    then show ?case
      using 2(2) App_Send(2,3,7) unfolding kme_buffer_app_send_consistent_def
      apply auto by (metis image_eqI)+
  next
    case (Kme_KMPost_NewKeyVal apps kmes bridges qkd net kmes' n sender otherKme keyID keyVal store route saeToKme msgs)
    then show ?case sorry
  next
    case (Kme_KMPut_Confirm apps kmes bridges qkd net kmes' n sender otherKme keyID store route saeToKme msgs)
    then show ?case sorry
  next
    case (Kme_GetKey apps kmes bridges qkd net kmes' n sender host slaveSae store route saeToKme msgs keyID val)
    then show ?case sorry
  next
    case (Kme_KMPut_Reserve apps kmes bridges qkd net kmes' n sender otherKme slaveSae store route saeToKme msgs keyID)
    then show ?case sorry
  next
    case (Kme_GetKey_Reserved apps kmes bridges qkd net kmes' n sender store keyID val conf res saeID route saeToKme msgs)
    then show ?case sorry
  next
    case (Kme_GetKeyWithID_IDFound apps kmes bridges qkd net kmes' n sender host store keyID val saeToKme masterSae route msgs)
    then show ?case sorry
  next
    case (Kme_GetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' n sender host masterSae keyID store route nextKme keyID2 val2 saeToKme msgs)
    then show ?case sorry
  next
    case (Kme_GetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' n nextKme masterSae slaveSae keyID keyID2 store route saeToKme msgs)
    then show ?case sorry
  next
    case (Kme_KMGetKeyWithID_IDFound apps kmes bridges qkd net kmes' n nextKme masterSae keyID keyID2 slaveSae store route saeToKme msgs sender val val2)
    then show ?case sorry
  next
    case (Kme_KMGetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' n nextKme masterSae keyID keyID2 slaveSae store val2 sender route keyID3 val3 saeToKme msgs)
    then show ?case sorry
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' n nextKme prevKme masterSae keyID keyID2 slaveSae store route keyID3 saeToKme msgs)
    then show ?case sorry
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' n nextKme prevKme keyID keyVal' store keyID2 val2 sender keyID3 val3 masterSae route saeToKme msgs slaveSae)
    then show ?case sorry
  next
    case (Kme_GetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' n nextKme keyID keyVal' store keyID2 val2 masterSae sender route saeToKme msgs)
    then show ?case sorry
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    have "\<forall>n' state msgs s1 s2 r1 r2 keyID keyVal1 keyVal2.
       n' \<in> nodes - {n} \<and>
       kme t n' = IoaState state msgs \<and>
       s2 \<in> kmeID ` nodes \<and>
       r1 \<in> appID ` nodes \<and>
       r2 \<in> appID ` nodes \<and>
       (s1, r1, KeyResponse keyID keyVal1) \<in> msgs \<and> (s2, r2, KeyResponse keyID keyVal2) \<in> network t \<longrightarrow>
       keyVal1 = keyVal2"
      sorry
    moreover have "\<forall>n' state msgs s1 s2 r1 r2 keyID keyVal1 keyVal2.
       n' \<in> {n} \<and>
       kme t n' = IoaState state msgs \<and>
       s2 \<in> kmeID ` nodes \<and>
       r1 \<in> appID ` nodes \<and>
       r2 \<in> appID ` nodes \<and>
       (s1, r1, KeyResponse keyID keyVal1) \<in> msgs \<and> (s2, r2, KeyResponse keyID keyVal2) \<in> network t \<longrightarrow>
       keyVal1 = keyVal2"
      sorry
    ultimately show ?case
      unfolding kme_buffer_app_send_consistent_def
      by (meson DiffI)
  next
    case (Bridge_Send apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState)
    have "b \<notin> kmeID ` nodes"
      by (metis kme_neq_bridge Bridge_Send.IH(5) image_iff)
    then show ?case
      using 2(2) Bridge_Send(2,3,8) unfolding kme_buffer_app_send_consistent_def
      apply auto by blast
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    have "pid \<notin> kmeID ` nodes"
      using disjoint_ids Qkd_Send(5)
      by (metis disjnt_iff image_iff range_eqI)
    then show ?case
      using 2(2) Qkd_Send(2,3,8) unfolding kme_buffer_app_send_consistent_def
      apply auto by blast
  next
    case (Network_Ext_Send apps kmes bridges qkd net net' sender rcpt msg all)
    then have "sender \<notin> kmeID ` nodes"
      by fast
    then show ?case
      using 2(2) Network_Ext_Send(2,3,12) unfolding kme_buffer_app_send_consistent_def
      apply auto by blast
  qed
    (use 2(2) in \<open>auto simp: kme_buffer_app_send_consistent_def\<close>)
qed

end

end