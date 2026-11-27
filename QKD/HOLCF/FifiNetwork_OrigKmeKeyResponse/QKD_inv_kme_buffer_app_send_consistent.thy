theory QKD_inv_kme_buffer_app_send_consistent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
          QKD_inv_kme_buffer_consistent
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
    case (Kme_GetKey_Reserved apps kmes bridges qkd net kmes' n sender store keyID val conf res saeID route saeToKme msgs)
    have "\<forall>n state msgs sharedSave c r s2 r2 keyID keyVal1 keyVal2.
            n \<in> nodes \<and>
            kme_has_key (kme s n) keyID keyVal1 \<and>
            s2 \<in> kmeID ` nodes \<and> 
            r2 \<in> appID ` nodes \<and>
            (s2, r2, KeyResponse keyID keyVal2) \<in> network s
            \<longrightarrow> keyVal1 = keyVal2"
      sorry
    then show ?case 
      using Kme_GetKey_Reserved(2,3,4,7,8,9) 2(2)
      unfolding kme_buffer_app_send_consistent_def apply auto
       apply (metis image_eqI kme_has_key.simps(2))
      by (meson image_eqI)
  next
    case (Kme_GetKeyWithID_IDFound apps kmes bridges qkd net kmes' n sender host store keyID val saeToKme masterSae route msgs)
    have "\<forall>n state msgs sharedSave c r s2 r2 keyID keyVal1 keyVal2.
            n \<in> nodes \<and> 
            kme_has_key (kme s n) keyID keyVal1 \<and>
            s2 \<in> kmeID ` nodes \<and> 
            r2 \<in> appID ` nodes \<and>
            (s2, r2, KeyResponse keyID keyVal2) \<in> network s
            \<longrightarrow> keyVal1 = keyVal2"
      sorry
    then show ?case 
      using Kme_GetKeyWithID_IDFound(2,3,4,7,8,9) 2(2)
      unfolding kme_buffer_app_send_consistent_def apply auto
       apply (metis image_eqI kme_has_key.simps(1))
      by (meson image_eqI)
  next
    case (Kme_KMGetKeyWithID_IDFound apps kmes bridges qkd net kmes' n nextKme masterSae keyID keyID2 slaveSae store route saeToKme msgs sender val val2)
    then show ?case sorry
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' n nextKme prevKme keyID keyVal' store keyID2 val2 sender keyID3 val3 masterSae route saeToKme msgs slaveSae)
      then show ?case sorry
  next
    case (Kme_GetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' n nextKme keyID keyVal' store keyID2 val2 masterSae sender route saeToKme msgs)
    then show ?case sorry
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    have "kme_buffer_consistent nodes appID s"
      using inv_kme_buffer_consistent 2(1) unfolding invariant_def by blast
    then show ?case
      using 2(2) Kme_Send(2,3,4,7,8,9,10)
      unfolding kme_buffer_app_send_consistent_def kme_buffer_consistent_def apply auto
             apply blast
            apply blast
           apply blast
      by (meson imageI)+
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