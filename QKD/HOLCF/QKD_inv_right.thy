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
   apply meson 
  by simp

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
    fix nA nB state msgs
    assume assm:"nA \<in> nodes \<and> nB \<in> nodes \<and> kme t nA = IoaState state msgs"
    have "card (kme_get_buffer_msg kmeID s nA nB is_KMGet) = card (kme_get_buffer_msg kmeID t nA nB is_KMGet)"
      using assms(1,2) by simp
    moreover have "length (filter is_KMGet (network t (kmeID nA, kmeID nB))) \<le> length (filter is_KMGet (network s (kmeID nA, kmeID nB)))"
      using assms(1,2,3) apply auto
      apply (cases "net (kmeID nA, kmeID nB)") by simp_all
    ultimately have "kme_get_msg_count kmeID t nA nB QKD_inv_def.is_KMGet \<le> kme_get_msg_count kmeID s nA nB QKD_inv_def.is_KMGet"
      by simp
    moreover have "kme_get_msg_count kmeID s nA nB QKD_inv_def.is_KMGet \<le> 1"
      using assm assms(4) unfolding inv3_def by (cases "kme s nA"; simp)
    moreover have "finite msgs"
      using assms assm unfolding inv3_def by simp
    ultimately show "kme_get_msg_count kmeID t nA nB QKD_inv_def.is_KMGet \<le> 1 \<and> finite msgs"
      by linarith
try0
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

lemma kme_network_has_msg_send_no_kme_change:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps', kmes, bridges', qkd', net')"
    and "net' = add_msg net sender rcpt msg"
    and "nA \<in> nodes \<and> nB \<in> nodes"
    and "sender \<notin> kmeID ` nodes"
  shows "\<And>msg. kme_network_has_msg kmeID t nA nB msg \<Longrightarrow> kme_network_has_msg kmeID s nA nB msg"
  using assms by (auto split: if_splits)

lemma right_helper_send_no_kme_change:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps', kmes, bridges', qkd', net')"
    and "net' = add_msg net sender rcpt msg"
    and "sender \<notin> kmeID ` nodes"
    and "right nodes kmeID s"
  shows "right nodes kmeID t"
proof -
  have "inv1 nodes kmeID t"
    using assms kme_network_has_msg_send_no_kme_change unfolding inv1_def
    apply simp by blast
  moreover have "inv2 nodes kmeID t"
    unfolding inv2_def
  proof (intro allI impI)
    fix nA nB slaveSae keyID' keyVal' keyID encKeyID masterSae
    assume assm:"nA \<in> nodes \<and> nB \<in> nodes \<and> kme_network_has_msg kmeID t nB nA (KeyResponse keyID' keyVal')"
    then have "kme_network_has_msg kmeID s nB nA (KeyResponse keyID' keyVal')"
      using kme_network_has_msg_send_no_kme_change[OF assms(1,2,3)] assms(4) by simp
    then have "\<not> kme_network_has_msg kmeID s nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      using assms(5) assm unfolding inv2_def by blast
    then show "\<not> kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      using kme_network_has_msg_send_no_kme_change[OF assms(1,2,3)] assm assms(4) by auto
  qed
  moreover have "inv3 nodes kmeID t"
    unfolding inv3_def
  proof (intro allI impI)
    fix nA nB state msgs
    assume assm:"nA \<in> nodes \<and> nB \<in> nodes \<and> kme t nA = IoaState state msgs"
    have "card (kme_get_buffer_msg kmeID s nA nB is_KMGet) = card (kme_get_buffer_msg kmeID t nA nB is_KMGet)"
      using assms(1,2) by simp
    moreover have "length (filter is_KMGet (network t (kmeID nA, kmeID nB))) = length (filter is_KMGet (network s (kmeID nA, kmeID nB)))"
      using assms(1,2,3,4) assm by auto
    ultimately have "kme_get_msg_count kmeID t nA nB QKD_inv_def.is_KMGet = kme_get_msg_count kmeID s nA nB QKD_inv_def.is_KMGet"
      by simp
    moreover have "kme_get_msg_count kmeID s nA nB QKD_inv_def.is_KMGet \<le> 1"
      using assm assms(5) unfolding inv3_def by (cases "kme s nA"; simp)
    moreover have "finite msgs"
      using assms assm unfolding inv3_def by simp
    ultimately show "kme_get_msg_count kmeID t nA nB QKD_inv_def.is_KMGet \<le> 1 \<and> finite msgs"
      by simp
  qed
  moreover have "inv4 nodes kmeID t"
    unfolding inv4_def
  proof (intro allI impI)
    fix nA nB slaveSae keyID encKeyID masterSae
    assume assm:"nA \<in> nodes \<and> nB \<in> nodes \<and> kme_network_has_msg kmeID t nB nA OK"
    then have "kme_network_has_msg kmeID s nB nA OK"
      using kme_network_has_msg_send_no_kme_change[OF assms(1,2,3)] assms(4) by simp
    then have "\<not> kme_network_has_msg kmeID s nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      using assms(5) assm unfolding inv4_def by blast
    then show "\<not> kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      using kme_network_has_msg_send_no_kme_change[OF assms(1,2,3)] assms(4) assm by auto
  qed
  moreover have "inv5 nodes kmeID t"
    unfolding inv5_def
  proof (intro allI impI)
    fix nA nB kmID keyID' reserveOption slaveSae keyID encKeyID masterSae
    assume assm:"nA \<in> nodes \<and> nB \<in> nodes \<and> kme_network_has_msg kmeID t nA nB (KMPut kmID keyID' reserveOption)"
    then have "kme_network_has_msg kmeID s nA nB (KMPut kmID keyID' reserveOption)"
      using kme_network_has_msg_send_no_kme_change[OF assms(1,2,3)] assms(4) assm by simp
    then have "\<not> kme_network_has_msg kmeID s nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      using assms(5) assm unfolding inv5_def by blast
    then show "\<not> kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      using kme_network_has_msg_send_no_kme_change[OF assms(1,2,3)] assms(4) assm by auto
  qed
  moreover have "inv6 nodes kmeID t"
    unfolding inv6_def
  proof (intro allI impI)
    fix nA nB slaveSae keyID encKeyID masterSae
    assume assm:"nA \<in> nodes \<and> nB \<in> nodes \<and> kme_has_decryptionKeyID (kme t nA) = None"
    then have "kme_has_decryptionKeyID (kme s nA) = None"
      using assms(1,2) by simp
    then have "\<not> kme_network_has_msg kmeID s nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      using assms(5) assm unfolding inv6_def by blast
    then show "\<not> kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      using kme_network_has_msg_send_no_kme_change[OF assms(1,2,3)] assms(4) assm by auto
  qed
  ultimately show ?thesis
    by simp
qed
  

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
    then have "appID n \<notin> kmeID ` nodes"
      using disjoint_ids unfolding disjnt_def by fast
    then show ?case 
      using right_helper_send_no_kme_change[OF App_Send(2,3,7)] 2(2) by fast
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
    have kmeNet:"\<And>nA nB msg. \<lbrakk>nA \<in> nodes; nB \<in> nodes; kme_network_has_msg kmeID t nA nB msg\<rbrakk> \<Longrightarrow> kme_network_has_msg kmeID s nA nB msg"
      using Kme_Send(2,3,4,7,8,9,10) inj_kme unfolding inj_on_def by (auto split: if_splits)
    have kmeDecKey:"\<And>n. kme_has_decryptionKeyID (kme s n) = kme_has_decryptionKeyID (kme t n)"
      using Kme_Send(2,3,9,10) apply auto apply(cases appState) by auto
    have "inv1 nodes kmeID t"
      using 2(2) kmeNet kmeDecKey unfolding inv1_def by metis
    moreover have "inv2 nodes kmeID t"
      using 2(2) kmeNet kmeDecKey unfolding inv2_def by metis
    moreover have "inv3 nodes kmeID t"
      unfolding inv3_def
    proof (intro allI impI)
      fix nA nB state msgs'
      assume assm:"nA \<in> nodes \<and> nB \<in> nodes \<and> kme t nA = IoaState state msgs'"
      show "kme_get_msg_count kmeID t nA nB QKD_inv_def.is_KMGet \<le> 1 \<and> finite msgs'"
      proof(cases "nA = n")
        case True
        then show ?thesis 
        proof(cases "kmeID nB = rcpt")
          case True
          then show ?thesis
          proof(cases "is_KMGet msg")
            case True
            have finite: "finite msgs"
              using assm \<open>nA = n\<close> Kme_Send(2,9) 2(2) unfolding inv3_def by force
            have "card (kme_get_buffer_msg kmeID s n nB is_KMGet) > 0"
              using finite True Kme_Send(2,8,9)  \<open>kmeID nB = rcpt\<close>
              apply auto
              apply (subst card_gt_0_iff)
              apply (rule conjI)
              apply blast
              apply (rule finite_subset[where B=msgs])
              by blast+
            moreover have "card (kme_get_buffer_msg kmeID s n nB is_KMGet) \<le> 1"
              using assm \<open>nA = n\<close> Kme_Send(2,3,9,10) 2(2) unfolding inv3_def by force
            ultimately have set_one: "card (kme_get_buffer_msg kmeID s n nB is_KMGet) = 1"
              by linarith
            then have new_zero:"card (kme_get_buffer_msg kmeID t n nB is_KMGet) = 0"
              using Kme_Send(2,3,8,9,10) True \<open>kmeID nB = rcpt\<close> apply auto
              by (smt (verit) card.empty card_1_singleton_iff empty_Collect_eq mem_Collect_eq prod.inject
                  singleton_iff)
            have "(length (filter is_KMGet (network s (kmeID n, kmeID nB)))) = 0"
              using set_one assm \<open>nA = n\<close> Kme_Send(2,3,9,10) 2(2) unfolding inv3_def by force
            then have "(length (filter is_KMGet (network t (kmeID n, kmeID nB)))) = 1"
              using Kme_Send(2,3,7,8,9,10) True \<open>kmeID nB = rcpt\<close> by auto
            then have "kme_get_msg_count kmeID t nA nB QKD_inv_def.is_KMGet \<le> 1"
              using new_zero \<open>nA = n\<close> by presburger
            then show ?thesis
              using assm \<open>nA = n\<close> Kme_Send(2,3,9,10) 2(2) unfolding inv3_def by force
          next
            case False
            then have "kme_get_msg_count kmeID s n nB is_KMGet = kme_get_msg_count kmeID t n nB is_KMGet"
              using assm Kme_Send(2,3,4,7,8,9,10) inj_kme unfolding inj_on_def apply auto
              by (rule arg_cong[where f=card], auto)
            then have "kme_get_msg_count kmeID t nA nB QKD_inv_def.is_KMGet \<le> 1 \<and> finite msgs"
              using \<open>nA = n\<close> 2(2) assm Kme_Send(2,3,9,10) unfolding inv3_def by fastforce
            then show ?thesis
              using \<open>nA = n\<close> assm Kme_Send(3,10) by force
          qed
        next
          case False
          then have "kme_get_msg_count kmeID s n nB is_KMGet = kme_get_msg_count kmeID t n nB is_KMGet"
            using assm Kme_Send(2,3,4,7,8,9,10) inj_kme unfolding inj_on_def by auto
          then have "kme_get_msg_count kmeID t nA nB QKD_inv_def.is_KMGet \<le> 1 \<and> finite msgs"
            using \<open>nA = n\<close> 2(2) assm Kme_Send(2,3,9,10) unfolding inv3_def by fastforce
          then show ?thesis
            using \<open>nA = n\<close> assm Kme_Send(3,10) by force
        qed
      next
        case False
        then have "kme_get_msg_count kmeID s nA nB is_KMGet = kme_get_msg_count kmeID t nA nB is_KMGet"
          using assm Kme_Send(2,3,4,7,9,10) inj_kme unfolding inj_on_def by force
        then show ?thesis
          using 2(2) Kme_Send(2,3,9,10) False assm unfolding inv3_def by force
      qed
    qed
    moreover have "inv4 nodes kmeID t"
      using 2(2) kmeNet kmeDecKey unfolding inv4_def by metis
    moreover have "inv5 nodes kmeID t"
      using 2(2) kmeNet kmeDecKey unfolding inv5_def by metis
    moreover have "inv6 nodes kmeID t"
      using 2(2) kmeNet kmeDecKey unfolding inv6_def by metis
    ultimately show ?case
      by simp
  next
    case (Bridge_Send apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState)
    then have "b \<notin> kmeID ` nodes"
      using disjoint_ids unfolding disjnt_def by fast
    then show ?case 
      using right_helper_send_no_kme_change[OF Bridge_Send(2,3,8)] 2(2) by fast
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    then have "pid \<notin> kmeID ` nodes"
      using disjoint_ids unfolding disjnt_def by fast
    then show ?case 
      using right_helper_send_no_kme_change[OF Qkd_Send(2,3,8)] 2(2) by fast
  next
    case (Network_Ext_Send apps kmes bridges qkd net net' sender rcpt msg all)
    then have "sender \<notin> kmeID ` nodes"
      using disjoint_ids unfolding disjnt_def by fast
    then show ?case 
      using right_helper_send_no_kme_change[OF Network_Ext_Send(2,3,12)] 2(2) by fast
  qed (use 2(2) right_helper_receive_no_kme_change in \<open>meson+\<close>)
qed

end

end