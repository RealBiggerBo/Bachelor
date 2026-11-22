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

lemma kme_receive_no_network_change:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes', bridges, qkd, net')"
    and "net' = rmv_msg net sender (kmeID n) msgR"
    and "can_send net sender (kmeID n) msgR"
    and "kmes n = IoaState state msgs"
    and "kmes' = kmes(n := IoaState state' (msgs \<union> newMsgs))"
    and "(kmeID n, kmeID nB, msg) \<notin> newMsgs"
    and "msgR \<noteq> msg"
  shows "kme_network_has_msg kmeID s nA nB msg = kme_network_has_msg kmeID t nA nB msg"
  using assms apply auto
       apply (metis list.exhaust_sel set_ConsD)
      apply (meson list.set_sel(2))
     apply (metis list.exhaust_sel set_ConsD)
    apply (metis list.set_sel(2))
   apply (metis list.collapse set_ConsD)
  by (metis list.set_sel(2))

lemma kme_network_has_msg_imp:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes', bridges, qkd, net')"
    and "net' = rmv_msg net sender (kmeID n) msgR"
    and "can_send net sender (kmeID n) msgR"
    and "kmes n = IoaState state msgs"
    and "kmes' = kmes(n := IoaState state' (msgs \<union> newMsgs))"
    and "(kmeID n, kmeID nB, msg) \<notin> newMsgs"
  shows "kme_network_has_msg kmeID t nA nB msg \<Longrightarrow> kme_network_has_msg kmeID s nA nB msg"
  using assms apply (cases "net (sender, kmeID n)") by (auto split: if_splits) 

lemma inv1_induct:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes', bridges, qkd, net')"
    and "net' = rmv_msg net sender (kmeID n) msgR"
    and "can_send net sender (kmeID n) msgR"
    and "kmes n = IoaState state msgs"
    and "kmes' = kmes(n := IoaState state' (msgs \<union> newMsgs))"
    and "\<And>nB slaveSae keyID encKeyID masterSae. (kmeID n, kmeID nB, KMGet slaveSae keyID encKeyID masterSae) \<notin> newMsgs"
    and "\<And>encKeyID. kme_has_decryptionKeyID (kme s n) = Some encKeyID \<Longrightarrow> kme_has_decryptionKeyID (kme t n) = Some encKeyID"
    and "inv1 nodes kmeID s"
  shows "inv1 nodes kmeID t"
proof -
  have "\<And>nA nB slaveSae keyID encKeyID masterSae. kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae) \<Longrightarrow> kme_network_has_msg kmeID s nA nB (KMGet slaveSae keyID encKeyID masterSae)"
    using kme_network_has_msg_imp[OF assms(1,2,3,4,5,6,7)] by auto
  moreover have "\<And>n encKeyID. kme_has_decryptionKeyID (kme s n) = Some encKeyID \<Longrightarrow> kme_has_decryptionKeyID (kme t n) = Some encKeyID"
    using assms(1,2,6,8) by auto
  ultimately show ?thesis
    using assms(9) unfolding inv1_def by metis
qed

lemma inv2_induct:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes', bridges, qkd, net')"
    and "net' = rmv_msg net sender (kmeID n) msgR"
    and "can_send net sender (kmeID n) msgR"
    and "kmes n = IoaState state msgs"
    and "kmes' = kmes(n := IoaState state' (msgs \<union> newMsgs))"
    and "\<And>nB keyID keyVal. nB \<in> nodes \<Longrightarrow> (kmeID n, kmeID nB, KeyResponse keyID keyVal) \<notin> newMsgs"
    and "\<And>nB slaveSae keyID encKeyID masterSae. nB \<in> nodes \<Longrightarrow> (kmeID n, kmeID nB, KMGet slaveSae keyID encKeyID masterSae) \<notin> newMsgs"
    and "inv2 nodes kmeID s"
  shows "inv2 nodes kmeID t"
proof -
  have "\<And>nA nB keyID keyVal. \<lbrakk>nA \<in> nodes; kme_network_has_msg kmeID t nB nA (KeyResponse keyID keyVal)\<rbrakk> \<Longrightarrow> kme_network_has_msg kmeID s nB nA (KeyResponse keyID keyVal)"
    using kme_network_has_msg_imp[OF assms(1,2,3,4,5,6,7)] by auto
  moreover have "\<And>nA nB slaveSae keyID encKeyID masterSae. \<lbrakk>nB \<in> nodes; kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae)\<rbrakk> \<Longrightarrow> kme_network_has_msg kmeID s nA nB (KMGet slaveSae keyID encKeyID masterSae)"
    using kme_network_has_msg_imp[OF assms(1,2,3,4,5,6,8)] by auto
  ultimately show ?thesis
    using assms(9) unfolding inv2_def by blast
qed

lemma inv3_induct:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes', bridges, qkd, net')"
    and "net' = rmv_msg net sender (kmeID n) msgR"
    and "can_send net sender (kmeID n) msgR"
    and "kmes n = IoaState state msgs"
    and "kmes' = kmes(n := IoaState state' (msgs \<union> newMsgs))"
    and "finite newMsgs"
    and "\<And>nB msg. (kmeID n, kmeID nB, msg) \<in> newMsgs \<Longrightarrow> \<not> is_KMGet msg"
    and "inv3 nodes kmeID s"
  shows "inv3 nodes kmeID t"
proof -
  have "\<And>nA nB. (length (filter is_KMGet (network t (kmeID nA, kmeID nB)))) \<le> (length (filter is_KMGet (network s (kmeID nA, kmeID nB))))"
    using assms(1,2,3,4) apply auto
    apply (cases "net (sender, kmeID n)")
     apply force
    by simp
  moreover have "\<And>nA nB. card (kme_get_buffer_msg kmeID s nA nB is_KMGet) = card (kme_get_buffer_msg kmeID t nA nB is_KMGet)"
    using assms(1,2,5,6,8) apply auto by meson
  ultimately have "\<And>nA nB. \<lbrakk>nA \<in> nodes; nB \<in> nodes\<rbrakk> \<Longrightarrow> kme_get_msg_count kmeID t nA nB QKD_inv_def.is_KMGet \<le> 1"
    using assms(9) unfolding inv3_def apply simp
  apply (drule_tac x=nA in meta_spec)
  apply (drule_tac x=nA in meta_spec)
  apply (drule_tac x=nB in meta_spec)
  apply (drule_tac x=nB in meta_spec)
    apply (drule_tac x=nA in spec, drule_tac x=nB in spec)
    apply (case_tac "kme s nA", rename_tac state msgs)
    by force
  moreover have "\<And>nA state msgs. \<lbrakk>nA \<in> nodes; kme t nA = IoaState state msgs\<rbrakk> \<Longrightarrow> finite msgs"
    using assms(1,2,5,6,7,9) unfolding inv3_def by(auto split: if_splits)
  ultimately show ?thesis
    using assms(9) unfolding inv3_def by blast
qed

lemma inv4_induct:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes', bridges, qkd, net')"
    and "net' = rmv_msg net sender (kmeID n) msgR"
    and "can_send net sender (kmeID n) msgR"
    and "kmes n = IoaState state msgs"
    and "kmes' = kmes(n := IoaState state' (msgs \<union> newMsgs))"
    and "\<And>nB. (kmeID n, kmeID nB, OK) \<notin> newMsgs"
    and "\<And>nB slaveSae keyID encKeyID masterSae. (kmeID n, kmeID nB, KMGet slaveSae keyID encKeyID masterSae) \<notin> newMsgs"
    and "inv4 nodes kmeID s"
  shows "inv4 nodes kmeID t"
proof -
  have "\<And>nA nB. kme_network_has_msg kmeID t nB nA OK \<Longrightarrow> kme_network_has_msg kmeID s nB nA OK"
    using kme_network_has_msg_imp[OF assms(1,2,3,4,5,6,7)] by auto
  moreover have "\<And>nA nB slaveSae keyID encKeyID masterSae. kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae) \<Longrightarrow> kme_network_has_msg kmeID s nA nB (KMGet slaveSae keyID encKeyID masterSae)"
    using kme_network_has_msg_imp[OF assms(1,2,3,4,5,6,8)] by auto
  ultimately show ?thesis
    using assms(9) unfolding inv4_def by blast
qed

lemma inv4_induct_confirm_reserve:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes', bridges, qkd, net')"
    and "net' = net((sender, kmeID n) := tl (net (sender, kmeID n)))"
    and "can_send net sender (kmeID n) (KMPut otherKme keyID reserveOption)"
    and "kmes n = IoaState (Kme store route' saeToKme' bridgeIDs' kmeIDs) msgs"
    and "kmes' = kmes(n := IoaState (Kme store' route' saeToKme' bridgeIDs' kmeIDs) (msgs \<union> {(kmeID n, sender, OK)}))"
    and "inv5 nodes kmeID s"
    and "inv4 nodes kmeID s"
  shows "inv4 nodes kmeID t"
proof -
  have "\<forall>nA nB slaveSae keyID encKeyID masterSae.
       nA \<in> nodes \<and> nB \<in> nodes-{n} \<and> kme_network_has_msg kmeID t nB nA OK \<longrightarrow>
       \<not> kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae)"
    using assms unfolding inv4_def
  proof(intro allI impI)
    fix nA nB slaveSae keyID encKeyID masterSae
    assume assm:"nA \<in> nodes \<and> nB \<in> nodes - {n} \<and> kme_network_has_msg kmeID t nB nA OK"
    then have "kme_network_has_msg kmeID t nB nA OK \<Longrightarrow> kme_network_has_msg kmeID s nB nA OK"
      using assms list.set_sel(2) apply (auto split: option.splits if_splits)
      by fast+
    then have "\<not> kme_network_has_msg kmeID s nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      using assms assm unfolding inv4_def by blast
    moreover have "\<not> kme_network_has_msg kmeID s nA nB (KMGet slaveSae keyID encKeyID masterSae) \<Longrightarrow> \<not> kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      using assms list.set_sel(2) apply (auto split: option.splits if_splits)
      by fast+
    ultimately show "\<not> kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      by fastforce
  qed
  moreover have "\<forall>nA slaveSae keyID encKeyID masterSae.
       nA \<in> nodes \<and> n \<in> nodes \<and> kme_network_has_msg kmeID t n nA OK \<longrightarrow>
       \<not> kme_network_has_msg kmeID t nA n (KMGet slaveSae keyID encKeyID masterSae)"
  proof(intro allI impI)
    fix nA slaveSae' keyID' encKeyID masterSae
    assume assm:"nA \<in> nodes \<and> n \<in> nodes \<and> kme_network_has_msg kmeID t n nA OK"
    show "\<not> kme_network_has_msg kmeID t nA n (KMGet slaveSae' keyID' encKeyID masterSae)"
    proof (cases "sender = kmeID nA")
      case True
      then have "kme_network_has_msg kmeID s nA n (KMPut otherKme keyID reserveOption)"
        using assms apply(cases "net (kmeID nA, kmeID n)") by auto
      then have "\<And>slaveSae keyID encKeyID masterSae. \<not> kme_network_has_msg kmeID s nA n (KMGet slaveSae keyID encKeyID masterSae)"
        using assms assm unfolding inv5_def by blast
      moreover have "\<And>slaveSae keyID encKeyID masterSae. \<not> kme_network_has_msg kmeID s nA n (KMGet slaveSae keyID encKeyID masterSae) \<Longrightarrow> \<not> kme_network_has_msg kmeID t nA n (KMGet slaveSae keyID encKeyID masterSae)"
        using kme_receive_no_network_change[OF assms(1,2,3,4,5,6)] by auto
      ultimately show ?thesis
        by blast
    next
      case False
      have "kme_network_has_msg kmeID t n nA OK = kme_network_has_msg kmeID s n nA OK"
        using assms False by (auto split:option.splits)
      then have "\<And>slaveSae keyID encKeyID masterSae. \<not> kme_network_has_msg kmeID s nA n (KMGet slaveSae keyID encKeyID masterSae)"
        using assms assm unfolding inv4_def by simp
      moreover have "\<And>slaveSae keyID encKeyID masterSae. \<not> kme_network_has_msg kmeID s nA n (KMGet slaveSae keyID encKeyID masterSae) \<Longrightarrow> \<not> kme_network_has_msg kmeID t nA n (KMGet slaveSae keyID encKeyID masterSae)"
        using kme_receive_no_network_change[OF assms(1-6)] by auto
      ultimately show ?thesis 
        by blast
    qed
  qed
  ultimately show ?thesis
    unfolding inv4_def by fast
qed

lemma inv5_induct:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes', bridges, qkd, net')"
    and "net' = rmv_msg net sender (kmeID n) msgR"
    and "can_send net sender (kmeID n) msgR"
    and "kmes n = IoaState state msgs"
    and "kmes' = kmes(n := IoaState state' (msgs \<union> newMsgs))"
    and "\<And>nB kmID keyID' reserveOption. (kmeID n, kmeID nB, KMPut kmID keyID' reserveOption) \<notin> newMsgs"
    and "\<And>nB slaveSae keyID encKeyID masterSae. (kmeID n, kmeID nB, KMGet slaveSae keyID encKeyID masterSae) \<notin> newMsgs"
    and "inv5 nodes kmeID s"
  shows "inv5 nodes kmeID t"
proof -
  have "\<And>nA nB kmID keyID' reserveOption. kme_network_has_msg kmeID t nB nA (KMPut kmID keyID' reserveOption) \<Longrightarrow> kme_network_has_msg kmeID s nB nA (KMPut kmID keyID' reserveOption)"
    using kme_network_has_msg_imp[OF assms(1,2,3,4,5,6,7)] by auto
  moreover have "\<And>nA nB slaveSae keyID encKeyID masterSae. kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae) \<Longrightarrow> kme_network_has_msg kmeID s nA nB (KMGet slaveSae keyID encKeyID masterSae)"
    using kme_network_has_msg_imp[OF assms(1,2,3,4,5,6,8)] by auto
  ultimately show ?thesis
    using assms(9) unfolding inv5_def by blast
qed

lemma inv5_induct_inv6:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes', bridges, qkd, net')"
    and "net' = net((sender, kmeID n) := tl (net (sender, kmeID n)))"
    and "can_send net sender (kmeID n) msgR"
    and "kmes n = IoaState state msgs"
    and "kmes' = kmes(n := IoaState state' (msgs \<union> newMsgs))"
    and "\<And>nB msg slaveSae keyID encKeyID masterSae. (kmeID n, kmeID nB, KMGet slaveSae keyID encKeyID masterSae) \<notin> newMsgs"
    and "\<And>slaveSae keyID encKeyID masterSae. msgR \<noteq> KMGet slaveSae keyID encKeyID masterSae"
    and "n \<in> nodes"
    and "kme_has_decryptionKeyID (kme s n) = None"
    and "inv6 nodes kmeID s"
    and "inv5 nodes kmeID s"
  shows "inv5 nodes kmeID t"
proof -
  have "\<forall>nA nB kmID keyID' reserveOption slaveSae keyID encKeyID masterSae.
       nA \<in> nodes-{n} \<and> nB \<in> nodes \<and> kme_network_has_msg kmeID t nA nB (KMPut kmID keyID' reserveOption) \<longrightarrow>
       \<not> kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae)"
    using assms(1-4,6,12) unfolding inv5_def
    by (smt (verit) Diff_iff fst_conv fun_upd_apply insert_compr list.set_sel(2) mem_Collect_eq
            snd_conv)
  moreover have "\<forall>nB kmID keyID' reserveOption slaveSae keyID encKeyID masterSae.
       n \<in> nodes \<and> nB \<in> nodes \<and> kme_network_has_msg kmeID t n nB (KMPut kmID keyID' reserveOption) \<longrightarrow>
       \<not> kme_network_has_msg kmeID t n nB (KMGet slaveSae keyID encKeyID masterSae)"
  proof -
    have "\<And>nB slaveSae keyID encKeyID masterSae. nB \<in> nodes \<Longrightarrow> \<not> kme_network_has_msg kmeID s n nB (KMGet slaveSae keyID encKeyID masterSae)"
      using assms(9,10,11) unfolding inv6_def by blast
    then have "\<And>nB slaveSae keyID encKeyID masterSae. nB \<in> nodes \<Longrightarrow> \<not> kme_network_has_msg kmeID t n nB (KMGet slaveSae keyID encKeyID masterSae)"
      using kme_receive_no_network_change[OF assms(1,2,3,4,5,6,7,8)] by blast
    then show ?thesis
      by simp 
  qed  
  ultimately show ?thesis
    unfolding inv5_def by fast    
qed

lemma inv6_induct:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes', bridges, qkd, net')"
    and "net' = rmv_msg net sender (kmeID n) msgR"
    and "can_send net sender (kmeID n) msgR"
    and "kmes n = IoaState state msgs"
    and "kmes' = kmes(n := IoaState state' (msgs \<union> newMsgs))"
    and "\<And>nB slaveSae keyID encKeyID masterSae. (kmeID n, kmeID nB, KMGet slaveSae keyID encKeyID masterSae) \<notin> newMsgs"
    and "kme_has_decryptionKeyID (kme t n) = None \<Longrightarrow> kme_has_decryptionKeyID (kme s n) = None"
    and "inv6 nodes kmeID s"
  shows "inv6 nodes kmeID t"
proof -
  have "\<And>nA. kme_has_decryptionKeyID (kme t nA) = None \<Longrightarrow> kme_has_decryptionKeyID (kme s nA) = None"
    using assms(1,2,6,8) by (auto split: if_splits)
  moreover have "\<And>nA nB slaveSae keyID encKeyID masterSae. kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae) \<Longrightarrow> kme_network_has_msg kmeID s nA nB (KMGet slaveSae keyID encKeyID masterSae)"
    using kme_network_has_msg_imp[OF assms(1-7)] by auto
  ultimately show ?thesis
    using assms(9) unfolding inv6_def by blast
qed

lemma kme_other_unchanged:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes', bridges, qkd, net')"
    and "kmes' = kmes(n := IoaState state' (msgs \<union> newMsgs))"
    and "nA \<noteq> n"
  shows "kme t nA = kme s nA"
  using assms by simp

lemma kme_network_has_msg_other_mono:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes', bridges, qkd, net')"
    and "net' = net((sender, kmeID n) := tl (net (sender, kmeID n)))"
    and "can_send net sender (kmeID n) msgR"
    and "kmes n = IoaState state msgs"
    and "kmes' = kmes(n := IoaState state' (msgs \<union> newMsgs))"
    and "nA \<noteq> n"
  shows "kme_network_has_msg kmeID t nA nB msg \<Longrightarrow> kme_network_has_msg kmeID s nA nB msg"
  using assms list.set_sel(2)
  by (auto split: option.splits if_splits)

lemma kme_other_exclusive_preserved:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes', bridges, qkd, net')"
    and "net' = net((sender, kmeID n) := tl (net (sender, kmeID n)))"
    and "can_send net sender (kmeID n) msgR"
    and "kmes n = IoaState state msgs"
    and "kmes' = kmes(n := IoaState state' (msgs \<union> newMsgs))"
    and "nA \<noteq> n"
    and "kme_network_has_msg kmeID s nA nB m1 \<longrightarrow> \<not> kme_network_has_msg kmeID s nA nB m2"
  shows "kme_network_has_msg kmeID t nA nB m1 \<longrightarrow> \<not> kme_network_has_msg kmeID t nA nB m2"
  using kme_network_has_msg_other_mono[OF assms(1-7)] assms(8) by blast

lemma inv1_induct_one_kme:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes', bridges, qkd, net')"
    and "net' = net((sender, kmeID n) := tl (net (sender, kmeID n)))"
    and "can_send net sender (kmeID n) msgR"
    and "kmes n = IoaState state msgs"
    and "kmes' = kmes(n := IoaState state' (msgs \<union> newMsgs))"
    and "n \<in> nodes"
    and "inv1 nodes kmeID s"
    and sent: "\<And>nB slaveSae keyID encKeyID masterSae.
                 nB \<in> nodes \<Longrightarrow>
                 (kmeID n, kmeID nB, KMGet slaveSae keyID encKeyID masterSae) \<in> newMsgs \<Longrightarrow>
                 kme_has_decryptionKeyID (IoaState state' (msgs \<union> newMsgs)) = Some encKeyID"
    and kept: "(\<forall>encKeyID. kme_has_decryptionKeyID (IoaState state msgs) = Some encKeyID \<longrightarrow>
                          kme_has_decryptionKeyID (IoaState state' (msgs \<union> newMsgs)) = Some encKeyID)
             \<or> (\<forall>nB slaveSae keyID encKeyID masterSae. nB \<in> nodes \<longrightarrow>
                  \<not> kme_network_has_msg kmeID s n nB (KMGet slaveSae keyID encKeyID masterSae))"
  shows "inv1 nodes kmeID t"
proof -
  have kme_s: "kme s n = IoaState state msgs"
    using assms(1,5) by simp
  have kme_t: "kme t n = IoaState state' (msgs \<union> newMsgs)"
    using assms(2,6) by simp
  have kme_other: "\<And>nA. nA \<noteq> n \<Longrightarrow> kme t nA = kme s nA"
    using assms(1,2,6) by simp
  have net_old: "\<And>p m. m \<in> set (network t p) \<Longrightarrow> m \<in> set (network s p)"
    using assms(1-3) apply (cases "net (sender, kmeID n)") by (auto split: if_splits)
  have other_mono: "\<And>nA nB m. nA \<noteq> n \<Longrightarrow>
        kme_network_has_msg kmeID t nA nB m \<Longrightarrow> kme_network_has_msg kmeID s nA nB m"
    by (auto dest: net_old simp: kme_other)
  have n_old_or_new: "\<And>nB m. kme_network_has_msg kmeID t n nB m \<Longrightarrow>
        kme_network_has_msg kmeID s n nB m \<or> (kmeID n, kmeID nB, m) \<in> newMsgs"
    by (auto dest: net_old simp: kme_s kme_t)
  have inv1_s: "\<And>nA nB slaveSae keyID encKeyID masterSae.
        nA \<in> nodes \<Longrightarrow> nB \<in> nodes \<Longrightarrow>
        kme_network_has_msg kmeID s nA nB (KMGet slaveSae keyID encKeyID masterSae) \<Longrightarrow>
        kme_has_decryptionKeyID (kme s nA) = Some encKeyID"
    using assms(8) unfolding inv1_def by blast
  show ?thesis
    unfolding inv1_def
  proof (intro allI impI)
    fix nA nB slaveSae keyID encKeyID masterSae
    assume a: "nA \<in> nodes \<and> nB \<in> nodes \<and>
               kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae)"
    then have nA_nodes: "nA \<in> nodes" and nB_nodes: "nB \<in> nodes"
      and has_t: "kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      by blast+
    show "kme_has_decryptionKeyID (kme t nA) = Some encKeyID"
    proof (cases "nA = n")
      case False
      have has_s: "kme_network_has_msg kmeID s nA nB (KMGet slaveSae keyID encKeyID masterSae)"
        by (rule other_mono[OF False has_t])
      have "kme_has_decryptionKeyID (kme s nA) = Some encKeyID"
        by (rule inv1_s[OF nA_nodes nB_nodes has_s])
      then show ?thesis
        by (simp add: kme_other[OF False])
    next
      case True
      have has_t_n: "kme_network_has_msg kmeID t n nB (KMGet slaveSae keyID encKeyID masterSae)"
        using has_t True by fastforce
      consider (new) "(kmeID n, kmeID nB, KMGet slaveSae keyID encKeyID masterSae) \<in> newMsgs"
        | (old) "kme_network_has_msg kmeID s n nB (KMGet slaveSae keyID encKeyID masterSae)"
        using n_old_or_new[OF has_t_n] by blast
      then show ?thesis
      proof cases
        case new
        from sent[OF nB_nodes new] show ?thesis
          by (simp add: True kme_t)
      next
        case old
        have dk_s: "kme_has_decryptionKeyID (IoaState state msgs) = Some encKeyID"
          using inv1_s[OF assms(7) nB_nodes old] by (simp add: kme_s)
        have "kme_has_decryptionKeyID (IoaState state' (msgs \<union> newMsgs)) = Some encKeyID"
          using kept dk_s old nB_nodes by blast
        then show ?thesis
          by (simp add: True kme_t)
      qed
    qed
  qed
qed

lemma inv5_induct_inv6lllllllll:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes', bridges, qkd, net')"
    and "net' = net((sender, kmeID n) := tl (net (sender, kmeID n)))"
    and "can_send net sender (kmeID n) msgR"
    and "kmes n = IoaState state msgs"
    and "kmes' = kmes(n := IoaState state' (msgs \<union> newMsgs))"
    and "\<And>nB msg slaveSae keyID encKeyID masterSae. (kmeID n, kmeID nB, KMGet slaveSae keyID encKeyID masterSae) \<notin> newMsgs"
    and "\<And>slaveSae keyID encKeyID masterSae. msgR \<noteq> KMGet slaveSae keyID encKeyID masterSae"
    and "n \<in> nodes"
    and "kme_has_decryptionKeyID (kme s n) = None"
    and "inv6 nodes kmeID s"
    and "inv5 nodes kmeID s"
  shows "inv5 nodes kmeID t"
proof -
  have "\<forall>nA nB kmID keyID' reserveOption slaveSae keyID encKeyID masterSae.
       nA \<in> nodes-{n} \<and> nB \<in> nodes \<and> kme_network_has_msg kmeID t nA nB (KMPut kmID keyID' reserveOption) \<longrightarrow>
       \<not> kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae)"
  proof (intro allI)
    fix nA nB kmID keyID' reserveOption slaveSae keyID encKeyID masterSae
    show "nA \<in> nodes-{n} \<and> nB \<in> nodes \<and> kme_network_has_msg kmeID t nA nB (KMPut kmID keyID' reserveOption) \<longrightarrow>
          \<not> kme_network_has_msg kmeID t nA nB (KMGet slaveSae keyID encKeyID masterSae)"
      using kme_other_exclusive_preserved[OF assms(1-4,5,6), of]
            assms(12) unfolding inv5_def by blast
  qed
  moreover have "\<forall>nB kmID keyID' reserveOption slaveSae keyID encKeyID masterSae.
       n \<in> nodes \<and> nB \<in> nodes \<and> kme_network_has_msg kmeID t n nB (KMPut kmID keyID' reserveOption) \<longrightarrow>
       \<not> kme_network_has_msg kmeID t n nB (KMGet slaveSae keyID encKeyID masterSae)"
  proof -
    have "\<And>nB slaveSae keyID encKeyID masterSae. nB \<in> nodes \<Longrightarrow> \<not> kme_network_has_msg kmeID s n nB (KMGet slaveSae keyID encKeyID masterSae)"
      using assms(9,10,11) unfolding inv6_def by blast
    then have "\<And>nB slaveSae keyID encKeyID masterSae. nB \<in> nodes \<Longrightarrow> \<not> kme_network_has_msg kmeID t n nB (KMGet slaveSae keyID encKeyID masterSae)"
      using kme_receive_no_network_change[OF assms(1,2,3,4,5,6,7,8)] by blast
    then show ?thesis
      by simp 
  qed  
  ultimately show ?thesis
    unfolding inv5_def by fast    
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
    case (Kme_KMPost_NewKeyVal apps kmes bridges qkd net kmes' net' n sender otherKme keyID keyVal store route saeToKme bridgeIDs' kmeIDs msgs)
    have "inv1 nodes kmeID t"
      using inv1_induct[OF Kme_KMPost_NewKeyVal(2,3,7,8,10,11)] Kme_KMPost_NewKeyVal(2,3,10,11) 2(2) by fastforce
    moreover have "inv2 nodes kmeID t"
      using inv2_induct[OF Kme_KMPost_NewKeyVal(2,3,7,8,10,11)] Kme_KMPost_NewKeyVal(2,3,10,11) 2(2) by fastforce
    moreover have "inv3 nodes kmeID t"
      using inv3_induct[OF Kme_KMPost_NewKeyVal(2,3,7,8,10,11)] Kme_KMPost_NewKeyVal(2,3,10,11) 2(2) by fastforce
    moreover have "inv4 nodes kmeID t"
    proof -
      have "sender \<in> \<Union> (bridgeIDs ` nodes)"
        sorry
      then have "\<And>nB. (kmeID n, kmeID nB, OK) \<notin> {(kmeID n, sender, OK), (kmeID n, otherKme, KMPut (kmeID n) keyID None)}"
        using disjoint_ids unfolding disjnt_def by fast
      then show ?thesis
        using inv4_induct[OF Kme_KMPost_NewKeyVal(2,3,7,8,10,11)] Kme_KMPost_NewKeyVal(2,3,10,11) 2(2) by fastforce
    qed
    moreover have "inv5 nodes kmeID t"
      using inv5_induct_inv6[OF Kme_KMPost_NewKeyVal(2,3,7,8,10,11)] Kme_KMPost_NewKeyVal(2,4,10) 2(2) by force
    moreover have "inv6 nodes kmeID t"
      using inv6_induct[OF Kme_KMPost_NewKeyVal(2,3,7,8,10,11)] Kme_KMPost_NewKeyVal(2,3,10,11) 2(2) by fastforce
    ultimately show ?case 
      by blast
  next
    case (Kme_KMPut_Confirm apps kmes bridges qkd net kmes' net' n sender otherKme keyID store route saeToKme bridgeIDs kmeIDs msgs)
    have "inv1 nodes kmeID t"
      using inv1_induct[OF Kme_KMPut_Confirm(2,3,7,8,10,11)] Kme_KMPut_Confirm(2,3,10,11) 2(2) by fastforce
    moreover have "inv2 nodes kmeID t"
      using inv2_induct[OF Kme_KMPut_Confirm(2,3,7,8,10,11)] Kme_KMPut_Confirm(2,3,10,11) 2(2) by fastforce
    moreover have "inv3 nodes kmeID t"
      using inv3_induct[OF Kme_KMPut_Confirm(2,3,7,8,10,11)] Kme_KMPut_Confirm(2,3,10,11) 2(2) by fastforce
    moreover have "inv4 nodes kmeID t"
      using inv4_induct_confirm_reserve[OF Kme_KMPut_Confirm(2,3,7,8,10,11)] 2(2) by blast
    moreover have "inv5 nodes kmeID t"
      using inv5_induct_inv6[OF Kme_KMPut_Confirm(2,3,7,8,10,11)] Kme_KMPut_Confirm(2,4,10) 2(2) by force
    moreover have "inv6 nodes kmeID t"
      using inv6_induct[OF Kme_KMPut_Confirm(2,3,7,8,10,11)] Kme_KMPut_Confirm(2,3,10,11) 2(2) by fastforce
    ultimately show ?case 
      by fast
  next
    case (Kme_GetKey apps kmes bridges qkd net kmes' net' n sender host slaveSae store route saeToKme bridgeIDs kmeIDs msgs keyID val)
    have "inv1 nodes kmeID t"
      using inv1_induct[OF Kme_GetKey(2,3,7,8,10,11)] Kme_GetKey(2,3,10,11) 2(2) by fastforce
    moreover have "inv2 nodes kmeID t"
      using inv2_induct[OF Kme_GetKey(2,3,7,8,10,11)] Kme_GetKey(2,3,10,11) 2(2) by fastforce
    moreover have "inv3 nodes kmeID t"
      using inv3_induct[OF Kme_GetKey(2,3,7,8,10,11)] Kme_GetKey(2,3,10,11) 2(2) by fastforce
    moreover have "inv4 nodes kmeID t"
      using inv4_induct[OF Kme_GetKey(2,3,7,8,10,11)] Kme_GetKey(2,3,10,11) 2(2) by fastforce
    moreover have "inv5 nodes kmeID t"
      using inv5_induct_inv6[OF Kme_GetKey(2,3,7,8,10,11)] Kme_GetKey(2,4,10) 2(2) by force
    moreover have "inv6 nodes kmeID t"
      using inv6_induct[OF Kme_GetKey(2,3,7,8,10,11)] Kme_GetKey(2,3,10,11) 2(2) by fastforce
    ultimately show ?case 
      by fast
  next
    case (Kme_KMPut_Reserve apps kmes bridges qkd net kmes' net' n sender otherKme slaveSae store route saeToKme bridgeIDs kmeIDs msgs keyID)
    have "inv1 nodes kmeID t"
      using inv1_induct[OF Kme_KMPut_Reserve(2,3,7,8,10,11)] Kme_KMPut_Reserve(2,3,10,11) 2(2) by fastforce
    moreover have "inv2 nodes kmeID t"
      using inv2_induct[OF Kme_KMPut_Reserve(2,3,7,8,10,11)] Kme_KMPut_Reserve(2,3,10,11) 2(2) by fastforce
    moreover have "inv3 nodes kmeID t"
      using inv3_induct[OF Kme_KMPut_Reserve(2,3,7,8,10,11)] Kme_KMPut_Reserve(2,3,10,11) 2(2) by fastforce
    moreover have "inv4 nodes kmeID t"
    proof -
      have "otherKme = sender"
        sorry
      then show ?thesis
        using inv4_induct_confirm_reserve[OF Kme_KMPut_Reserve(2,3,7,8,10)] Kme_KMPut_Reserve(3,11) 2(2) by blast
    qed
    moreover have "inv5 nodes kmeID t"
      using inv5_induct[OF Kme_KMPut_Reserve(2,3,7,8,10,11)] Kme_KMPut_Reserve(2,3,10,11) 2(2) by fastforce
    moreover have "inv6 nodes kmeID t"
      using inv6_induct[OF Kme_KMPut_Reserve(2,3,7,8,10,11)] Kme_KMPut_Reserve(2,3,10,11) 2(2) by fastforce
    ultimately show ?case 
      by fast
  next
    case (Kme_GetKey_Reserved apps kmes bridges qkd net kmes' net' n sender store keyID val conf res saeID route saeToKme bridgeIDs kmeIDs msgs)
    have "inv1 nodes kmeID t"
      using inv1_induct[OF Kme_GetKey_Reserved(2,3,7,8,10,11)] Kme_GetKey_Reserved(2,3,10,11) 2(2) by fastforce
    moreover have "inv2 nodes kmeID t"
    proof -
      have "saeID \<notin> kmeID ` nodes"
        sorry
      then show ?thesis
        using inv2_induct[OF Kme_GetKey_Reserved(2,3,7,8,10,11)] Kme_GetKey_Reserved(2,3,10,11) 2(2) by fast
    qed
    moreover have "inv3 nodes kmeID t"
      using inv3_induct[OF Kme_GetKey_Reserved(2,3,7,8,10,11)] Kme_GetKey_Reserved(2,3,10,11) 2(2) by fastforce
    moreover have "inv4 nodes kmeID t"
      using inv4_induct[OF Kme_GetKey_Reserved(2,3,7,8,10,11)] Kme_GetKey_Reserved(2,3,10,11) 2(2) by fastforce
    moreover have "inv5 nodes kmeID t"
      using inv5_induct[OF Kme_GetKey_Reserved(2,3,7,8,10,11)] Kme_GetKey_Reserved(2,3,10,11) 2(2) by fastforce
    moreover have "inv6 nodes kmeID t"
      using inv6_induct[OF Kme_GetKey_Reserved(2,3,7,8,10,11)] Kme_GetKey_Reserved(2,3,10,11) 2(2) by fastforce
    ultimately show ?case 
      by fast
  next
    case (Kme_GetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n sender host store keyID val saeToKme bridgeIDs kmeIDs masterSae route msgs)
    have "inv1 nodes kmeID t"
      using inv1_induct[OF Kme_GetKeyWithID_IDFound(2,3,7,8,10,11)] Kme_GetKeyWithID_IDFound(2,3,10,11) 2(2) by fastforce
    moreover have "inv2 nodes kmeID t"
    proof -
      have "sender \<notin> kmeID ` nodes"
        sorry
      then show ?thesis
        using inv2_induct[OF Kme_GetKeyWithID_IDFound(2,3,7,8,10,11)] Kme_GetKeyWithID_IDFound(2,3,10,11) 2(2) by fast
    qed
    moreover have "inv3 nodes kmeID t"
      using inv3_induct[OF Kme_GetKeyWithID_IDFound(2,3,7,8,10,11)] Kme_GetKeyWithID_IDFound(2,3,10,11) 2(2) by fastforce
    moreover have "inv4 nodes kmeID t"
      using inv4_induct[OF Kme_GetKeyWithID_IDFound(2,3,7,8,10,11)] Kme_GetKeyWithID_IDFound(2,3,10,11) 2(2) by fastforce
    moreover have "inv5 nodes kmeID t"
      using inv5_induct[OF Kme_GetKeyWithID_IDFound(2,3,7,8,10,11)] Kme_GetKeyWithID_IDFound(2,3,10,11) 2(2) by fastforce
    moreover have "inv6 nodes kmeID t"
      using inv6_induct[OF Kme_GetKeyWithID_IDFound(2,3,7,8,10,11)] Kme_GetKeyWithID_IDFound(2,3,10,11) 2(2) by fastforce
    ultimately show ?case 
      by fast
  next
    case (Kme_GetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' net' n sender host masterSae keyID store route nextKme keyID2 val2 saeToKme bridgeIDs kmeIDs msgs)
    have "inv1 nodes kmeID t"
      using inv1_induct[OF Kme_GetKeyWithID_IDNotFound(2,3,7,8,12,13)] Kme_GetKeyWithID_IDNotFound(2,3,12,13) 2(2) by simp
    moreover have "inv2 nodes kmeID t"
      using inv2_induct[OF Kme_GetKeyWithID_IDNotFound(2,3,7,8,12,13)] Kme_GetKeyWithID_IDNotFound(2,3) 2(2) by fastforce
    moreover have "inv3 nodes kmeID t"
      using inv3_induct[OF Kme_GetKeyWithID_IDNotFound(2,3,7,8,12,13)] Kme_GetKeyWithID_IDNotFound(2,3) 2(2) by fastforce
    moreover have "inv4 nodes kmeID t"
      using inv4_induct[OF Kme_GetKeyWithID_IDNotFound(2,3,7,8,12,13)] Kme_GetKeyWithID_IDNotFound(2,3) 2(2) by fastforce
    moreover have "inv5 nodes kmeID t"
      using inv5_induct_inv6[OF Kme_GetKeyWithID_IDNotFound(2,3,7,8,12,13)] Kme_GetKeyWithID_IDNotFound(2,4,12) 2(2) by force
    moreover have "inv6 nodes kmeID t"
      using inv6_induct[OF Kme_GetKeyWithID_IDNotFound(2,3,7,8,12,13)] Kme_GetKeyWithID_IDNotFound(2,3,12,13) 2(2) by simp
    ultimately show ?case 
      by fast
  next
    case (Kme_GetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' net' n nextKme masterSae slaveSae keyID keyID2 store route saeToKme bridgeIDs kmeIDs msgs)
    have "inv1 nodes kmeID t"
      using inv1_induct_one_kme[OF Kme_GetKeyWithID_IDNotFound_Reserved(2,3,7,8,9,10,4)] Kme_GetKeyWithID_IDNotFound_Reserved(3,10) 2(2)
      by auto
    moreover have "inv2 nodes kmeID t"
      using inv2_induct[OF Kme_GetKeyWithID_IDNotFound_Reserved(2,3,7-10)] Kme_GetKeyWithID_IDNotFound_Reserved 2(2) sorry
    moreover have "inv3 nodes kmeID t"
      using inv3_induct[OF Kme_GetKeyWithID_IDNotFound_Reserved(2,3,7-10)] Kme_GetKeyWithID_IDNotFound_Reserved 2(2) sorry
    moreover have "inv4 nodes kmeID t"
      using inv4_induct[OF Kme_GetKeyWithID_IDNotFound_Reserved(2,3,7-10)] Kme_GetKeyWithID_IDNotFound_Reserved 2(2) sorry
    moreover have "inv5 nodes kmeID t"
      using inv5_induct[OF Kme_GetKeyWithID_IDNotFound_Reserved(2,3,7-10)] Kme_GetKeyWithID_IDNotFound_Reserved 2(2) sorry
    moreover have "inv6 nodes kmeID t"
      using inv6_induct[OF Kme_GetKeyWithID_IDNotFound_Reserved(2,3,7-10)] Kme_GetKeyWithID_IDNotFound_Reserved 2(2) sorry
    ultimately show ?case 
      by fast
  next
    case (Kme_KMGetKeyWithID_IDFound apps kmes bridges qkd net kmes' net' n masterSae keyID keyID2 slaveSae store route saeToKme bridgeIDs kmeIDs msgs sender val val2)
    have "inv1 nodes kmeID t"
      using inv1_induct[OF Kme_KMGetKeyWithID_IDFound(2,3,7,8,11,12)] Kme_KMGetKeyWithID_IDFound(2,3,11,12) 2(2) by auto
    moreover have "inv2 nodes kmeID t"
      using inv2_induct[OF Kme_KMGetKeyWithID_IDFound(2,3,7,8,11,12)] Kme_KMGetKeyWithID_IDFound(2,3,11,12) 2(2) sorry
    moreover have "inv3 nodes kmeID t"
      using inv3_induct[OF Kme_KMGetKeyWithID_IDFound(2,3,7,8,11,12)] Kme_KMGetKeyWithID_IDFound(2,3,11,12) 2(2) by auto
    moreover have "inv4 nodes kmeID t"
      using inv4_induct[OF Kme_KMGetKeyWithID_IDFound(2,3,7,8,11,12)] Kme_KMGetKeyWithID_IDFound(2,3,11,12) 2(2) by fastforce
    moreover have "inv5 nodes kmeID t"
      using inv5_induct[OF Kme_KMGetKeyWithID_IDFound(2,3,7,8,11,12)] Kme_KMGetKeyWithID_IDFound(2,3,11,12) 2(2) by fastforce
    moreover have "inv6 nodes kmeID t"
      using inv6_induct[OF Kme_KMGetKeyWithID_IDFound(2,3,7,8,11,12)] Kme_KMGetKeyWithID_IDFound(2,3,11,12) 2(2) by auto
    ultimately show ?case 
      by fast
  next
    case (Kme_KMGetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' net' n nextKme masterSae keyID keyID2 slaveSae store val2 sender route keyID3 val3 saeToKme bridgeIDs kmeIDs msgs)
    have "inv1 nodes kmeID t"
      using inv1_induct[OF Kme_KMGetKeyWithID_IDNotFound(2,3,7,8,13,14)] Kme_KMGetKeyWithID_IDNotFound(2,3,13,14) 2(2) by simp
    moreover have "inv2 nodes kmeID t"
      using inv2_induct[OF Kme_KMGetKeyWithID_IDNotFound(2,3,7,8,13,14)] Kme_KMGetKeyWithID_IDNotFound(2,3,13,14) 2(2) by fast
    moreover have "inv3 nodes kmeID t"
      using inv3_induct[OF Kme_KMGetKeyWithID_IDNotFound(2,3,7,8,13,14)] Kme_KMGetKeyWithID_IDNotFound(2,3,13,14) 2(2) by auto
    moreover have "inv4 nodes kmeID t"
      using inv4_induct[OF Kme_KMGetKeyWithID_IDNotFound(2,3,7,8,13,14)] Kme_KMGetKeyWithID_IDNotFound(2,3,13,14) 2(2) by fast
    moreover have "inv5 nodes kmeID t"
      using inv5_induct_inv6[OF Kme_KMGetKeyWithID_IDNotFound(2,3,7,8,13,14)] Kme_KMGetKeyWithID_IDNotFound(2,3,13,14) 2(2) sorry
    moreover have "inv6 nodes kmeID t"
      using inv6_induct[OF Kme_KMGetKeyWithID_IDNotFound(2,3,7,8,13,14)] Kme_KMGetKeyWithID_IDNotFound(2,3,13,14) 2(2) by auto
    ultimately show ?case 
      by fast
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' net' n nextKme prevKme masterSae keyID keyID2 slaveSae store route keyID3 saeToKme bridgeIDs kmeIDs msgs)
    have "inv1 nodes kmeID t"
      using inv1_induct_one_kme[OF Kme_KMGetKeyWithID_IDNotFound_Reserved(2,3,7,8,9,10,4)] Kme_KMGetKeyWithID_IDNotFound_Reserved(2,3,9,10) 2(2) by simp
    moreover have "inv2 nodes kmeID t"
      using inv2_induct[OF Kme_KMGetKeyWithID_IDNotFound_Reserved(2,3,7,8,9,10)] Kme_KMGetKeyWithID_IDNotFound_Reserved(2,3,9,10) 2(2) sorry
    moreover have "inv3 nodes kmeID t"
      using inv3_induct[OF Kme_KMGetKeyWithID_IDNotFound_Reserved(2,3,7,8,9,10)] Kme_KMGetKeyWithID_IDNotFound_Reserved(2,3,9,10) 2(2) sorry
    moreover have "inv4 nodes kmeID t"
      using inv4_induct[OF Kme_KMGetKeyWithID_IDNotFound_Reserved(2,3,7,8,9,10)] Kme_KMGetKeyWithID_IDNotFound_Reserved(2,3,9,10) 2(2) sorry
    moreover have "inv5 nodes kmeID t"
      using inv5_induct[OF Kme_KMGetKeyWithID_IDNotFound_Reserved(2,3,7,8,9,10)] Kme_KMGetKeyWithID_IDNotFound_Reserved(2,3,9,10) 2(2) sorry
    moreover have "inv6 nodes kmeID t"
      using inv6_induct[OF Kme_KMGetKeyWithID_IDNotFound_Reserved(2,3,7,8,9,10)] Kme_KMGetKeyWithID_IDNotFound_Reserved(2,3,9,10) 2(2) sorry
    ultimately show ?case 
      by fast
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme prevKme keyID keyVal' store keyID2 val2 keyID3 val3 masterSae route saeToKme bridgeIDs kmeIDs msgs slaveSae)
    have "inv1 nodes kmeID t"
      using inv1_induct_one_kme[OF Kme_KMGetKeyWithID_IDNotFound_Return(2,3,7,8,11,12,4)] Kme_KMGetKeyWithID_IDNotFound_Return(2,3,11,12) 2(2) sorry
    moreover have "inv2 nodes kmeID t"
      using inv2_induct[OF Kme_KMGetKeyWithID_IDNotFound_Return(2,3,7,8,11,12)] Kme_KMGetKeyWithID_IDNotFound_Return(2,3,11,12) 2(2) sorry
    moreover have "inv3 nodes kmeID t"
      using inv3_induct[OF Kme_KMGetKeyWithID_IDNotFound_Return(2,3,7,8,11,12)] Kme_KMGetKeyWithID_IDNotFound_Return(2,3,11,12) 2(2) by fastforce
    moreover have "inv4 nodes kmeID t"
      using inv4_induct[OF Kme_KMGetKeyWithID_IDNotFound_Return(2,3,7,8,11,12)] Kme_KMGetKeyWithID_IDNotFound_Return(2,3,11,12) 2(2) by fastforce
    moreover have "inv5 nodes kmeID t"
      using inv5_induct[OF Kme_KMGetKeyWithID_IDNotFound_Return(2,3,7,8,11,12)] Kme_KMGetKeyWithID_IDNotFound_Return(2,3,11,12) 2(2) by fastforce
    moreover have "inv6 nodes kmeID t"
      using inv6_induct[OF Kme_KMGetKeyWithID_IDNotFound_Return(2,3,7,8,11,12)] Kme_KMGetKeyWithID_IDNotFound_Return(2,3,11,12) 2(2) sorry
    ultimately show ?case 
      by fast
  next
    case (Kme_GetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' net' n nextKme keyID keyVal' store keyID2 val2 masterSae sender route saeToKme bridgeIDs kmeIDs msgs)
    have "inv1 nodes kmeID t"
      using inv1_induct_one_kme[OF Kme_GetKeyWithID_IDNotFound_Return(2,3,7,8,10,11,4)] Kme_GetKeyWithID_IDNotFound_Return(2,3,10,11) 2(2) sorry
    moreover have "inv2 nodes kmeID t"
    proof -
      have "sender \<notin> kmeID ` nodes"
        sorry
      then show ?thesis
        using inv2_induct[OF Kme_GetKeyWithID_IDNotFound_Return(2,3,7,8,10,11)] Kme_GetKeyWithID_IDNotFound_Return(2,3,10,11) 2(2) by blast
    qed
    moreover have "inv3 nodes kmeID t"
      using inv3_induct[OF Kme_GetKeyWithID_IDNotFound_Return(2,3,7,8,10,11)] Kme_GetKeyWithID_IDNotFound_Return(2,3,10,11) 2(2) by fastforce
    moreover have "inv4 nodes kmeID t"
      using inv4_induct[OF Kme_GetKeyWithID_IDNotFound_Return(2,3,7,8,10,11)] Kme_GetKeyWithID_IDNotFound_Return(2,3,10,11) 2(2) by fastforce
    moreover have "inv5 nodes kmeID t"
      using inv5_induct[OF Kme_GetKeyWithID_IDNotFound_Return(2,3,7,8,10,11)] Kme_GetKeyWithID_IDNotFound_Return(2,3,10,11) 2(2) by fastforce
    moreover have "inv6 nodes kmeID t"
      using inv6_induct[OF Kme_GetKeyWithID_IDNotFound_Return(2,3,7,8,10,11)] Kme_GetKeyWithID_IDNotFound_Return(2,3,10,11) 2(2) sorry
    ultimately show ?case 
      by fast
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