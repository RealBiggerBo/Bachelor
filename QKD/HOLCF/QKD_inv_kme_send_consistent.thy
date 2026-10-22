theory QKD_inv_kme_send_consistent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
          QKD_inv_qkd_layer_consistent
begin

context QKD_Network
begin

lemma inv_kme_send_consistent:
  shows "invariant System.ioa (kme_send_consistent nodes kmeID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 tn qkd net)
    then show ?thesis
      unfolding kme_send_consistent_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (App_Send apps kmes bridges qkd net apps' net' n msgs rcpt msg appState)
    then have "appID n \<notin> kmeID ` nodes"
      using disjoint_ids
      by (metis (no_types, opaque_lifting) disjnt_iff image_iff range_eqI)
    then have "kme_send_consistent nodes kmeID s \<longleftrightarrow> kme_send_consistent nodes kmeID t"
      using App_Send(2,3,7) unfolding kme_send_consistent_def
      by (metis (mono_tags, lifting) Un_iff prod.inject singletonD sndI)
    then show ?case 
      using 2(2) by argo
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    then have "\<forall>n s1 r1 k v1 state msgs s2 r2 v2.
        n \<in> nodes \<and>
        kmes n = IoaState state msgs \<and>
        (s1,r1,KeyResponse k v1) \<in> msgs \<and>
        (s2,r2,KeyResponse k v2) \<in> network s
        \<longrightarrow> v1 = v2"
      sorry
    then show ?case
      using kme_send_consistent_def
      by (smt (verit, del_insts) "2.IH"(2) Kme_Send.IH(2,3,4) Kme_Send.hyps(1,2,3) Un_commute insert_def insert_iff msg.inject(3)
          singleton_conv snd_conv)
  next
    case (Bridge_Send apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState)
    then have "b \<notin> kmeID ` nodes"
      using disjoint_ids
      by (smt (verit, ccfv_threshold) UNIV_I Union_iff disjnt_insert2 image_iff insert_absorb)
    then have "kme_send_consistent nodes kmeID s \<longleftrightarrow> kme_send_consistent nodes kmeID t"
      using Bridge_Send(2,3,8) unfolding kme_send_consistent_def
      by (metis (mono_tags, lifting) Un_iff prod.inject singletonD sndI)
    then show ?case 
      using 2(2) by argo
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    then have "pid \<notin> kmeID ` nodes"
      using disjoint_ids
      by (metis (no_types, opaque_lifting) disjnt_iff image_iff insertCI insert_UNIV)
    then have "kme_send_consistent nodes kmeID s \<longleftrightarrow> kme_send_consistent nodes kmeID t"
      using Qkd_Send(2,3,8) unfolding kme_send_consistent_def
      by (metis (mono_tags, lifting) Un_iff prod.inject singletonD sndI)
    then show ?case 
      using 2(2) by argo
  next
    case (Network_Ext_Send apps kmes bridges qkd net net' sender rcpt msg all)
    then have "sender \<notin> kmeID ` nodes"
      by fast
    then have "kme_send_consistent nodes kmeID s \<longleftrightarrow> kme_send_consistent nodes kmeID t"
      using Network_Ext_Send(2,3,12) unfolding kme_send_consistent_def
      by (metis (mono_tags, lifting) Un_iff prod.inject singletonD sndI)
    then show ?case 
      using 2(2) by argo
  qed
  (use 2(2) in \<open>auto simp: kme_send_consistent_def\<close>)
qed

end

end