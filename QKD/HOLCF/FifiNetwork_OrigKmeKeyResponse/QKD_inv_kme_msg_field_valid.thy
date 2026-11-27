theory QKD_inv_kme_msg_field_valid
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
          QKD_inv_kme_buffer_msg_field_valid
begin

lemma kme_msg_field_valid_helper:
  assumes "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps', kmes', bridges', qkd', net')"
    and "a = Receive sender rcpt msg"
    and "net' = rmv_msg net sender rcpt msg \<or> net' = net"
    and "kme_msg_field_valid nodes kmeID s"
  shows "kme_msg_field_valid nodes kmeID t"
proof -
  have "\<And>sender rcpt msg. network_has_msg t sender rcpt msg \<longrightarrow> network_has_msg s sender rcpt msg"
    using assms apply simp
    apply (cases "net = net'")
     apply fast
    by (metis fun_upd_other fun_upd_same list.sel(2) list.set_sel(2))
  then
  show ?thesis
  using assms unfolding kme_msg_field_valid_def by fast
qed

context QKD_Network
begin

lemma inv_kme_msg_field_valid:
  shows "invariant System.ioa (kme_msg_field_valid nodes kmeID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 apps kmes bridges qkd net)
    then show ?thesis
      unfolding kme_msg_field_valid_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (App_Send apps kmes bridges qkd net apps' net' n msgs rcpt msg appState)
    have "appID n \<notin> kmeID ` nodes"
      using disjoint_ids unfolding disjnt_def by fast
    then show ?case
      using 2(2) App_Send(2-10) unfolding kme_msg_field_valid_def by simp
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    have "kme_buffer_msg_field_valid nodes kmeID s"
      using inv_kme_buffer_msg_field_valid 2(1) unfolding invariant_def by blast
    then show ?case
      using 2(2) Kme_Send(2-10) unfolding kme_msg_field_valid_def kme_buffer_msg_field_valid_def
      apply simp apply auto by blast+
  next
    case (Bridge_Send apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState)
    then have "b \<notin> kmeID ` nodes"
      using disjoint_ids unfolding disjnt_def by fast
    then show ?case
      using 2(2) Bridge_Send(2,3,8) unfolding kme_msg_field_valid_def by simp
  next
    case (Qkd_Send apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal)
    then show ?case 
      using 2(2) unfolding kme_msg_field_valid_def by auto
  next
    case (Network_Ext_Send apps kmes bridges qkd net net' sender rcpt msg all)
    then show ?case 
      using 2(2) unfolding kme_msg_field_valid_def by auto
  qed
  (use 2(2) kme_msg_field_valid_helper in \<open>meson+\<close>)
qed

end

end