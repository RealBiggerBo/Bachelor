theory QKD_inv_bridge_buffer_msg_field_valid
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
          QKD_inv_bridge_otherKme_field_valid
begin

context QKD_Network
begin

lemma inv_bridge_buffer_msg_field_valid:
  shows "invariant System.ioa (bridge_buffer_msg_field_valid nodes bridgeIDs kmeID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 apps kmes bridges qkd net)
    then show ?thesis
      unfolding bridge_buffer_msg_field_valid_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (Bridge_Master_KeyResponse apps kmes bridges qkds net bridges' net' n b slaveBridge otherKme qkd kme msgs keyID keyVal)
    then have "otherKme \<in> kmeID ` nodes"
      using inv_bridge_otherKme_field_valid 2(1) unfolding invariant_def bridge_otherKme_field_valid_def by fastforce
    then show ?case 
      using 2(2) Bridge_Master_KeyResponse(2,3,10,11) unfolding bridge_buffer_msg_field_valid_def
      by (smt (verit, best) Un_insert_right boolean_algebra.disj_zero_right fstI fun_upd_other fun_upd_same insertE
          ioa_state.inject msg.distinct(43) msg.inject(5) sndI)
  next
    case (Bridge_Slave_KeyResponse apps kmes bridges qkds net bridges' net' n b masterBridge otherKme qkd kme msgs keyID keyVal)
    then have "otherKme \<in> kmeID ` nodes"
      using inv_bridge_otherKme_field_valid 2(1) unfolding invariant_def bridge_otherKme_field_valid_def by fastforce
    then show ?case 
      using 2(2) Bridge_Slave_KeyResponse(2,3,10,11) unfolding bridge_buffer_msg_field_valid_def
      by (smt (verit, best) Un_insert_right boolean_algebra.disj_zero_right fstI fun_upd_other fun_upd_same insertE
          ioa_state.inject msg.distinct(43) msg.inject(5) sndI)
  next
    case (Bridge_Send apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState)
    then have "\<And>n b state msgs rcpt otherKme keyID keyVal. 
                bridge t n b = IoaState state msgs \<and> (b, rcpt, KMPost otherKme keyID keyVal) \<in> msgs
                \<longrightarrow> (\<exists>msgs'. 
                      bridge s n b = IoaState state msgs' \<and> (b, rcpt, KMPost otherKme keyID keyVal) \<in> msgs')"
      by auto
    then show ?case
      using 2(2) unfolding bridge_buffer_msg_field_valid_def by blast
  qed
  (use 2(2) in \<open>auto simp: bridge_buffer_msg_field_valid_def\<close>)
qed

end

end