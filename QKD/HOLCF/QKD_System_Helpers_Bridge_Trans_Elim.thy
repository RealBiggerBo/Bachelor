theory QKD_System_Helpers_Bridge_Trans_Elim
  imports QKD_System_Helpers_Trans_Elim QKD_System_ActsDisj
begin

context QKD_Network
begin

lemma bridges_trans_elim [elim]:
  assumes "bridges \<midarrow>a\<midarrow>bridges.ioa\<rightarrow> bridges'"
  shows "(a \<in> act (bridge.ioa b n) \<and> n \<in> nodes \<and> b \<in> bridgeIDs n \<longrightarrow> bridges (n,b) \<midarrow>a\<midarrow>bridge.ioa b n\<rightarrow> bridges' (n,b)) \<and> 
         (a \<notin> act (bridge.ioa b n) \<or> n \<notin> nodes \<or> b \<notin> bridgeIDs n \<longrightarrow> bridges (n,b) = bridges' (n,b))"
  using set_ioa_trans_elim[OF assms] by fast

lemma bridge_invariant_step[consumes 7, case_names 
    Tick_GetKey
    Master_KeyResponse
    Slave_GetKeyWithID
    Slave_KeyResponse
    Send]:
  assumes "reachable System.ioa s"
    and "P s"
    and "n \<in> nodes"
    and "b \<in> bridgeIDs n"
    and "a \<in> act (bridge.ioa b n)"
    and "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps, kmes, bridges', qkd, net')"
    and "\<And>slaveBridge otherKme qkd kme msgs.
         \<lbrakk>a = TimerTick b; net = net';
          bridges (n,b) = IoaState (Bridge True slaveBridge otherKme qkd kme) msgs;
          bridges' = bridges((n,b) := IoaState (Bridge True slaveBridge otherKme qkd kme) (msgs \<union> {(b, qkd, GetKey qkd otherKme)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>slaveBridge otherKme qkd kme msgs sender keyID keyVal.
         \<lbrakk>a = Receive sender b (KeyResponse keyID keyVal); net = net';
          (sender, b, KeyResponse keyID keyVal) \<in> net;
          bridges (n,b) = IoaState (Bridge True slaveBridge otherKme qkd kme) msgs;
          bridges' = bridges((n,b) := IoaState (Bridge True slaveBridge otherKme qkd kme) (msgs \<union> {(b, kme, KMPost otherKme keyID keyVal), (b, slaveBridge, BridgeIDRelay keyID)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>masterBridge otherKme qkd kme msgs sender keyID.
         \<lbrakk>a = Receive sender b (BridgeIDRelay keyID); net = net';
          (sender, b, BridgeIDRelay keyID) \<in> net;
          bridges (n,b) = IoaState (Bridge False masterBridge otherKme qkd kme) msgs;
          bridges' = bridges((n,b) := IoaState (Bridge False masterBridge otherKme qkd kme) (msgs \<union> {(b, qkd, GetKeyWithID qkd otherKme keyID)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>masterBridge otherKme qkd kme msgs sender keyID keyVal.
         \<lbrakk>a = Receive sender b (KeyResponse keyID keyVal); net = net';
          (sender, b, KeyResponse keyID keyVal) \<in> net;
          bridges (n,b) = IoaState (Bridge False masterBridge otherKme qkd kme) msgs;
          bridges' = bridges((n,b) := IoaState (Bridge False masterBridge otherKme qkd kme) (msgs \<union> {(b, kme, KMPost otherKme keyID keyVal)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>msgs rcpt msg bridgeState.
         \<lbrakk>a = Send b rcpt msg; net' = net \<union> {(b, rcpt, msg)};
          (b, rcpt, msg) \<in> msgs;
          bridges (n,b) = IoaState bridgeState msgs;
          bridges' = bridges((n,b) := IoaState bridgeState (msgs - {(b, rcpt, msg)}))\<rbrakk> \<Longrightarrow> P t"
  shows "s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t \<longrightarrow> P t"
proof
  assume sat_trans:"s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t"
  note sys_trans = System_trans_elim[OF sat_trans assms(6,7)]
  have "a \<in> act bridges.ioa \<longrightarrow> bridges \<midarrow>a\<midarrow>bridges.ioa\<rightarrow> bridges'"
    using sys_trans by fast
  moreover have "a \<in> act bridges.ioa"
    using assms(3-5) unfolding actions_of_set_ioa by fast
  ultimately have bridges_trans:"bridges \<midarrow>a\<midarrow>bridges.ioa\<rightarrow> bridges'"
    by fastforce
  then have bridge_node_trans: "bridges (n,b) \<midarrow>a\<midarrow>bridge.ioa b n\<rightarrow> bridges' (n,b)"
    using assms(3,4,5) bridges_trans_elim[OF bridges_trans] by blast
  have "\<And>n' b'. \<lbrakk>n' \<in> nodes; b' \<in> bridgeIDs n'; b' \<noteq> b\<rbrakk> \<Longrightarrow> bridges (n',b') = bridges' (n',b')"
    using bridges_trans_elim[OF bridges_trans] actsDisj_bridge_bridge assms(3-5) by blast
  then have "\<And>s. \<lbrakk>s \<in> Sigma nodes bridgeIDs; s \<noteq> (n,b)\<rbrakk> \<Longrightarrow> bridges s = bridges' s"
    using bridges_trans_elim[OF bridges_trans] assms(3-5) 
    by (metis (no_types, opaque_lifting) SigmaE bridge_determines_node)
  moreover have "\<And>s. \<lbrakk>s \<notin> Sigma nodes bridgeIDs\<rbrakk> \<Longrightarrow> bridges s = bridges' s"
    using bridges_trans unfolding trans_of_set_ioa apply (simp; auto)
    by metis+
  ultimately have bridges': "bridges' = bridges ((n,b) := bridges' (n,b))"
    apply (intro ext)
    by (metis fun_upd_apply)
  consider "a = TimerTick b" | "\<exists>sender msg. a = Receive sender b msg" | "\<exists>rcpt msg. a = Send b rcpt msg"
    using assms(5) unfolding actions_def asig_projections asig_of_def 
    by (auto split: if_splits)
  then show "P t"
  proof cases
    case 1
    then have "a \<notin> act network.ioa"
      unfolding actions_def asig_projections asig_of_def by force
    then have net_eq:"net = net'"
      using sys_trans by fast
    then show ?thesis
    proof (cases "bridges (n,b)")
      case (IoaState state msgs)
      then show ?thesis
      proof (cases state)
        case (Bridge isMaster otherBridge otherKme qkd kme)
        then show ?thesis
        proof (cases isMaster)
          case True
          then have "bridges' (n,b) = IoaState (Bridge True otherBridge otherKme qkd kme) (msgs \<union> {(b, qkd, GetKey qkd otherKme)})"
            using 1 bridge_node_trans IoaState Bridge unfolding trans_of_def actions_def apply simp 
            unfolding asig_projections asig_of_def apply auto
            using bridge_step.cases apply blast+
            by (meson Tick_GetKey)
          then show "P t"
            using IoaState Bridge bridges' True assms(8)[OF 1 net_eq] by simp
        next
          case False
          then have "bridges' (n,b) = bridges (n,b)"
            using 1 bridge_node_trans IoaState Bridge unfolding trans_of_def actions_def apply simp 
            unfolding asig_projections asig_of_def apply auto
            using bridge_step.cases by blast+
          then show ?thesis
            using bridges' assms(2,6,7) net_eq by simp
        qed
      qed
    qed
  next
    case 2
    then have "a \<in> act network.ioa"
      unfolding actions_def asig_projections asig_of_def by auto
    then have net_trans:"net \<midarrow>a\<midarrow>network.ioa\<rightarrow> net'"
      using sys_trans by force
    then have net_eq:"net = net'"
      using 2 unfolding trans_of_def by auto
    obtain sender msg where a_split:"a = Receive sender b msg"
      using 2 by blast
    then have rec_in_net: "(sender, b, msg) \<in> net"
      using net_trans unfolding trans_of_def by simp
    show ?thesis
    proof (cases "bridges (n,b)")
      case (IoaState state msgs)
      show ?thesis
      proof (cases state)
        case (Bridge isMaster otherBridge otherKme qkd kme)
        show ?thesis
        proof (cases isMaster)
          case True
          show "P t"
          proof (cases "\<exists>keyID keyVal. msg = KeyResponse keyID keyVal")
            case True
            then obtain keyID keyVal where msg_split:"msg = KeyResponse keyID keyVal"
              by blast
            then have "bridges' (n,b) = IoaState (Bridge True otherBridge otherKme qkd kme) (msgs \<union> {(b, kme, KMPost otherKme keyID keyVal), (b, otherBridge, BridgeIDRelay keyID)})"
              using a_split assms(5) bridge_node_trans IoaState Bridge \<open>isMaster\<close> unfolding trans_of_def apply simp
              unfolding actions_def asig_projections asig_of_def apply simp
              using bridge_step.cases apply auto
                   apply fast
                  apply blast+
              using QKD_ETSI_Bridge.Master_KeyResponse apply meson
              using QKD_ETSI_Bridge.Master_KeyResponse by meson
            then show ?thesis
              using IoaState Bridge \<open>isMaster\<close> net_eq assms(9) a_split msg_split rec_in_net bridges' by presburger
          next
            case False
            then have "bridges' (n,b) = bridges (n,b)"
              using a_split assms(4) bridge_node_trans IoaState Bridge \<open>isMaster\<close> unfolding trans_of_def apply simp
              unfolding actions_def asig_projections asig_of_def 
              by (simp add: bridge_step.simps)
            then show ?thesis
              using bridges' assms(2,3,6,7) net_eq by fastforce
          qed
        next
          case False
          show "P t"
          proof (cases "\<exists>keyID keyVal. msg = KeyResponse keyID keyVal")
            case True
            then obtain keyID keyVal where msg_split:"msg = KeyResponse keyID keyVal"
              by blast
            then have "bridges' (n,b) = IoaState (Bridge False otherBridge otherKme qkd kme ) (msgs \<union> {(b,kme, KMPost otherKme keyID keyVal)})"
              using a_split assms(5) bridge_node_trans IoaState Bridge \<open>\<not>isMaster\<close> unfolding trans_of_def apply simp
              unfolding actions_def asig_projections asig_of_def apply simp
              using bridge_step.cases apply auto
                  apply fast
              apply blast+
              using QKD_ETSI_Bridge.Slave_KeyResponse by meson
            then show ?thesis
              using IoaState Bridge \<open>\<not>isMaster\<close> net_eq assms(11) a_split msg_split rec_in_net bridges' by presburger
          next
            case False
            then show ?thesis 
            proof (cases "\<exists>keyID. msg = BridgeIDRelay keyID")
              case True
              then obtain keyID where msg_split:"msg = BridgeIDRelay keyID"
                by blast
              then have "bridges' (n,b) = IoaState (Bridge False otherBridge otherKme qkd kme) (msgs \<union> {(b, qkd, GetKeyWithID qkd otherKme keyID)})"
                using a_split assms(5) bridge_node_trans IoaState Bridge \<open>\<not>isMaster\<close> unfolding trans_of_def apply simp
                unfolding actions_def asig_projections asig_of_def apply simp
                using bridge_step.cases apply auto
                    apply fast
                   apply blast+
                using Slave_GetKeyWithID by fast
              then show ?thesis
                using IoaState Bridge \<open>\<not>isMaster\<close> net_eq assms(10) a_split msg_split rec_in_net bridges' by presburger
            next
              case False
              then have "bridges' (n,b) = bridges (n,b)"
                using a_split assms(4) bridge_node_trans IoaState Bridge \<open>\<not>isMaster\<close> \<open>\<nexists>keyID keyVal. msg = KeyResponse keyID keyVal\<close> 
                unfolding trans_of_def actions_def asig_projections asig_of_def
                by (simp add: bridge_step.simps)
            then show ?thesis
              using bridges' assms(2,6,7) net_eq by fastforce
            qed
          qed
        qed
      qed
    qed
  next
    case 3
    then have "a \<in> act network.ioa"
      unfolding actions_def asig_projections asig_of_def by auto
    then have net_trans:"net \<midarrow>a\<midarrow>network.ioa\<rightarrow> net'"
      using sys_trans by force
    obtain rcpt msg where a_split:"a = Send b rcpt msg"
      using 3 by blast
    then have net':"net' = net \<union> {(b, rcpt, msg)}"
      using net_trans unfolding trans_of_def by auto
    then show ?thesis
    proof (cases "bridges (n,b)")
      case (IoaState state msgs)
      then have "(b, rcpt, msg) \<in> msgs"
        using bridge_node_trans a_split unfolding trans_of_def apply simp
        by (meson bridge.valid_ins)
      moreover have "bridges' (n,b) = IoaState state (msgs - {(b, rcpt, msg)})"
        using bridge_node_trans a_split IoaState unfolding trans_of_def apply simp
        by (simp add: bridge.valid_ins)
      ultimately show ?thesis
        using assms(12) a_split net' IoaState bridges' by presburger
    qed
  qed
qed

end

end