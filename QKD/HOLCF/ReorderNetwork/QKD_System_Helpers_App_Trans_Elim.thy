theory QKD_System_Helpers_App_Trans_Elim
  imports QKD_System_Helpers_Trans_Elim QKD_System_ActsDisj
begin

context QKD_Network
begin

lemma apps_trans_elim [elim]:
  assumes "apps \<midarrow>a\<midarrow>apps.ioa\<rightarrow> apps'"
  shows "(a \<in> act (app.ioa n) \<and> n \<in> nodes \<longrightarrow> apps n \<midarrow>a\<midarrow>app.ioa n\<rightarrow> apps' n) \<and> 
         (a \<notin> act (app.ioa n) \<or> n \<notin> nodes \<longrightarrow> apps n = apps' n)"
  using set_ioa_trans_elim[OF assms] by blast

lemma app_invariant_step[consumes 6, case_names 
    Master_RequestKey
    Master_KeyResponse
    Slave_AppIDRelay
    Slave_KeyResponse
    Send]:
  assumes "reachable System.ioa s"
    and "P s"
    and "n \<in> nodes"
    and "a \<in> act (app.ioa n)"
    and "s = (apps, kmes, bridges, qkd, net)"
    and "t = (apps', kmes, bridges, qkd, net')"
    and "\<And>sae kme keys msgs.
         \<lbrakk>a = RequestKey (appID n); net = net';
          apps n = IoaState (App True sae kme keys) msgs;
          apps' = apps(n := IoaState (App True sae kme keys) (msgs \<union> {(appID n, kme, GetKey kme sae)}))\<rbrakk> \<Longrightarrow> P t"
    (*change sender to kme*)
    and "\<And>sae kme keys msgs keyID keyVal.
         \<lbrakk>a = Receive kme (appID n) (KeyResponse keyID keyVal); net = net';
          (kme, appID n, KeyResponse keyID keyVal) \<in> net;
          apps n = IoaState (App True sae kme keys) msgs;
          apps' = apps(n := IoaState (App True sae kme (keys \<union> {(keyID, keyVal)})) (msgs \<union> {(appID n, sae, AppIDRelay keyID)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>sae kme keys msgs sender keyID.
         \<lbrakk>a = Receive sender (appID n) (AppIDRelay keyID); net = net';
          (sender, appID n, AppIDRelay keyID) \<in> net;
          apps n = IoaState (App False sae kme keys) msgs;
          apps' = apps(n := IoaState (App False sae kme keys) (msgs \<union> {(appID n, kme, GetKeyWithID kme sae keyID)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>sae kme keys msgs keyID keyVal.
         \<lbrakk>a = Receive kme (appID n) (KeyResponse keyID keyVal); net = net';
          (kme, appID n, KeyResponse keyID keyVal) \<in> net;
          apps n = IoaState (App False sae kme keys) msgs;
          apps' = apps(n := IoaState (App False sae kme (keys \<union> {(keyID, keyVal)})) msgs)\<rbrakk> \<Longrightarrow> P t"
    and "\<And>msgs rcpt msg appState.
         \<lbrakk>a = Send (appID n) rcpt msg; net' = net \<union> {(appID n, rcpt, msg)};
          (appID n, rcpt, msg) \<in> msgs;
          apps n = IoaState appState msgs;
          apps' = apps(n := IoaState appState (msgs - {(appID n, rcpt, msg)}))\<rbrakk> \<Longrightarrow> P t"
  shows "s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t \<longrightarrow> P t"
proof
  assume sat_trans:"s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t"
  note sys_trans = System_trans_elim[OF sat_trans assms(5,6)]
  have apps_trans:"apps \<midarrow>a\<midarrow>apps.ioa\<rightarrow> apps'"
    using sys_trans assms(3,4) unfolding actions_of_set_ioa by blast
  then have app_node_trans: "apps n \<midarrow>a\<midarrow>app.ioa n\<rightarrow> apps' n"
    using assms(3,4) apps_trans_elim by blast
  moreover have other_apps_eq: "\<And>n'. \<lbrakk>n' \<in> nodes; n' \<noteq> n\<rbrakk> \<Longrightarrow> apps n' = apps' n'"
    using apps_trans_elim[OF apps_trans] actsDisj_app_app assms(3,4) by blast
  moreover have "\<And>n'. \<lbrakk>n' \<notin> nodes\<rbrakk> \<Longrightarrow> apps n' = apps' n'"
    using apps_trans unfolding trans_of_set_ioa by simp
  ultimately have apps': "apps' = apps (n := apps' n)"
    by fastforce
  consider "a = RequestKey (appID n)" | "\<exists>sender msg. a = Receive sender (appID n) msg" | "\<exists>rcpt msg. a = Send (appID n) rcpt msg"
    using assms(4) unfolding actions_def asig_projections asig_of_def apply auto
    by (metis insert_iff empty_iff)
  then show "P t"
  proof cases
    case 1
    then have "a \<notin> act network.ioa"
      unfolding actions_def asig_projections asig_of_def by force
    then have net_eq:"net = net'"
      using sys_trans by fast
    then show ?thesis
    proof (cases "apps n")
      case (IoaState state msgs)
      then show ?thesis
      proof (cases state)
        case (App isMaster sae kme keys)
        then show ?thesis
        proof (cases isMaster)
          case True
          then have "apps' n = IoaState (App True sae kme keys) (msgs \<union> {(appID n, kme, GetKey kme sae)})"
            using 1 assms(4) app_node_trans IoaState App unfolding trans_of_def actions_def apply simp 
            unfolding asig_projections asig_of_def apply auto
            using app_step.cases apply blast+
            by (meson Master_GetKey)
          then show "P t"
            using IoaState App apps' True assms(7)[OF 1 net_eq] by simp
        next
          case False
          then have "apps' n = apps n"
            using 1 assms(4) app_node_trans IoaState App unfolding trans_of_def actions_def apply simp 
            unfolding asig_projections asig_of_def apply auto
            using app_step.cases by blast+
          then show ?thesis
            using apps' assms(2,5,6) net_eq by simp
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
    obtain sender msg where a_split:"a = Receive sender (appID n) msg"
      using 2 by blast
    then have rec_in_net: "(sender, appID n, msg) \<in> net"
      using net_trans unfolding trans_of_def by simp
    show ?thesis
    proof (cases "apps n")
      case (IoaState state msgs)
      show ?thesis
      proof (cases state)
        case (App isMaster sae kme keys)
        show ?thesis
        proof (cases isMaster)
          case True
          show "P t"
          proof (cases "\<exists>keyID keyVal. msg = KeyResponse keyID keyVal")
            case True
            then obtain keyID keyVal where msg_split:"msg = KeyResponse keyID keyVal"
              by blast
            then show ?thesis
            proof(cases "sender = kme")
              case True
              then have "apps' n = IoaState (App True sae kme (keys \<union> {(keyID, keyVal)})) (msgs \<union> {(appID n, sae, AppIDRelay keyID)})"
                using a_split assms(4) app_node_trans IoaState App \<open>isMaster\<close> msg_split unfolding trans_of_def apply simp
                unfolding actions_def asig_projections asig_of_def apply simp
                using app_step.cases apply auto
                     apply fast
                    apply blast+
                using QKD_App.Master_KeyResponse apply meson
                using QKD_App.Master_KeyResponse by meson
              then show ?thesis
                using IoaState App \<open>isMaster\<close> net_eq assms(8) a_split msg_split rec_in_net apps' True by force
            next
              case False
              then have "apps' n = apps n"
                using a_split assms(4) app_node_trans IoaState App \<open>isMaster\<close> unfolding trans_of_def apply simp
                unfolding actions_def asig_projections asig_of_def 
                by (simp add: app_step.simps)
              then show ?thesis
                using apps' assms(2,5,6) net_eq by fastforce
            qed
          next
            case False
            then have "apps' n = apps n"
              using a_split assms(4) app_node_trans IoaState App \<open>isMaster\<close> unfolding trans_of_def apply simp
              unfolding actions_def asig_projections asig_of_def 
              by (simp add: app_step.simps)
            then show ?thesis
              using apps' assms(2,5,6) net_eq by fastforce
          qed
        next
          case False
          show "P t"
          proof (cases "\<exists>keyID keyVal. msg = KeyResponse keyID keyVal")
            case True
            then obtain keyID keyVal where msg_split:"msg = KeyResponse keyID keyVal"
              by blast
            then show ?thesis
            proof(cases "sender = kme")
              case True
              then have "apps' n = IoaState (App False sae kme (keys \<union> {(keyID, keyVal)})) msgs"
                using a_split assms(4) app_node_trans IoaState App \<open>\<not>isMaster\<close> msg_split unfolding trans_of_def apply simp
                unfolding actions_def asig_projections asig_of_def apply simp
                using app_step.cases apply auto
                  apply fast
                apply blast
                using QKD_App.Slave_KeyResponse by meson
              then show ?thesis
                using IoaState App \<open>\<not>isMaster\<close> net_eq assms(10) a_split msg_split rec_in_net apps' True by force
            next
              case False
              then have "apps' n = apps n"
                using a_split assms(4) app_node_trans IoaState App msg_split \<open>\<not>isMaster\<close>
                unfolding trans_of_def actions_def asig_projections asig_of_def
                by (simp add: app_step.simps)
              then show ?thesis
                using apps' assms(2,5,6) net_eq by fastforce
            qed
          next
            case False
            then show ?thesis 
            proof (cases "\<exists>keyID. msg = AppIDRelay keyID")
              case True
              then obtain keyID where msg_split:"msg = AppIDRelay keyID"
                by blast
              then have "apps' n = IoaState (App False sae kme keys) (msgs \<union> {(appID n, kme, GetKeyWithID kme sae keyID)})"
                using a_split assms(4) app_node_trans IoaState App \<open>\<not>isMaster\<close> unfolding trans_of_def apply simp
                unfolding actions_def asig_projections asig_of_def apply simp
                using app_step.cases apply auto
                    apply fast
                   apply blast+
                using Slave_GetKey by fast
              then show ?thesis
                using IoaState App \<open>\<not>isMaster\<close> net_eq assms(9) a_split msg_split rec_in_net apps' by presburger
            next
              case False
              then have "apps' n = apps n"
                using a_split assms(4) app_node_trans IoaState App \<open>\<not>isMaster\<close> \<open>\<nexists>keyID keyVal. msg = KeyResponse keyID keyVal\<close> 
                unfolding trans_of_def actions_def asig_projections asig_of_def
                by (simp add: app_step.simps)
              then show ?thesis
                using apps' assms(2,5,6) net_eq by fastforce
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
    obtain rcpt msg where a_split:"a = Send (appID n) rcpt msg"
      using 3 by blast
    then have net':"net' = net \<union> {(appID n, rcpt, msg)}"
      using net_trans unfolding trans_of_def by auto
    then show ?thesis
    proof (cases "apps n")
      case (IoaState state msgs)
      then have "(appID n, rcpt, msg) \<in> msgs"
        using app_node_trans a_split unfolding trans_of_def apply simp
        by (meson app.valid_ins)
      moreover have "apps' n = IoaState state (msgs - {(appID n, rcpt, msg)})"
        using calculation app_node_trans a_split IoaState unfolding trans_of_def apply simp
        by (simp add: app.valid_ins)
      ultimately show ?thesis
        using assms(11) a_split net' IoaState apps' by presburger
    qed
  qed
qed
end

end