theory QKD_System_Helpers
  imports QKD_System_Helpers_App_Trans_Elim
begin

context QKD_Network 
begin

lemma starts_of_System [elim]:
  assumes "s \<in> starts_of System.ioa"
  obtains apps kmes bridges qkd net where
    "s = (apps, kmes, bridges, qkd, net)"
    "\<And>n. n \<in> nodes \<Longrightarrow> apps n = IoaState (App (isMaster (appID n)) (appOtherSae n) (kmeID n) {}) {}"
    "\<And>n. n \<in> nodes \<Longrightarrow> kmes n = IoaState (Kme (\<lambda>id. None) (route n) saeToKme) {}"
    "\<And>n i. (n, i) \<in> Sigma nodes bridgeIDs \<Longrightarrow> bridges (n,i) = IoaState (Bridge (isMaster i) (bridgeOtherBridge i) (bridgeOtherKme i) (qkdID i) (kmeID n)) {}"
    "qkd = QKD {} {}"
    "net = {}"
proof -
  obtain apps kmes bridges qkd net where split:"s = (apps, kmes, bridges, qkd, net)"
    using prod_cases5 by blast
  have "apps \<in> starts_of apps.ioa"
    using assms split unfolding starts_of_par by fastforce
  then have "\<And>n. n \<in> nodes \<Longrightarrow> apps n = IoaState (App (isMaster (appID n)) (appOtherSae n) (kmeID n) {}) {}"
    unfolding starts_of_set_ioa
    unfolding starts_of_def by simp
  moreover have "kmes \<in> starts_of kmes.ioa"
    using assms split unfolding starts_of_par by fastforce
  then have "\<And>n. n \<in> nodes \<Longrightarrow> kmes n = IoaState (Kme (\<lambda>id. None) (route n) saeToKme) {}"
    unfolding starts_of_set_ioa
    unfolding starts_of_def by simp
  moreover have "bridges \<in> starts_of bridges.ioa"
    using assms split unfolding starts_of_par by fastforce
  then have "\<And>n i. (n, i) \<in> Sigma nodes bridgeIDs \<Longrightarrow> bridges (n,i) = IoaState (Bridge (isMaster i) (bridgeOtherBridge i) (bridgeOtherKme i) (qkdID i) (kmeID n)) {}"
    unfolding starts_of_set_ioa
    unfolding starts_of_def by simp
  moreover have "qkd \<in> starts_of qkd_layer.ioa"
    using assms split unfolding starts_of_par by fastforce
  then have "qkd = QKD {} {}"
    unfolding starts_of_set_ioa
    unfolding starts_of_def by simp
  moreover have "net \<in> starts_of network.ioa"
    using assms split unfolding starts_of_par by fastforce
  then have "net = {}"
    unfolding starts_of_set_ioa
    unfolding starts_of_def by simp
  ultimately show "(\<And>apps kmes bridges qkd net.
        s = (apps, kmes, bridges, qkd, net) \<Longrightarrow>
        (\<And>n. n \<in> nodes \<Longrightarrow> apps n = IoaState (App (isMaster (appID n)) (appOtherSae n) (kmeID n) {}) {}) \<Longrightarrow>
        (\<And>n. n \<in> nodes \<Longrightarrow> kmes n = IoaState (Kme (\<lambda>id. None) (route n) saeToKme) {}) \<Longrightarrow>
        (\<And>n i. (n, i) \<in> Sigma nodes bridgeIDs \<Longrightarrow>
                bridges (n, i) =
                IoaState (Bridge (isMaster i) (bridgeOtherBridge i) (bridgeOtherKme i) (qkdID i) (kmeID n)) {}) \<Longrightarrow>
        qkd = QKD {} {} \<Longrightarrow> net = {} \<Longrightarrow> thesis) \<Longrightarrow>
    thesis"
    sorry
qed

lemma test2 [consumes 2, case_names
    (* App Cases *)
    App_Master_GetKey App_Master_KeyResponse App_Slave_GetKey App_Slave_KeyResponse App_Send
]:
assumes "reachable System.ioa s"
    and "P s"
\<comment> \<open>================ APP CASES ================\<close>
    and "\<And>apps kmes bridges qkd net apps' pid n sae kme keys msgs.
         \<lbrakk>s = (apps, kmes, bridges, qkd, net); t = (apps', kmes, bridges, qkd, net); a = RequestKey pid;
          apps n = IoaState (App True sae kme keys) msgs;
          apps' = apps(n := IoaState (App True sae kme keys) (msgs \<union> {(pid, kme, GetKey kme sae)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net apps' pid n sae kme keys msgs sender keyID keyVal.
         \<lbrakk>s = (apps, kmes, bridges, qkd, net); t = (apps', kmes, bridges, qkd, net); a = Receive sender pid (KeyResponse keyID keyVal);
          (sender, pid, KeyResponse keyID keyVal) \<in> net;
          apps n = IoaState (App True sae kme keys) msgs;
          apps' = apps(n := IoaState (App True sae kme (keys \<union> {(keyID, keyVal)})) (msgs \<union> {(pid, sae, AppIDRelay keyID)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net apps' pid n sae kme keys msgs sender keyID.
         \<lbrakk>s = (apps, kmes, bridges, qkd, net); t = (apps', kmes, bridges, qkd, net); a = Receive sender pid (AppIDRelay keyID);
          (sender, pid, AppIDRelay keyID) \<in> net;
          apps n = IoaState (App False sae kme keys) msgs;
          apps' = apps(n := IoaState (App False sae kme keys) (msgs \<union> {(pid, kme, GetKeyWithID kme sae keyID)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net apps' pid n sae kme keys msgs sender keyID keyVal.
         \<lbrakk>s = (apps, kmes, bridges, qkd, net); t = (apps', kmes, bridges, qkd, net); a = Receive sender pid (KeyResponse keyID keyVal);
          (sender, pid, KeyResponse keyID keyVal) \<in> net;
          apps n = IoaState (App False sae kme keys) msgs;
          apps' = apps(n := IoaState (App False sae kme (keys \<union> {(keyID, keyVal)})) msgs)\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net apps' net' pid n msgs rcpt msg appState.
         \<lbrakk>s = (apps, kmes, bridges, qkd, net); t = (apps', kmes, bridges, qkd, net'); a = Send pid rcpt msg;
          (pid, rcpt, msg) \<in> msgs;
          apps n = IoaState appState msgs;
          apps' = apps(n := IoaState appState (msgs - {(pid, rcpt, msg)}));
          net' = net \<union> {(pid, rcpt, msg)}\<rbrakk> \<Longrightarrow> P t"
\<comment> \<open>================ KME CASES ================\<close>
\<comment> \<open>================ BRIDGE CASES ================\<close>
\<comment> \<open>================ QKD LAYER & NETWORK ================\<close>
  shows "s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t \<longrightarrow> P t"
  sorry

end

end