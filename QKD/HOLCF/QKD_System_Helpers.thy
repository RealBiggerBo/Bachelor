theory QKD_System_Helpers
  imports QKD_System_Def
begin

context QKD_Network 
begin

lemma starts_of_System [elim]:
  assumes "s \<in> starts_of System.ioa"
  obtains tn qkd net where
    "s = (tn, (qkd, net))"
    "\<forall>n \<in> nodes. \<exists>app kme bridges. 
        tn n = (app, kme, bridges) \<and>
        app = IoaState (App (isMaster (appID n)) (appOtherSae n) (kmeID n) {}) {} \<and>
        kme = IoaState (Kme (\<lambda>id. None) (route n) saeToKme) {} \<and>
        (\<forall>i \<in> bridgeIDs n. bridges i = IoaState (Bridge (isMaster i) (bridgeOtherBridge i) (bridgeOtherKme i) (qkdID i) (kmeID n)) {})"
    "qkd = QKD {} {}"
    "net = {}"
proof -
  obtain tn qkd net where split: "s = (tn, qkd, net)"
    by (metis prod_cases3)
  then have in_starts: "tn \<in> starts_of trusted_nodes.ioa \<and> qkd \<in> starts_of qkd_layer.ioa \<and> net \<in> starts_of network.ioa"
    using assms
    unfolding starts_of_par by force
  have "\<forall>n \<in> nodes. \<exists>app kme bridges.
        tn n = (app, kme, bridges) \<and>
        app = IoaState (App (isMaster (appID n)) (appOtherSae n) (kmeID n) {}) {} \<and>
        kme = IoaState (Kme (\<lambda>id. None) (route n) saeToKme) {} \<and>
        (\<forall>i \<in> bridgeIDs n. bridges i = IoaState (Bridge (isMaster i) (bridgeOtherBridge i) (bridgeOtherKme i) (qkdID i) (kmeID n)) {})"
  proof
    fix n assume "n \<in> nodes"
    have tn_starts: "tn n \<in> starts_of (trusted_node.ioa n)"
      using in_starts \<open>n \<in> nodes\<close> by fastforce
    obtain app kme bridges where split:"tn n = (app, kme, bridges)"
      using prod_cases3 by blast
    moreover have "app = IoaState (App (isMaster (appID n)) (appOtherSae n) (kmeID n) {}) {}"
      using split tn_starts 
      unfolding starts_of_par
      unfolding starts_of_def by auto
    moreover have "kme = IoaState (Kme (\<lambda>id. None) (route n) saeToKme) {}"
      using split tn_starts 
      unfolding starts_of_par
      unfolding starts_of_def by auto
    moreover have "(\<forall>i \<in> bridgeIDs n. bridges i = IoaState (Bridge (isMaster i) (bridgeOtherBridge i) (bridgeOtherKme i) (qkdID i) (kmeID n)) {})"
      using split tn_starts 
      unfolding starts_of_par starts_of_set_ioa
      unfolding starts_of_def by auto
    ultimately show "\<exists>app kme bridges.
        tn n = (app, (kme, bridges)) \<and>
        app = IoaState (App (isMaster (appID n)) (appOtherSae n) (kmeID n) {}) {} \<and>
        kme = IoaState (Kme (\<lambda>id. None) (route n) saeToKme) {} \<and>
        (\<forall>i \<in> bridgeIDs n. bridges i = IoaState (Bridge (isMaster i) (bridgeOtherBridge i) (bridgeOtherKme i) (qkdID i) (kmeID n)) {})"
      by fast
  qed
  moreover have qkd_net_def: "qkd = QKD {} {} \<and> net = {}"
    using in_starts unfolding starts_of_def by simp
  ultimately show ?thesis
    using that split in_starts by simp
qed

lemma TEST:
  assumes "\<lbrakk>P s; a = RequestKey pid; t = n\<rbrakk> \<Longrightarrow> P t"
  shows "s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t \<longrightarrow> P t"
  sorry


end

end