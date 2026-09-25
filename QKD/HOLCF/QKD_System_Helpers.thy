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

lemma test2 [consumes 2, case_names
    (* App Cases *)
    App_Master_GetKey Master_KeyResponse
]:
assumes "reachable System.ioa s"
    and "P s"
\<comment> \<open>================ APP CASES ================\<close>
    and "\<And>tn qkd net tn' pid n app_state kme_state bridges app'_state sae kme keys msgs.
         \<lbrakk>s = (tn, qkd, net); t = (tn', qkd, net); a = RequestKey pid;
          tn n = (app_state, kme_state, bridges); tn' = tn(n := (app'_state, kme_state, bridges));
          app_state = IoaState (App True sae kme keys) msgs;
          app'_state = IoaState (App True sae kme keys) (msgs \<union> {(pid, kme, GetKey kme sae)})\<rbrakk> \<Longrightarrow> P t"
    and "\<And>tn qkd net tn' pid n app_state kme_state bridges app'_state sae kme keys msgs sender keyID keyVal.
         \<lbrakk>s = (tn, qkd, net); t = (tn', qkd, net); a = Receive sender pid (KeyResponse keyID keyVal);
          tn n = (app_state, kme_state, bridges); tn' = tn(n := (app'_state, kme_state, bridges));
          app_state = IoaState (App True sae kme keys) msgs;
          app'_state = IoaState (App True sae kme (keys \<union> {(keyID, keyVal)})) (msgs \<union> {(pid, sae, AppIDRelay keyID)})\<rbrakk> \<Longrightarrow> P t"
\<comment> \<open>================ BRIDGE CASES ================\<close>
\<comment> \<open>================ KME CASES ================\<close>
\<comment> \<open>================ QKD LAYER & NETWORK ================\<close>
  shows "s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t \<longrightarrow> P t"
  sorry

lemma System_trans_cases [consumes 2, case_names 
  (* App Cases *)
  App_Master_GetKey App_Master_KeyResponse App_Slave_GetKey App_Slave_KeyResponse
  (* Bridge Cases *)
  Bridge_Tick_GetKey Bridge_Master_KeyResponse Bridge_Slave_GetKeyWithID Bridge_Slave_KeyResponse
  (* KME Cases *)
  KME_KMPost_NewKeyVal KME_KMPut_Confirm KME_GetKey KME_KMPut_Reserve KME_GetKey_Reserved 
  KME_GetKeyWithID_IDFound KME_GetKeyWithID_IDNotFound KME_GetKeyWithID_IDNotFound_Reserved 
  KME_KMGetKeyWithID_IDFound KME_KMGetKeyWithID_IDNotFound KME_KMGetKeyWithID_IDNotFound_Reserved 
  KME_KMGetKeyWithID_IDNotFound_Return KME_GetKeyWithID_IDNotFound_Return
  (* QKD & Net Cases *)
  QKD_GetKey_Gen QKD_Send
  Net_Send Net_Receive Stuttering]:
  
  assumes "reachable System.ioa s"
    and "P s"

    \<comment> \<open>================ APP CASES ================\<close>
    and "\<And>tn qkd net tn' qkd' net' pid sae kme keys.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           a = RequestKey pid; qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"
           
    and "\<And>tn qkd net tn' qkd' net' sender rcpt keyID keyVal sae kme keys.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           a = Receive sender rcpt (KeyResponse keyID keyVal); qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"
           
    and "\<And>tn qkd net tn' qkd' net' sender rcpt keyID sae kme keys.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           a = Receive sender rcpt (AppIDRelay keyID); qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"

    and "\<And>tn qkd net tn' qkd' net' sender rcpt keyID keyVal sae kme keys.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           a = Receive sender rcpt (KeyResponse keyID keyVal); qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"


    \<comment> \<open>================ BRIDGE CASES ================\<close>
    and "\<And>tn qkd net tn' qkd' net' pid bridge otherKme qkd_id kme.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           a = TimerTick pid; qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"

    and "\<And>tn qkd net tn' qkd' net' sender rcpt keyID keyVal bridge otherKme qkd_id kme.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           a = Receive sender rcpt (KeyResponse keyID keyVal); qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"

    and "\<And>tn qkd net tn' qkd' net' sender rcpt keyID bridge otherKme qkd_id kme.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           a = Receive sender rcpt (BridgeIDRelay keyID); qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"

    and "\<And>tn qkd net tn' qkd' net' sender rcpt keyID keyVal bridge otherKme qkd_id kme.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           a = Receive sender rcpt (KeyResponse keyID keyVal); qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"


    \<comment> \<open>================ KME CASES ================\<close>
    and "\<And>tn qkd net tn' qkd' net' sender rcpt otherKme keyID keyVal store route saeToKme.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           a = Receive sender rcpt (KMPost otherKme keyID keyVal); qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"

    and "\<And>tn qkd net tn' qkd' net' sender rcpt otherKme keyID store route saeToKme.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           a = Receive sender rcpt (KMPut otherKme keyID None); qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"
 (* Adapt keyID matching *)
    and "\<And>tn qkd net tn' qkd' net' sender rcpt host slaveSae store route saeToKme val.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           store (keyID_of_GetKey host slaveSae) = Some (Some val, saeToKme slaveSae, True, None);
           a = Receive sender rcpt (GetKey host slaveSae); qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"

    and "\<And>tn qkd net tn' qkd' net' sender rcpt otherKme keyID slaveSae store route saeToKme.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           a = Receive sender rcpt (KMPut otherKme keyID (Some slaveSae)); qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"

    and "\<And>tn qkd net tn' qkd' net' sender rcpt keyID saeID store route saeToKme val conf res.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           store keyID = Some (Some val, sender, conf, res);
           a = Receive sender rcpt OK; qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"

    and "\<And>tn qkd net tn' qkd' net' sender rcpt host masterSae keyID store route saeToKme val.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           store keyID = Some (Some val, saeToKme masterSae, True, Some sender);
           a = Receive sender rcpt (GetKeyWithID host masterSae keyID); qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"

    and "\<And>tn qkd net tn' qkd' net' sender rcpt host masterSae keyID store route saeToKme nextKme keyID2 val2.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           store keyID = None; route masterSae = nextKme; store keyID2 = Some (Some val2, nextKme, True, None);
           a = Receive sender rcpt (GetKeyWithID host masterSae keyID); qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"

    and "\<And>tn qkd net tn' qkd' net' nextKme rcpt masterSae slaveSae keyID keyID2 store route saeToKme.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           a = Receive nextKme rcpt OK; qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"

    and "\<And>tn qkd net tn' qkd' net' sender rcpt masterSae keyID keyID2 slaveSae store route saeToKme val val2.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           store keyID = Some (Some val, saeToKme masterSae, True, Some sender);
           store keyID2 = Some (Some val2, sender, True, Some sender);
           a = Receive sender rcpt (KMGet masterSae keyID keyID2 slaveSae); qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"

    and "\<And>tn qkd net tn' qkd' net' sender rcpt masterSae keyID keyID2 slaveSae store route saeToKme nextKme keyID3 val2 val3.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           store keyID = None; store keyID2 = Some (Some val2, sender, True, Some sender);
           route masterSae = nextKme; store keyID3 = Some (Some val3, nextKme, True, None);
           a = Receive sender rcpt (KMGet masterSae keyID keyID2 slaveSae); qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"

    and "\<And>tn qkd net tn' qkd' net' nextKme rcpt keyID3 masterSae sender keyID keyID2 store route saeToKme.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           a = Receive nextKme rcpt OK; qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"

    and "\<And>tn qkd net tn' qkd' net' nextKme rcpt keyID' keyVal' keyID3 masterSae sender keyID keyID2 store route saeToKme val2 val3.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           store keyID2 = Some (Some val2, sender, True, Some sender); store keyID3 = Some (Some val3, nextKme, True, None);
           a = Receive nextKme rcpt (KeyResponse keyID' keyVal'); qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"

    and "\<And>tn qkd net tn' qkd' net' nextKme rcpt keyID' keyVal' masterSae sender keyID keyID2 store route saeToKme keyID3 val3.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           store keyID3 = Some (Some val3, nextKme, True, None);
           a = Receive nextKme rcpt (KeyResponse keyID' keyVal'); qkd' = qkd; net' = net \<rbrakk> \<Longrightarrow> P t"


    \<comment> \<open>================ QKD LAYER & NETWORK ================\<close>
    and "\<And>tn qkd net tn' qkd' net' sender rcpt target keyID qkdIDs gen sent.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           rcpt \<in> qkdIDs; keyID \<notin> fst ` ((snd ` gen) \<union> sent);
           a = Receive sender rcpt (GetKey rcpt target); tn' = tn; net' = net \<rbrakk> \<Longrightarrow> P t"

    and "\<And>tn qkd net tn' qkd' net' sender rcpt keyID keyVal qkdIDs gen sent.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           sender \<in> qkdIDs; (rcpt, keyID, keyVal) \<in> gen;
           a = Send sender rcpt (KeyResponse keyID keyVal); tn' = tn; net' = net \<rbrakk> \<Longrightarrow> P t"

    and "\<And>tn qkd net tn' qkd' net' pid_a pid_b m.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           a = Send pid_a pid_b m; tn' = tn; qkd' = qkd \<rbrakk> \<Longrightarrow> P t"

    and "\<And>tn qkd net tn' qkd' net' pid_a pid_b m.
         \<lbrakk> s = (tn, qkd, net); t = (tn', qkd', net');
           a = Receive pid_a pid_b m; tn' = tn; qkd' = qkd \<rbrakk> \<Longrightarrow> P t"

    \<comment> \<open>================ STUTTERING ================\<close>
    and "\<And>tn qkd net.
         \<lbrakk> s = (tn, qkd, net); t = (tn, qkd, net) \<rbrakk> \<Longrightarrow> P t"

  shows "s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t \<longrightarrow> P t"
  sorry


end

end