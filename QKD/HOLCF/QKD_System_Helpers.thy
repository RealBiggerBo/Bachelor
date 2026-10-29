theory QKD_System_Helpers
  imports QKD_System_Helpers_App_Trans_Elim
          QKD_System_Helpers_Kme_Trans_Elim
          QKD_System_Helpers_Bridge_Trans_Elim
          QKD_System_Helpers_QKD_Trans_Elim
          QKD_System_Helpers_Network_Trans_Elim
begin

context QKD_Network
begin

lemma starts_of_System [elim]:
  assumes "s \<in> starts_of System.ioa"
  obtains apps kmes bridges qkd net where
    "s = (apps, kmes, bridges, qkd, net)"
    "\<And>n. n \<in> nodes \<Longrightarrow> apps n = IoaState (App (isMaster (appID n)) (appOtherSae n) (kmeID n) {}) {}"
    "\<And>n. n \<in> nodes \<Longrightarrow> kmes n = IoaState (Kme (\<lambda>id. None) (route n) saeToKme (bridgeIDs n)) {}"
    "\<And>n i. (n, i) \<in> Sigma nodes bridgeIDs \<Longrightarrow> bridges (n,i) = IoaState (Bridge (isMaster i) (bridgeOtherBridge i) (bridgeOtherKme i) (qkdID i) (kmeID n)) {}"
    "qkd = QKD {} {}"
    "net = (\<lambda>set. [])"
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
  then have "\<And>n. n \<in> nodes \<Longrightarrow> kmes n = IoaState (Kme (\<lambda>id. None) (route n) saeToKme (bridgeIDs n)) {}"
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
  then have "net = (\<lambda>set. [])"
    unfolding starts_of_set_ioa
    unfolding starts_of_def by simp
  ultimately show "thesis"
    by (rule that[OF split])
qed

lemma System_step_induct[consumes 2, case_names
    (* App cases *)
    App_Master_RequestKey
    App_Master_KeyResponse
    App_Slave_AppIDRelay
    App_Slave_KeyResponse
    App_ReceiveStutter
    App_Send
    (* Kme cases*)
    Kme_KMPost_NewKeyVal
    Kme_KMPut_Confirm
    Kme_GetKey
    Kme_KMPut_Reserve
    Kme_GetKey_Reserved
    Kme_GetKeyWithID_IDFound
    Kme_GetKeyWithID_IDNotFound
    Kme_GetKeyWithID_IDNotFound_Reserved
    Kme_KMGetKeyWithID_IDFound
    Kme_KMGetKeyWithID_IDNotFound
    Kme_KMGetKeyWithID_IDNotFound_Reserved
    Kme_KMGetKeyWithID_IDNotFound_Return
    Kme_GetKeyWithID_IDNotFound_Return
    Kme_ReceiveStutter
    Kme_Send
    (* Bridge cases*)
    Bridge_Tick_GetKey
    Bridge_Master_KeyResponse
    Bridge_Slave_GetKeyWithID
    Bridge_Slave_KeyResponse
    Bridge_ReceiveStutter
    Bridge_Send
    (* Qkd cases*)
    Qkd_GetKey_Gen
    Qkd_GetKeyWithID_Reserve
    Qkd_ReceiveStutter
    Qkd_Send
    (* Net cases*)
    Network_Ext_Receive
    Network_Ext_Send
]:
assumes "reachable System.ioa s"
    and "P s"
\<comment> \<open>================ APP CASES ================\<close>
    and "\<And>apps kmes bridges qkd net apps' net' n sae kme keys msgs.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps', kmes, bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (app.ioa n);
          a = RequestKey (appID n); net' = net;
          apps n = IoaState (App True sae kme keys) msgs;
          apps' = apps(n := IoaState (App True sae kme keys) (msgs \<union> {(appID n, kme, GetKey kme sae)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net apps' net' n sae kme keys msgs keyID keyVal.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps', kmes, bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (app.ioa n);
          a = Receive kme (appID n) (KeyResponse keyID keyVal);
          net' = rmv_msg net kme (appID n) (KeyResponse keyID keyVal);
          can_send net kme (appID n) (KeyResponse keyID keyVal);
          apps n = IoaState (App True sae kme keys) msgs;
          apps' = apps(n := IoaState (App True sae kme (keys \<union> {(keyID, keyVal)})) (msgs \<union> {(appID n, sae, AppIDRelay keyID)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net apps' net' n sae kme keys msgs sender keyID.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps', kmes, bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (app.ioa n);
          a = Receive sender (appID n) (AppIDRelay keyID);
          net' = rmv_msg net sender (appID n) (AppIDRelay keyID);
          can_send net sender (appID n) (AppIDRelay keyID);
          apps n = IoaState (App False sae kme keys) msgs;
          apps' = apps(n := IoaState (App False sae kme keys) (msgs \<union> {(appID n, kme, GetKeyWithID kme sae keyID)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net apps' net' n sae kme keys msgs keyID keyVal.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps', kmes, bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (app.ioa n);
          a = Receive kme (appID n) (KeyResponse keyID keyVal);
          net' = rmv_msg net kme (appID n) (KeyResponse keyID keyVal);
          can_send net kme (appID n) (KeyResponse keyID keyVal);
          apps n = IoaState (App False sae kme keys) msgs;
          apps' = apps(n := IoaState (App False sae kme (keys \<union> {(keyID, keyVal)})) msgs)\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net net' n sender msg.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes, bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (app.ioa n);
          a = Receive sender (appID n) msg;
          net' = rmv_msg net sender (appID n) msg;
          can_send net sender (appID n) msg\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net apps' net' n msgs rcpt msg appState.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps', kmes, bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (app.ioa n);
          a = Send (appID n) rcpt msg; net' = add_msg net (appID n) rcpt msg;
          (appID n, rcpt, msg) \<in> msgs;
          apps n = IoaState appState msgs;
          apps' = apps(n := IoaState appState (msgs - {(appID n, rcpt, msg)}))\<rbrakk> \<Longrightarrow> P t"
\<comment> \<open>================ KME CASES ================\<close>
    and "\<And>apps kmes bridges qkd net kmes' net' n sender otherKme keyID keyVal store route saeToKme bridgeIDs msgs.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes', bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (kme.ioa n);
          a = Receive sender (kmeID n) (KMPost otherKme keyID keyVal);
          net' = rmv_msg net sender (kmeID n) (KMPost otherKme keyID keyVal);
          can_send net sender (kmeID n) (KMPost otherKme keyID keyVal);
          sender \<in> bridgeIDs;
          kmes n = IoaState (Kme store route saeToKme bridgeIDs) msgs;
          kmes' = kmes(n := IoaState (Kme (keyStore_add store keyID (Some keyVal) otherKme) route saeToKme bridgeIDs) 
          (msgs \<union> {(kmeID n, sender, OK), (kmeID n, otherKme, KMPut (kmeID n) keyID None)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net kmes' net' n sender otherKme keyID store route saeToKme bridgeIDs msgs.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes', bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (kme.ioa n);
          a = Receive sender (kmeID n) (KMPut otherKme keyID None);
          net' = rmv_msg net sender (kmeID n) (KMPut otherKme keyID None);
          can_send net sender (kmeID n) (KMPut otherKme keyID None);
          kmes n = IoaState (Kme store route saeToKme bridgeIDs) msgs;
          kmes' = kmes(n := IoaState (Kme (keyStore_confirm store keyID otherKme) route saeToKme bridgeIDs)
          (msgs \<union> {(kmeID n, sender, OK)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net kmes' net' n sender host slaveSae store route saeToKme bridgeIDs msgs keyID val.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes', bridges, qkd, net');
          n \<in> nodes; a \<in> act (kme.ioa n);
          a = Receive sender (kmeID n) (GetKey host slaveSae);
          net' = rmv_msg net sender (kmeID n) (GetKey host slaveSae);
          can_send net sender (kmeID n) (GetKey host slaveSae);
          store keyID = Some (Some val, route slaveSae, True, None);
          kmes n = IoaState (Kme store route saeToKme bridgeIDs) msgs;
          kmes' = kmes(n := IoaState (KmeWaitReserve keyID sender store route saeToKme bridgeIDs)
          (msgs \<union> {(kmeID n, route slaveSae, KMPut (kmeID n) keyID (Some slaveSae))}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net kmes' net' n sender otherKme slaveSae store route saeToKme bridgeIDs msgs keyID.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes', bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (kme.ioa n);
          a = Receive sender (kmeID n) (KMPut otherKme keyID (Some slaveSae));
          net' = rmv_msg net sender (kmeID n) (KMPut otherKme keyID (Some slaveSae));
          can_send net sender (kmeID n) (KMPut otherKme keyID (Some slaveSae));
          kmes n = IoaState (Kme store route saeToKme bridgeIDs) msgs;
          kmes' = kmes(n := IoaState (Kme (keyStore_reserve store keyID slaveSae) route saeToKme bridgeIDs)
          (msgs \<union> {(kmeID n, otherKme, OK)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net kmes' net' n sender store keyID val conf res saeID route saeToKme bridgeIDs msgs.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes', bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (kme.ioa n);
          a = Receive sender (kmeID n) OK;
          net' = rmv_msg net sender (kmeID n) OK;
          can_send net sender (kmeID n) OK;
          store keyID = Some (Some val, sender, conf, res);
          kmes n = IoaState (KmeWaitReserve keyID saeID store route saeToKme bridgeIDs) msgs;
          kmes' = kmes(n := IoaState (Kme (keyStore_remove store keyID) route saeToKme bridgeIDs)
          (msgs \<union> {(kmeID n, saeID, KeyResponse keyID val)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net kmes' net' n sender host store keyID val saeToKme bridgeIDs masterSae route msgs.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes', bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (kme.ioa n);
          a = Receive sender (kmeID n) (GetKeyWithID host masterSae keyID);
          net' = rmv_msg net sender (kmeID n) (GetKeyWithID host masterSae keyID);
          can_send net sender (kmeID n) (GetKeyWithID host masterSae keyID);
          store keyID = Some (Some val, saeToKme masterSae, True, Some sender);
          kmes n = IoaState (Kme store route saeToKme bridgeIDs) msgs;
          kmes' = kmes(n := IoaState (Kme (keyStore_remove store keyID) route saeToKme bridgeIDs)
          (msgs \<union> {(kmeID n, sender, KeyResponse keyID val)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net kmes' net' n sender host masterSae keyID store route nextKme keyID2 val2 saeToKme bridgeIDs msgs.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes', bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (kme.ioa n);
          a = Receive sender (kmeID n) (GetKeyWithID host masterSae keyID);
          net' = rmv_msg net sender (kmeID n) (GetKeyWithID host masterSae keyID);
          can_send net sender (kmeID n) (GetKeyWithID host masterSae keyID);
          store keyID = None;
          route masterSae = nextKme;
          store keyID2 = Some (Some val2, nextKme, True, None);
          kmes n = IoaState (Kme store route saeToKme bridgeIDs) msgs;
          kmes' = kmes(n := IoaState (KmeWaitHop masterSae sender nextKme keyID keyID2 store route saeToKme bridgeIDs)
          (msgs \<union> {(kmeID n, nextKme, KMPut (kmeID n) keyID2 (Some (kmeID n)))}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net kmes' net' n nextKme masterSae slaveSae keyID keyID2 store route saeToKme bridgeIDs msgs.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes', bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (kme.ioa n);
          a = Receive nextKme (kmeID n) OK;
          net' = rmv_msg net nextKme (kmeID n) OK;
          can_send net nextKme (kmeID n) OK;
          kmes n = IoaState (KmeWaitHop masterSae slaveSae nextKme keyID keyID2 store route saeToKme bridgeIDs) msgs;
          kmes' = kmes(n := IoaState (KmeWaitHop masterSae slaveSae nextKme keyID keyID2 store route saeToKme bridgeIDs)
          (msgs \<union> {(kmeID n, nextKme, KMGet masterSae keyID keyID2 slaveSae)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net kmes' net' n nextKme masterSae keyID keyID2 slaveSae store route saeToKme bridgeIDs msgs sender val val2.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes', bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (kme.ioa n);
          a = Receive nextKme (kmeID n) (KMGet masterSae keyID keyID2 slaveSae);
          net' = rmv_msg net nextKme (kmeID n) (KMGet masterSae keyID keyID2 slaveSae);
          can_send net nextKme (kmeID n) (KMGet masterSae keyID keyID2 slaveSae);
          store keyID = Some (Some val, saeToKme masterSae, True, Some slaveSae);
          store keyID2 = Some (Some val2, sender, True, Some sender);
          kmes n = IoaState (Kme store route saeToKme bridgeIDs) msgs;
          kmes' = kmes(n := IoaState (Kme (keyStore_remove (keyStore_remove store keyID) keyID2) route saeToKme bridgeIDs)
          (msgs \<union> {(kmeID n, sender, KMKeyResponse keyID2 keyID (enc val val2))}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net kmes' net' n nextKme masterSae keyID keyID2 slaveSae store val2 sender route keyID3 val3 saeToKme bridgeIDs msgs.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes', bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (kme.ioa n);
          a = Receive sender (kmeID n) (KMGet masterSae keyID keyID2 slaveSae);
          net' = rmv_msg net sender (kmeID n) (KMGet masterSae keyID keyID2 slaveSae);
          can_send net sender (kmeID n) (KMGet masterSae keyID keyID2 slaveSae);
          store keyID = None;
          store keyID2 = Some (Some val2, sender, True, Some sender);
          route masterSae = nextKme;
          store keyID3 = Some (Some val3, nextKme, True, None);
          kmes n = IoaState (Kme store route saeToKme bridgeIDs) msgs;
          kmes' = kmes(n := IoaState (KmeWaitHopRec keyID3 masterSae slaveSae sender nextKme keyID keyID2 store route saeToKme bridgeIDs)
          (msgs \<union> {(kmeID n, nextKme, KMPut (kmeID n) keyID3 (Some (kmeID n)))}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net kmes' net' n nextKme prevKme masterSae keyID keyID2 slaveSae store route keyID3 saeToKme bridgeIDs msgs.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes', bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (kme.ioa n);
          a = Receive nextKme (kmeID n) OK;
          net' = rmv_msg net nextKme (kmeID n) OK;
          can_send net nextKme (kmeID n) OK;
          kmes n = IoaState (KmeWaitHopRec keyID3 masterSae slaveSae prevKme nextKme keyID keyID2 store route saeToKme bridgeIDs) msgs;
          kmes' = kmes(n := IoaState (KmeWaitHopRec keyID3 masterSae slaveSae prevKme nextKme keyID keyID2 store route saeToKme bridgeIDs)
          (msgs \<union> {(kmeID n, nextKme, KMGet masterSae keyID keyID3 slaveSae)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net kmes' net' n nextKme prevKme keyID keyVal' store keyID2 val2 sender keyID3 val3 masterSae route saeToKme bridgeIDs msgs slaveSae.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes', bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (kme.ioa n);
          a = Receive nextKme (kmeID n) (KMKeyResponse keyID3 keyID keyVal');
          net' = rmv_msg net nextKme (kmeID n) (KMKeyResponse keyID3 keyID keyVal');
          can_send net nextKme (kmeID n) (KMKeyResponse keyID3 keyID keyVal');
          store keyID2 = Some (Some val2, sender, True, Some sender);
          store keyID3 = Some (Some val3, nextKme, True, None);
          kmes n = IoaState (KmeWaitHopRec keyID3 masterSae slaveSae prevKme nextKme keyID keyID2 store route saeToKme bridgeIDs) msgs;
          kmes' = kmes(n := IoaState (Kme (keyStore_remove (keyStore_remove store keyID2) keyID3) route saeToKme bridgeIDs)
          (msgs \<union> {(kmeID n, prevKme, KMKeyResponse keyID2 keyID (enc (dec keyVal' val3) val2))}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net kmes' net' n nextKme keyID keyVal' store keyID2 val2 masterSae sender route saeToKme bridgeIDs msgs.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes', bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (kme.ioa n);
          a = Receive nextKme (kmeID n) (KMKeyResponse keyID2 keyID keyVal');
          net' = rmv_msg net nextKme (kmeID n) (KMKeyResponse keyID2 keyID keyVal');
          can_send net nextKme (kmeID n) (KMKeyResponse keyID2 keyID keyVal');
          store keyID2 = Some (Some val2, nextKme, True, None);
          kmes n = IoaState (KmeWaitHop masterSae sender nextKme keyID keyID2 store route saeToKme bridgeIDs) msgs;
          kmes' = kmes(n := IoaState (Kme (keyStore_remove store keyID2) route saeToKme bridgeIDs)
          (msgs \<union> {(kmeID n, sender, KeyResponse keyID (dec keyVal' val2))}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net net' n sender msg.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes, bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (kme.ioa n);
          a = Receive sender (kmeID n) msg;
          net' = rmv_msg net sender (kmeID n) msg;
          can_send net sender (kmeID n) msg\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes', bridges, qkd, net'); 
          n \<in> nodes; a \<in> act (kme.ioa n);
          a = Send (kmeID n) rcpt msg; net' = add_msg net (kmeID n) rcpt msg;
          (kmeID n, rcpt, msg) \<in> msgs;
          kmes n = IoaState appState msgs;
          kmes' = kmes(n := IoaState appState (msgs - {(kmeID n, rcpt, msg)}))\<rbrakk> \<Longrightarrow> P t"
\<comment> \<open>================ BRIDGE CASES ================\<close>
    and "\<And>apps kmes bridges qkds net bridges' net' n b slaveBridge otherKme qkd kme msgs.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkds, net); t = (apps, kmes, bridges', qkds, net'); 
          n \<in> nodes; b \<in> bridgeIDs n; a \<in> act (bridge.ioa b n);
          a = TimerTick b; net' = net;
          bridges (n,b) = IoaState (Bridge True slaveBridge otherKme qkd kme) msgs;
          bridges' = bridges((n,b) := IoaState (Bridge True slaveBridge otherKme qkd kme) (msgs \<union> {(b, qkd, GetKey qkd otherKme)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkds net bridges' net' n b slaveBridge otherKme qkd kme msgs keyID keyVal.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkds, net); t = (apps, kmes, bridges', qkds, net'); 
          n \<in> nodes; b \<in> bridgeIDs n; a \<in> act (bridge.ioa b n);
          a = Receive qkd b (KeyResponse keyID keyVal);
          net' = rmv_msg net qkd b (KeyResponse keyID keyVal);
          can_send net qkd b (KeyResponse keyID keyVal);
          bridges (n,b) = IoaState (Bridge True slaveBridge otherKme qkd kme) msgs;
          bridges' = bridges((n,b) := IoaState (Bridge True slaveBridge otherKme qkd kme) (msgs \<union> {(b, kme, KMPost otherKme keyID keyVal), (b, slaveBridge, BridgeIDRelay keyID)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkds net bridges' net' n b masterBridge otherKme qkd kme msgs sender keyID.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkds, net); t = (apps, kmes, bridges', qkds, net'); 
          n \<in> nodes; b \<in> bridgeIDs n; a \<in> act (bridge.ioa b n);
          a = Receive sender b (BridgeIDRelay keyID);
          net' = rmv_msg net sender b (BridgeIDRelay keyID);
          can_send net sender b (BridgeIDRelay keyID);
          bridges (n,b) = IoaState (Bridge False masterBridge otherKme qkd kme) msgs;
          bridges' = bridges((n,b) := IoaState (Bridge False masterBridge otherKme qkd kme) (msgs \<union> {(b, qkd, GetKeyWithID qkd otherKme keyID)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkds net bridges' net' n b masterBridge otherKme qkd kme msgs keyID keyVal.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkds, net); t = (apps, kmes, bridges', qkds, net'); 
          n \<in> nodes; b \<in> bridgeIDs n; a \<in> act (bridge.ioa b n);
          a = Receive qkd b (KeyResponse keyID keyVal);
          net' = rmv_msg net qkd b (KeyResponse keyID keyVal);
          can_send net qkd b (KeyResponse keyID keyVal);
          bridges (n,b) = IoaState (Bridge False masterBridge otherKme qkd kme) msgs;
          bridges' = bridges((n,b) := IoaState (Bridge False masterBridge otherKme qkd kme) (msgs \<union> {(b, kme, KMPost otherKme keyID keyVal)}))\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkds net net' n b sender msg.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkds, net); t = (apps, kmes, bridges, qkds, net'); 
          n \<in> nodes; b \<in> bridgeIDs n; a \<in> act (bridge.ioa b n);
          a = Receive sender b msg;
          net' = rmv_msg net sender b msg;
          can_send net sender b msg\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkds net bridges' net' n b msgs rcpt msg bridgeState.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkds, net); t = (apps, kmes, bridges', qkds, net'); 
          n \<in> nodes; b \<in> bridgeIDs n; a \<in> act (bridge.ioa b n);
          a = Send b rcpt msg; net' = add_msg net b rcpt msg;
          (b, rcpt, msg) \<in> msgs;
          bridges (n,b) = IoaState bridgeState msgs;
          bridges' = bridges((n,b) := IoaState bridgeState (msgs - {(b, rcpt, msg)}))\<rbrakk> \<Longrightarrow> P t"
\<comment> \<open>================ QKD LAYER ================\<close>
    and "\<And>apps kmes bridges qkd net qkd' net' pid gen sent sender target keyID keyVal.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes, bridges, qkd', net'); 
          a \<in> act qkd_layer.ioa;
          pid \<in> qkdID ` (\<Union>(bridgeIDs ` nodes));
          keyID \<notin> fst ` ((snd ` gen) \<union> sent);
          a = Receive sender pid (GetKey pid target);
          net' = rmv_msg net sender pid (GetKey pid target);
          can_send net sender pid (GetKey pid target);
          qkd  = QKD gen sent;
          qkd' = QKD (gen \<union> {(sender, keyID, keyVal)}) sent\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net qkd' net' pid gen sent sender target keyID keyVal.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes, bridges, qkd', net'); 
          a \<in> act qkd_layer.ioa;
          pid \<in> qkdID ` (\<Union>(bridgeIDs ` nodes));
          (keyID, keyVal) \<in> sent;
          a = Receive sender pid (GetKeyWithID pid target keyID);
          net' = rmv_msg net sender pid (GetKeyWithID pid target keyID);
          can_send net sender pid (GetKeyWithID pid target keyID);
          qkd  = QKD gen sent;
          qkd' = QKD (gen \<union> {(sender, keyID, keyVal)}) (sent - {(keyID, keyVal)})\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net qkd' net' pid sender msg.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes, bridges, qkd', net'); 
          a \<in> act qkd_layer.ioa;
          pid \<in> qkdID ` (\<Union>(bridgeIDs ` nodes));
          a = Receive sender pid msg;
          net' = rmv_msg net sender pid msg;
          can_send net sender pid msg;
          qkd = qkd'\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net qkd' net' pid gen sent rcpt keyID keyVal.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes, bridges, qkd', net'); 
          a \<in> act qkd_layer.ioa;
          pid \<in> qkdID ` (\<Union>(bridgeIDs ` nodes));
          (rcpt, keyID, keyVal) \<in> gen;
          a = Send pid rcpt (KeyResponse keyID keyVal); 
          net' = add_msg net pid rcpt (KeyResponse keyID keyVal);
          qkd  = QKD gen sent;
          qkd' = QKD (gen - {(rcpt, keyID, keyVal)}) (sent \<union> {(keyID, keyVal)})\<rbrakk> \<Longrightarrow> P t"
\<comment> \<open>================ NETWORK ================\<close>
    and "\<And>apps kmes bridges qkd net net' sender rcpt msg all.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes, bridges, qkd, net');
          a \<in> act network.ioa; a \<notin> act apps.ioa; a \<notin> act kmes.ioa; a \<notin> act bridges.ioa; a \<notin> act qkd_layer.ioa;
          a = Receive sender rcpt msg;
          all = (appID ` nodes) \<union> (kmeID ` nodes) \<union> \<Union>(bridgeIDs ` nodes) \<union> qkdID ` (\<Union>(bridgeIDs ` nodes));
          net' = rmv_msg net sender rcpt msg;
          rcpt \<notin> all\<rbrakk> \<Longrightarrow> P t"
    and "\<And>apps kmes bridges qkd net net' sender rcpt msg all.
         \<lbrakk>s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t;
          s = (apps, kmes, bridges, qkd, net); t = (apps, kmes, bridges, qkd, net');
          a \<in> act network.ioa; a \<notin> act apps.ioa; a \<notin> act kmes.ioa; a \<notin> act bridges.ioa; a \<notin> act qkd_layer.ioa;
          a = Send sender rcpt msg;
          all = (appID ` nodes) \<union> (kmeID ` nodes) \<union> \<Union>(bridgeIDs ` nodes) \<union> qkdID ` (\<Union>(bridgeIDs ` nodes));
          sender \<notin> all;
          net' = add_msg net sender rcpt msg\<rbrakk> \<Longrightarrow> P t"
  shows "s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t \<longrightarrow> P t"
proof
  assume sat_trans: "s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t"
  obtain apps kmes bridges qkd net where s_split:"s = (apps, kmes, bridges, qkd, net)"
    using prod_cases5 by blast
  obtain apps' kmes' bridges' qkd' net' where t_split_init:"t = (apps', kmes', bridges', qkd', net')"
    using prod_cases5 by blast
  have "a \<in> act System.ioa"
    using sat_trans by (meson is_trans_of_par trans_in_actions)
  then consider "a \<in> act apps.ioa" | "a \<in> act kmes.ioa" | "a \<in> act bridges.ioa" | "a \<in> act qkd_layer.ioa" | "a \<in> act network.ioa \<and> a \<notin> act apps.ioa \<and> a \<notin> act kmes.ioa \<and> a \<notin> act bridges.ioa \<and> a \<notin> act qkd_layer.ioa"
    using System_trans_act_elim[OF sat_trans] by blast
  then show "P t"
  proof(cases)
    case 1
    then have "a \<notin> act kmes.ioa"
      using actsDisj_app_kme unfolding actions_of_set_ioa by fast
    moreover have "a \<notin> act bridges.ioa"
      using 1 actsDisj_app_bridge unfolding actions_of_set_ioa by fast
    moreover have "a \<notin> act qkd_layer.ioa"
      using 1 actsDisj_app_qkd unfolding actions_of_set_ioa by fast
    ultimately have "kmes = kmes' \<and> bridges = bridges' \<and> qkd = qkd'"
      using System_trans_elim[OF sat_trans] s_split t_split_init by presburger
    then have t_split:"t = (apps', kmes, bridges, qkd, net')"
      using t_split_init by meson
    obtain n where A: "n \<in> nodes" and B:"a \<in> act (app.ioa n)"
      using 1 unfolding actions_of_set_ioa Sigma_def by fast
    have "s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t \<longrightarrow> P t"
      using assms(1,2) A B s_split t_split
      apply (induction rule: app_invariant_step)
      using assms(3)[OF sat_trans s_split] t_split A B apply blast
      using assms(4)[OF sat_trans s_split] t_split A B apply blast
      using assms(5)[OF sat_trans s_split] t_split A B apply blast
      using assms(6)[OF sat_trans s_split] t_split A B apply blast
      using assms(7)[OF sat_trans s_split] t_split A B apply blast
      using assms(8)[OF sat_trans s_split] t_split A B by blast
    then show ?thesis 
      using sat_trans by meson
  next
    case 2
    then have "a \<notin> act apps.ioa"
      using actsDisj_app_kme unfolding actions_of_set_ioa by fast
    moreover have "a \<notin> act bridges.ioa"
      using 2 actsDisj_kme_bridge unfolding actions_of_set_ioa by fast
    moreover have "a \<notin> act qkd_layer.ioa"
      using 2 actsDisj_kme_qkd unfolding actions_of_set_ioa by fast
    ultimately have "apps = apps' \<and> bridges = bridges' \<and> qkd = qkd'"
      using System_trans_elim[OF sat_trans] s_split t_split_init by presburger
    then have t_split:"t = (apps, kmes', bridges, qkd, net')"
      using t_split_init by meson
    obtain n where A: "n \<in> nodes" and B:"a \<in> act (kme.ioa n)"
      using 2 unfolding actions_of_set_ioa Sigma_def by fast
    have "s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t \<longrightarrow> P t"
      using assms(1,2) A B s_split t_split
      apply (induction rule: kme_invariant_step)
      using assms(9)[OF sat_trans s_split] t_split A B apply blast
      using assms(10)[OF sat_trans s_split] t_split A B apply blast
      using assms(11)[OF sat_trans s_split] t_split A B apply blast
      using assms(12)[OF sat_trans s_split] t_split A B apply blast
      using assms(13)[OF sat_trans s_split] t_split A B apply blast
      using assms(14)[OF sat_trans s_split] t_split A B apply blast
      using assms(15)[OF sat_trans s_split] t_split A B apply blast
      using assms(16)[OF sat_trans s_split] t_split A B apply blast
      using assms(17)[OF sat_trans s_split] t_split A B apply blast
      using assms(18)[OF sat_trans s_split] t_split A B apply blast
      using assms(19)[OF sat_trans s_split] t_split A B apply blast
      using assms(20)[OF sat_trans s_split] t_split A B apply blast
      using assms(21)[OF sat_trans s_split] t_split A B apply blast
      using assms(22)[OF sat_trans s_split] t_split A B apply blast
      using assms(23)[OF sat_trans s_split] t_split A B by blast
    then show ?thesis 
      using sat_trans by meson
  next
    case 3
    then have "a \<notin> act apps.ioa"
      using actsDisj_app_bridge unfolding actions_of_set_ioa by fast
    moreover have "a \<notin> act kmes.ioa"
      using 3 actsDisj_kme_bridge unfolding actions_of_set_ioa by fast
    moreover have "a \<notin> act qkd_layer.ioa"
      using 3 actsDisj_bridge_qkd unfolding actions_of_set_ioa by fast
    ultimately have "apps = apps' \<and> kmes = kmes' \<and> qkd = qkd'"
      using System_trans_elim[OF sat_trans] s_split t_split_init by presburger
    then have t_split:"t = (apps, kmes, bridges', qkd, net')"
      using t_split_init by meson
    obtain n b where A: "n \<in> nodes" and B: "b \<in> bridgeIDs n" and C:"a \<in> act (bridge.ioa b n)"
      using 3 unfolding actions_of_set_ioa Sigma_def by fast
    have "s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t \<longrightarrow> P t"
      using assms(1,2) A B C s_split t_split
      apply (induction rule: bridge_invariant_step)
      using assms(24)[OF sat_trans s_split] t_split A B C sat_trans apply blast
      using assms(25)[OF sat_trans s_split] t_split A B C sat_trans apply blast
      using assms(26)[OF sat_trans s_split] t_split A B C sat_trans apply blast
      using assms(27)[OF sat_trans s_split] t_split A B C sat_trans apply blast
      using assms(28)[OF sat_trans s_split] t_split A B C sat_trans apply blast
      using assms(29)[OF sat_trans s_split] t_split A B C sat_trans by blast
    then show ?thesis 
      using sat_trans by meson
  next
    case 4
    then have "a \<notin> act apps.ioa"
      using actsDisj_app_qkd unfolding actions_of_set_ioa by fast
    moreover have "a \<notin> act kmes.ioa"
      using 4 actsDisj_kme_qkd unfolding actions_of_set_ioa by blast
    moreover have "a \<notin> act bridges.ioa"
      using 4 actsDisj_bridge_qkd unfolding actions_of_set_ioa by fast
    ultimately have "apps = apps' \<and> kmes = kmes' \<and> bridges = bridges'"
      using System_trans_elim[OF sat_trans] s_split t_split_init by presburger
    then have t_split:"t = (apps, kmes, bridges, qkd', net')"
      using t_split_init by meson
    have "s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t \<longrightarrow> P t"
      using assms(1,2) 4 s_split t_split
      apply (induction rule:qkd_invariant_step)
      using assms(30)[OF sat_trans s_split] t_split 4 apply blast
      using assms(31)[OF sat_trans s_split] t_split 4 apply blast
      using assms(32)[OF sat_trans s_split] t_split 4 apply blast
      using assms(33)[OF sat_trans s_split] t_split 4 by blast
    then show ?thesis 
      using sat_trans by meson
  next
    case 5
    then have "apps = apps' \<and> kmes = kmes' \<and> bridges = bridges' \<and> qkd = qkd'"
      using System_trans_elim[OF sat_trans] s_split t_split_init by blast
    then have t_split:"t = (apps, kmes, bridges, qkd, net')"
      using t_split_init by meson
    have A:"a \<notin> act apps.ioa"
      using 5 by simp
    have B:"a \<notin> act kmes.ioa"
      using 5 by simp
    have C:"a \<notin> act bridges.ioa"
      using 5 by simp
    have D:"a \<notin> act qkd_layer.ioa"
      using 5 by simp
    have E:"a \<in> act network.ioa"
      using 5 by simp
    have "s \<midarrow>a\<midarrow>System.ioa\<rightarrow> t \<longrightarrow> P t"
      using assms(1,2) A B C D E s_split t_split
      apply (induction rule:network_invariant_step)
      using assms(34)[OF sat_trans s_split _ E A B C D] t_split apply blast
      using assms(35)[OF sat_trans s_split _ E A B C D] t_split by blast
    then show ?thesis
      using sat_trans by meson
  qed
qed

end

end