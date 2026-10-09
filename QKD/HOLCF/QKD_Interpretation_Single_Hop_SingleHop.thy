theory QKD_Interpretation_Single_Hop_SingleHop
  imports QKD_Interpretation_Single_Hop_Trans_Helpers
begin

(*App asks for key*)
lemma
  assumes "app1 = IoaState (App True (AppProc Node2) (KmeProc Node1) {}) {}"
    and "app1' = IoaState (App True (AppProc Node2) (KmeProc Node1) {}) {(AppProc Node1, KmeProc Node1, GetKey (KmeProc Node1) (AppProc Node2))}"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = RequestKey (AppProc Node1)"
    and "t = (apps app1' app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_app_no_netw)
  show "\<forall>sender receiver msg. a \<noteq> Send sender receiver msg"
    unfolding assms by simp
  show "\<forall>sender receiver msg. a \<noteq> Receive sender receiver msg"
    unfolding assms by simp
  show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    using assms by simp
  show "t = (apps app1' app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    using assms by simp
  show "Node1 \<in> c_nodes"
    unfolding c_nodes_def by simp
  show "(Node1 = Node1 \<longrightarrow> app2 = app2) \<and> (Node1 = Node2 \<longrightarrow> app1 = app1')"
    by simp
  show "app s Node1 \<midarrow>a\<midarrow>SingleHop.app.ioa Node1\<rightarrow> app t Node1"
    apply (simp only: assms apps_def trans_of_def c_isMaster_def c_appID_def; simp)
    using Master_GetKey by fastforce
qed

(*Bridge asks qkdm for key*)
lemma
  assumes "bridge1 = IoaState (Bridge True (BridgeProc Node2) (KmeProc Node2) (QkdProc Node1) (KmeProc Node1)) {}"
    and "bridge1' = IoaState (Bridge True (BridgeProc Node2) (KmeProc Node2) (QkdProc Node1) (KmeProc Node1)) {(BridgeProc Node1, QkdProc Node1, GetKey (QkdProc Node1) (KmeProc Node2))}"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = TimerTick (BridgeProc Node1)"
    and "t = (apps app1 app2, kmes kme1 kme2, bridges bridge1' bridge2, qkd, netw)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_bridge_no_netw, goal_cases)
  show "\<forall>sender receiver msg. a \<noteq> Send sender receiver msg"
    using assms by blast
  show "\<forall>sender receiver msg. a \<noteq> Receive sender receiver msg"
    using assms by blast
  show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    using assms by blast
  show "t = (apps app1 app2, kmes kme1 kme2, bridges bridge1' bridge2, qkd, netw)"
    using assms by blast
  show "Node1 \<in> c_nodes"
    using c_nodes_def by blast
  show "BridgeProc Node1 \<in> c_bridgeIDs Node1"
    using c_bridgeIDs_def by blast
  show "bridge s Node1
     (BridgeProc Node1) \<midarrow>a\<midarrow>SingleHop.bridge.ioa (BridgeProc Node1) Node1\<rightarrow> bridge t Node1 (BridgeProc Node1)"
    apply (simp only: assms bridges_def trans_of_def c_isMaster_def c_appID_def; simp)
    using Tick_GetKey by fastforce
  show "(Node1 = Node1 \<longrightarrow> bridge2 = bridge2) \<and> (Node1 = Node2 \<longrightarrow> bridge1 = bridge1')"
    by (simp only: assms; simp)
qed

(*QKD receives GetKey and generates new key*)
lemma
  assumes "qkd = QKD {} {}"
    and "qkd' = QKD {(BridgeProc Node1, keyID, keyVal)} {}"
    and "(BridgeProc Node1, QkdProc Node1, GetKey (QkdProc Node1) (KmeProc Node2)) \<in> netw"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = Receive (BridgeProc Node1) (QkdProc Node1) (GetKey (QkdProc Node1) (KmeProc Node2))"
    and "t = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd', netw)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_qkd_netw, goal_cases)
  case 1
  then show ?case
    using assms by blast
  case 2
  then show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    using assms by blast
  case 3
  then show "t = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd', netw)"
    using assms by blast
  case 4
  then show ?case
    using GetKey_Gen[of "QkdProc Node1" "c_qkdID ` (c_bridgeIDs Node1 \<union> c_bridgeIDs Node2)" keyID "{}" "{}" "BridgeProc Node1" "KmeProc Node2" keyVal]
    apply(simp only: assms  trans_of_def SingleHop.qkd_layer.layer_trans; simp)
    by(simp only: c_qkdID_def c_bridgeIDs_def c_nodes_def; simp)
  case 5
  then show ?case
    apply(simp only: assms trans_of_def SingleHop.qkd_layer.layer_trans; simp)
    unfolding c_qkdID_def c_bridgeIDs_def c_nodes_def c_appID_def c_kmeID_def 
    using assms by simp
qed


(*QKD sends new key to bridge*)
lemma
  assumes "qkd = QKD {(BridgeProc Node1, keyID, keyVal)} {}"
    and "qkd' = QKD {} {(keyID, keyVal)}"
    and "netw' = netw \<union> {(QkdProc Node1, BridgeProc Node1, KeyResponse keyID keyVal)}"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = Send (QkdProc Node1) (BridgeProc Node1) (KeyResponse keyID keyVal)"
    and "t = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd', netw')"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_qkd_netw, goal_cases)
  case 1
  then show ?case
    using assms by blast
next
  case 2
  then show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)" 
    using assms by blast
next
  case 3
  then show "t = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd', netw')"
    using assms by blast
next
  case 4
  then show ?case
    using Send[of "QkdProc Node1" "c_qkdID ` (c_bridgeIDs Node1 \<union> c_bridgeIDs Node2)" "BridgeProc Node1" keyID keyVal "{(BridgeProc Node1, keyID, keyVal)}" "{}"]
    apply(simp only: assms trans_of_def SingleHop.qkd_layer.layer_trans; simp)
    by(simp only: c_qkdID_def c_bridgeIDs_def c_nodes_def; simp)
next
  case 5
  then show ?case
    apply(simp only: assms snd_conv)
    apply(simp only: assms trans_of_def SingleHop.qkd_layer.layer_trans; simp)
    unfolding c_qkdID_def c_bridgeIDs_def c_nodes_def c_appID_def c_kmeID_def by simp
qed


(*Bridges receives new key and sends it to kme and to otherBridge*)
lemma
  assumes "bridge1 = IoaState (Bridge True (BridgeProc Node2) (KmeProc Node2) (QkdProc Node1) (KmeProc Node1)) {}"
    and "bridge1' = IoaState (Bridge True (BridgeProc Node2) (KmeProc Node2) (QkdProc Node1) (KmeProc Node1)) 
        {(BridgeProc Node1, KmeProc Node1, KMPost (KmeProc Node2) keyID keyVal), (BridgeProc Node1, BridgeProc Node2, BridgeIDRelay keyID)}"
    and "(QkdProc Node1, BridgeProc Node1, KeyResponse keyID keyVal) \<in> netw"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = Receive (QkdProc Node1)(BridgeProc Node1) (KeyResponse keyID keyVal)"
    and "t = (apps app1 app2, kmes kme1 kme2, bridges bridge1' bridge2, qkd, netw)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_bridge_netw, goal_cases)
  case 1
  then show ?case
    using assms by blast
  case 2
  then show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    using assms by blast
  case 3
  then show "t = (apps app1 app2, kmes kme1 kme2, bridges bridge1' bridge2, qkd, netw)"
    using assms by blast
  case 4
  then show "Node1 \<in> c_nodes"
    using c_nodes_def by blast
  case 5
  then show "BridgeProc Node1 \<in> c_bridgeIDs Node1"
    using c_bridgeIDs_def by simp
  case 6
  then show "bridge s Node1
     (BridgeProc Node1) \<midarrow>a\<midarrow>SingleHop.bridge.ioa (BridgeProc Node1) Node1\<rightarrow> bridge t Node1 (BridgeProc Node1)"
    apply(simp only: assms bridges_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    by (metis (no_types, lifting) bridge_step.Master_KeyResponse image_empty image_insert)
  case 7
  then show ?case 
    apply(simp only: assms fst_conv bridges_def snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 8
  then show "(Node1 = Node1 \<longrightarrow> bridge2 = bridge2) \<and> (Node1 = Node2 \<longrightarrow> bridge1 = bridge1')"
    using assms by blast
qed



(*otherBridge receives keyID; asks for it in qkdLayer*)
lemma
  assumes "bridge2 = IoaState (Bridge False (BridgeProc Node1) (KmeProc Node1) (QkdProc Node2) (KmeProc Node2)) {}"
    and "bridge2' = IoaState (Bridge False (BridgeProc Node1) (KmeProc Node1) (QkdProc Node2) (KmeProc Node2)) 
        {(BridgeProc Node2, QkdProc Node2, GetKeyWithID (QkdProc Node2) (KmeProc Node1) keyID)}"
    and "(BridgeProc Node1, BridgeProc Node2, (BridgeIDRelay keyID)) \<in> netw"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = Receive (BridgeProc Node1) (BridgeProc Node2) (BridgeIDRelay keyID)"
    and "t = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2', qkd, netw)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_bridge_netw, goal_cases)
  case 1
  then show ?case
    using assms by blast
  case 2
  then show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    using assms by blast
  case 3
  then show "t = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2', qkd, netw)"
    using assms by blast
  case 4
  then show "Node2 \<in> c_nodes"
    using c_nodes_def by blast
  case 5
  then show "BridgeProc Node2 \<in> c_bridgeIDs Node2"
    using c_bridgeIDs_def by simp
  case 6
  then show "bridge s Node2
     (BridgeProc Node2) \<midarrow>a\<midarrow>SingleHop.bridge.ioa (BridgeProc Node2) Node2\<rightarrow> bridge t Node2 (BridgeProc Node2)"
    apply(simp only: assms bridges_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    by (metis (no_types, lifting) bridge_step.Slave_GetKeyWithID image_empty image_insert)
  case 7
  then show ?case 
    apply(simp only: assms fst_conv bridges_def snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 8
  then show "(Node2 = Node1 \<longrightarrow> bridge2 = bridge2') \<and> (Node2 = Node2 \<longrightarrow> bridge1 = bridge1)"
    using assms by blast
qed


(*qkdLayer receives GetKeyWithID from otherBridge *)
lemma
  assumes "qkd = QKD {} {(keyID, keyVal)}"
    and "qkd' = QKD {(BridgeProc Node2, keyID, keyVal)} {}"
    and "msg = GetKeyWithID (QkdProc Node2) (KmeProc Node1) keyID"
    and "(BridgeProc Node2, QkdProc Node2, msg) \<in> netw"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = Receive (BridgeProc Node2) (QkdProc Node2) msg"
    and "t = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd', netw)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_qkd_netw, goal_cases)
  case 1
  then show ?case
    using assms by blast
  case 2
  then show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    using assms by blast
  case 3
  then show "t = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd', netw)"
    using assms by blast
  case 4
  then show ?case
    using GetKeyWithID_Reserve[of "QkdProc Node2" "c_qkdID ` (c_bridgeIDs Node1 \<union> c_bridgeIDs Node2)" keyID keyVal "{(keyID, keyVal)}" "{}" "BridgeProc Node2" "KmeProc Node1"]
    apply(simp only: assms trans_of_def SingleHop.qkd_layer.layer_trans; simp)
    by(simp only: c_qkdID_def c_bridgeIDs_def c_nodes_def; simp)
  case 5
  then show ?case
    apply(simp only: assms trans_of_def SingleHop.qkd_layer.layer_trans; simp)
    unfolding c_qkdID_def c_bridgeIDs_def c_nodes_def c_appID_def c_kmeID_def 
    using assms by simp
qed

(*qkdLayer sends Key to otherBridge*)
lemma
  assumes "qkd = QKD {(BridgeProc Node2, keyID, keyVal)} {}"
    and "qkd' = QKD {} {(keyID, keyVal)}"
    and "netw' = netw \<union> {(QkdProc Node2, BridgeProc Node2, KeyResponse keyID keyVal)}"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = Send (QkdProc Node2) (BridgeProc Node2) (KeyResponse keyID keyVal)"
    and "t = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd', netw')"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_qkd_netw, goal_cases)
  case 1
  then show ?case
    using assms by blast
  case 2
  then show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    using assms by blast
  case 3
  then show "t = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd', netw')"
    using assms by blast
  case 4
  then show ?case
    using Send[of "QkdProc Node2" "c_qkdID ` (c_bridgeIDs Node1 \<union> c_bridgeIDs Node2)" "BridgeProc Node2" keyID keyVal "{(BridgeProc Node2, keyID, keyVal)}" "{}"]
    apply(simp only: assms trans_of_def SingleHop.qkd_layer.layer_trans; simp)
    by(simp only: c_qkdID_def c_bridgeIDs_def c_nodes_def; simp)
  case 5
  then show ?case
    apply(simp only: assms trans_of_def SingleHop.qkd_layer.layer_trans; simp)
    unfolding c_qkdID_def c_bridgeIDs_def c_nodes_def c_appID_def c_kmeID_def 
    using assms by simp
qed


(*otherBridge receives key and sends it to otherkme*)
lemma
  assumes "bridge2 = IoaState (Bridge False (BridgeProc Node1) (KmeProc Node1) (QkdProc Node2) (KmeProc Node2)) {}"
    and "bridge2' = IoaState (Bridge False (BridgeProc Node1) (KmeProc Node1) (QkdProc Node2) (KmeProc Node2)) 
        {(BridgeProc Node2, KmeProc Node2, KMPost (KmeProc Node1) keyID keyVal)}"
    and "(QkdProc Node2, BridgeProc Node2, KeyResponse keyID keyVal) \<in> netw"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = Receive (QkdProc Node2)(BridgeProc Node2) (KeyResponse keyID keyVal)"
    and "t = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2', qkd, netw)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_bridge_netw, goal_cases)
  case 1
  then show ?case
    using assms by blast
  case 2
  then show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    using assms by blast
  case 3
  then show "t = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2', qkd, netw)"
    using assms by blast
  case 4
  then show "Node2 \<in> c_nodes"
    using c_nodes_def by blast
  case 5
  then show "BridgeProc Node2 \<in> c_bridgeIDs Node2"
    using c_bridgeIDs_def by simp
  case 6
  then show "bridge s Node2
     (BridgeProc Node2) \<midarrow>a\<midarrow>SingleHop.bridge.ioa (BridgeProc Node2) Node2\<rightarrow> bridge t Node2 (BridgeProc Node2)"
    apply(simp only: assms fst_conv bridges_def snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    by (metis (no_types, lifting) bridge_step.Slave_KeyResponse image_empty image_insert)
  case 7
  then show ?case 
    apply(simp only: assms fst_conv bridges_def snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 8
  then show "(Node2 = Node1 \<longrightarrow> bridge2 = bridge2') \<and> (Node2 = Node2 \<longrightarrow> bridge1 = bridge1)"
    using assms by blast
qed


(*kme receives key from bridge; saves it and sends confirmed to otherkme*)
lemma
  assumes "kme1 = IoaState (Kme store route saeToKme) {}"
    and "kme1' = IoaState (Kme (keyStore_add store keyID (Some keyVal) (KmeProc Node2)) route saeToKme) 
        {(KmeProc Node1, BridgeProc Node1, OK), (KmeProc Node1, KmeProc Node2, KMPut (KmeProc Node1) keyID None)}"
    and "(BridgeProc Node1, KmeProc Node1, KMPost (KmeProc Node2) keyID keyVal) \<in> netw"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = Receive (BridgeProc Node1) (KmeProc Node1) (KMPost (KmeProc Node2) keyID keyVal)"
    and "t = (apps app1 app2, kmes kme1' kme2, bridges bridge1 bridge2, qkd, netw)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_kme_netw, goal_cases)
  case 1
  then show ?case
    using assms by blast
  case 2
  then show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    using assms by blast
  case 3
  then show "t = (apps app1 app2, kmes kme1' kme2, bridges bridge1 bridge2, qkd, netw)"
    using assms by blast
  case 4
  then show "Node1 \<in> c_nodes"
    using c_nodes_def by blast
  case 5
  then show "kme s Node1 \<midarrow>a\<midarrow>SingleHop.kme.ioa Node1\<rightarrow> kme t Node1"
    apply(simp only: assms kmes_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    using KMPost_NewKeyVal[of c_enc c_dec store route saeToKme "BridgeProc Node1" "KmeProc Node1" "KmeProc Node2" keyID keyVal]
    apply auto
    by (metis (no_types, lifting) image_empty image_insert)
  case 6
  then show ?case 
    apply(simp only: assms kmes_def fst_conv bridges_def snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node1 = Node1 \<longrightarrow> kme2 = kme2) \<and> (Node1 = Node2 \<longrightarrow> kme1 = kme1')"
    using assms by blast
qed


(*otherkme receives confirm and updates keyStore*)
lemma
  assumes "kme2 = IoaState (Kme store route saeToKme) {}"
    and "kme2' = IoaState (Kme (keyStore_confirm store keyID (KmeProc Node1)) route saeToKme)
        {(rcpt, sender, OK)}"
    and "sender = KmeProc Node1"
    and "rcpt = KmeProc Node2"
    and "msg = KMPut (KmeProc Node1) keyID None"
    and "(sender, rcpt, msg) \<in> netw"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = Receive sender rcpt msg"
    and "t = (apps app1 app2, kmes kme1 kme2', bridges bridge1 bridge2, qkd, netw)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_kme_netw, goal_cases)
  case 1
  then show ?case
    using assms by blast
  case 2
  then show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    using assms by blast
  case 3
  then show "t = (apps app1 app2, kmes kme1 kme2', bridges bridge1 bridge2, qkd, netw)"
    using assms by blast
  case 4
  then show "Node2 \<in> c_nodes"
    using c_nodes_def by blast
  case 5
  then show "kme s Node2 \<midarrow>a\<midarrow>SingleHop.kme.ioa Node2\<rightarrow> kme t Node2"
    apply(simp only: assms kmes_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    using KMPut_Confirm[of c_enc c_dec store route saeToKme sender rcpt "KmeProc Node1" keyID] assms
    by auto
  case 6
  then show ?case 
    apply(simp only: assms kmes_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node2 = Node1 \<longrightarrow> kme2 = kme2') \<and> (Node2 = Node2 \<longrightarrow> kme1 = kme1)"
    using assms by blast
qed


(*otherKme receives key from otherBridge and updates keyStore; sends confirm to kme*)
lemma
  assumes "kme2 = IoaState (Kme store route saeToKme) {}"
    and "kme2' = IoaState (Kme store' route saeToKme) 
        {(rcpt, sender, OK), (rcpt, KmeProc Node1, KMPut (KmeProc Node2) keyID None)}"
    and "store = keyStore_confirm store_init keyID (KmeProc Node1)"
    and "store' = keyStore_add store keyID (Some keyVal) (KmeProc Node1)"
    and "sender = BridgeProc Node2"
    and "rcpt = KmeProc Node2"
    and "msg = KMPost (KmeProc Node1) keyID keyVal"
    and "(sender, rcpt, msg) \<in> netw"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = Receive sender rcpt msg"
    and "t = (apps app1 app2, kmes kme1 kme2', bridges bridge1 bridge2, qkd, netw)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_kme_netw, goal_cases)
  case 1
  then show ?case
    using assms by blast
  case 2
  then show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    using assms by blast
  case 3
  then show "t = (apps app1 app2, kmes kme1 kme2', bridges bridge1 bridge2, qkd, netw)"
    using assms by blast
  case 4
  then show "Node2 \<in> c_nodes"
    using c_nodes_def by blast
  case 5
  then show "kme s Node2 \<midarrow>a\<midarrow>SingleHop.kme.ioa Node2\<rightarrow> kme t Node2"
    apply(simp only: assms kmes_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    using KMPost_NewKeyVal[of c_enc c_dec store route saeToKme sender rcpt "KmeProc Node1" keyID keyVal]
    using assms apply simp
    by (metis (no_types, lifting) image_empty image_insert)
  case 6
  then show ?case 
    apply(simp only: assms kmes_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node2 = Node1 \<longrightarrow> kme2 = kme2') \<and> (Node2 = Node2 \<longrightarrow> kme1 = kme1)"
    using assms by blast
qed


(*kme receives confirm from otherkme and updates keyStore*)
lemma
  assumes "kme1 = IoaState (Kme store route saeToKme) {}"
    and "kme1' = IoaState (Kme store' route saeToKme) 
        {(rcpt, sender, OK)}"
    and "store = keyStore_add store_init keyID (Some keyVal) (KmeProc Node2)"
    and "store' = keyStore_confirm store keyID (KmeProc Node2)"
    and "sender = KmeProc Node2"
    and "rcpt = KmeProc Node1"
    and "msg = KMPut (KmeProc Node2) keyID None"
    and "(sender, rcpt, msg) \<in> netw"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = Receive sender rcpt msg"
    and "t = (apps app1 app2, kmes kme1' kme2, bridges bridge1 bridge2, qkd, netw)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_kme_netw, goal_cases)
  case 1
  then show ?case
    using assms by blast
  case 2
  then show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    using assms by blast
  case 3
  then show "t = (apps app1 app2, kmes kme1' kme2, bridges bridge1 bridge2, qkd, netw)"
    using assms by blast
  case 4
  then show "Node1 \<in> c_nodes"
    using c_nodes_def by blast
  case 5
  then show "kme s Node1 \<midarrow>a\<midarrow>SingleHop.kme.ioa Node1\<rightarrow> kme t Node1"
    apply(simp only: assms kmes_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    using KMPut_Confirm[of c_enc c_dec store route saeToKme sender rcpt "KmeProc Node2" keyID]
    using assms by auto
  case 6
  then show ?case 
    apply(simp only: assms kmes_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node1 = Node1 \<longrightarrow> kme2 = kme2) \<and> (Node1 = Node2 \<longrightarrow> kme1 = kme1')"
    using assms by blast
qed


(*kme receives GetKey from App; sends reserve to otherKme*)
lemma
  assumes "kme1 = IoaState (Kme store route c_saeToKme) {}"
    and "kme1' = IoaState (KmeWaitReserve keyID sender store route c_saeToKme) 
        {(rcpt, c_saeToKme (AppProc Node2), KMPut rcpt keyID (Some (AppProc Node2)))}"
    and "store_init = (\<lambda>id. None)"
    and "store = keyStore_confirm (keyStore_add store_init keyID (Some keyVal) (KmeProc Node2)) keyID (KmeProc Node2)"
    and "sender = AppProc Node1"
    and "rcpt = KmeProc Node1"
    and "msg = GetKey (KmeProc Node1) (AppProc Node2)"
    and "(sender, rcpt, msg) \<in> netw"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = Receive sender rcpt msg"
    and "t = (apps app1 app2, kmes kme1' kme2, bridges bridge1 bridge2, qkd, netw)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_kme_netw, goal_cases)
  case 1
  then show ?case
    using assms by blast
  case 2
  then show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    using assms by blast
  case 3
  then show "t = (apps app1 app2, kmes kme1' kme2, bridges bridge1 bridge2, qkd, netw)"
    using assms by blast
  case 4
  then show "Node1 \<in> c_nodes"
    using c_nodes_def by blast
  case 5
  then show "kme s Node1 \<midarrow>a\<midarrow>SingleHop.kme.ioa Node1\<rightarrow> kme t Node1"
    apply(simp only: assms kmes_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    using GetKey[of store keyID keyVal c_saeToKme "AppProc Node2" c_enc c_dec route sender rcpt "KmeProc Node1"]
    using assms apply simp
    unfolding c_saeToKme_def by auto
  case 6
  then show ?case 
    apply(simp only: assms kmes_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node1 = Node1 \<longrightarrow> kme2 = kme2) \<and> (Node1 = Node2 \<longrightarrow> kme1 = kme1')"
    using assms by blast
qed


(*otherKme receives reserve for keyID; reserves key and Sends OK to kme*)
lemma
  assumes "kme2 = IoaState (Kme store route saeToKme) {}"
    and "kme2' = IoaState (Kme (keyStore_reserve store keyID (AppProc Node2)) route saeToKme) 
        {(KmeProc Node2, KmeProc Node1, OK)}"
    and "sender = KmeProc Node1"
    and "rcpt = KmeProc Node2"
    and "msg = KMPut (KmeProc Node1) keyID (Some (AppProc Node2))"
    and "(sender, rcpt, msg) \<in> netw"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = Receive sender rcpt msg"
    and "t = (apps app1 app2, kmes kme1 kme2', bridges bridge1 bridge2, qkd, netw)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_kme_netw, goal_cases)
  case 1
  then show ?case using assms by blast
  case 2
  then show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)" using assms by blast
  case 3
  then show "t = (apps app1 app2, kmes kme1 kme2', bridges bridge1 bridge2, qkd, netw)" using assms by blast
  case 4
  then show "Node2 \<in> c_nodes" using c_nodes_def by blast
  case 5
  then show "kme s Node2 \<midarrow>a\<midarrow>SingleHop.kme.ioa Node2\<rightarrow> kme t Node2"
    apply(simp only: assms kmes_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    using KMPut_Reserve[of c_enc c_dec store route saeToKme sender rcpt "KmeProc Node1" keyID "AppProc Node2"] assms
    by auto
  case 6
  then show ?case 
    apply(simp only: assms kmes_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node2 = Node1 \<longrightarrow> kme2 = kme2') \<and> (Node2 = Node2 \<longrightarrow> kme1 = kme1)" using assms by blast
qed


(*kme receives OK removesKey and sends key to App*)
lemma
  assumes "kme1 = IoaState (KmeWaitReserve keyID (AppProc Node1) store route saeToKme) {}"
    and "kme1' = IoaState (Kme (keyStore_remove store keyID) route saeToKme) 
        {(KmeProc Node1, AppProc Node1, KeyResponse keyID keyVal)}"
    and "store_init = (\<lambda>id. None)"
    and "store = keyStore_confirm (keyStore_add store_init keyID (Some keyVal) (KmeProc Node2)) keyID (KmeProc Node2)"
    and "sender = KmeProc Node2"
    and "rcpt = KmeProc Node1"
    and "(sender, rcpt, OK) \<in> netw"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = Receive sender rcpt OK"
    and "t = (apps app1 app2, kmes kme1' kme2, bridges bridge1 bridge2, qkd, netw)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_kme_netw, goal_cases)
  case 1
  then show ?case using assms by blast
  case 2
  then show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)" using assms by blast
  case 3
  then show "t = (apps app1 app2, kmes kme1' kme2, bridges bridge1 bridge2, qkd, netw)" using assms by blast
  case 4
  then show "Node1 \<in> c_nodes" using c_nodes_def by blast
  case 5
  then show "kme s Node1 \<midarrow>a\<midarrow>SingleHop.kme.ioa Node1\<rightarrow> kme t Node1"
    apply(simp only: assms kmes_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    using GetKey_Reserved[of store keyID keyVal "KmeProc Node2" True None c_enc c_dec "AppProc Node1" route saeToKme] assms
    apply simp
    by auto
  case 6
  then show ?case 
    apply(simp only: assms kmes_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node1 = Node1 \<longrightarrow> kme2 = kme2) \<and> (Node1 = Node2 \<longrightarrow> kme1 = kme1')" using assms by blast
qed


(*App receives key and sends keyID to otherApp*)
lemma
  assumes "app1 = IoaState (App True (AppProc Node2) (KmeProc Node1) keys) {}"
    and "app1' = IoaState (App True (AppProc Node2) (KmeProc Node1) (keys \<union> {(keyID, keyVal)})) 
        {(AppProc Node1, AppProc Node2, AppIDRelay keyID)}"
    and "sender = KmeProc Node1"
    and "rcpt = AppProc Node1"
    and "msg = KeyResponse keyID keyVal"
    and "(sender, rcpt, msg) \<in> netw"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = Receive sender rcpt msg"
    and "t = (apps app1' app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_app_netw, goal_cases)
  case 1
  then show ?case using assms by blast
  case 2
  then show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)" using assms by blast
  case 3
  then show "t = (apps app1' app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)" using assms by blast
  case 4
  then show "Node1 \<in> c_nodes" using c_nodes_def by blast
  case 5
  then show "app s Node1 \<midarrow>a\<midarrow>SingleHop.app.ioa Node1\<rightarrow> app t Node1"
    apply(simp only: assms apps_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def apply simp
    using QKD_App.app_step.Master_KeyResponse[of "AppProc Node2" "KmeProc Node1" keys sender rcpt keyID keyVal] assms
    by auto
  case 6
  then show ?case
    apply(simp only: assms apps_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node1 = Node1 \<longrightarrow> app2 = app2) \<and> (Node1 = Node2 \<longrightarrow> app1 = app1')" using assms by blast
qed


(*otherApp receives keyID; asks for it in otherKme*)
lemma
  assumes "app2 = IoaState (App False (AppProc Node1) (KmeProc Node2) keys) {}"
    and "app2' = IoaState (App False (AppProc Node1) (KmeProc Node2) keys) 
        {(AppProc Node2, KmeProc Node2, GetKeyWithID (KmeProc Node2) (AppProc Node1) keyID)}"
    and "sender = AppProc Node1"
    and "rcpt = AppProc Node2"
    and "msg = AppIDRelay keyID"
    and "(sender, rcpt, msg) \<in> netw"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = Receive sender rcpt msg"
    and "t = (apps app1 app2', kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_app_netw, goal_cases)
  case 1
  then show ?case using assms by blast
  case 2
  then show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)" using assms by blast
  case 3
  then show "t = (apps app1 app2', kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)" using assms by blast
  case 4
  then show "Node2 \<in> c_nodes" using c_nodes_def by blast
  case 5
  then show "app s Node2 \<midarrow>a\<midarrow>SingleHop.app.ioa Node2\<rightarrow> app t Node2"
    apply(simp only: assms apps_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def apply simp
    using Slave_GetKey[of "AppProc Node1" "KmeProc Node2" keys sender rcpt keyID] assms
    by auto
  case 6
  then show ?case
    apply(simp only: assms apps_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node2 = Node1 \<longrightarrow> app2 = app2') \<and> (Node2 = Node2 \<longrightarrow> app1 = app1)" using assms by blast
qed


(*otherKme receives GetKeyWithID and answers with whole key*)
lemma
  assumes "kme2 = IoaState (Kme store route c_saeToKme) {}"
    and "kme2' = IoaState (Kme (keyStore_remove store keyID) route c_saeToKme) 
        {(KmeProc Node2, AppProc Node2, KeyResponse keyID keyVal)}"
    and "store_init = (\<lambda>id. None)"
    and "store_base = keyStore_add (keyStore_confirm store_init keyID (KmeProc Node1)) keyID (Some keyVal) (KmeProc Node1)"
    and "store = keyStore_reserve store_base keyID (AppProc Node2)"
    and "sender = AppProc Node2"
    and "rcpt = KmeProc Node2"
    and "msg = GetKeyWithID (KmeProc Node2) (AppProc Node1) keyID"
    and "(sender, rcpt, msg) \<in> netw"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = Receive sender rcpt msg"
    and "t = (apps app1 app2, kmes kme1 kme2', bridges bridge1 bridge2, qkd, netw)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_kme_netw, goal_cases)
  case 1
  then show ?case using assms by blast
  case 2
  then show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)" using assms by blast
  case 3
  then show "t = (apps app1 app2, kmes kme1 kme2', bridges bridge1 bridge2, qkd, netw)" using assms by blast
  case 4
  then show "Node2 \<in> c_nodes" using c_nodes_def by blast
  case 5
  then show "kme s Node2 \<midarrow>a\<midarrow>SingleHop.kme.ioa Node2\<rightarrow> kme t Node2"
    apply(simp only: assms kmes_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    using GetKeyWithID_IDFound[of store keyID keyVal c_saeToKme "AppProc Node1" sender c_enc c_dec route rcpt rcpt] assms
    unfolding c_saeToKme_def apply simp
    by auto
  case 6
  then show ?case 
    apply(simp only: assms kmes_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node2 = Node1 \<longrightarrow> kme2 = kme2') \<and> (Node2 = Node2 \<longrightarrow> kme1 = kme1)" using assms by blast
qed


(*otherApp receives key*)
lemma
  assumes "app2 = IoaState (App False (AppProc Node1) (KmeProc Node2) keys) {}"
    and "app2' = IoaState (App False (AppProc Node1) (KmeProc Node2) (keys \<union> {(keyID, keyVal)})) {}"
    and "sender = KmeProc Node2"
    and "rcpt = AppProc Node2"
    and "msg = KeyResponse keyID keyVal"
    and "(sender, rcpt, msg) \<in> netw"
    and "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
    and "a = Receive sender rcpt msg"
    and "t = (apps app1 app2', kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)"
  shows "(s,a,t) \<in> trans_of SingleHop.System.ioa"
proof (rule trans_in_app_netw, goal_cases)
  case 1
  then show ?case using assms by blast
  case 2
  then show "s = (apps app1 app2, kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)" using assms by blast
  case 3
  then show "t = (apps app1 app2', kmes kme1 kme2, bridges bridge1 bridge2, qkd, netw)" using assms by blast
  case 4
  then show "Node2 \<in> c_nodes" using c_nodes_def by blast
  case 5
  then show "app s Node2 \<midarrow>a\<midarrow>SingleHop.app.ioa Node2\<rightarrow> app t Node2"
    apply(simp only: assms apps_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    using QKD_App.app_step.Slave_KeyResponse[of "AppProc Node1" "KmeProc Node2" keys sender rcpt keyID keyVal] assms
    unfolding c_appID_def by simp
  case 6
  then show ?case
    apply(simp only: assms apps_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node2 = Node1 \<longrightarrow> app2 = app2') \<and> (Node2 = Node2 \<longrightarrow> app1 = app1)" using assms by blast
qed

end