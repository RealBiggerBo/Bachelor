theory QKD_Interpretation_4Hop_KeyRelay
  imports QKD_Interpretation_4Hop_Trans_Helpers
begin

(* KME2 receives GetKeyWithID from app2; keyID not found; sends KMPut to reserve hop-key keyID2 with KME3 and enters KmeWaitHop )
( Rule: GetKeyWithID_IDNotFound *)
lemma
  assumes "kme2 = IoaState (Kme store_init (c_route Node2) c_saeToKme) {}"
  assumes "kme2' = IoaState (KmeWaitHop (AppProc Node4) sender (KmeProc Node3) keyID id2_3 store_init (c_route Node2) c_saeToKme) 
        {(KmeProc Node2, KmeProc Node3, KMPut rcpt id2_3 (Some rcpt))}"
    and "store_init = (\<lambda>id. None)(id2_3 := Some (Some val2_3, KmeProc Node3, True, None))"
    and "id2_3 \<noteq> keyID"
    and "sender = AppProc Node2"
    and "rcpt = KmeProc Node2"
    and "msg = GetKeyWithID (KmeProc Node2) (AppProc Node4) keyID"
    and "(sender, rcpt, msg) \<in> netw"
    and "s = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)"
    and "a = Receive sender rcpt msg"
    and "t = (apps app1 app2 app4 app4, kmes kme1 kme2' kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)"
  shows "(s,a,t) \<in> trans_of Line4Hop.System.ioa"
proof (rule trans_in_kme_netw, goal_cases)
  case 1
  then show ?case 
    using assms by blast
  case 2
  then show "s = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)" 
    using assms by blast
  case 3
  then show "t = (apps app1 app2 app4 app4, kmes kme1 kme2' kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)" 
    using assms by blast
  case 4
  then show "Node2 \<in> c_nodes" 
    using c_nodes_def by blast
  case 5
  have "store_init keyID = None"
    using assms(3,4) by force
  moreover have "(c_route Node2) (AppProc Node4) = (KmeProc Node3)"
    unfolding c_route_def by fastforce
  moreover have "store_init id2_3 = Some (Some val2_3, KmeProc Node3, True, None)"
    using assms(3) by auto
  ultimately show "kme s Node2 \<midarrow>a\<midarrow>Line4Hop.kme.ioa Node2\<rightarrow> kme t Node2"
    apply(simp only: assms kmes_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    using GetKeyWithID_IDNotFound[of store_init keyID "c_route Node2" "AppProc Node4" "KmeProc Node3" id2_3 val2_3 c_enc c_dec c_saeToKme sender rcpt rcpt] assms
    unfolding c_saeToKme_def apply simp
    by auto
  case 6
  then show "network s \<midarrow>a\<midarrow>Line4Hop.network.ioa\<rightarrow> network t" 
    apply(simp only: assms kmes_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node2 = Node1 \<longrightarrow> kme2 = kme2' \<and> kme3 = kme3 \<and> kme4 = kme4) \<and>
              (Node2 = Node2 \<longrightarrow> kme1 = kme1 \<and> kme3 = kme3 \<and> kme4 = kme4) \<and>
              (Node2 = Node3 \<longrightarrow> kme1 = kme1 \<and> kme2 = kme2' \<and> kme4 = kme4) \<and>
              (Node2 = Node4 \<longrightarrow> kme1 = kme1 \<and> kme2 = kme2' \<and> kme3 = kme3)" 
    using assms by blast
qed

(* KME3 receives KMPut from KME2; reserves hop-key keyID2 and sends OK back to KME2 )
( Rule: KMPut_Reserve *)
lemma
  assumes "kme3 = IoaState (Kme store_init (c_route Node3) c_saeToKme) {}"
  assumes "kme3' = IoaState (Kme store' (c_route Node3) c_saeToKme) 
        {(KmeProc Node3, sender, OK)}"
    and "store_init = (\<lambda>id. None)(id2_3 := Some (Some val2_3, KmeProc Node2, True, None), id3_4 := Some (Some val3_4, KmeProc Node4, True, None))"
    and "store' = keyStore_reserve store_init id2_3 sender"
    and "id2_3 \<noteq> keyID \<and> id3_4 \<noteq> keyID \<and> id2_3 \<noteq> id3_4"
    and "sender = KmeProc Node2"
    and "rcpt = KmeProc Node3"
    and "msg = KMPut sender id2_3 (Some sender)"
    and "(sender, rcpt, msg) \<in> netw"
    and "s = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)"
    and "a = Receive sender rcpt msg"
    and "t = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3' kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)"
  shows "(s,a,t) \<in> trans_of Line4Hop.System.ioa"
proof (rule trans_in_kme_netw, goal_cases)
  case 1
  then show ?case 
    using assms by blast
  case 2
  then show "s = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)" 
    using assms by blast
  case 3
  then show "t = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3' kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)" 
    using assms by blast
  case 4
  then show "Node3 \<in> c_nodes" 
    using c_nodes_def by blast
  case 5
  then show "kme s Node3 \<midarrow>a\<midarrow>Line4Hop.kme.ioa Node3\<rightarrow> kme t Node3"
    apply(simp only: assms kmes_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    using KMPut_Reserve[of c_enc c_dec store_init "c_route Node3" c_saeToKme sender rcpt sender id2_3 sender] assms
    unfolding c_saeToKme_def apply simp
    by auto
  case 6
  then show "network s \<midarrow>a\<midarrow>Line4Hop.network.ioa\<rightarrow> network t" 
    apply(simp only: assms kmes_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node3 = Node1 \<longrightarrow> kme2 = kme2 \<and> kme3 = kme3' \<and> kme4 = kme4) \<and>
              (Node3 = Node2 \<longrightarrow> kme1 = kme1 \<and> kme3 = kme3' \<and> kme4 = kme4) \<and>
              (Node3 = Node3 \<longrightarrow> kme1 = kme1 \<and> kme2 = kme2 \<and> kme4 = kme4) \<and>
              (Node3 = Node4 \<longrightarrow> kme1 = kme1 \<and> kme2 = kme2 \<and> kme3 = kme3')" 
    using assms by blast
qed


(* KME2 receives OK from KME3; sends KMGet to KME3 requesting keyID via reserved hop-key keyID2 )
( Rule: GetKeyWithID_IDNotFound_Reserved *)
lemma
  assumes "kme2 = IoaState (KmeWaitHop (AppProc Node4) (AppProc Node2) (KmeProc Node3) keyID id2_3 store_init (c_route Node2) c_saeToKme) {}"
  assumes "kme2' = IoaState (KmeWaitHop (AppProc Node4) (AppProc Node2) (KmeProc Node3) keyID id2_3 store_init (c_route Node2) c_saeToKme) 
        {(KmeProc Node2, KmeProc Node3, KMGet (AppProc Node4) keyID id2_3 (AppProc Node2))}"
    and "store_init = (\<lambda>id. None)(id2_3 := Some (Some val2_3, KmeProc Node3, True, None))"
    and "id2_3 \<noteq> keyID"
    and "sender = KmeProc Node3"
    and "rcpt = KmeProc Node2"
    and "msg = OK"
    and "(sender, rcpt, msg) \<in> netw"
    and "s = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)"
    and "a = Receive sender rcpt msg"
    and "t = (apps app1 app2 app4 app4, kmes kme1 kme2' kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)"
  shows "(s,a,t) \<in> trans_of Line4Hop.System.ioa"
proof (rule trans_in_kme_netw, goal_cases)
  case 1
  then show ?case 
    using assms by blast
  case 2
  then show "s = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)" 
    using assms by blast
  case 3
  then show "t = (apps app1 app2 app4 app4, kmes kme1 kme2' kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)" 
    using assms by blast
  case 4
  then show "Node2 \<in> c_nodes" 
    using c_nodes_def by blast
  case 5
  then show "kme s Node2 \<midarrow>a\<midarrow>Line4Hop.kme.ioa Node2\<rightarrow> kme t Node2"
    apply(simp only: assms kmes_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    using GetKeyWithID_IDNotFound_Reserved[of c_enc c_dec "AppProc Node4" "AppProc Node2" "KmeProc Node3" keyID id2_3 store_init "c_route Node2" c_saeToKme rcpt] assms
    unfolding c_saeToKme_def apply simp
    by auto
  case 6
  then show "network s \<midarrow>a\<midarrow>Line4Hop.network.ioa\<rightarrow> network t" 
    apply(simp only: assms kmes_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node2 = Node1 \<longrightarrow> kme2 = kme2' \<and> kme3 = kme3 \<and> kme4 = kme4) \<and>
              (Node2 = Node2 \<longrightarrow> kme1 = kme1 \<and> kme3 = kme3 \<and> kme4 = kme4) \<and>
              (Node2 = Node3 \<longrightarrow> kme1 = kme1 \<and> kme2 = kme2' \<and> kme4 = kme4) \<and>
              (Node2 = Node4 \<longrightarrow> kme1 = kme1 \<and> kme2 = kme2' \<and> kme3 = kme3)" 
    using assms by blast
qed

(* KME3 receives KMGet from KME2; keyID not found; sends KMPut to reserve hop-key keyID3 with KME4 and enters KmeWaitHopRec )
( Rule: KMGetKeyWithID_IDNotFound *)
lemma
  assumes "kme3 = IoaState (Kme store (c_route Node3) c_saeToKme) {}"
  assumes "kme3' = IoaState (KmeWaitHopRec id3_4 (AppProc Node4) (AppProc Node2) sender (KmeProc Node4) keyID id2_3 store (c_route Node3) c_saeToKme) 
        {(KmeProc Node3, KmeProc Node4, KMPut rcpt id3_4 (Some rcpt))}"
    and "store_init = (\<lambda>id. None)(id2_3 := Some (Some val2_3, KmeProc Node2, True, None), id3_4 := Some (Some val3_4, KmeProc Node4, True, None))"
    and "store = keyStore_reserve store_init id2_3 (KmeProc Node2)"
    and "id2_3 \<noteq> keyID \<and> id3_4 \<noteq> keyID \<and> id2_3 \<noteq> id3_4"
    and "sender = KmeProc Node2"
    and "rcpt = KmeProc Node3"
    and "msg = KMGet (AppProc Node4) keyID id2_3 (AppProc Node2)"
    and "(sender, rcpt, msg) \<in> netw"
    and "s = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)"
    and "a = Receive sender rcpt msg"
    and "t = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3' kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)"
  shows "(s,a,t) \<in> trans_of Line4Hop.System.ioa"
proof (rule trans_in_kme_netw, goal_cases)
  case 1
  then show ?case 
    using assms by blast
  case 2
  then show "s = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)" 
    using assms by blast
  case 3
  then show "t = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3' kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)" 
    using assms by blast
  case 4
  then show "Node3 \<in> c_nodes" 
    using c_nodes_def by blast
  case 5
  have "store keyID = None"
    using assms(3,4,5) by force
  moreover have "store id2_3 = Some (Some val2_3, KmeProc Node2, True, Some (KmeProc Node2))"
    using assms(3,4,5) by auto
  moreover have "(c_route Node3) (AppProc Node4) = (KmeProc Node4)"
    unfolding c_route_def by force
  moreover have "store_init id3_4 = Some (Some val3_4, KmeProc Node4, True, None)"
    using assms(3,4) by auto
  ultimately show "kme s Node3 \<midarrow>a\<midarrow>Line4Hop.kme.ioa Node3\<rightarrow> kme t Node3"
    apply(simp only: assms kmes_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    using KMGetKeyWithID_IDNotFound[of store keyID id2_3 val2_3 sender "c_route Node3" "AppProc Node4" "KmeProc Node4" id3_4 val3_4 c_enc c_dec c_saeToKme rcpt "AppProc Node2"] assms
    unfolding c_saeToKme_def c_route_def apply simp
    by auto
  case 6
  then show "network s \<midarrow>a\<midarrow>Line4Hop.network.ioa\<rightarrow> network t" 
    apply(simp only: assms kmes_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node3 = Node1 \<longrightarrow> kme2 = kme2 \<and> kme3 = kme3' \<and> kme4 = kme4) \<and>
              (Node3 = Node2 \<longrightarrow> kme1 = kme1 \<and> kme3 = kme3' \<and> kme4 = kme4) \<and>
              (Node3 = Node3 \<longrightarrow> kme1 = kme1 \<and> kme2 = kme2 \<and> kme4 = kme4) \<and>
              (Node3 = Node4 \<longrightarrow> kme1 = kme1 \<and> kme2 = kme2 \<and> kme3 = kme3')" 
    using assms by blast
qed


(* KME4 receives KMPut from KME3; reserves hop-key keyID3 and sends OK back to KME3 )
( Rule: KMPut_Reserve *)
lemma
  assumes "kme4 = IoaState (Kme store_init (c_route Node4) c_saeToKme) {}"
  assumes "kme4' = IoaState (Kme store' (c_route Node4) c_saeToKme) 
        {(KmeProc Node4, sender, OK)}"
    and "store_init = (\<lambda>id. None)(id3_4 := Some (Some val3_4, KmeProc Node3, True, None), keyID := Some (Some val, c_saeToKme (AppProc Node4), True, None))"
    and "store' = keyStore_reserve store_init id3_4 sender"
    and "id3_4 \<noteq> keyID"
    and "sender = KmeProc Node3"
    and "rcpt = KmeProc Node4"
    and "msg = KMPut sender id3_4 (Some sender)"
    and "(sender, rcpt, msg) \<in> netw"
    and "s = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)"
    and "a = Receive sender rcpt msg"
    and "t = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4', bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)"
  shows "(s,a,t) \<in> trans_of Line4Hop.System.ioa"
proof (rule trans_in_kme_netw, goal_cases)
  case 1
  then show ?case 
    using assms by blast
  case 2
  then show "s = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)" 
    using assms by blast
  case 3
  then show "t = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4', bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)" 
    using assms by blast
  case 4
  then show "Node4 \<in> c_nodes" 
    using c_nodes_def by blast
  case 5
  then show "kme s Node4 \<midarrow>a\<midarrow>Line4Hop.kme.ioa Node4\<rightarrow> kme t Node4"
    apply(simp only: assms kmes_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    using KMPut_Reserve[of c_enc c_dec store_init "c_route Node4" c_saeToKme sender rcpt sender id3_4 sender] assms
    unfolding c_saeToKme_def apply simp
    by auto
  case 6
  then show "network s \<midarrow>a\<midarrow>Line4Hop.network.ioa\<rightarrow> network t" 
    apply(simp only: assms kmes_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node4 = Node1 \<longrightarrow> kme2 = kme2 \<and> kme3 = kme3 \<and> kme4 = kme4') \<and>
              (Node4 = Node2 \<longrightarrow> kme1 = kme1 \<and> kme3 = kme3 \<and> kme4 = kme4') \<and>
              (Node4 = Node3 \<longrightarrow> kme1 = kme1 \<and> kme2 = kme2 \<and> kme4 = kme4') \<and>
              (Node4 = Node4 \<longrightarrow> kme1 = kme1 \<and> kme2 = kme2 \<and> kme3 = kme3)" 
    using assms by blast
qed


(* KME3 receives OK from KME4; sends KMGet to KME4 requesting keyID via reserved hop-key keyID3 )
( Rule: KMGetKeyWithID_IDNotFound_Reserved *)
lemma
  assumes "kme3 = IoaState (KmeWaitHopRec id3_4 (AppProc Node4) (AppProc Node2) (KmeProc Node2) (KmeProc Node4) keyID id2_3 store (c_route Node3) c_saeToKme) {}"
  assumes "kme3' = IoaState (KmeWaitHopRec id3_4 (AppProc Node4) (AppProc Node2) (KmeProc Node2) (KmeProc Node4) keyID id2_3 store (c_route Node3) c_saeToKme) 
        {(KmeProc Node3, KmeProc Node4, KMGet (AppProc Node4) keyID id3_4 (AppProc Node2))}"
    and "store_init = (\<lambda>id. None)(id2_3 := Some (Some val2_3, KmeProc Node2, True, None), id3_4 := Some (Some val3_4, KmeProc Node4, True, None))"
    and "store = keyStore_reserve store_init id2_3 (KmeProc Node2)"
    and "id2_3 \<noteq> keyID \<and> id3_4 \<noteq> keyID \<and> id2_3 \<noteq> id3_4"
    and "sender = KmeProc Node4"
    and "rcpt = KmeProc Node3"
    and "msg = OK"
    and "(sender, rcpt, msg) \<in> netw"
    and "s = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)"
    and "a = Receive sender rcpt msg"
    and "t = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3' kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)"
  shows "(s,a,t) \<in> trans_of Line4Hop.System.ioa"
proof (rule trans_in_kme_netw, goal_cases)
  case 1
  then show ?case 
    using assms by blast
  case 2
  then show "s = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)" 
    using assms by blast
  case 3
  then show "t = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3' kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)" 
    using assms by blast
  case 4
  then show "Node3 \<in> c_nodes" 
    using c_nodes_def by blast
  case 5
  then show "kme s Node3 \<midarrow>a\<midarrow>Line4Hop.kme.ioa Node3\<rightarrow> kme t Node3"
    apply(simp only: assms kmes_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    using KMGetKeyWithID_IDNotFound_Reserved[of c_enc c_dec id3_4 "AppProc Node4" "AppProc Node2" "KmeProc Node2" "KmeProc Node4" keyID id2_3 store "c_route Node3" c_saeToKme rcpt ] assms
    unfolding c_saeToKme_def apply simp
    by auto
  case 6
  then show "network s \<midarrow>a\<midarrow>Line4Hop.network.ioa\<rightarrow> network t" 
    apply(simp only: assms kmes_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node3 = Node1 \<longrightarrow> kme2 = kme2 \<and> kme3 = kme3' \<and> kme4 = kme4) \<and>
              (Node3 = Node2 \<longrightarrow> kme1 = kme1 \<and> kme3 = kme3' \<and> kme4 = kme4) \<and>
              (Node3 = Node3 \<longrightarrow> kme1 = kme1 \<and> kme2 = kme2 \<and> kme4 = kme4) \<and>
              (Node3 = Node4 \<longrightarrow> kme1 = kme1 \<and> kme2 = kme2 \<and> kme3 = kme3')" 
    using assms by blast
qed


(* KME4 receives KMGet from KME3; keyID is found; removes keyID and hop-key keyID3 from store, encrypts val with hop-key val3, and sends KeyResponse (enc val val3) to KME3 )
( Rule: KMGetKeyWithID_IDFound *)
lemma
  assumes "kme4 = IoaState (Kme store (c_route Node4) c_saeToKme) {}"
  assumes "kme4' = IoaState (Kme store' (c_route Node4) c_saeToKme) 
        {(KmeProc Node4, sender, KeyResponse keyID (c_enc val val3_4))}"
    and "store_init = (\<lambda>id. None)(id3_4 := Some (Some val3_4, KmeProc Node3, True, None), keyID := Some (Some val, c_saeToKme (AppProc Node4), True, Some (AppProc Node2)))"
    and "store = keyStore_reserve store_init id3_4 sender"
    and "store' = keyStore_remove (keyStore_remove store keyID) id3_4"
    and "id3_4 \<noteq> keyID"
    and "sender = KmeProc Node3"
    and "rcpt = KmeProc Node4"
    and "msg = KMGet (AppProc Node4) keyID id3_4 (AppProc Node2)"
    and "(sender, rcpt, msg) \<in> netw"
    and "s = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)"
    and "a = Receive sender rcpt msg"
    and "t = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4', bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)"
  shows "(s,a,t) \<in> trans_of Line4Hop.System.ioa"
proof (rule trans_in_kme_netw, goal_cases)
  case 1
  then show ?case 
    using assms by blast
  case 2
  then show "s = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)" 
    using assms by blast
  case 3
  then show "t = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4', bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)" 
    using assms by blast
  case 4
  then show "Node4 \<in> c_nodes" 
    using c_nodes_def by blast
  case 5
  have "store keyID = Some (Some val, c_saeToKme (AppProc Node4), True, Some (AppProc Node2))"
    using assms by auto
  moreover have "store id3_4 = Some (Some val3_4, KmeProc Node3, True, Some (KmeProc Node3))"
    using assms by auto
  ultimately show "kme s Node4 \<midarrow>a\<midarrow>Line4Hop.kme.ioa Node4\<rightarrow> kme t Node4"
    apply(simp only: assms kmes_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    using KMGetKeyWithID_IDFound[of store keyID val c_saeToKme "AppProc Node4" "AppProc Node2" id3_4 val3_4 sender c_enc c_dec "c_route Node4" rcpt] assms
    unfolding c_saeToKme_def c_route_def by auto
  case 6
  then show "network s \<midarrow>a\<midarrow>Line4Hop.network.ioa\<rightarrow> network t" 
    apply(simp only: assms kmes_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node4 = Node1 \<longrightarrow> kme2 = kme2 \<and> kme3 = kme3 \<and> kme4 = kme4') \<and>
              (Node4 = Node2 \<longrightarrow> kme1 = kme1 \<and> kme3 = kme3 \<and> kme4 = kme4') \<and>
              (Node4 = Node3 \<longrightarrow> kme1 = kme1 \<and> kme2 = kme2 \<and> kme4 = kme4') \<and>
              (Node4 = Node4 \<longrightarrow> kme1 = kme1 \<and> kme2 = kme2 \<and> kme3 = kme3)" 
    using assms by blast
qed

(* KME3 receives KeyResponse from KME4; decrypts payload with hop-key val3, re-encrypts val with hop-key val2, cleans up store, and sends KeyResponse (enc val val2) to KME2 )
( Rule: KMGetKeyWithID_IDNotFound_Return *)
lemma
  assumes "kme3 = IoaState (KmeWaitHopRec id3_4 (AppProc Node4) (AppProc Node2) original_sender (KmeProc Node4) keyID id2_3 store (c_route Node3) c_saeToKme) {}"
  assumes "kme3' = IoaState (Kme store' (c_route Node3) c_saeToKme) 
        {(KmeProc Node3, original_sender, KeyResponse keyID (c_enc (c_dec (c_enc val val3_4) val3_4) val2_3))}"
    and "store_init = (\<lambda>id. None)(id2_3 := Some (Some val2_3, KmeProc Node2, True, None), id3_4 := Some (Some val3_4, KmeProc Node4, True, None))"
    and "store = keyStore_reserve store_init id2_3 original_sender"
    and "store' = keyStore_remove (keyStore_remove store id2_3) id3_4"
    and "id2_3 \<noteq> keyID \<and> id3_4 \<noteq> keyID \<and> id2_3 \<noteq> id3_4"
    and "original_sender = KmeProc Node2"
    and "sender = KmeProc Node4"
    and "rcpt = KmeProc Node3"
    and "msg = KeyResponse keyID (c_enc val val3_4)"
    and "(sender, rcpt, msg) \<in> netw"
    and "s = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)"
    and "a = Receive sender rcpt msg"
    and "t = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3' kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)"
  shows "(s,a,t) \<in> trans_of Line4Hop.System.ioa"
proof (rule trans_in_kme_netw, goal_cases)
  case 1
  then show ?case 
    using assms by blast
  case 2
  then show "s = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)" 
    using assms by blast
  case 3
  then show "t = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3' kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)" 
    using assms by blast
  case 4
  then show "Node3 \<in> c_nodes" 
    using c_nodes_def by blast
  case 5
  have "store' = (\<lambda>id. None)" (*UNUSED; Just to verify*)
    using assms by simp
  have "store id2_3 = Some (Some val2_3, KmeProc Node2, True, Some (KmeProc Node2))"
    using assms by auto
  moreover have "store id3_4 = Some (Some val3_4, KmeProc Node4, True, None)"
    using assms by auto
  ultimately show "kme s Node3 \<midarrow>a\<midarrow>Line4Hop.kme.ioa Node3\<rightarrow> kme t Node3"
    apply(simp only: assms kmes_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    using KMGetKeyWithID_IDNotFound_Return[of store id2_3 val2_3 "KmeProc Node2" id3_4 val3_4 "KmeProc Node4" c_enc c_dec "AppProc Node4" "AppProc Node2" keyID "c_route Node3" c_saeToKme rcpt "c_enc val val3_4"] assms
    unfolding c_saeToKme_def apply simp
    by auto
  case 6
  then show "network s \<midarrow>a\<midarrow>Line4Hop.network.ioa\<rightarrow> network t" 
    apply(simp only: assms kmes_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node3 = Node1 \<longrightarrow> kme2 = kme2 \<and> kme3 = kme3' \<and> kme4 = kme4) \<and>
              (Node3 = Node2 \<longrightarrow> kme1 = kme1 \<and> kme3 = kme3' \<and> kme4 = kme4) \<and>
              (Node3 = Node3 \<longrightarrow> kme1 = kme1 \<and> kme2 = kme2 \<and> kme4 = kme4) \<and>
              (Node3 = Node4 \<longrightarrow> kme1 = kme1 \<and> kme2 = kme2 \<and> kme3 = kme3')" 
    using assms by blast
qed

(* KME2 receives KeyResponse from KME3; decrypts payload with hop-key val2, cleans up store, and sends final KeyResponse keyID val to app2 )
( Rule: GetKeyWithID_IDNotFound_Return *)
lemma
  assumes "kme2 = IoaState (KmeWaitHop (AppProc Node4) (AppProc Node2) (KmeProc Node3) keyID id2_3 store_init (c_route Node2) c_saeToKme) {}"
  assumes "kme2' = IoaState (Kme store' (c_route Node2) c_saeToKme) 
        {(KmeProc Node2, original_sender, KeyResponse keyID (c_dec (c_enc val val2_3) val2_3))}"
    and "store_init = (\<lambda>id. None)(id2_3 := Some (Some val2_3, KmeProc Node3, True, None))"
    and "store' = keyStore_remove store_init id2_3"
    and "id2_3 \<noteq> keyID"
    and "original_sender = AppProc Node2"
    and "sender = KmeProc Node3"
    and "rcpt = KmeProc Node2"
    and "msg = KeyResponse keyID (c_enc val val2_3)"
    and "(sender, rcpt, msg) \<in> netw"
    and "s = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)"
    and "a = Receive sender rcpt msg"
    and "t = (apps app1 app2 app4 app4, kmes kme1 kme2' kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)"
  shows "(s,a,t) \<in> trans_of Line4Hop.System.ioa"
proof (rule trans_in_kme_netw, goal_cases)
  case 1
  then show ?case 
    using assms by blast
  case 2
  then show "s = (apps app1 app2 app4 app4, kmes kme1 kme2 kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)" 
    using assms by blast
  case 3
  then show "t = (apps app1 app2 app4 app4, kmes kme1 kme2' kme3 kme4, bridges bridge1_2 bridge2_1 bridge2_3 bridge3_2 bridge3_4 bridge4_3, qkd, netw)" 
    using assms by blast
  case 4
  then show "Node2 \<in> c_nodes" 
    using c_nodes_def by blast
  case 5
  have "store_init id2_3 = Some (Some val2_3, KmeProc Node3, True, None)"
    using assms by auto
  then show "kme s Node2 \<midarrow>a\<midarrow>Line4Hop.kme.ioa Node2\<rightarrow> kme t Node2"
    apply(simp only: assms kmes_def fst_conv snd_conv fun_upd_apply; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def apply simp
    using GetKeyWithID_IDNotFound_Return[of store_init id2_3 val2_3 sender c_enc c_dec "AppProc Node4" original_sender keyID "c_route Node2" c_saeToKme rcpt "c_enc val val2_3"] assms
    unfolding c_saeToKme_def apply simp
    by auto
  case 6
  then show "network s \<midarrow>a\<midarrow>Line4Hop.network.ioa\<rightarrow> network t" 
    apply(simp only: assms kmes_def fst_conv snd_conv c_isMaster_def; simp)
    unfolding c_bridgeOtherKme_def c_qkdID_def c_kmeID_def trans_of_def c_appID_def c_nodes_def apply simp
    unfolding c_bridgeIDs_def using assms by simp
  case 7
  then show "(Node2 = Node1 \<longrightarrow> kme2 = kme2' \<and> kme3 = kme3 \<and> kme4 = kme4) \<and>
              (Node2 = Node2 \<longrightarrow> kme1 = kme1 \<and> kme3 = kme3 \<and> kme4 = kme4) \<and>
              (Node2 = Node3 \<longrightarrow> kme1 = kme1 \<and> kme2 = kme2' \<and> kme4 = kme4) \<and>
              (Node2 = Node4 \<longrightarrow> kme1 = kme1 \<and> kme2 = kme2' \<and> kme3 = kme3)" 
    using assms by blast
qed

end