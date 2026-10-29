theory QKD_inv_def
  imports QKD_Datatypes
begin

abbreviation app where
  \<open>app s n \<equiv> (fst s) n\<close>

abbreviation kme where
  \<open>kme s n \<equiv> (fst (snd s)) n\<close>

abbreviation bridge where
  \<open>bridge s n bridgeID \<equiv> (fst (snd (snd s))) (n, bridgeID)\<close>

abbreviation qkd_layer where
  \<open>qkd_layer s \<equiv> fst (snd (snd (snd s)))\<close>

abbreviation network where
  \<open>network s \<equiv> snd (snd (snd (snd s)))\<close>

fun kme_has_key where
  \<open>kme_has_key (IoaState (Kme store _ _ _) _) keyID keyVal = (\<exists>a b c. store(keyID) = Some (Some keyVal, a, b, c))\<close> |
  \<open>kme_has_key (IoaState (KmeWaitReserve _ _ store _ _ _) _) keyID keyVal = (\<exists>a b c. store(keyID) = Some (Some keyVal, a, b, c))\<close> |
  \<open>kme_has_key (IoaState (KmeWaitHop _ _ _ _ _ store _ _ _) _) keyID keyVal = (\<exists>a b c. store(keyID) = Some (Some keyVal, a, b, c))\<close> |
  \<open>kme_has_key (IoaState (KmeWaitHopRec _ _ _ _ _ _ _ store _ _ _) _) keyID keyVal = (\<exists>a b c. store(keyID) = Some (Some keyVal, a, b, c))\<close>

definition key_consistent where
  \<open>key_consistent nodes s \<longleftrightarrow>
    (\<forall>n1 n2 msgs1 msgs2 master1 master2 oSae1 oSae2 kme1 kme2 store1 store2 keyID keyVal1 keyVal2.
      n1 \<in> nodes \<and> 
      n2 \<in> nodes \<and> 
      app s n1 = IoaState (App master1 oSae1 kme1 store1) msgs1 \<and>
      app s n2 = IoaState (App master2 oSae2 kme2 store2) msgs2 \<and>
      (keyID, keyVal1) \<in> store1 \<and>
      (keyID, keyVal2) \<in> store2
      \<longrightarrow> keyVal1 = keyVal2)\<close>

definition app_key_sent where
  \<open>app_key_sent nodes appID s \<longleftrightarrow>
    (\<forall>n master oSae kme store msgs keyID keyVal.
      n \<in> nodes \<and>
      app s n = IoaState (App master oSae kme store) msgs \<and>
      (keyID, keyVal) \<in> store
      \<longrightarrow> (kme, appID n, KeyResponse keyID keyVal) \<in> network s)\<close>

definition app_kme_field_valid where
  \<open>app_kme_field_valid nodes kmeID s \<longleftrightarrow>
    (\<forall>n master oSae kme store msgs.
      n \<in> nodes \<and>
      app s n = IoaState (App master oSae kme store) msgs
      \<longrightarrow> kme \<in> kmeID ` nodes)\<close>

definition kme_app_send_consistent where
  \<open>kme_app_send_consistent nodes appID kmeID s \<longleftrightarrow>
    (\<forall>s1 s2 r1 r2 keyID keyVal1 keyVal2.
      s1 \<in> kmeID ` nodes \<and>
      s2 \<in> kmeID ` nodes \<and>
      r1 \<in> appID ` nodes \<and>
      r2 \<in> appID ` nodes \<and>
      (s1, r1, KeyResponse keyID keyVal1) \<in> network s \<and>
      (s2, r2, KeyResponse keyID keyVal2) \<in> network s
      \<longrightarrow> keyVal1 = keyVal2)\<close>

(*not used right now - needs further invariants*)
definition kme_app_msg_sent where
  \<open>kme_app_msg_sent nodes appID kmeID bridgeIDs s \<longleftrightarrow>
    (\<forall>s1 r1 keyID keyVal.
      s1 \<in> kmeID ` nodes \<and>
      r1 \<in> appID ` nodes \<and>
      (s1, r1, KeyResponse keyID keyVal) \<in> network s
      \<longrightarrow> (\<exists>s2 r2 otherKme. 
            s2 \<in> \<Union>(bridgeIDs ` nodes) \<and>
            r2 \<in> kmeID ` nodes \<and>
            (s2, r2, KMPost otherKme keyID keyVal) \<in> network s))\<close>

(*not used right now*)
definition bridge_kme_send_consistent where
  \<open>bridge_kme_send_consistent nodes kmeID bridgeIDs s \<longleftrightarrow>
    (\<forall>s1 s2 r1 r2 otherKme1 otherKme2 keyID keyVal1 keyVal2.
      s1 \<in> \<Union>(bridgeIDs ` nodes) \<and>
      s2 \<in> \<Union>(bridgeIDs ` nodes) \<and>
      r1 \<in> kmeID ` nodes \<and>
      r2 \<in> kmeID ` nodes \<and>
      (s1, r1, KMPost otherKme1 keyID keyVal1) \<in> network s \<and>
      (s2, r2, KMPost otherKme2 keyID keyVal2) \<in> network s
      \<longrightarrow> keyVal1 = keyVal2)\<close>

definition bridge_kme_msg_sent where
  \<open>bridge_kme_msg_sent nodes kmeID bridgeIDs qkdID s \<longleftrightarrow>
    (\<forall>s1 r1 otherKme keyID keyVal.
      s1 \<in> \<Union>(bridgeIDs ` nodes) \<and>
      r1 \<in> kmeID ` nodes \<and>
      (s1, r1, KMPost otherKme keyID keyVal) \<in> network s
      \<longrightarrow> (\<exists>s2 r2. 
            s2 \<in> qkdID ` \<Union>(bridgeIDs ` nodes) \<and>
            r2 \<in> \<Union>(bridgeIDs ` nodes) \<and>
            (s2, r2, KeyResponse keyID keyVal) \<in> network s))\<close>

definition bridge_kme_buffer_sent where
  \<open>bridge_kme_buffer_sent nodes kmeID bridgeIDs qkdID s \<longleftrightarrow>
    (\<forall>n b state msgs otherKme rcpt keyID keyVal.
      n \<in> nodes \<and>
      b \<in> bridgeIDs n \<and>
      bridge s n b = IoaState state msgs \<and>
      (b, rcpt, KMPost otherKme keyID keyVal) \<in> msgs
      \<longrightarrow> (\<exists>s2 r2.
            s2 \<in> qkdID ` \<Union> (bridgeIDs ` nodes) \<and> 
            r2 \<in> \<Union> (bridgeIDs ` nodes) \<and> 
            (s2, r2, KeyResponse keyID keyVal) \<in> network s))\<close>

definition qkd_bridge_send_consistent where
  \<open>qkd_bridge_send_consistent nodes bridgeIDs qkdID s \<longleftrightarrow>
    (\<forall>s1 s2 r1 r2 keyID keyVal1 keyVal2.
      s1 \<in> qkdID ` \<Union>(bridgeIDs ` nodes) \<and>
      s2 \<in> qkdID ` \<Union>(bridgeIDs ` nodes) \<and>
      r1 \<in> \<Union>(bridgeIDs ` nodes) \<and>
      r2 \<in> \<Union>(bridgeIDs ` nodes) \<and>
      (s1, r1, KeyResponse keyID keyVal1) \<in> network s \<and>
      (s2, r2, KeyResponse keyID keyVal2) \<in> network s
      \<longrightarrow> keyVal1 = keyVal2)\<close>

definition qkd_bridge_msg_sent where
  \<open>qkd_bridge_msg_sent nodes bridgeIDs qkdID s \<longleftrightarrow>
    (\<forall>s1 r1 keyID keyVal.
      s1 \<in> qkdID ` \<Union>(bridgeIDs ` nodes) \<and>
      r1 \<in> \<Union>(bridgeIDs ` nodes) \<and>
      (s1, r1, KeyResponse keyID keyVal) \<in> network s
      \<longrightarrow> (\<exists>gen sent.
            qkd_layer s = QKD gen sent \<and>
            (keyID, keyVal) \<in> (snd ` gen \<union> sent)))\<close>

definition qkd_layer_consistent where
  \<open>qkd_layer_consistent s \<longleftrightarrow>
    (\<forall>gen sent keyID keyVal1 keyVal2.
      qkd_layer s = QKD gen sent \<and>
      (keyID, keyVal1) \<in> (snd ` gen \<union> sent) \<and>
      (keyID, keyVal2) \<in> (snd ` gen \<union> sent)
      \<longrightarrow> keyVal1 = keyVal2)\<close>





definition kme_buffer_app_send_consistent where
  \<open>kme_buffer_app_send_consistent nodes appID kmeID s \<longleftrightarrow>
    (\<forall>n state msgs s1 s2 r1 r2 keyID keyVal1 keyVal2.
      n \<in> nodes \<and>
      kme s n = IoaState state msgs \<and>
      s2 \<in> kmeID ` nodes \<and>
      r1 \<in> appID ` nodes \<and>
      r2 \<in> appID ` nodes \<and>
      (s1,r1,KeyResponse keyID keyVal1) \<in> msgs \<and>
      (s2,r2,KeyResponse keyID keyVal2) \<in> network s
      \<longrightarrow> keyVal1 = keyVal2)\<close>

definition kme_buffer_consistent where
 \<open>kme_buffer_consistent nodes appID s \<longleftrightarrow>
   (\<forall>n1 n2 state1 state2 msgs1 msgs2 s1 s2 r1 r2 keyID keyVal1 keyVal2.
            n1 \<in> nodes \<and>
            n2 \<in> nodes \<and>
            kme s n1 = IoaState state1 msgs1 \<and>
            kme s n2 = IoaState state2 msgs2 \<and>
            r1 \<in> appID ` nodes \<and>
            r2 \<in> appID ` nodes \<and>
            (s1, r1, KeyResponse keyID keyVal1) \<in> msgs1 \<and>
            (s2, r2, KeyResponse keyID keyVal2) \<in> msgs2
            \<longrightarrow> keyVal1 = keyVal2)\<close>

definition kme_store_buffer_consistent where
  \<open>kme_store_buffer_consistent nodes appID s \<longleftrightarrow>
    (\<forall>n1 n2 keyID state msgs sender rcpt keyVal1 keyVal2.
            n1 \<in> nodes \<and>
            n2 \<in> nodes \<and>
            kme_has_key (kme s n1) keyID keyVal1 \<and>
            kme s n2 = IoaState state msgs \<and>
            rcpt \<in> appID ` nodes \<and>
            (sender, rcpt, KeyResponse keyID keyVal2) \<in> msgs
            \<longrightarrow> keyVal1 = keyVal2)\<close>

definition kme_stores_consistent where
  \<open>kme_stores_consistent nodes s \<longleftrightarrow>
    (\<forall>n1 n2 keyID keyVal1 keyVal2. 
      n1 \<in> nodes \<and>
      n2 \<in> nodes \<and>
      kme_has_key (kme s n1) keyID keyVal1 \<and>
      kme_has_key (kme s n2) keyID keyVal2
      \<longrightarrow> keyVal1 = keyVal2)\<close>

end