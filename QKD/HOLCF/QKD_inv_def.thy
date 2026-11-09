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
  \<open>network s \<equiv> (snd (snd (snd (snd s))))\<close>

fun kme_has_key where
  \<open>kme_has_key (IoaState (Kme store _ _ _ _) _) keyID keyVal = (\<exists>a b c. store(keyID) = Some (Some keyVal, a, b, c))\<close> |
  \<open>kme_has_key (IoaState (KmeWaitReserve _ _ store _ _ _ _) _) keyID keyVal = (\<exists>a b c. store(keyID) = Some (Some keyVal, a, b, c))\<close> |
  \<open>kme_has_key (IoaState (KmeWaitHop _ _ _ _ _ store _ _ _ _) _) keyID keyVal = (\<exists>a b c. store(keyID) = Some (Some keyVal, a, b, c))\<close> |
  \<open>kme_has_key (IoaState (KmeWaitHopRec _ _ _ _ _ _ _ store _ _ _ _) _) keyID keyVal = (\<exists>a b c. store(keyID) = Some (Some keyVal, a, b, c))\<close>

fun kme_get_store where
  \<open>kme_get_store (IoaState (Kme store _ _ _ _) _) = store\<close> |
  \<open>kme_get_store (IoaState (KmeWaitReserve _ _ store _ _ _ _) _) = store\<close> |
  \<open>kme_get_store (IoaState (KmeWaitHop _ _ _ _ _ store _ _ _ _) _) = store\<close> |
  \<open>kme_get_store (IoaState (KmeWaitHopRec _ _ _ _ _ _ _ store _ _ _ _) _) = store\<close>

fun kme_get_bridgeIDs_field where
  \<open>kme_get_bridgeIDs_field (IoaState (Kme _ _ _ bridgeIDs _) _) = bridgeIDs\<close> |
  \<open>kme_get_bridgeIDs_field (IoaState (KmeWaitReserve _ _ _ _ _ bridgeIDs _) _) = bridgeIDs\<close> |
  \<open>kme_get_bridgeIDs_field (IoaState (KmeWaitHop _ _ _ _ _ _ _ _ bridgeIDs _) _) = bridgeIDs\<close> |
  \<open>kme_get_bridgeIDs_field (IoaState (KmeWaitHopRec _ _ _ _ _ _ _ _ _ _ bridgeIDs _) _) = bridgeIDs\<close>

abbreviation qkd_has_key where
  \<open>qkd_has_key s keyID keyVal \<equiv> \<exists>gen sent. (qkd_layer s = QKD gen sent) \<and> (keyID, keyVal) \<in> (snd ` gen \<union> sent)\<close>

abbreviation network_has_msg where
  \<open>network_has_msg s sender rcpt msg \<equiv> msg \<in> (set ((network s) (sender, rcpt)))\<close>

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
  \<open>app_key_sent nodes s \<longleftrightarrow>
    (\<forall>n master oSae kme store msgs keyID keyVal.
      n \<in> nodes \<and>
      app s n = IoaState (App master oSae kme store) msgs \<and>
      (keyID, keyVal) \<in> store
      \<longrightarrow> qkd_has_key s keyID keyVal)\<close>

definition app_kme_field_valid where
  \<open>app_kme_field_valid nodes kmeID s \<longleftrightarrow>
    (\<forall>n master oSae kme store msgs.
      n \<in> nodes \<and>
      app s n = IoaState (App master oSae kme store) msgs
      \<longrightarrow> kme \<in> kmeID ` nodes)\<close>

definition kme_app_msg_sent where
  \<open>kme_app_msg_sent nodes appID kmeID s \<longleftrightarrow>
    (\<forall>s1 r1 keyID keyVal.
      s1 \<in> kmeID ` nodes \<and>
      r1 \<in> appID ` nodes \<and>
      network_has_msg (network s) s1 r1 (KeyResponse keyID keyVal)
      \<longrightarrow> qkd_has_key s keyID keyVal)\<close>

definition kme_app_buffer_sent where
  \<open>kme_app_buffer_sent nodes appID kmeID s \<longleftrightarrow>
    (\<forall>n state msgs keyID keyVal.
      n \<in> nodes \<and>
      kme s n = IoaState state msgs \<and>
      (kmeID n, appID n, KeyResponse keyID keyVal) \<in> msgs
      \<longrightarrow> qkd_has_key s keyID keyVal)\<close>

definition kme_store_partnerField_valid where
  \<open>kme_store_partnerField_valid nodes kmeID s \<longleftrightarrow>
    (\<forall>n keyID keyVal partner conf res.
      n \<in> nodes \<and>
      kme_get_store (kme s n) keyID = Some (Some keyVal, partner, conf, res)
      \<longrightarrow> partner \<in> kmeID ` nodes)\<close>

(*Proofed till here*)
definition kme_store_key_sent where
  \<open>kme_store_key_sent nodes kmeID s \<longleftrightarrow>
    (\<forall>n keyID keyVal.
      n \<in> nodes \<and>
      kme_has_key (kme s n) keyID keyVal
      \<longrightarrow> qkd_has_key s keyID keyVal)\<close>

definition kme_bridgeIDs_field_valid where
  \<open>kme_bridgeIDs_field_valid nodes bridgeIDs s \<longleftrightarrow>
    (\<forall>n bridgeIDs'.
      n \<in> nodes \<and>
      bridgeIDs' = kme_get_bridgeIDs_field (kme s n)
      \<longrightarrow> bridgeIDs' = bridgeIDs n)\<close>

definition bridge_kme_msg_sent where
  \<open>bridge_kme_msg_sent nodes kmeID bridgeIDs s \<longleftrightarrow>
    (\<forall>s1 r1 otherKme keyID keyVal.
      s1 \<in> \<Union>(bridgeIDs ` nodes) \<and>
      r1 \<in> kmeID ` nodes \<and>
      network_has_msg s s1 r1 (KMPost otherKme keyID keyVal)
      \<longrightarrow> qkd_has_key s keyID keyVal)\<close>

definition bridge_kme_buffer_sent where
  \<open>bridge_kme_buffer_sent nodes bridgeIDs s \<longleftrightarrow>
    (\<forall>n b state msgs otherKme rcpt keyID keyVal.
      n \<in> nodes \<and>
      b \<in> bridgeIDs n \<and>
      bridge s n b = IoaState state msgs \<and>
      (b, rcpt, KMPost otherKme keyID keyVal) \<in> msgs
      \<longrightarrow> qkd_has_key s keyID keyVal)\<close>

definition bridge_qkd_field_valid where
  \<open>bridge_qkd_field_valid nodes bridgeIDs qkdID s \<longleftrightarrow>
    (\<forall>n b isMaster masterBridge otherKme qkd kme msgs.
      n \<in> nodes \<and>
      b \<in> bridgeIDs n \<and>
      bridge s n b = IoaState (Bridge isMaster masterBridge otherKme qkd kme) msgs
      \<longrightarrow> qkd \<in> qkdID ` \<Union> (bridgeIDs ` nodes))\<close>

definition qkd_bridge_msg_sent where
  \<open>qkd_bridge_msg_sent nodes bridgeIDs qkdID s \<longleftrightarrow>
    (\<forall>s1 r1 keyID keyVal.
      s1 \<in> qkdID ` \<Union>(bridgeIDs ` nodes) \<and>
      r1 \<in> \<Union>(bridgeIDs ` nodes) \<and>
      network_has_msg s s1 r1 (KeyResponse keyID keyVal)
      \<longrightarrow> qkd_has_key s keyID keyVal)\<close>

definition qkd_layer_consistent where
  \<open>qkd_layer_consistent s \<longleftrightarrow>
    (\<forall>keyID keyVal1 keyVal2.
      qkd_has_key s keyID keyVal1 \<and>
      qkd_has_key s keyID keyVal2
      \<longrightarrow> keyVal1 = keyVal2)\<close>

end