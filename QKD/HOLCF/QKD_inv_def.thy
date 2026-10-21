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
  \<open>kme_has_key (IoaState (Kme store _ _) _) keyID keyVal = (\<exists>a b c. store(keyID) = Some (Some keyVal, a, b, c))\<close> |
  \<open>kme_has_key (IoaState (KmeWaitReserve _ _ store _ _) _) keyID keyVal = (\<exists>a b c. store(keyID) = Some (Some keyVal, a, b, c))\<close> |
  \<open>kme_has_key (IoaState (KmeWaitHop _ _ _ _ _ store _ _) _) keyID keyVal = (\<exists>a b c. store(keyID) = Some (Some keyVal, a, b, c))\<close> |
  \<open>kme_has_key (IoaState (KmeWaitHopRec _ _ _ _ _ _ _ store _ _) _) keyID keyVal = (\<exists>a b c. store(keyID) = Some (Some keyVal, a, b, c))\<close>

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
  \<open>app_key_sent nodes kmeID appID s \<longleftrightarrow>
    (\<forall>n master oSae kme store keyID keyVal.
      n \<in> nodes \<and>
      app s n = IoaState (App master oSae kme store) \<and>
      (keyID, keyVal) \<in> store
      \<longrightarrow> (kmeID n, appID n, KeyResponse keyID keyVal) \<in> network s)\<close>

definition app_kme_network_consistent where
  \<open>app_kme_network_consistent s \<longleftrightarrow>
    (\<forall>s1 s2 r1 r2 keyID keyVal1 keyVal2.
      (s1, r1, KeyResponse keyID keyVal1) \<in> network s \<and>
      (s2, r2, KeyResponse keyID keyVal2) \<in> network s
      \<longrightarrow> keyVal1 = keyVal2)\<close>

definition kme_layer_consistent where
  \<open>kme_layer_consistent s \<longleftrightarrow>
    (\<forall>n1 n2 keyID keyVal1 keyVal2. 
      kme_has_key (kme s n1) keyID keyVal1 \<and>
      kme_has_key (kme s n2) keyID keyVal2
      \<longrightarrow> keyVal1 = keyVal2)\<close>

definition qkd_layer_consistent where
  \<open>qkd_layer_consistent s \<longleftrightarrow>
    (\<forall>gen sent keyID keyVal1 keyVal2.
      qkd_layer s = QKD gen sent \<and>
      (keyID, keyVal1) \<in> (snd ` gen \<union> sent) \<and>
      (keyID, keyVal2) \<in> (snd ` gen \<union> sent)
      \<longrightarrow> keyVal1 = keyVal2)\<close>

end