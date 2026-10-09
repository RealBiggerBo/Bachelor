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

definition qkd_layer_consistent where
  \<open>qkd_layer_consistent s \<longleftrightarrow>
    (\<forall>gen sent keyID keyVal1 keyVal2.
      qkd_layer s = QKD gen sent \<and>
      (keyID, keyVal1) \<in> (snd ` gen \<union> sent) \<and>
      (keyID, keyVal2) \<in> (snd ` gen \<union> sent)
      \<longrightarrow> keyVal1 = keyVal2)\<close>

end