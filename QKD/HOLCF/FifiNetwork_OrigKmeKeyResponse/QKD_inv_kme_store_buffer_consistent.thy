theory QKD_inv_kme_store_buffer_consistent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
begin

context QKD_Network
begin

lemma inv_kme_store_buffer_consistent:
  shows "invariant System.ioa (kme_store_buffer_consistent nodes appID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 apps kmes bridges qkd net)
    then show ?thesis
      unfolding kme_store_buffer_consistent_def by force      
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (Kme_KMPost_NewKeyVal apps kmes bridges qkd net kmes' n sender otherKme keyID keyVal store route saeToKme bridgeIDs' msgs)
    (*if store has keyID keyVal then a KMPost keyID keyVal exists*)
    have "bridgeIDs' \<subseteq> \<Union>(bridgeIDs ` nodes)"
      sorry
    moreover have "\<forall>n keyID keyVal.
            (kme_has_key (kme s n) keyID keyVal
            \<longrightarrow> (\<exists>sender otherKme. 
                  (sender, (kmeID n), KMPost otherKme keyID keyVal) \<in> network s \<and>
                  sender \<in> \<Union>(bridgeIDs ` nodes)))"
      sorry
    (*bridge - kme network consistent*)
    moreover have "(\<forall>s1 s2 r1 r2 otherKme1 otherKme2 keyID keyVal1 keyVal2.
              s1 \<in> \<Union>(bridgeIDs ` nodes) \<and>
              s2 \<in> \<Union>(bridgeIDs ` nodes) \<and>
              r1 \<in> kmeID ` nodes \<and>
              r2 \<in> kmeID ` nodes \<and>
              (s1, r1, KMPost otherKme1 keyID keyVal1) \<in> network s \<and>
              (s2, r2, KMPost otherKme2 keyID keyVal2) \<in> network s
              \<longrightarrow> keyVal1 = keyVal2)"
      sorry
    moreover have "\<forall>n2 st ms snd rcpt keyID v.
    n2 \<in> nodes \<and> kme s n2 = IoaState st ms \<and>
    rcpt \<in> appID ` nodes \<and> (snd, rcpt, KeyResponse keyID v) \<in> ms
    \<longrightarrow> (\<exists>b r ot. b \<in> \<Union>(bridgeIDs ` nodes) \<and> r \<in> kmeID ` nodes \<and>
               (b, r, KMPost ot keyID v) \<in> network s)"
      sorry
      ultimately show ?case
        using 2(2) Kme_KMPost_NewKeyVal(2,3,4,7,8,9,10)
        unfolding kme_store_buffer_consistent_def
        apply simp apply auto
      sorry
  next
    case (Kme_KMPut_Confirm apps kmes bridges qkd net kmes' n sender otherKme keyID store route saeToKme bridgeIDs msgs)
    have "\<forall>n keyID keyVal. 
            kme_has_key (kme s n) keyID keyVal 
            \<longleftrightarrow> kme_has_key (kme t n) keyID keyVal"
      using Kme_KMPut_Confirm(2,3,7,8)
      by (auto split: option.splits prod.splits)
    moreover have h2: "\<forall>n st ms st' ms' snd rcpt k v.
                        kme s n = IoaState st ms \<and> 
                        kme t n = IoaState st' ms' 
                        \<longrightarrow> (((snd, rcpt, KeyResponse k v) \<in> ms) \<longleftrightarrow> ((snd, rcpt, KeyResponse k v) \<in> ms'))"
      using Kme_KMPut_Confirm(2,3,7,8)
      by (auto split: option.splits prod.splits)
    ultimately show ?case
      using 2(2) Kme_KMPut_Confirm(2-8) unfolding kme_store_buffer_consistent_def
      by (smt (verit, ccfv_SIG) "2.IH"(2) fstI fun_upd_other sndI)
  next
    case (Kme_GetKey apps kmes bridges qkd net kmes' n sender host slaveSae store route saeToKme bridgeIDs msgs keyID val)
    have "\<forall>n keyID keyVal. 
            kme_has_key (kme s n) keyID keyVal 
            \<longleftrightarrow> kme_has_key (kme t n) keyID keyVal"
      using Kme_GetKey(2,3,8,9)
      by (auto split: option.splits prod.splits)
    moreover have h2: "\<forall>n st ms st' ms' snd rcpt k v.
                        kme s n = IoaState st ms \<and> 
                        kme t n = IoaState st' ms' 
                        \<longrightarrow> (((snd, rcpt, KeyResponse k v) \<in> ms) \<longleftrightarrow> ((snd, rcpt, KeyResponse k v) \<in> ms'))"
      using Kme_GetKey(2,3,8,9)
      by (auto split: option.splits prod.splits)
    ultimately show ?case
      using 2(2) Kme_GetKey(2,3,8,9) unfolding kme_store_buffer_consistent_def
      by (smt (verit, ccfv_SIG) "2.IH"(2) fstI fun_upd_other sndI)
  next
    case (Kme_KMPut_Reserve apps kmes bridges qkd net kmes' n sender otherKme slaveSae store route saeToKme bridgeIDs msgs keyID)
    have "\<forall>n keyID keyVal. 
            kme_has_key (kme s n) keyID keyVal 
            \<longleftrightarrow> kme_has_key (kme t n) keyID keyVal"
      using Kme_KMPut_Reserve(2,3,7,8)
      by (auto split: option.splits prod.splits)
    moreover have h2: "\<forall>n st ms st' ms' snd rcpt k v.
                        kme s n = IoaState st ms \<and> 
                        kme t n = IoaState st' ms' 
                        \<longrightarrow> (((snd, rcpt, KeyResponse k v) \<in> ms) \<longleftrightarrow> ((snd, rcpt, KeyResponse k v) \<in> ms'))"
      using Kme_KMPut_Reserve(2,3,7,8)
      by (auto split: option.splits prod.splits)
    ultimately show ?case
      using 2(2) Kme_KMPut_Reserve(2,3,7,8) unfolding kme_store_buffer_consistent_def
      by (smt (verit, ccfv_SIG) "2.IH"(2) fstI fun_upd_other sndI)
  next
    case (Kme_GetKey_Reserved apps kmes bridges qkd net kmes' n sender store keyID val conf res saeID route saeToKme bridgeIDs msgs)
    have "kme_stores_consistent nodes s"
      unfolding kme_stores_consistent_def sorry
    then show ?case
      using 2(2) Kme_GetKey_Reserved(2,3,7,8,9)
      unfolding kme_stores_consistent_def kme_store_buffer_consistent_def
      apply simp apply auto
         apply (metis imageI kme_has_key.simps(2))
        apply (metis image_eqI kme_has_key.simps(2))
       apply (metis kme_has_key.simps(2))
      by fast
  next
    case (Kme_GetKeyWithID_IDFound apps kmes bridges qkd net kmes' n sender host store keyID val saeToKme bridgeIDs masterSae route msgs)
    have "kme_stores_consistent nodes s"
      unfolding kme_stores_consistent_def sorry
    then show ?case 
      using 2(2) Kme_GetKeyWithID_IDFound(2,3,7,8,9)
      unfolding kme_stores_consistent_def kme_store_buffer_consistent_def
      apply simp apply auto
         apply fastforce
        apply (metis image_eqI kme_has_key.simps(1))
       apply (metis kme_has_key.simps(1))
      by fast
  next
    case (Kme_GetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' n sender host masterSae keyID store route nextKme keyID2 val2 saeToKme bridgeIDs msgs)
    have "\<forall>n keyID keyVal. 
            kme_has_key (kme s n) keyID keyVal 
            \<longleftrightarrow> kme_has_key (kme t n) keyID keyVal"
      using Kme_GetKeyWithID_IDNotFound(2,3,10,11)
      by (auto split: option.splits prod.splits)
    moreover have h2: "\<forall>n st ms st' ms' snd rcpt k v.
                        kme s n = IoaState st ms \<and> 
                        kme t n = IoaState st' ms' 
                        \<longrightarrow> (((snd, rcpt, KeyResponse k v) \<in> ms) \<longleftrightarrow> ((snd, rcpt, KeyResponse k v) \<in> ms'))"
      using Kme_GetKeyWithID_IDNotFound(2,3,10,11)
      by (auto split: option.splits prod.splits)
    ultimately show ?case
      using 2(2) Kme_GetKeyWithID_IDNotFound(2,3,10,11) unfolding kme_store_buffer_consistent_def
      by (smt (verit, ccfv_SIG) "2.IH"(2) fstI fun_upd_other sndI)
  next
    case (Kme_GetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' n nextKme masterSae slaveSae keyID keyID2 store route saeToKme bridgeIDs msgs)
    have "\<forall>n keyID keyVal. 
            kme_has_key (kme s n) keyID keyVal 
            \<longleftrightarrow> kme_has_key (kme t n) keyID keyVal"
      using Kme_GetKeyWithID_IDNotFound_Reserved(2,3,7,8)
      by (auto split: option.splits prod.splits)
    moreover have h2: "\<forall>n st ms st' ms' snd rcpt k v.
                        kme s n = IoaState st ms \<and> 
                        kme t n = IoaState st' ms' 
                        \<longrightarrow> (((snd, rcpt, KeyResponse k v) \<in> ms) \<longleftrightarrow> ((snd, rcpt, KeyResponse k v) \<in> ms'))"
      using Kme_GetKeyWithID_IDNotFound_Reserved(2,3,7,8)
      by (auto split: option.splits prod.splits)
    ultimately show ?case
      using 2(2) Kme_GetKeyWithID_IDNotFound_Reserved(2,3,7,8) unfolding kme_store_buffer_consistent_def
      by (smt (verit, ccfv_SIG) fstI fun_upd_other sndI)
  next
    case (Kme_KMGetKeyWithID_IDFound apps kmes bridges qkd net kmes' n nextKme masterSae keyID keyID2 slaveSae store route saeToKme bridgeIDs msgs sender val val2)
    have "sender \<notin> appID ` nodes"
      sorry
    then show ?case 
      using 2(2) Kme_KMGetKeyWithID_IDFound(2,3,9,10)
      unfolding kme_store_buffer_consistent_def 
      apply simp apply auto
         apply fastforce
        apply (metis image_eqI kme_has_key.simps(1))
      by fast
  next
    case (Kme_KMGetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' n nextKme masterSae keyID keyID2 slaveSae store val2 sender route keyID3 val3 saeToKme bridgeIDs msgs)
    have "\<forall>n keyID keyVal. 
            kme_has_key (kme s n) keyID keyVal 
            \<longleftrightarrow> kme_has_key (kme t n) keyID keyVal"
      using Kme_KMGetKeyWithID_IDNotFound(2,3,11,12)
      by (auto split: option.splits prod.splits)
    moreover have h2: "\<forall>n st ms st' ms' snd rcpt k v.
                        kme s n = IoaState st ms \<and> 
                        kme t n = IoaState st' ms' 
                        \<longrightarrow> (((snd, rcpt, KeyResponse k v) \<in> ms) \<longleftrightarrow> ((snd, rcpt, KeyResponse k v) \<in> ms'))"
      using Kme_KMGetKeyWithID_IDNotFound(2,3,11,12)
      by (auto split: option.splits prod.splits)
    ultimately show ?case
      using 2(2) Kme_KMGetKeyWithID_IDNotFound(2,3,11,12) unfolding kme_store_buffer_consistent_def
      by (smt (verit, ccfv_SIG) fstI fun_upd_other sndI)
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' n nextKme prevKme masterSae keyID keyID2 slaveSae store route keyID3 saeToKme bridgeIDs msgs)
    have "\<forall>n keyID keyVal. 
            kme_has_key (kme s n) keyID keyVal 
            \<longleftrightarrow> kme_has_key (kme t n) keyID keyVal"
      using Kme_KMGetKeyWithID_IDNotFound_Reserved(2,3,7,8)
      by (auto split: option.splits prod.splits)
    moreover have h2: "\<forall>n st ms st' ms' snd rcpt k v.
                        kme s n = IoaState st ms \<and> 
                        kme t n = IoaState st' ms' 
                        \<longrightarrow> (((snd, rcpt, KeyResponse k v) \<in> ms) \<longleftrightarrow> ((snd, rcpt, KeyResponse k v) \<in> ms'))"
      using Kme_KMGetKeyWithID_IDNotFound_Reserved(2,3,7,8)
      by (auto split: option.splits prod.splits)
    ultimately show ?case
      using 2(2) Kme_KMGetKeyWithID_IDNotFound_Reserved(2,3,7,8) unfolding kme_store_buffer_consistent_def
      by (smt (verit, ccfv_SIG) fstI fun_upd_other sndI)
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' n nextKme prevKme keyID keyVal' store keyID2 val2 sender keyID3 val3 masterSae route saeToKme bridgeIDs msgs slaveSae)
    have "prevKme \<notin> appID ` nodes"
      sorry
    then show ?case 
      using 2(2) Kme_KMGetKeyWithID_IDNotFound_Return(2,3,9,10)
      unfolding kme_store_buffer_consistent_def 
      apply simp apply auto
         apply fastforce
        apply (metis image_eqI kme_has_key.simps(4))
      by fast
  next
    case (Kme_GetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' n nextKme keyID keyVal' store keyID2 val2 masterSae sender route saeToKme bridgeIDs msgs)
    have "sender \<notin> appID ` nodes"
      sorry
    then show ?case 
      using 2(2) Kme_GetKeyWithID_IDNotFound_Return(2,3,8,9)
      unfolding kme_store_buffer_consistent_def 
      apply simp apply auto
         apply fastforce
        apply (metis image_eqI kme_has_key.simps(3))
      by fast
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    have "\<And>st m k v m'. kme_has_key (IoaState st m) k v = kme_has_key (IoaState st m') k v"
      apply auto
      using kme_has_key.elims by fastforce+
    then show ?case
      using 2(2) Kme_Send(2-4,6-10)
      unfolding kme_store_buffer_consistent_def
      apply simp apply auto
            apply fastforce
           apply fastforce
          apply fastforce
      by (metis image_eqI)+
  qed (use 2(2) in \<open>auto simp: kme_store_buffer_consistent_def\<close>)
qed

end

end