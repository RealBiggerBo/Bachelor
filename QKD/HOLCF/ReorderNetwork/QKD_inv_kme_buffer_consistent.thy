theory QKD_inv_kme_buffer_consistent
  imports QKD_inv_def QKD_System_Def QKD_System_Helpers
          QKD_inv_kme_store_buffer_consistent
begin

context QKD_Network
begin

lemma inv_kme_buffer_consistent:
  shows "invariant System.ioa (kme_buffer_consistent nodes appID)"
proof (induction rule: invariantI)
  case (1 s)
  then show ?case
  proof (cases rule: starts_of_System)
    case (1 tn qkd net)
    then show ?thesis
      unfolding kme_buffer_consistent_def by force
  qed
next
  case (2 s t a)
  then show ?case
  proof (induction rule: System_step_induct)
    case (Kme_KMPost_NewKeyVal apps kmes bridges qkd net kmes' n sender otherKme keyID keyVal store route saeToKme msgs)
    then show ?case 
      using 2(2)
      unfolding kme_buffer_consistent_def apply auto
      by blast+
  next
    case (Kme_KMPut_Confirm apps kmes bridges qkd net kmes' n sender otherKme keyID store route saeToKme msgs)
    then show ?case 
      using 2(2)
      unfolding kme_buffer_consistent_def apply auto
      by blast+
  next
    case (Kme_GetKey apps kmes bridges qkd net kmes' n sender host slaveSae store route saeToKme msgs keyID val)
    then show ?case 
      using 2(2)
      unfolding kme_buffer_consistent_def apply auto
      by blast+
  next
    case (Kme_KMPut_Reserve apps kmes bridges qkd net kmes' n sender otherKme slaveSae store route saeToKme msgs keyID)
    then show ?case 
      using 2(2)
      unfolding kme_buffer_consistent_def apply auto
      by blast+
  next
    case (Kme_GetKey_Reserved apps kmes bridges qkd net kmes' n sender store keyID val conf res saeID route saeToKme msgs)
    have "kme_store_buffer_consistent nodes appID s"
      using inv_kme_store_buffer_consistent 2(1) unfolding invariant_def by fast
    then show ?case
      using 2(2) Kme_GetKey_Reserved(2,3,4,7,8,9)
      unfolding kme_buffer_consistent_def kme_store_buffer_consistent_def apply simp
      apply auto
            apply (metis imageI kme_has_key.simps(2))
           apply (metis imageI kme_has_key.simps(2))
          apply (metis imageI)
         apply (metis imageI kme_has_key.simps(2))
        apply (meson image_eqI)
       apply (metis imageI kme_has_key.simps(2))
      by (meson image_eqI)
  next
    case (Kme_GetKeyWithID_IDFound apps kmes bridges qkd net kmes' n sender host store keyID val saeToKme masterSae route msgs)
    have "kme_store_buffer_consistent nodes appID s"
      using inv_kme_store_buffer_consistent 2(1) unfolding invariant_def by fast
    then show ?case
      using 2(2) Kme_GetKeyWithID_IDFound(2,3,4,7,8,9)
      unfolding kme_buffer_consistent_def kme_store_buffer_consistent_def apply simp
      apply auto
            apply (metis imageI kme_has_key.simps(1))
           apply (metis imageI kme_has_key.simps(1))
          apply (metis imageI)
         apply (metis imageI kme_has_key.simps(1))
        apply (meson image_eqI)
       apply (metis imageI kme_has_key.simps(1))
      by (meson image_eqI)
  next
    case (Kme_GetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' n sender host masterSae keyID store route nextKme keyID2 val2 saeToKme msgs)
    then show ?case 
      using 2(2)
      unfolding kme_buffer_consistent_def apply auto
      by blast+
  next
    case (Kme_GetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' n nextKme masterSae slaveSae keyID keyID2 store route saeToKme msgs)
    then show ?case 
      using 2(2)
      unfolding kme_buffer_consistent_def apply auto
      by blast+
  next
    case (Kme_KMGetKeyWithID_IDFound apps kmes bridges qkd net kmes' n nextKme masterSae keyID keyID2 slaveSae store route saeToKme bridgeIDs msgs sender val val2)
    have "sender \<notin> appID ` nodes"
      sorry
    then show ?case
      using 2(2) Kme_KMGetKeyWithID_IDFound(2,3,9,10)
      unfolding kme_buffer_consistent_def apply simp
      by meson
  next
    case (Kme_KMGetKeyWithID_IDNotFound apps kmes bridges qkd net kmes' n nextKme masterSae keyID keyID2 slaveSae store val2 sender route keyID3 val3 saeToKme msgs)
    then show ?case 
      using 2(2)
      unfolding kme_buffer_consistent_def apply auto
      by blast+
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Reserved apps kmes bridges qkd net kmes' n nextKme prevKme masterSae keyID keyID2 slaveSae store route keyID3 saeToKme msgs)
    then show ?case 
      using 2(2)
      unfolding kme_buffer_consistent_def apply auto
      by blast+
  next
    case (Kme_KMGetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' n nextKme prevKme keyID keyVal' store keyID2 val2 sender keyID3 val3 masterSae route saeToKme msgs slaveSae)
    have "prevKme \<notin> appID ` nodes"
      sorry
    then show ?case
      using 2(2) Kme_KMGetKeyWithID_IDNotFound_Return(2,3,9,10)
      unfolding kme_buffer_consistent_def apply simp
      by meson
  next
    case (Kme_GetKeyWithID_IDNotFound_Return apps kmes bridges qkd net kmes' n nextKme keyID keyVal' store keyID2 val2 masterSae sender route saeToKme bridgeIDs msgs)
    have "sender \<notin> appID ` nodes"
      sorry
    then show ?case
      using 2(2) Kme_GetKeyWithID_IDNotFound_Return(2,3,8,9)
      unfolding kme_buffer_consistent_def apply simp
      by meson
  next
    case (Kme_Send apps kmes bridges qkd net kmes' net' n msgs rcpt msg appState)
    show ?case
      using 2(2) Kme_Send(2,3,9,10)
      unfolding kme_buffer_consistent_def
      apply auto
      by blast+
  qed (use 2(2) in \<open>auto simp: kme_buffer_consistent_def\<close>)
qed

end

end