theory QKD_KME
  imports QKD_Network_IOA
begin

fun keyStore_add:: "('keyID, 'keyVal, 'proc) key_store \<Rightarrow> 'keyID \<Rightarrow> 'keyVal option \<Rightarrow> 'proc \<Rightarrow> ('keyID, 'keyVal, 'proc) key_store" where
  \<open>keyStore_add store keyID keyVal kmePartner = 
    (case store keyID of
      Some (oldVal, oldPartner, conf, res) \<Rightarrow> store(keyID \<mapsto> (keyVal, kmePartner, conf, res))
    | None \<Rightarrow> store(keyID \<mapsto> (keyVal, kmePartner, False, None)))\<close>

fun keyStore_confirm:: "('keyID, 'keyVal, 'proc) key_store \<Rightarrow> 'keyID \<Rightarrow> 'proc \<Rightarrow> ('keyID, 'keyVal, 'proc) key_store" where
  \<open>keyStore_confirm store keyID kmePartner = 
    (case store keyID of
      Some (oldVal, oldPartner, conf, res) \<Rightarrow> store(keyID \<mapsto> (oldVal, oldPartner, True, res))
    | None \<Rightarrow> store(keyID \<mapsto> (None, kmePartner, True, None)))\<close>

fun keyStore_reserve:: "('keyID, 'keyVal, 'proc) key_store \<Rightarrow> 'keyID \<Rightarrow> 'proc \<Rightarrow> ('keyID, 'keyVal, 'proc) key_store" where
  \<open>keyStore_reserve store keyID procID = 
    (case store keyID of
      Some (oldVal, oldPartner, conf, res) \<Rightarrow> store(keyID \<mapsto> (oldVal, oldPartner, conf, Some procID))
    | None \<Rightarrow> store)\<close> (*hier muss evtl der Schlüssel neu angelegt werden*)

fun keyStore_remove:: "('keyID, 'keyVal, 'proc) key_store \<Rightarrow> 'keyID \<Rightarrow> ('keyID, 'keyVal, 'proc) key_store" where
  \<open>keyStore_remove store keyID = store(keyID := None)\<close>

type_synonym 'keyVal cipher_function = "'keyVal \<Rightarrow> 'keyVal \<Rightarrow> 'keyVal"

inductive kme_step :: "'keyVal cipher_function \<Rightarrow> 'keyVal cipher_function \<Rightarrow> ('keyID, 'keyVal, 'proc) kme_state \<Rightarrow> ('proc, ('keyID, 'keyVal, 'proc) msg) action \<Rightarrow> ('keyID, 'keyVal, 'proc) kme_state \<Rightarrow> ('proc \<times> ('keyID, 'keyVal, 'proc) msg) set \<Rightarrow> bool" where
  KMPost_NewKeyVal:
  \<open>kme_step enc dec
            (Kme store route saeToKme) 
            (Receive sender rcpt (KMPost otherKme keyID keyVal))
            (Kme (keyStore_add store keyID (Some keyVal) otherKme) route saeToKme) 
            {(sender, OK), (otherKme, KMPut rcpt keyID None)}\<close> |
  KMPut_Confirm:
  \<open>kme_step enc dec
            (Kme store route saeToKme) 
            (Receive sender rcpt (KMPut otherKme keyID None))
            (Kme (keyStore_confirm store keyID otherKme) route saeToKme) 
            {(sender, OK)}\<close> |
  GetKey:
  \<open>store keyID = Some (Some val, saeToKme slaveSae, True, None) \<Longrightarrow> 
   kme_step enc dec
            (Kme store route saeToKme) 
            (Receive sender rcpt (GetKey host slaveSae))
            (KmeWaitReserve keyID sender store route saeToKme) 
            {(saeToKme slaveSae, KMPut rcpt keyID (Some slaveSae))}\<close> |
  KMPut_Reserve:
  \<open>kme_step enc dec
            (Kme store route saeToKme)
            (Receive sender rcpt (KMPut otherKme keyID (Some slaveSae)))
            (Kme (keyStore_reserve store keyID slaveSae) route saeToKme)
            {(otherKme, OK)}\<close> |
  GetKey_Reserved:
  \<open>store keyID = Some (Some val, sender, conf, res) \<Longrightarrow>
   kme_step enc dec
            (KmeWaitReserve keyID saeID store route saeToKme) 
            (Receive sender rcpt OK)
            (Kme (keyStore_remove store keyID) route saeToKme) 
            {(saeID, KeyResponse keyID val)}\<close> |
  GetKeyWithID_IDFound:
  \<open>store keyID = Some (Some val, saeToKme masterSae, True, Some sender) \<Longrightarrow>
   kme_step enc dec
            (Kme store route saeToKme) 
            (Receive sender rcpt (GetKeyWithID host masterSae keyID))
            (Kme (keyStore_remove store keyID) route saeToKme) 
            {(sender, KeyResponse keyID val)}\<close> |
  GetKeyWithID_IDNotFound:
  \<open>store keyID = None \<Longrightarrow>
   route masterSae = nextKme \<Longrightarrow>
   store keyID2 = Some (Some val2, nextKme, True, None) \<Longrightarrow>
   kme_step enc dec
            (Kme store route saeToKme) 
            (Receive sender rcpt (GetKeyWithID host masterSae keyID))
            (KmeWaitHop masterSae sender nextKme keyID keyID2 store route saeToKme) 
            {(nextKme, KMPut rcpt keyID2 (Some rcpt))}\<close> |
  GetKeyWithID_IDNotFound_Reserved:
  \<open>kme_step enc dec
            (KmeWaitHop masterSae slaveSae nextKme keyID keyID2 store route saeToKme) 
            (Receive nextKme rcpt OK)
            (KmeWaitHop masterSae slaveSae nextKme keyID keyID2 store route saeToKme) 
            {(nextKme, KMGet masterSae keyID keyID2 slaveSae)}\<close> |
  KMGetKeyWithID_IDFound:
  \<open>store keyID = Some (Some val, saeToKme masterSae, True, Some sender) \<Longrightarrow>
   store keyID2 = Some (Some val2, sender, True, Some sender) \<Longrightarrow>
   kme_step enc dec
            (Kme store route saeToKme) 
            (Receive sender rcpt (KMGet masterSae keyID keyID2 slaveSae))
            (Kme (keyStore_remove (keyStore_remove store keyID) keyID2) route saeToKme) 
            {(sender, KeyResponse keyID (enc val val2))}\<close> |
  KMGetKeyWithID_IDNotFound:
  \<open>store keyID = None \<Longrightarrow>
   store keyID2 = Some (Some val2, sender, True, Some sender) \<Longrightarrow>
   route masterSae = nextKme \<Longrightarrow>
   store keyID3 = Some (Some val3, nextKme, True, None) \<Longrightarrow>
   kme_step enc dec
            (Kme store route saeToKme) 
            (Receive sender rcpt (KMGet masterSae keyID keyID2 slaveSae))
            (KmeWaitHopRec keyID3 masterSae sender nextKme keyID keyID2 store route saeToKme) 
            {(nextKme, KMPut rcpt keyID3 (Some rcpt))}\<close> |
  KMGetKeyWithID_IDNotFound_Reserved:
  \<open>kme_step enc dec
            (KmeWaitHopRec keyID3 masterSae sender nextKme keyID keyID2 store route saeToKme) 
            (Receive nextKme rcpt OK)
            (KmeWaitHopRec keyID3 masterSae sender nextKme keyID keyID2 store route saeToKme) 
            {(nextKme, KMGet masterSae keyID keyID3 slaveSae)}\<close> |
  KMGetKeyWithID_IDNotFound_Return:
  \<open>store keyID2 = Some (Some val2, sender, True, Some sender) \<Longrightarrow>
   store keyID3 = Some (Some val3, nextKme, True, None) \<Longrightarrow>
   kme_step enc dec
            (KmeWaitHopRec keyID3 masterSae sender nextKme keyID keyID2 store route saeToKme)
            (Receive nextKme rcpt (KeyResponse keyID' keyVal'))
            (Kme store route saeToKme) 
            {(sender, KeyResponse keyID (enc (dec keyVal' val3) val2))}\<close> |
  GetKeyWithID_IDNotFound_Return:
  \<open>store keyID3 = Some (Some val3, nextKme, True, None) \<Longrightarrow>
   kme_step enc dec
            (KmeWaitHop masterSae sender nextKme keyID keyID2 store route saeToKme)
            (Receive nextKme rcpt (KeyResponse keyID' keyVal'))
            (Kme store route saeToKme) 
            {(sender, KeyResponse keyID (dec keyVal' val3))}\<close>

locale Kme_locale =
  fixes kmeID :: 'proc
    and route :: "'proc \<Rightarrow> 'proc"
    and saeToKme :: "'proc \<Rightarrow> 'proc"
    and enc :: "'keyVal \<Rightarrow> 'keyVal \<Rightarrow> 'keyVal"
    and dec :: "'keyVal \<Rightarrow> 'keyVal \<Rightarrow> 'keyVal"
  assumes cipher_correctness: "dec (enc val v1) v2 = val \<longleftrightarrow> v1 = v2"
begin

sublocale Network_IOA
  kmeID
  "{}"
  "Kme (\<lambda>keyID. None) route saeToKme"
  "kme_step enc dec"
proof
  show "\<forall>rcpt msg. Send kmeID rcpt msg \<notin> {}"
    by auto
qed

end

end