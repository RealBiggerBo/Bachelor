theory QKD_Datatypes
  imports Main
begin

datatype ('state, 'msg) ioa_state = IoaState (IoaState_curState: 'state) (IoaState_msgBuffer: "'msg set")

datatype ('keyID, 'keyVal, 'proc) msg = 
  GetKey (GetKey_host: 'proc) (GetKey_slaveSaeID: 'proc) |
  GetKeyWithID (GetKeyWithID_host: 'proc) (GetKeyWithID_masterSaeID: 'proc) (GetKeyWithID_keyID: 'keyID) |
  KeyResponse (KeyResponse_keyID: 'keyID) (Key_Response_keyVal: 'keyVal) |
  KMKeyResponse (KMKeyResponse_encryptionKeyID: 'keyID) (KMKeyResponse_keyID: 'keyID) (KMKey_Response_keyVal: 'keyVal) |
  BridgeIDRelay (BridgeIDRelay_keyID: 'keyID) |
  KMPost (KMPost_kmePartner: 'proc) (KMPost_keyID: 'keyID) (KMPost_keyVal: 'keyVal) |
  KMPut (KMPut_ownKmeID: 'proc) (KMPut_keyID: 'keyID) (KMPut_reservedOption: "'proc option") |
  KMGet (KMGet_masterSaeID: 'proc) (KMGet_keyID: 'keyID) (KMGet_encryptionKeyID: 'keyID) (KMGet_slaveSaeID: 'proc)|
  AppIDRelay (AppIDRelay_keyID: 'keyID) |
  OK

datatype ('proc, 'msg) action = 
  RequestKey (RequestKey_target: 'proc) |
  TimerTick (TimerTick_target: 'proc) |
  Send (Send_sender: 'proc) (Send_rcpt: 'proc) (Send_msg: 'msg) | 
  Receive (Receive_sender: 'proc) (Receive_rcpt: 'proc) (Receive_msg: 'msg)

type_synonym ('keyID, 'keyVal, 'proc) key_store = "'keyID \<rightharpoonup> ('keyVal option \<times> 'proc \<times> bool \<times> 'proc option)"

datatype ('keyID, 'keyVal, 'proc) app_state = 
  App (App_isMaster: bool) (App_otherSaeID: 'proc) (App_kmeID: 'proc) (App_keys: "('keyID \<times> 'keyVal) set")
datatype ('keyID, 'keyVal, 'proc) kme_state = 
  Kme (Kme_keyStore: "('keyID, 'keyVal, 'proc) key_store") (Kme_routeFunc: "'proc \<Rightarrow> 'proc") (Kme_saeToKme: "'proc \<Rightarrow> 'proc") (Kme_bridgeIDs: "'proc set") |
  KmeWaitReserve (KmeWaitReseve_keyID: 'keyID) (KmeWaitReseve_saeID: 'proc)  (KmeWaitReseve_keyStore: "('keyID, 'keyVal, 'proc) key_store") (KmeWaitReseve_routeFunc: "'proc \<Rightarrow> 'proc") (KmeWaitReseve_saeToKme: "'proc \<Rightarrow> 'proc") (KmeWaitReserve_bridgeIDs: "'proc set") |
  KmeWaitHop (KmeWaitHop_masterSae: 'proc) (KmeWaitHop_slaveSae: 'proc) (KmeWaitHop_nextKme: 'proc) (KmeWaitHop_keyID: 'keyID) (KmeWaitHop_encryptionKeyID: 'keyID) (KmeWaitHop_keyStore: "('keyID, 'keyVal, 'proc) key_store") (KmeWaitHop_routeFunc: "'proc \<Rightarrow> 'proc") (KmeWaitHop_saeToKme: "'proc \<Rightarrow> 'proc") (KmeWaitHop_bridgeIDs: "'proc set") |
  KmeWaitHopRec (KmeWaitHopRec_encryptionKey: 'keyID) (KmeWaitHopRec_masterSae: 'proc) (KmeWaitHopRec_slaveSae: 'proc) (KmeWaitHopRec_prevKme: 'proc) (KmeWaitHopRec_nextKme: 'proc) (KmeWaitHopRec_keyID: 'keyID) (KmeWaitHopRec_encryptionKeyID: 'keyID) (KmeWaitHopRec_keyStore: "('keyID, 'keyVal, 'proc) key_store") (KmeWaitHop_routeFunc: "'proc \<Rightarrow> 'proc") (KmeWaitHopRec_saeToKme: "'proc \<Rightarrow> 'proc") (KmeWaitHopRec_bridgeIDs: "'proc set")
datatype 'proc bridge_state = 
  Bridge (Bridge_isMaster: bool) (Bridge_otherBridgeID: 'proc) (Bridge_otherKmeID: 'proc) (Bridge_qkdID: 'proc) (Bridge_kmeID: 'proc)
datatype ('keyID, 'keyVal, 'proc) qkd_layer_state = 
  QKD (QKD_generatedKeys: "('proc \<times> 'keyID \<times> 'keyVal) set") (QKD_sentKeys: "('keyID \<times> 'keyVal) set")

end