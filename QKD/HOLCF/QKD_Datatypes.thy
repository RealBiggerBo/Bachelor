theory QKD_Datatypes
  imports Main
begin

datatype ('state, 'msg) ioa_state = IoaState (IoaState_curState: 'state) (IoaState_msgBuffer: "'msg set")

datatype ('keyId, 'keyVal, 'proc) msg = 
  GetKeyFor (GetKeyFor_Target: 'proc) |
  GetKeyWith (GetKeyWith_KeyId: 'keyId) |
  GetKeyId |
  KeyResponse (KeyResponse_KeyId: 'keyId) (Key_Response_KeyVal: 'keyVal) |
  KeyRelay (KeyRelay_KeyId: 'keyId) (KeyRelay_KeyVal: 'keyVal) (KeyRelay_Target: 'proc) |
  Error

datatype ('proc, 'msg) action = 
  RequestKey (RequestKey_Target: 'proc)| 
  Send (Send_Sender: 'proc) (Send_Rcpt: 'proc) (Send_Msg: 'msg) | 
  Receive (Receive_Sender: 'proc) (Receive_Rcpt: 'proc) (Receive_Msg: 'msg)

datatype 'proc sstate = Count (Count_clientIDs: "'proc set") (Count_curCounter: nat)
datatype 'proc cstate = Count (Count_server: 'proc) (Count_curCount: nat)
end