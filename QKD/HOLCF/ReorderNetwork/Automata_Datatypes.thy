theory Automata_Datatypes
  imports Main
begin

datatype ('state, 'msg) ioa_state = IoaState (IoaState_curState: 'state) (IoaState_msgBuffer: "'msg set")

datatype msg = CounterMsg nat | Ping | Pong

datatype ('proc, 'msg) action = 
  UpdateCount (UpdateCount_target: 'proc) | 
  PingServer (PingServer_target: 'proc) |
  ClientJoined (ClientJoined_target: 'proc) (ClientJoined_client: 'proc) |
  Send (Send_sender: 'proc) (Send_rcpt: 'proc) (Send_msg: 'msg) | 
  Receive (Receive_sender: 'proc) (Receive_rcpt: 'proc) (Receive_msg: 'msg)

datatype 'proc sstate = Count (Count_clientIDs: "'proc set") (Count_curCounter: nat)
datatype 'proc cstate = Count (Count_server: 'proc) (Count_curCount: nat)
end