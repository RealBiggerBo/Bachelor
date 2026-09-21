theory QKD_ETSI_Bridge
  imports QKD_Network_IOA
begin

inductive bridge_step :: "'proc bridge_state \<Rightarrow> ('proc, ('keyID, 'keyVal, 'proc) msg) action \<Rightarrow> 'proc bridge_state \<Rightarrow> ('proc \<times> ('keyID, 'keyVal, 'proc) msg) set \<Rightarrow> bool" where
  Tick_GetKey:
  \<open>bridge_step (Bridge True bridge otherKme qkd kme) 
               (TimerTick pid)
               (Bridge True bridge otherKme qkd kme) 
               {(qkd, GetKey qkd otherKme)}\<close> |
  Master_KeyResponse:
  \<open>bridge_step (Bridge True bridge otherKme qkd kme)
               (Receive sender rcpt (KeyResponse keyID keyVal))
               (Bridge True bridge otherKme qkd kme)
               {(kme, KMPost otherKme keyID keyVal), (bridge, BridgeIDRelay keyID)}\<close> |
  Slave_GetKeyWithID:
  \<open>bridge_step (Bridge False bridge otherKme qkd kme) 
               (Receive sender rcpt (BridgeIDRelay keyID))
               (Bridge False bridge otherKme qkd kme)
               {(qkd, GetKeyWithID qkd otherKme keyID)}\<close> |
  Slave_KeyResponse:
  \<open>bridge_step (Bridge False bridge otherKme qkd kme) 
               (Receive sender rcpt (KeyResponse keyID keyVal))
               (Bridge False bridge otherKme qkd kme)
               {(kme, KMPost otherKme keyID keyVal)}\<close>

locale ETSI_Bridge_locale =
  fixes bridgeID :: 'proc
    and isMaster :: bool
    and bridge :: 'proc
    and otherKme :: 'proc
    and qkd :: 'proc
    and kme :: 'proc
begin

sublocale Network_IOA
  bridgeID
  "if isMaster then {TimerTick bridgeID} else {}"
  "Bridge isMaster bridge otherKme qkd kme"
  bridge_step
proof
  show "\<forall>rcpt msg. Send bridgeID rcpt msg \<notin> (if isMaster then {TimerTick bridgeID} else {})"
    by auto
qed

end

end