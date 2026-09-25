theory QKD_App
  imports QKD_Network_IOA
begin

inductive app_step :: "('keyID, 'keyVal, 'proc) app_state \<Rightarrow> ('proc, ('keyID, 'keyVal, 'proc) msg) action \<Rightarrow> ('keyID, 'keyVal, 'proc) app_state \<Rightarrow> ('proc \<times> ('keyID, 'keyVal, 'proc) msg) set \<Rightarrow> bool" where
  Master_GetKey:
  \<open>app_step (App True sae kme keys)
            (RequestKey pid)
            (App True sae kme keys)
            {(kme, GetKey kme sae)}\<close> |
  Master_KeyResponse:
  \<open>app_step (App True sae kme keys)
            (Receive sender rcpt (KeyResponse keyID keyVal))
            (App True sae kme (keys \<union> {(keyID, keyVal)}))
            {(sae, AppIDRelay keyID)}\<close> |
  Slave_GetKey:
  \<open>app_step (App False sae kme keys)
            (Receive sender rcpt (AppIDRelay keyID))
            (App False sae kme keys)
            {(kme, GetKeyWithID kme sae keyID)}\<close> |
  Slave_KeyResponse:
  \<open>app_step (App False sae kme keys)
            (Receive sender rcpt (KeyResponse keyID keyVal))
            (App False sae kme (keys \<union> {(keyID, keyVal)}))
            {}\<close>

locale App_locale =
  fixes appID :: 'proc
    and isMaster :: bool
    and otherSae :: 'proc
    and kme :: 'proc
begin

sublocale Network_IOA
  appID
  "if isMaster then {RequestKey appID} else {}"
  "App isMaster otherSae kme {}"
  app_step
proof
  show "\<forall>rcpt msg. Send appID rcpt msg \<notin> (if isMaster then {RequestKey appID} else {})"
    by auto
qed

end

end