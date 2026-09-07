theory
  Network
imports
  Main
begin

datatype ('proc, 'msg) send
  = Send (msg_recipient: 'proc) (send_msg: 'msg)

datatype ('proc, 'msg) event
  = Start
  | Receive (msg_sender: 'proc) (recv_msg: 'msg)
  | Timeout
  | Restart

type_synonym ('proc, 'state, 'msg) step_func =
  "'proc ⇒ 'state ⇒ ('proc, 'msg) event ⇒ ('state × ('proc, 'msg) send set)"

fun valid_event :: "('proc, 'msg) event ⇒ 'proc ⇒
                    ('proc × ('proc, 'msg) send) set ⇒ bool" where
  "valid_event Start _ _ = True" |
  "valid_event (Receive sender msg) proc msgs = ((sender, Send proc msg) ∈ msgs)" |
  "valid_event _ _ _ = True"

inductive execute ::
    "('proc, 'state, 'msg) step_func ⇒ ('proc ⇒ 'state) ⇒ 'proc set ⇒
     ('proc × ('proc, 'msg) event) list ⇒
     ('proc × ('proc, 'msg) send) set ⇒ ('proc ⇒ 'state) ⇒ bool" where
  "execute step init procs [] {} init" |
  "⟦execute step init procs events msgs states;
    proc ∈ procs;
    valid_event event proc msgs;
    step proc (states proc) event = (new_state, sent);
    events' = events @ [(proc, event)];
    msgs' = msgs ∪ ((λmsg. (proc, msg)) ` sent);
    states' = states (proc := new_state)
   ⟧ ⟹ execute step init procs events' msgs' states'"

inductive_cases execute_indcases: "execute step init procs events msg states"

lemma execute_init:
  assumes "execute step init procs [] msgs states"
  shows "msgs = {} ∧ states = init"
  using assms by(auto elim: execute.cases)

inductive_cases execute_snocE [elim!]:
  "execute step init procs (events @ [(proc, event)]) msgs' states'"

lemma execute_step:
  assumes "execute step init procs (events @ [(proc, event)]) msgs' states'"
  shows "∃msgs states sent new_state.
          execute step init procs events msgs states ∧
          proc ∈ procs ∧
          valid_event event proc msgs ∧
          step proc (states proc) event = (new_state, sent) ∧
          msgs' = msgs ∪ ((λmsg. (proc, msg)) ` sent) ∧
          states' = states (proc := new_state)"
  using assms by blast

lemma execute_receive:
  assumes "execute step init procs (events @ [(recpt, Receive sender msg)]) msgs' states'"
  shows "(sender, Send recpt msg) ∈ msgs'"
  using assms execute_step by fastforce

end