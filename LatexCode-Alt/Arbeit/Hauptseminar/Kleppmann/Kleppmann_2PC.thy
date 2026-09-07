theory Kleppmann_2PC
  imports Network
begin

datatype 't msg = Prepare (transaction: 't) | Yes | No | Commit | Abort | Ack

datatype ('t, 'proc) state = Initial (transaction: 't) (all: "'proc set") (retry_count:"nat")
  | Collecting (transaction: 't) (all: "'proc set") (yes:"'proc set") (retry_count:"nat")
  | Prepared 
  | Committed (all: "'proc set") (ack: "'proc set") 
  | Aborted (all: "'proc set") (ack: "'proc set") 
  | Forgotten

fun coordinator_step:: 
    "'proc ⇒ ('t, 'proc) state ⇒ ('proc, 't msg) event ⇒ ('t, 'proc) state × ('proc, 't msg) send set"  where
  ‹coordinator_step pid (Initial t a r) Start = (Collecting t a {pid} r, {Send p (Prepare t) | p. p ∈ a})› |
  ‹coordinator_step pid (Collecting t a y r) (Receive sender msg) = 
      (case msg of
        Yes ⇒(if y ∪ {sender} = a then (Committed a {pid}, {Send p (Commit) | p. p ∈ a}) else (Collecting t a (y ∪ {sender}) r, {})) |
        No ⇒(Aborted a {pid}, {Send p (Abort) | p. p ∈ a}) |
        _ ⇒(Collecting t a y r, {}))› |
  ‹coordinator_step pid (Collecting t a y 0) Timeout = (Aborted a {pid}, {Send p (Abort) | p. p ∈ a})› |
  ‹coordinator_step _ (Collecting t a y (Suc r)) Timeout = (Collecting t a y r, {Send p (Prepare t) | p. p ∈ (a - y)})› |
  ‹coordinator_step _ (Committed a ack') (Receive sender Ack) = 
      (if {sender} ∪ ack' = a then (Forgotten, {}) else (Committed a (ack' ∪ {sender}), {}))› |
  ‹coordinator_step _ (Committed a ack') Timeout = (Committed a ack', {Send p Commit | p. p ∈ (a - ack')})› |
  ‹coordinator_step _ (Committed a ack') Restart = (Committed a ack', {Send p Commit | p. p ∈ a})› |
  ‹coordinator_step _ (Aborted a ack') (Receive sender Ack) = 
      (if {sender} ∪ ack' = a then (Forgotten, {}) else (Aborted a (ack' ∪ {sender}), {}))› |
  ‹coordinator_step _ (Aborted a ack') Timeout = (Aborted a ack', {Send p Abort  | p. p ∈ (a - ack')})› |
  ‹coordinator_step _ (Aborted a ack') Restart = (Aborted a ack', {Send p Abort  | p. p ∈ a})› |
  ‹coordinator_step _ state _ = (state, {})›

fun participant_step::
    "('t, 'proc) state ⇒ ('proc, 't msg) event ⇒ ('t, 'proc) state × ('proc, 't msg) send set" where
  ‹participant_step (Initial t _ _) (Receive sender (Prepare t')) = (if t = t' then (Prepared, {Send sender Yes}) else (Aborted {} {}, {Send sender No}))› |
  ‹participant_step (Initial _ _ _) Timeout = (Aborted {} {}, {})› |
  ‹participant_step Prepared (Receive sender msg) = 
      (case msg of
        Commit ⇒ (Committed {} {}, {Send sender Ack}) |
        Abort ⇒ (Aborted {} {}, {Send sender Ack}) |
        _ ⇒ (Prepared, {}))› |
  ‹participant_step (Committed _ _) (Receive sender Commit) = (Committed {} {}, {Send sender Ack})› |
  ‹participant_step (Aborted _ _) (Receive sender Abort) = (Aborted {} {}, {Send sender Ack})› |
  ‹participant_step state _ = (state, {})›

fun tupac_step where
  ‹tupac_step proc = (if proc = 0 then coordinator_step proc else participant_step)›

end