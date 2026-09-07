theory Kleppmann_inv_def
  imports Kleppmann_2PC
begin

(* Invariant 1: for any participant p, if p's state is ``Committed'',
   then there exists a message ``Commit''*)

definition inv1 where
  ‹inv1 msgs states ⟷
     ((∃proc a ack'. proc ≠ 0 ∧ states proc = Committed a ack') ⟶
                 (∃sender rcpt. (sender, Send rcpt Commit) ∈ msgs))›

definition inv11 where
  ‹inv11 msgs states procs ⟷
    ((∃sender rcpt. (sender, Send rcpt Commit) ∈ msgs) ∨ (∃all ack. states 0 = Committed all ack) ⟶
                 (∀p ∈ procs. p ≠ 0 ⟶ (∃rcpt. (p, Send rcpt Yes) ∈ msgs)))›

definition inv12 where
  ‹inv12 msgs states procs ⟷
    (∀p ∈ procs. p ≠ 0 ⟶ ((∃rcpt. (p, Send rcpt Yes) ∈ msgs) ⟶ (∀rcpt. (p, Send rcpt No) ∉ msgs)))›

definition inv13 where
  ‹inv13 msgs states procs ⟷
    (∀t all yes r. states 0 = Collecting t all yes r ⟶ 
                (procs = all ∧ (∀p ∈ yes. p ≠ 0 ⟶ (∃rcpt. (p, Send rcpt Yes) ∈ msgs))))›

definition inv14 where
  ‹inv14 msgs states procs ⟷
    (∀t all r. states 0 = Initial t all r ⟶ procs = all)›

definition inv15 where
  ‹inv15 msgs states ⟷
    ((∃t all yes r. states 0 = Initial t all r ∨ states 0 = Collecting t all yes r ∨ states 0 = Committed all yes) ⟶ 
              (∀sender rcpt. (sender, Send rcpt Abort) ∉ msgs))›

definition inv16 where
  ‹inv16 msgs states ⟷
    (∀sender rcpt. (sender, Send rcpt Yes) ∈ msgs ⟶ (states sender = Prepared ∨ states sender = Aborted {} {} ∨ states sender = Committed {} {}))›

definition inv17 where
  ‹inv17 msgs states ⟷
    (∀p. p ≠ 0 ∧ (∃all ack. states p = Aborted all ack) ∧ (∀sender recpt. (sender, Send recpt Abort) ∉ msgs) ⟶ (∀rcpt. (p, Send rcpt Yes) ∉ msgs))›

definition inv18 where
  ‹inv18 msgs states ⟷
    (∀p t all r. p ≠ 0 ∧ states p = Initial t all r ⟶ (∀rcpt. (p, Send rcpt Yes) ∉ msgs))›

definition inv19 where
  ‹inv19 msgs states ⟷
    ((∃all ack. states 0 = Committed all ack) ⟶ (∃sender rcpt. (sender, Send rcpt Commit) ∈ msgs))›

definition inv110 where
  ‹inv110 msgs states ⟷
    ((∃t all yes r. states 0 = Initial t all r ∨ states 0 = Collecting t all yes r ∨ states 0 = Aborted all yes) ⟶ 
              (∀sender rcpt. (sender, Send rcpt Commit) ∉ msgs))›

definition inv111 where
  ‹inv111 msgs states ⟷
    ((∃sender rcpt. (sender, Send rcpt Commit) ∈ msgs) ⟶ (∃all ack. states 0 = Committed all ack ∨ states 0 = Forgotten))›

definition inv112 where
  ‹inv112 msgs states procs ⟷
    ((∃all ack. states 0 = Committed all ack) ⟶ (∀p ∈ procs. p ≠ 0 ⟶ (∃rcpt. (p, Send rcpt Yes) ∈ msgs)))›

(* Invariant 3: if a Commit msg has been sent then an abort or no msg cannot also have been sent*)

definition inv3 where
  ‹inv3 msgs states ⟷
    (∃sender recpt. (sender, Send recpt Commit) ∈ msgs) ⟶ (∀sender recpt. (sender, Send recpt Abort) ∉ msgs)›

definition inv21 where
  ‹inv21 p old_state new_state ⟷ 
    (∃all ack. old_state = Committed all ack) ⟶ (∃all ack. new_state = Committed all ack ∨ (p = 0 ∧ new_state = Forgotten))›

definition inv22 where
  ‹inv22 p old_state new_state ⟷ 
    (∃all ack. old_state = Aborted all ack) ⟶ (∃all ack. new_state = Aborted all ack ∨ (p = 0 ∧ new_state = Forgotten))›

definition inv23 where
  ‹inv23 p old_state new_state ⟷
    (old_state = Forgotten ⟶ (p = 0 ∧ new_state = Forgotten))›

definition inv24 where
  ‹inv24 states ⟷
    (∀p ≠ 0.  states p ≠ Forgotten)›

definition inv41 where
  ‹inv41 msgs states ⟷
    ((∃t a r. states 0 = Initial t a r) ⟶ msgs = {})›

definition inv42 where
  ‹inv42 msgs ⟷
    (∀proc rcpt t. (proc, Send rcpt (Prepare t)) ∈ msgs ⟶ proc = 0)›

definition inv43 where
  ‹inv43 msgs init_val⟷
    (∀rcpt t. (0, Send rcpt (Prepare t)) ∈ msgs ⟶ t = init_val)›

definition inv44 where
  ‹inv44 msgs states ⟷
    ((∃t a r. states 0 = Initial t a r) ⟶ (∀proc rcpt t. (proc, Send rcpt (Prepare t)) ∉ msgs))›

end