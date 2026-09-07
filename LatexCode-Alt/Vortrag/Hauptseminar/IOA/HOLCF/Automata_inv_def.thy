theory Automata_inv_def
  imports Automata_2PC
begin


definition inv1 where
  ‹inv1 s ⟷
     ((∃msgs p. (snd s) p = PState PCommitted msgs) ⟶
                 (∃sender rcpt. (sender, rcpt, Commit) ∈ snd (fst s)))›

definition inv11 where
  ‹inv11 procs s ⟷
    ((∃sender rcpt. (sender, rcpt, Commit) ∈ snd (fst s)) ∨ (∃all ack msgs. fst (fst s) = CState (CCommitted all ack) msgs) ⟶
                 (∀p ∈ procs. p ≠ 0 ⟶ (∃rcpt. (p, rcpt, Yes) ∈ snd (fst s))))›

definition inv13 where
  ‹inv13 procs s ⟷
    (∀t all yes r msgs. fst (fst s) = CState (Collecting t all yes r) msgs ⟶ 
                (procs = all ∧ (∀p ∈ yes. p ≠ 0 ⟶ (∃rcpt. (p, rcpt, Yes) ∈ snd (fst s)))))›

definition inv14 where
  ‹inv14 procs s ⟷
    (∀t all r msgs. fst (fst s) = CState (CInitial t all r) msgs ⟶ procs = all)›

definition inv15 where
  ‹inv15 s ⟷
    ((∃t all yes r msgs. fst (fst s) = CState (CInitial t all r) msgs ∨ fst (fst s) = CState (Collecting t all yes r) msgs ∨ fst (fst s) = CState (CCommitted all yes) msgs) ⟶ 
              (∀sender rcpt. (sender, rcpt, Abort) ∉ snd (fst s)))›

definition inv17 where
  ‹inv17 s ⟷
    (∀p. p ≠ 0 ∧ (∃msgs. (snd s) p = PState PAborted msgs) ∧ (∀sender recpt. (sender, recpt, Abort) ∉ snd (fst s)) ⟶ (∀rcpt. (p, rcpt, Yes) ∉ snd (fst s)))›

definition inv110 where
  ‹inv110 s ⟷
    ((∃t all yes r msgs. fst (fst s) = CState (CInitial t all r) msgs ∨ fst (fst s) = CState (Collecting t all yes r) msgs ∨ fst (fst s) = CState (CAborted all yes) msgs) ⟶ 
              (∀sender rcpt. (sender, rcpt, Commit) ∉ snd (fst s)))›

definition inv111 where
  ‹inv111 s ⟷
    ((∃sender rcpt. (sender, rcpt, Commit) ∈ snd (fst s)) ⟶
     (∃all ack cmsgs. fst (fst s) = CState (CCommitted all ack) cmsgs ∨ fst (fst s) = CState Forgotten cmsgs))›

definition inv3 where
  ‹inv3 s ⟷
    (∃sender recpt. (sender, recpt, Commit) ∈ snd (fst s)) ⟶ (∀sender recpt. (sender, recpt, Abort) ∉ snd (fst s))›

definition inv_part_commit_msg  where
  ‹inv_part_commit_msg s ⟷
    (∀p. (∃msgs. (snd s) p = PState PCommitted msgs) ⟶ 
      (∃sender rcpt. (sender, rcpt, Commit) ∈ snd (fst s)))›

end