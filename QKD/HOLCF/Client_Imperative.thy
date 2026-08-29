theory Client_Imperative
  imports
    "HOL-Imperative_HOL.Ref"
    "HOL-Library.Code_Target_Nat"
begin


section \<open>Message type\<close>

datatype exec_msg =
    Counter nat
  | Ping
  | Pong
  | Stop


section \<open>Imperative client state\<close>

type_synonym client_state =
  "nat ref \<times> bool ref"


section \<open>Initial state\<close>

definition initial_client :: "client_state Heap" where
  "initial_client = do {
      counter \<leftarrow> ref 0;
      active \<leftarrow> ref False;
      return (counter, active)
   }"


section \<open>Client transition\<close>

fun client_step ::
    "client_state \<Rightarrow> exec_msg \<Rightarrow> unit Heap"
where

  "client_step (counter, active) (Counter n) =
      Ref.update counter n"

| "client_step (counter, active) Ping =
      Ref.update active True"

| "client_step (counter, active) Pong =
      Ref.update active False"

| "client_step (counter, active) Stop =
      return ()"


section \<open>Observation functions\<close>

definition client_counter ::
    "client_state \<Rightarrow> nat Heap"
where
  "client_counter (counter, active) =
      Ref.lookup counter"


definition client_active ::
    "client_state \<Rightarrow> bool Heap"
where
  "client_active (counter, active) =
      Ref.lookup active"


section \<open>Code export\<close>

export_code
    initial_client
    client_step
    client_counter
    client_active
    Counter
    Ping
    Pong
    Stop
  in Haskell
  module_name ClientAutomaton
  file "ClientAutomaton"

end