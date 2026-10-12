import Verification.DistributedByzantineThreeGeneralsOralImpossibility

open DistributedByzantineThreeGeneralsOralImpossibility Node

example (T : ℕ) (Msg State : Type) (P : Protocol T Msg State) (r : ℕ) :
    execution P 0 (some lieutenant2) (adv0 P) r lieutenant1 =
      execution P 0 (some commander) (adv2 P) r lieutenant1 :=
  local_state_induction_scen0_scen2 P r

example (T : ℕ) (Msg State : Type) (P : Protocol T Msg State) (r : ℕ) :
    execution P 1 (some lieutenant1) (adv1 P) r lieutenant2 =
      execution P 0 (some commander) (adv2 P) r lieutenant2 :=
  local_state_induction_scen1_scen2 P r

example (T : ℕ) :
    ¬ ∃ (Msg State : Type) (P : Protocol T Msg State), Agreement P ∧ CommanderValidity P :=
  no_correct_protocol T

example (Msg State : Type) (P : Protocol 0 Msg State) :
    ¬ (Agreement P ∧ CommanderValidity P) := zero_horizon_impossibility P

example : Agreement (retreatProtocol 7) ∧ ¬ CommanderValidity (retreatProtocol 7) :=
  constant_retreat_regression 7

example : CommanderValidity followCommander ∧ ¬ Agreement followCommander :=
  naive_follow_commander_violates_agreement

-- Evaluate the two honest recipients against an equivocating commander.
example : decision followCommander 0 (some commander) conflictingOrders lieutenant1 = 0 ∧
    decision followCommander 0 (some commander) conflictingOrders lieutenant2 = 1 := by decide

-- Changing the private command never changes either lieutenant's initial state.
example (T : ℕ) (Msg State : Type) (P : Protocol T Msg State) (v w : Order) :
    initial P v lieutenant1 = initial P w lieutenant1 ∧
    initial P v lieutenant2 = initial P w lieutenant2 := by simp [initial]

-- No-fault executions satisfy both recipients for each possible order.
example : decision followCommander 0 none silent lieutenant1 = 0 ∧
    decision followCommander 1 none silent lieutenant2 = 1 := by decide

-- Reliable honest delivery retains sender identity, while the faulty node can omit.
example (T : ℕ) (Msg State : Type) (P : Protocol T Msg State)
    (adv : Adversary T Msg) (r : Fin T) (s : Node → State) :
    inbox P (some lieutenant2) adv r s lieutenant1 commander =
      P.send_msg commander lieutenant1 r (s commander) := by simp [inbox]

example : inbox followCommander (some commander) silent 0 (fun _ => 1)
    lieutenant1 commander = none := by decide
