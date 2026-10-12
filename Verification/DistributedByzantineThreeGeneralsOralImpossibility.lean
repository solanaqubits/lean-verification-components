/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedCoordinatedAttackImpossibility

/-!
# Three generals: impossibility of oral Byzantine broadcast

Synchronous rounds, reliable authenticated immediate senders, no transferable
signatures, one static faulty identity, and an arbitrary fixed finite horizon.
The four-state simulation constructs adversarial schedules from earlier states;
local indistinguishability is proved from transitions, not assumed.
-/

namespace DistributedByzantineThreeGeneralsOralImpossibility

inductive Node where
  | commander | lieutenant1 | lieutenant2
  deriving DecidableEq, Repr

open Node

abbrev Order := Fin 2
abbrev Fault := Option Node
abbrev Adversary (T : ℕ) (Msg : Type) := Node → Fin T → Option Msg

/-- Only the commander initially receives the private order. Honest sends can
vary by recipient. The inbox records the immediate sender, never a signature. -/
structure Protocol (T : ℕ) (Msg State : Type) where
  initial_state : Node → Option Order → State
  send_msg : Node → Node → Fin T → State → Option Msg
  step : Node → Fin T → State → (Node → Option Msg) → State
  decide : Node → State → Order

variable {T : ℕ} {Msg State : Type}

def initial (P : Protocol T Msg State) (v : Order) (p : Node) : State :=
  P.initial_state p (if p = commander then some v else none)

/-- A schedule describes all outgoing messages of the single faulty identity.
Universal quantification includes every transcript of an adaptive adversary. -/
def inbox (P : Protocol T Msg State) (fault : Fault) (adv : Adversary T Msg)
    (r : Fin T) (st : Node → State) (recipient sender : Node) : Option Msg :=
  if sender = recipient then none
  else if fault = some sender then adv recipient r
  else P.send_msg sender recipient r (st sender)

def execution (P : Protocol T Msg State) (v : Order) (fault : Fault)
    (adv : Adversary T Msg) : ℕ → Node → State
  | 0 => initial P v
  | r + 1 => fun p => if h : r < T then
      P.step p ⟨r, h⟩ (execution P v fault adv r p)
        (inbox P fault adv ⟨r, h⟩ (execution P v fault adv r) p)
    else execution P v fault adv r p

def decision (P : Protocol T Msg State) (v : Order) (fault : Fault)
    (adv : Adversary T Msg) (p : Node) : Order :=
  P.decide p (execution P v fault adv T p)

def Agreement (P : Protocol T Msg State) : Prop :=
  ∀ v fault adv, fault ≠ some lieutenant1 → fault ≠ some lieutenant2 →
    decision P v fault adv lieutenant1 = decision P v fault adv lieutenant2

def CommanderValidity (P : Protocol T Msg State) : Prop :=
  ∀ v fault adv, fault ≠ some commander → ∀ p, p ≠ commander → fault ≠ some p →
    decision P v fault adv p = v

/-- Two commander copies and two shared lieutenants, updated simultaneously. -/
structure VirtualState (State : Type) where
  c0 : State
  c1 : State
  l1 : State
  l2 : State

def virtualStep (P : Protocol T Msg State) (r : Fin T) (s : VirtualState State) :
    VirtualState State where
  c0 := P.step commander r s.c0 (fun p => match p with
    | commander => none
    | lieutenant1 => P.send_msg lieutenant1 commander r s.l1
    | lieutenant2 => none)
  c1 := P.step commander r s.c1 (fun p => match p with
    | commander => none
    | lieutenant1 => none
    | lieutenant2 => P.send_msg lieutenant2 commander r s.l2)
  l1 := P.step lieutenant1 r s.l1 (fun p => match p with
    | commander => P.send_msg commander lieutenant1 r s.c0
    | lieutenant1 => none
    | lieutenant2 => P.send_msg lieutenant2 lieutenant1 r s.l2)
  l2 := P.step lieutenant2 r s.l2 (fun p => match p with
    | commander => P.send_msg commander lieutenant2 r s.c1
    | lieutenant1 => P.send_msg lieutenant1 lieutenant2 r s.l1
    | lieutenant2 => none)

def virtualExecution (P : Protocol T Msg State) : ℕ → VirtualState State
  | 0 => ⟨initial P 0 commander, initial P 1 commander,
      initial P 0 lieutenant1, initial P 0 lieutenant2⟩
  | r + 1 => if h : r < T then virtualStep P ⟨r, h⟩ (virtualExecution P r)
      else virtualExecution P r

def adv0 (P : Protocol T Msg State) : Adversary T Msg := fun p r =>
  match p with
  | lieutenant1 => P.send_msg lieutenant2 lieutenant1 r (virtualExecution P r.val).l2
  | _ => none

def adv1 (P : Protocol T Msg State) : Adversary T Msg := fun p r =>
  match p with
  | lieutenant2 => P.send_msg lieutenant1 lieutenant2 r (virtualExecution P r.val).l1
  | _ => none

def adv2 (P : Protocol T Msg State) : Adversary T Msg := fun p r =>
  match p with
  | commander => none
  | lieutenant1 => P.send_msg commander lieutenant1 r (virtualExecution P r.val).c0
  | lieutenant2 => P.send_msg commander lieutenant2 r (virtualExecution P r.val).c1

theorem scenario0_simulation (P : Protocol T Msg State) (r : ℕ) :
    execution P 0 (some lieutenant2) (adv0 P) r commander = (virtualExecution P r).c0 ∧
    execution P 0 (some lieutenant2) (adv0 P) r lieutenant1 = (virtualExecution P r).l1 := by
  induction r with
  | zero => exact ⟨rfl, rfl⟩
  | succ r ih =>
    by_cases h : r < T
    · simp only [execution, virtualExecution, h, ↓reduceDIte]
      constructor
      · apply congrArg₂ (P.step commander ⟨r, h⟩) ih.1
        funext p
        cases p <;> simp [inbox, adv0, ih.2]
      · apply congrArg₂ (P.step lieutenant1 ⟨r, h⟩) ih.2
        funext p
        cases p <;> simp [inbox, adv0, ih.1]
    · simpa only [execution, virtualExecution, h, ↓reduceDIte] using ih

theorem scenario1_simulation (P : Protocol T Msg State) (r : ℕ) :
    execution P 1 (some lieutenant1) (adv1 P) r commander = (virtualExecution P r).c1 ∧
    execution P 1 (some lieutenant1) (adv1 P) r lieutenant2 = (virtualExecution P r).l2 := by
  induction r with
  | zero => constructor <;> simp [execution, virtualExecution, initial]
  | succ r ih =>
    by_cases h : r < T
    · simp only [execution, virtualExecution, h, ↓reduceDIte]
      constructor
      · apply congrArg₂ (P.step commander ⟨r, h⟩) ih.1
        funext p
        cases p <;> simp [inbox, adv1, ih.2]
      · apply congrArg₂ (P.step lieutenant2 ⟨r, h⟩) ih.2
        funext p
        cases p <;> simp [inbox, adv1, ih.1]
    · simpa only [execution, virtualExecution, h, ↓reduceDIte] using ih

theorem scenario2_simulation (P : Protocol T Msg State) (r : ℕ) :
    execution P 0 (some commander) (adv2 P) r lieutenant1 = (virtualExecution P r).l1 ∧
    execution P 0 (some commander) (adv2 P) r lieutenant2 = (virtualExecution P r).l2 := by
  induction r with
  | zero => exact ⟨rfl, rfl⟩
  | succ r ih =>
    by_cases h : r < T
    · simp only [execution, virtualExecution, h, ↓reduceDIte]
      constructor
      · apply congrArg₂ (P.step lieutenant1 ⟨r, h⟩) ih.1
        funext p
        cases p <;> simp [inbox, adv2, ih.2]
      · apply congrArg₂ (P.step lieutenant2 ⟨r, h⟩) ih.2
        funext p
        cases p <;> simp [inbox, adv2, ih.1]
    · simpa only [execution, virtualExecution, h, ↓reduceDIte] using ih

theorem local_state_induction_scen0_scen2 (P : Protocol T Msg State) (r : ℕ) :
    execution P 0 (some lieutenant2) (adv0 P) r lieutenant1 =
      execution P 0 (some commander) (adv2 P) r lieutenant1 :=
  (scenario0_simulation P r).2.trans (scenario2_simulation P r).1.symm

theorem local_state_induction_scen1_scen2 (P : Protocol T Msg State) (r : ℕ) :
    execution P 1 (some lieutenant1) (adv1 P) r lieutenant2 =
      execution P 0 (some commander) (adv2 P) r lieutenant2 :=
  (scenario1_simulation P r).2.trans (scenario2_simulation P r).2.symm

theorem lieutenant1_decides_zero (P : Protocol T Msg State) (hv : CommanderValidity P) :
    decision P 0 (some commander) (adv2 P) lieutenant1 = 0 := by
  have h := hv 0 (some lieutenant2) (adv0 P) (by decide) lieutenant1
    (by decide) (by decide)
  simpa only [decision, local_state_induction_scen0_scen2] using h

theorem lieutenant2_decides_one (P : Protocol T Msg State) (hv : CommanderValidity P) :
    decision P 0 (some commander) (adv2 P) lieutenant2 = 1 := by
  have h := hv 1 (some lieutenant1) (adv1 P) (by decide) lieutenant2
    (by decide) (by decide)
  simpa only [decision, local_state_induction_scen1_scen2] using h

theorem byzantine_three_generals_oral_impossibility (P : Protocol T Msg State) :
    ¬ (Agreement P ∧ CommanderValidity P) := by
  rintro ⟨ha, hv⟩
  have h := ha 0 (some commander) (adv2 P) (by decide) (by decide)
  rw [lieutenant1_decides_zero P hv, lieutenant2_decides_one P hv] at h
  exact (by decide : (0 : Order) ≠ 1) h

theorem no_correct_protocol (T : ℕ) :
    ¬ ∃ (Msg State : Type) (P : Protocol T Msg State), Agreement P ∧ CommanderValidity P := by
  rintro ⟨Msg, State, P, h⟩
  exact byzantine_three_generals_oral_impossibility P h

def silent : Adversary T Msg := fun _ _ => none

def retreatProtocol (T : ℕ) : Protocol T Unit Unit where
  initial_state := fun _ _ => ()
  send_msg := fun _ _ _ _ => none
  step := fun _ _ _ _ => ()
  decide := fun _ _ => 0

theorem constant_retreat_regression (T : ℕ) :
    Agreement (retreatProtocol T) ∧ ¬ CommanderValidity (retreatProtocol T) := by
  constructor
  · intro _ _ _ _ _; rfl
  · intro hv
    have h := hv 1 none silent (by decide) lieutenant1 (by decide) (by decide)
    exact (by decide : (0 : Order) ≠ 1) h

theorem zero_horizon_impossibility (P : Protocol 0 Msg State) :
    ¬ (Agreement P ∧ CommanderValidity P) := byzantine_three_generals_oral_impossibility P

/-- One round suffices for validity, but an equivocating commander breaks agreement. -/
def followCommander : Protocol 1 Order Order where
  initial_state := fun _ input => input.getD 0
  send_msg := fun _ _ _ s => some s
  step := fun p _ s box => if p = commander then s else (box commander).getD 0
  decide := fun _ s => s

theorem follow_commander_validity : CommanderValidity followCommander := by
  intro v fault adv hc p hp hf
  cases p with
  | commander => exact (hp rfl).elim
  | lieutenant1 => simp [decision, execution, initial, inbox, followCommander, hc]
  | lieutenant2 => simp [decision, execution, initial, inbox, followCommander, hc]

def conflictingOrders : Adversary 1 Order := fun p _ =>
  if p = lieutenant2 then some 1 else some 0

theorem conflicting_orders_regression :
    decision followCommander 0 (some commander) conflictingOrders lieutenant1 = 0 ∧
    decision followCommander 0 (some commander) conflictingOrders lieutenant2 = 1 := by decide

theorem naive_follow_commander_violates_agreement :
    CommanderValidity followCommander ∧ ¬ Agreement followCommander := by
  refine ⟨follow_commander_validity, ?_⟩
  intro ha
  have h := ha 0 (some commander) conflictingOrders (by decide) (by decide)
  rw [conflicting_orders_regression.1, conflicting_orders_regression.2] at h
  exact (by decide : (0 : Order) ≠ 1) h

theorem all_honest_follow_commander (v : Order) :
    decision followCommander v none silent lieutenant1 = v ∧
    decision followCommander v none silent lieutenant2 = v := by
  constructor
  · exact follow_commander_validity v none silent (by decide) lieutenant1 (by decide) (by decide)
  · exact follow_commander_validity v none silent (by decide) lieutenant2 (by decide) (by decide)

structure DistributedByzantineThreeGeneralsOralImpossibilitySuite : Prop where
  histories0 : ∀ (T : ℕ) (Msg State : Type) (P : Protocol T Msg State) r,
    execution P 0 (some lieutenant2) (adv0 P) r lieutenant1 =
      execution P 0 (some commander) (adv2 P) r lieutenant1
  histories1 : ∀ (T : ℕ) (Msg State : Type) (P : Protocol T Msg State) r,
    execution P 1 (some lieutenant1) (adv1 P) r lieutenant2 =
      execution P 0 (some commander) (adv2 P) r lieutenant2
  impossible : ∀ T, ¬ ∃ (Msg State : Type) (P : Protocol T Msg State),
    Agreement P ∧ CommanderValidity P
  constant_retreat : ∀ T,
    Agreement (retreatProtocol T) ∧ ¬ CommanderValidity (retreatProtocol T)
  zero_rounds : ∀ (Msg State : Type) (P : Protocol 0 Msg State),
    ¬ (Agreement P ∧ CommanderValidity P)
  naive_protocol : CommanderValidity followCommander ∧ ¬ Agreement followCommander
  honest_execution : ∀ v, decision followCommander v none silent lieutenant1 = v ∧
    decision followCommander v none silent lieutenant2 = v

theorem byzantine_three_generals_oral_master_suite :
    DistributedByzantineThreeGeneralsOralImpossibilitySuite where
  histories0 := fun _ _ _ => local_state_induction_scen0_scen2
  histories1 := fun _ _ _ => local_state_induction_scen1_scen2
  impossible := no_correct_protocol
  constant_retreat := constant_retreat_regression
  zero_rounds := fun _ _ => zero_horizon_impossibility
  naive_protocol := naive_follow_commander_violates_agreement
  honest_execution := all_honest_follow_commander

end DistributedByzantineThreeGeneralsOralImpossibility
