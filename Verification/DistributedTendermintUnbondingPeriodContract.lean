/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedTendermintSlashingReplayProtection

/-! A sequential two-phase slot model. A queued tranche is liable only for heights
at or before its request. Closing admission asserts that the supplied slot batch
is complete; network delivery, authenticated clocks and persistent storage are external. -/
namespace DistributedTendermintUnbondingPeriodContract
open Finset DistributedTendermintCoreSafety DistributedTendermintAccountableSafety
open DistributedTendermintSlashingPenaltyContract DistributedTendermintSlashingReplayProtection

inductive Phase where
  | admission | withdrawal
  deriving DecidableEq, Repr

structure Window where
  duration : ℕ
  positive : 0 < duration

@[ext] structure Withdrawal (V : Type*) where
  validator : V
  amount : ℚ
  requested : ℕ
  deriving DecidableEq

def Withdrawal.maturity (q : Withdrawal V) (w : Window) : ℕ := q.requested + w.duration

@[ext] structure UnbondingState (V : Type*) where
  now : ℕ
  phase : Phase
  active : V → ℚ
  queue : List (Withdrawal V)
  confiscated : ℚ
  completed : V → ℚ
  processed : Finset (ℕ × V)

variable {V : Type*} [DecidableEq V]

def is_timely (w : Window) (h τ : ℕ) : Prop := h ≤ τ ∧ τ ≤ h + w.duration
instance (w : Window) (h τ : ℕ) : Decidable (is_timely w h τ) :=
  inferInstanceAs (Decidable (h ≤ τ ∧ τ ≤ h + w.duration))

def queueValue (qs : List (Withdrawal V)) : ℚ := (qs.map Withdrawal.amount).sum

def eligibleMass (qs : List (Withdrawal V)) (h : ℕ) (v : V) : ℚ :=
  (qs.map fun q => if q.validator = v ∧ h ≤ q.requested then q.amount else 0).sum

def available (s : UnbondingState V) (h : ℕ) (v : V) : ℚ :=
  s.active v + eligibleMass s.queue h v

def toLedger (s : UnbondingState V) (h : ℕ) : SlashingLedgerState V :=
  ⟨available s h, s.confiscated, s.processed⟩

def slashQueue (qs : List (Withdrawal V)) (h : ℕ) (B : Finset V) (α : ℚ) :=
  qs.map fun q => if q.validator ∈ B ∧ h ≤ q.requested then
    { q with amount := (1 - α) * q.amount } else q

/-- Internal algebraic step; the checked interface derives B from real evidence. -/
def slashSet (s : UnbondingState V) (h : ℕ) (B : Finset V) (α : ℚ) : UnbondingState V :=
  let fresh := freshOffenders (toLedger s h) h B
  let next := applyCertifiedSet (toLedger s h) h B α
  { s with active := stakeSlashing s.active fresh α,
           queue := slashQueue s.queue h fresh α,
           confiscated := next.confiscated, processed := next.processed }

theorem eligible_slash (qs : List (Withdrawal V)) (h : ℕ) (B : Finset V) (α : ℚ) (v : V) :
    eligibleMass (slashQueue qs h B α) h v =
      if v ∈ B then (1 - α) * eligibleMass qs h v else eligibleMass qs h v := by
  induction qs with
  | nil => simp [slashQueue, eligibleMass]
  | cons q qs ih =>
    by_cases he : q.validator = v
    · subst v
      by_cases hb : q.validator ∈ B <;> by_cases ht : h ≤ q.requested <;>
        simpa [slashQueue, eligibleMass, hb, ht, mul_add] using ih
    · by_cases hb : v ∈ B <;> by_cases hq : q.validator ∈ B <;>
        by_cases ht : h ≤ q.requested <;>
          simpa [slashQueue, eligibleMass, he, hb, hq, ht] using ih

theorem ledger_refinement (s : UnbondingState V) (h : ℕ) (B : Finset V) (α : ℚ) :
    toLedger (slashSet s h B α) h = applyCertifiedSet (toLedger s h) h B α := by
  apply SlashingLedgerState.ext
  · funext v
    change stakeSlashing s.active (freshOffenders (toLedger s h) h B) α v +
      eligibleMass (slashQueue s.queue h (freshOffenders (toLedger s h) h B) α) h v =
      stakeSlashing (available s h) (freshOffenders (toLedger s h) h B) α v
    rw [eligible_slash]
    unfold stakeSlashing
    split_ifs <;> simp [available, mul_add]
  · rfl
  · rfl

def WellFormed (s : UnbondingState V) : Prop :=
  (∀ v, 0 ≤ s.active v) ∧ (∀ q ∈ s.queue, 0 ≤ q.amount) ∧
    0 ≤ s.confiscated ∧ (∀ v, 0 ≤ s.completed v)

theorem eligible_nonnegative (qs : List (Withdrawal V)) (h : ℕ) (v : V)
    (hq : ∀ q ∈ qs, 0 ≤ q.amount) : 0 ≤ eligibleMass qs h v := by
  induction qs with
  | nil => simp [eligibleMass]
  | cons q qs ih =>
    simp only [eligibleMass, List.map_cons, List.sum_cons]
    apply add_nonneg
    · split <;> simp_all
    · exact ih (fun a ha => hq a (List.mem_cons_of_mem _ ha))

theorem available_nonnegative (s : UnbondingState V) (hw : WellFormed s) h v :
    0 ≤ available s h v := add_nonneg (hw.1 v) (eligible_nonnegative _ _ _ hw.2.1)

theorem slash_wellFormed (s : UnbondingState V) h B α (hw : WellFormed s)
    (ha : 0 ≤ α) (ha1 : α ≤ 1) : WellFormed (slashSet s h B α) := by
  refine ⟨slashing_nonnegative _ _ _ hw.1 ha1, ?_, ?_, hw.2.2.2⟩
  · intro q hq
    obtain ⟨a, ham, rfl⟩ := List.mem_map.mp hq
    split
    · exact mul_nonneg (sub_nonneg.mpr ha1) (hw.2.1 a ham)
    · exact hw.2.1 a ham
  · exact add_nonneg hw.2.2.1 (confiscated_nonnegative _ _ _
      (available_nonnegative s hw h) ha)

section Finite
variable [Fintype V]

def totalValue (s : UnbondingState V) : ℚ :=
  totalStake s.active + queueValue s.queue + s.confiscated + totalStake s.completed

omit [Fintype V] in
theorem eligible_total (qs : List (Withdrawal V)) h (B : Finset V) :
    stakeMass (eligibleMass qs h) B =
      (qs.map fun q => if q.validator ∈ B ∧ h ≤ q.requested then q.amount else 0).sum := by
  induction qs with
  | nil => simp [eligibleMass, stakeMass]
  | cons q qs ih =>
    simp only [eligibleMass, List.map_cons, List.sum_cons, stakeMass, Finset.sum_add_distrib] at *
    rw [ih]
    congr 1
    by_cases ht : h ≤ q.requested <;> simp [ht, eq_comm]

omit [Fintype V] in
theorem queue_debit (qs : List (Withdrawal V)) h B α :
    queueValue (slashQueue qs h B α) + α * stakeMass (eligibleMass qs h) B = queueValue qs := by
  rw [eligible_total]
  induction qs with
  | nil => simp [slashQueue, queueValue]
  | cons q qs ih =>
    by_cases hc : q.validator ∈ B ∧ h ≤ q.requested <;>
      simp [slashQueue, queueValue, hc] at ih ⊢ <;> linarith

theorem slash_conservation (s : UnbondingState V) h B α :
    totalValue (slashSet s h B α) = totalValue s := by
  let fresh := freshOffenders (toLedger s h) h B
  have hc := slashing_conservation s.active fresh α
  have hq := queue_debit s.queue h fresh α
  rw [confiscated_eq] at hc
  have hm : stakeMass (available s h) fresh =
      stakeMass s.active fresh + stakeMass (eligibleMass s.queue h) fresh := by
    simp [stakeMass, available, Finset.sum_add_distrib]
  dsimp [totalValue, slashSet, applyCertifiedSet]
  rw [confiscated_eq]
  change totalStake (stakeSlashing s.active fresh α) + queueValue (slashQueue s.queue h fresh α) +
    (s.confiscated + α * stakeMass (available s h) fresh) + totalStake s.completed = _
  rw [hm]
  dsimp [fresh] at hc hq
  linarith
end Finite

/-- Rejected time, phase, rate, or evidence leaves every field unchanged. -/
def slash_unbonding {n : ℕ} (w : Window) (c : Config n) (reference : Option (Finset (Vote n)))
  (e : EvidenceView n) (α : ℚ)
    (s : UnbondingState (Fin n)) : UnbondingState (Fin n) :=
  if s.phase = .admission ∧ is_timely w c.height s.now ∧ 0 < α ∧ α ≤ 1 then
    match attribute_evidence c reference e with
    | .error _ => s
    | .ok B => slashSet s c.height B α
  else s

theorem accepted_certificate {n : ℕ} (w : Window) (c : Config n) reference e α
    (s : UnbondingState (Fin n)) B (hc : attribute_evidence c reference e = .ok B)
    (hg : s.phase = .admission ∧ is_timely w c.height s.now ∧ 0 < α ∧ α ≤ 1) :
    slash_unbonding w c reference e α s = slashSet s c.height B α := by
  simp [slash_unbonding, hg, hc]

theorem no_future_evidence_accepted {n : ℕ} (w : Window) (c : Config n) reference e α
    (s : UnbondingState (Fin n)) (hh : s.now < c.height) :
    slash_unbonding w c reference e α s = s := by
  simp [slash_unbonding, is_timely, Nat.not_le_of_lt hh]

theorem expired_evidence_rejected {n : ℕ} (w : Window) (c : Config n) reference e α
    (s : UnbondingState (Fin n)) (hh : c.height + w.duration < s.now) :
    slash_unbonding w c reference e α s = s := by
  simp [slash_unbonding, is_timely, Nat.not_le_of_lt hh]

theorem closed_admission_rejected {n : ℕ} (w : Window) (c : Config n) reference e α
    (s : UnbondingState (Fin n)) (hp : s.phase = .withdrawal) :
    slash_unbonding w c reference e α s = s := by
  simp [slash_unbonding, hp]

theorem invalid_certificate_noop {n : ℕ} (w : Window) (c : Config n) reference e α
    (s : UnbondingState (Fin n)) err (he : attribute_evidence c reference e = .error err) :
    slash_unbonding w c reference e α s = s := by simp [slash_unbonding, he]

theorem checked_conservation {n : ℕ} (w : Window) (c : Config n) reference e α
    (s : UnbondingState (Fin n)) :
    totalValue (slash_unbonding w c reference e α s) = totalValue s := by
  unfold slash_unbonding
  split_ifs
  · cases attribute_evidence c reference e with
    | error _ => rfl
    | ok B => exact slash_conservation s c.height B α
  · rfl

theorem checked_wellFormed {n : ℕ} (w : Window) (c : Config n) reference e α
    (s : UnbondingState (Fin n)) (hw : WellFormed s) :
    WellFormed (slash_unbonding w c reference e α s) := by
  unfold slash_unbonding
  split_ifs with hg
  · cases attribute_evidence c reference e with
    | error _ => exact hw
    | ok B => exact slash_wellFormed s c.height B α hw (le_of_lt hg.2.2.1) hg.2.2.2
  · exact hw

/-- The request moves existing value; it neither creates value nor clears replay keys. -/
def request_unbonding (s : UnbondingState V) (v : V) (amount : ℚ) : UnbondingState V :=
  if s.phase = .admission ∧ 0 < amount ∧ amount ≤ s.active v then
    { s with
      active := (fun u => if u = v then s.active u - amount else s.active u)
      queue := ⟨v, amount, s.now⟩ :: s.queue }
  else s

/-- This boundary closes certificate admission for the current slot. -/
def close_admission (s : UnbondingState V) : UnbondingState V :=
  { s with phase := .withdrawal }

def matured (w : Window) (s : UnbondingState V) : List (Withdrawal V) :=
  s.queue.filter fun q => q.maturity w ≤ s.now

def pending (w : Window) (s : UnbondingState V) : List (Withdrawal V) :=
  s.queue.filter fun q => ¬ q.maturity w ≤ s.now

/-- Only reduced, currently held amounts are paid. No remembered face-value is used. -/
def finalize_unbonding (w : Window) (s : UnbondingState V) : UnbondingState V :=
  if s.phase = .withdrawal then
    { s with queue := pending w s
             completed := fun v => s.completed v + eligibleMass (matured w s) 0 v }
  else s

/-- Time cannot advance while certificate admission is open. -/
def advance_time (s : UnbondingState V) : UnbondingState V :=
  if s.phase = .withdrawal then { s with now := s.now + 1, phase := .admission } else s

theorem admission_finalize_noop (w : Window) (s : UnbondingState V)
    (hp : s.phase = .admission) : finalize_unbonding w s = s := by
  simp [finalize_unbonding, hp]

omit [DecidableEq V] in
theorem no_escape_theorem (w : Window) (q : Withdrawal V) h τ
    (hli : h ≤ q.requested) (ht : is_timely w h τ) : τ ≤ q.maturity w :=
  ht.2.trans (Nat.add_le_add_right hli w.duration)

/-- Before maturity the tranche survives finalization; at equality admission blocks it. -/
theorem no_early_withdrawal (w : Window) (s : UnbondingState V) (q : Withdrawal V)
    (hq : q ∈ s.queue) (ht : s.now < q.maturity w) :
    q ∈ (finalize_unbonding w s).queue := by
  unfold finalize_unbonding
  split_ifs
  · simpa [pending, hq] using ht
  · exact hq

theorem no_escape_at_admission (w : Window) (s : UnbondingState V) (q : Withdrawal V)
    (hq : q ∈ s.queue) (hp : s.phase = .admission) :
    q ∈ (finalize_unbonding w s).queue := by rw [admission_finalize_noop w s hp]; exact hq

theorem later_offence_excluded (q : Withdrawal V) h B α (hh : q.requested < h) :
    slashQueue [q] h B α = [q] := by
  simp [slashQueue, Nat.not_le_of_lt hh]

theorem request_wellFormed (s : UnbondingState V) v amount (hw : WellFormed s) :
    WellFormed (request_unbonding s v amount) := by
  unfold request_unbonding
  split_ifs with hg
  · refine ⟨?_, ?_, hw.2.2⟩
    · intro u
      dsimp
      split_ifs with he
      · subst u; exact sub_nonneg.mpr hg.2.2
      · exact hw.1 u
    · intro q hq
      rcases List.mem_cons.mp hq with he | hm
      · subst q; exact le_of_lt hg.2.1
      · exact hw.2.1 q hm
  · exact hw

theorem finalize_wellFormed (w : Window) (s : UnbondingState V) (hw : WellFormed s) :
    WellFormed (finalize_unbonding w s) := by
  unfold finalize_unbonding
  split_ifs
  · refine ⟨hw.1, ?_, hw.2.2.1, ?_⟩
    · intro q hq; exact hw.2.1 q (List.mem_filter.mp hq).1
    · intro v
      apply add_nonneg (hw.2.2.2 v)
      apply eligible_nonnegative
      intro q hq; exact hw.2.1 q (List.mem_filter.mp hq).1
  · exact hw

omit [DecidableEq V] in
theorem close_wellFormed (s : UnbondingState V) (hw : WellFormed s) :
    WellFormed (close_admission s) := hw

omit [DecidableEq V] in
theorem advance_wellFormed (s : UnbondingState V) (hw : WellFormed s) :
    WellFormed (advance_time s) := by unfold advance_time; split_ifs <;> exact hw

section Finite
variable [Fintype V]

theorem request_conservation (s : UnbondingState V) v amount :
    totalValue (request_unbonding s v amount) = totalValue s := by
  unfold request_unbonding
  split_ifs
  · have he : (fun u => if u = v then s.active u - amount else s.active u) =
        fun u => s.active u - if u = v then amount else 0 := by
      funext u; split_ifs <;> simp
    simp [totalValue, he, totalStake, stakeMass, Finset.sum_sub_distrib, queueValue]
    ring
  · rfl

omit [Fintype V] [DecidableEq V] in
theorem partition_value (w : Window) (qs : List (Withdrawal V)) τ :
    queueValue (qs.filter fun q => ¬ q.maturity w ≤ τ) +
      queueValue (qs.filter fun q => q.maturity w ≤ τ) = queueValue qs := by
  induction qs with
  | nil => simp [queueValue]
  | cons q qs ih =>
    by_cases ht : q.maturity w ≤ τ
    · simp [ht, queueValue] at ih ⊢; linarith
    · have hn := Nat.lt_of_not_ge ht
      simp [ht, hn, queueValue] at ih ⊢; linarith

theorem finalize_conservation (w : Window) (s : UnbondingState V) :
    totalValue (finalize_unbonding w s) = totalValue s := by
  unfold finalize_unbonding
  split_ifs
  · have hm := eligible_total (matured w s) 0 (Finset.univ : Finset V)
    simp only [Finset.mem_univ, Nat.zero_le, and_self, if_true] at hm
    have hp := partition_value w s.queue s.now
    simp only [totalValue, totalStake, stakeMass, Finset.sum_add_distrib]
    change _ + _ + _ + ((∑ v, s.completed v) + stakeMass (eligibleMass (matured w s) 0) univ) = _
    rw [hm]
    change _ + _ + _ + (_ + queueValue (matured w s)) = _
    dsimp [pending, matured]
    linarith
  · rfl

omit [DecidableEq V] in
theorem close_conservation (s : UnbondingState V) :
    totalValue (close_admission s) = totalValue s := rfl

omit [DecidableEq V] in
theorem advance_conservation (s : UnbondingState V) :
    totalValue (advance_time s) = totalValue s := by
  unfold advance_time; split_ifs <;> rfl
end Finite

/-- Exact payout formula, also for a slot whose certificate batch is empty. -/
theorem honest_liveness_theorem (w : Window) (s : UnbondingState V) (v : V) :
    (finalize_unbonding w (close_admission s)).completed v =
      s.completed v + eligibleMass (matured w s) 0 v := by
  simp [finalize_unbonding, close_admission, matured]
  rfl

theorem singleton_full_withdrawal (w : Window) (s : UnbondingState V) (q : Withdrawal V)
    (hq : s.queue = [q]) (ht : q.maturity w ≤ s.now) :
    (finalize_unbonding w (close_admission s)).completed q.validator =
      s.completed q.validator + q.amount := by
  rw [honest_liveness_theorem]
  simp [matured, hq, ht, eligibleMass]

/-- At the inclusive deadline a liable tranche is reduced before it can be paid. -/
theorem deadline_precedence_theorem (w : Window) (s : UnbondingState V)
    (q : Withdrawal V) h B α (hq : s.queue = [q])
    (hb : q.validator ∈ B) (hf : (h, q.validator) ∉ s.processed)
    (hli : h ≤ q.requested) (hd : s.now = h + w.duration)
    (hm : q.maturity w = s.now) :
    (finalize_unbonding w (close_admission (slashSet s h B α))).completed q.validator =
      s.completed q.validator + (1 - α) * q.amount := by
  have hmat : q.requested + w.duration ≤ s.now := by
    exact Nat.le_of_eq hm
  have hq' : (slashSet s h B α).queue = [{ q with amount := (1 - α) * q.amount }] := by
    simp [slashSet, slashQueue, hq, hb, hf, toLedger, hli]
  have hd' : h ≤ s.now := by omega
  have _ht : is_timely w h s.now := ⟨hd', Nat.le_of_eq hd⟩
  rw [honest_liveness_theorem]
  change s.completed q.validator + eligibleMass
    ((slashSet s h B α).queue.filter (fun a => a.maturity w ≤ s.now)) 0 q.validator = _
  rw [hq']
  simp [Withdrawal.maturity, hmat, eligibleMass]

/-- Conservation and nonnegativity for the supplied, sequential certificate batch. -/
def processSlot {n : ℕ} (w : Window) (α : ℚ) (s : UnbondingState (Fin n))
    (requests : List (CertificateRequest n)) : UnbondingState (Fin n) :=
  advance_time (finalize_unbonding w (close_admission
    (requests.foldl (fun st req
      => slash_unbonding w req.config req.reference req.evidence α st) s)))

theorem batch_conservation {n : ℕ} (w : Window) α (rs : List (CertificateRequest n))
    (s : UnbondingState (Fin n)) :
    totalValue (rs.foldl (fun st req
      => slash_unbonding w req.config req.reference req.evidence α st) s) =
      totalValue s := by
  induction rs generalizing s with
  | nil => rfl
  | cons req rs ih =>
    rw [List.foldl_cons, ih, checked_conservation]

theorem total_value_conservation {n : ℕ} (w : Window) α (s : UnbondingState (Fin n)) rs :
    totalValue (processSlot w α s rs) = totalValue s := by
  rw [processSlot, advance_conservation, finalize_conservation, close_conservation,
    batch_conservation]

theorem batch_wellFormed {n : ℕ} (w : Window) α (rs : List (CertificateRequest n))
    (s : UnbondingState (Fin n)) (hw : WellFormed s) :
    WellFormed (rs.foldl (fun st req
      => slash_unbonding w req.config req.reference req.evidence α st) s) := by
  induction rs generalizing s with
  | nil => exact hw
  | cons req rs ih => exact ih _ (checked_wellFormed w req.config req.reference req.evidence α s hw)

theorem slot_wellFormed {n : ℕ} (w : Window) α (s : UnbondingState (Fin n)) rs (hw : WellFormed s) :
    WellFormed (processSlot w α s rs) :=
  advance_wellFormed _ (finalize_wellFormed w _ (close_wellFormed _ (batch_wellFormed w α rs s hw)))


theorem no_fresh_noop (s : UnbondingState V) h B α
    (hf : freshOffenders (toLedger s h) h B = ∅) : slashSet s h B α = s := by
  have he := DistributedTendermintSlashingReplayProtection.no_fresh_noop (toLedger s h) h B α hf
  simp only [slashSet, hf, he]
  simp [slashQueue, toLedger]

theorem replay_set (s : UnbondingState V) h B α β :
    slashSet (slashSet s h B α) h B β = slashSet s h B α := by
  apply no_fresh_noop
  rw [ledger_refinement]
  ext v
  simp
  tauto

theorem replay_idempotence {n : ℕ} (w : Window) (c : Config n) reference e α
    (s : UnbondingState (Fin n)) :
    slash_unbonding w c reference e α (slash_unbonding w c reference e α s) =
      slash_unbonding w c reference e α s := by
  by_cases hg : s.phase = .admission ∧ is_timely w c.height s.now ∧ 0 < α ∧ α ≤ 1
  · cases hc : attribute_evidence c reference e with
    | error err => simp only [invalid_certificate_noop w c reference e α s err hc]
    | ok B =>
      rw [accepted_certificate w c reference e α s B hc hg]
      rw [accepted_certificate w c reference e α (slashSet s c.height B α) B hc hg]
      exact replay_set s c.height B α α
  · have he : slash_unbonding w c reference e α s = s := by simp [slash_unbonding, hg]
    simp only [he]

/-- The current eligible stake is positive, not merely its historical face value. -/
theorem positive_confiscation (s : UnbondingState V) h B α v (hw : WellFormed s)
    (hb : v ∈ B) (hf : (h, v) ∉ s.processed) (ha : 0 < α)
    (hp : 0 < available s h v) : s.confiscated < (slashSet s h B α).confiscated := by
  have hv : v ∈ freshOffenders (toLedger s h) h B := by simp [toLedger, hb, hf]
  have hs : available s h v ≤ stakeMass (available s h) (freshOffenders (toLedger s h) h B) :=
    Finset.single_le_sum (fun a _ => available_nonnegative s hw h a) hv
  have hm := mul_pos ha (lt_of_lt_of_le hp hs)
  change s.confiscated < s.confiscated + confiscated (available s h) _ α
  rw [confiscated_eq]
  linarith

theorem timely_slashing_guarantee {n : ℕ} (w : Window) (c : Config n) reference e α
    (s : UnbondingState (Fin n)) B v (hc : attribute_evidence c reference e = .ok B)
    (hg : s.phase = .admission ∧ is_timely w c.height s.now ∧ 0 < α ∧ α ≤ 1)
    (hw : WellFormed s) (hb : v ∈ B) (hf : (c.height, v) ∉ s.processed)
    (hp : 0 < available s c.height v) :
    s.confiscated < (slash_unbonding w c reference e α s).confiscated := by
  rw [accepted_certificate w c reference e α s B hc hg]
  exact positive_confiscation s c.height B α v hw hb hf hg.2.2.1 hp

omit [DecidableEq V] in
/-- A prior slot cannot already have paid a liable tranche while evidence is timely now. -/
theorem no_prior_finalization (w : Window) (q : Withdrawal V) h τ previous
    (hli : h ≤ q.requested) (ht : is_timely w h τ) (hp : previous < τ) :
    ¬ q.maturity w ≤ previous := by
  have he := no_escape_theorem w q h τ hli ht
  omega

theorem slash_queue_unchanged (qs : List (Withdrawal V)) h B α
    (hs : ∀ q ∈ qs, q.validator ∉ B ∨ q.requested < h) : slashQueue qs h B α = qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    have hi := ih (fun a ha => hs a (List.mem_cons_of_mem q ha))
    rcases hs q (by simp) with hb | ht
    · simp only [slashQueue, List.map_cons] at *
      simp [hb, hi]
    · simp only [slashQueue, List.map_cons] at *
      simp [Nat.not_le_of_lt ht, hi]

/-- Explicitly excludes certificates relevant to these queued tranches. -/
def QueueSafe {n : ℕ} (qs : List (Withdrawal (Fin n))) (req : CertificateRequest n) : Prop :=
  ∀ B, attribute_evidence req.config req.reference req.evidence = .ok B →
    ∀ q ∈ qs, q.validator ∉ B ∨ q.requested < req.config.height

theorem checked_safe_queue {n : ℕ} (w : Window) α (s : UnbondingState (Fin n))
    (req : CertificateRequest n) (hs : QueueSafe s.queue req) :
    (slash_unbonding w req.config req.reference req.evidence α s).queue = s.queue := by
  unfold slash_unbonding
  split_ifs
  · cases hc : attribute_evidence req.config req.reference req.evidence with
    | error _ => rfl
    | ok B =>
      apply slash_queue_unchanged
      intro q hq
      rcases hs B hc q hq with hb | ht
      · exact Or.inl (fun hm => hb (mem_fresh _ _ _ _ |>.mp hm).1)
      · exact Or.inr ht
  · rfl

/-- Module 179 supplies the safety premise for honest validators and a reachable reference. -/
theorem honest_queue_safe {n : ℕ} (c : Config n) {history : State n}
    (hr : Reachable c history) e (qs : List (Withdrawal (Fin n)))
    (hh : ∀ q ∈ qs, q.validator ∉ c.byzantine) :
    QueueSafe qs ⟨c, some history.votes, e⟩ := by
  intro B hc q hq
  exact Or.inl (attribution_honest c hr e B hc q.validator (hh q hq))

theorem checked_context {n : ℕ} (w : Window) (c : Config n) reference e α
    (s : UnbondingState (Fin n)) :
    (slash_unbonding w c reference e α s).now = s.now ∧
    (slash_unbonding w c reference e α s).completed = s.completed := by
  unfold slash_unbonding
  split_ifs
  · cases attribute_evidence c reference e <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem batch_safe_context {n : ℕ} (w : Window) α (rs : List (CertificateRequest n))
    (s : UnbondingState (Fin n)) (hs : ∀ r ∈ rs, QueueSafe s.queue r) :
    let out := rs.foldl (fun st r => slash_unbonding w r.config r.reference r.evidence α st) s
    out.queue = s.queue ∧ out.now = s.now ∧ out.completed = s.completed := by
  induction rs generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons r rs ih =>
    have hq := checked_safe_queue w α s r (hs r (by simp))
    have hc := checked_context w r.config r.reference r.evidence α s
    have hi := ih (slash_unbonding w r.config r.reference r.evidence α s)
      (fun a ha => by rw [hq]; exact hs a (by simp [ha]))
    exact ⟨hi.1.trans hq, hi.2.1.trans hc.1, hi.2.2.trans hc.2⟩

/-- Fairness is explicit: execute this slot after time has reached maturity.
With no relevant accepted penalties the full queue amount is paid. -/
theorem honest_withdrawal_liveness {n : ℕ} (w : Window) α (s : UnbondingState (Fin n))
    rs (q : Withdrawal (Fin n)) (hq : s.queue = [q]) (ht : q.maturity w ≤ s.now)
    (hs : ∀ r ∈ rs, QueueSafe s.queue r) :
    (processSlot w α s rs).completed q.validator = s.completed q.validator + q.amount := by
  have hc := batch_safe_context w α rs s hs
  have he := singleton_full_withdrawal w
    (rs.foldl (fun st r => slash_unbonding w r.config r.reference r.evidence α st) s)
    q (hc.1.trans hq) (by rw [hc.2.1]; exact ht)
  unfold processSlot advance_time
  split_ifs
  · simpa only [hc.2.2] using he
  · simpa only [hc.2.2] using he

theorem checked_deadline_precedence {n : ℕ} (w : Window) (c : Config n) reference e α
    (s : UnbondingState (Fin n)) (q : Withdrawal (Fin n)) B
    (hc : attribute_evidence c reference e = .ok B) (hp : s.phase = .admission)
    (ha : 0 < α ∧ α ≤ 1) (hq : s.queue = [q]) (hb : q.validator ∈ B)
    (hf : (c.height, q.validator) ∉ s.processed) (hli : c.height ≤ q.requested)
    (hd : s.now = c.height + w.duration) (hm : q.maturity w = s.now) :
    (finalize_unbonding w (close_admission
      (slash_unbonding w c reference e α s))).completed q.validator =
      s.completed q.validator + (1 - α) * q.amount := by
  have ht : is_timely w c.height s.now := by unfold is_timely; omega
  rw [accepted_certificate w c reference e α s B hc ⟨hp, ht, ha⟩]
  exact deadline_precedence_theorem w s q c.height B α hq hb hf hli hd hm

theorem safe_batch_payout {n : ℕ} (w : Window) α (s : UnbondingState (Fin n)) rs v
    (hs : ∀ r ∈ rs, QueueSafe s.queue r) :
    (processSlot w α s rs).completed v = s.completed v + eligibleMass (matured w s) 0 v := by
  have hc := batch_safe_context w α rs s hs
  have he := honest_liveness_theorem w
    (rs.foldl (fun st r => slash_unbonding w r.config r.reference r.evidence α st) s) v
  simp only [matured, hc.1, hc.2.1, hc.2.2] at he
  unfold processSlot advance_time
  split_ifs <;> exact he

theorem slot_advances_time {n : ℕ} (w : Window) α (s : UnbondingState (Fin n)) rs :
    (processSlot w α s rs).now = s.now + 1 := by
  have hn : ∀ (rs : List (CertificateRequest n)) (s : UnbondingState (Fin n)),
      (rs.foldl (fun st r => slash_unbonding w r.config r.reference r.evidence α st) s).now
        = s.now := by
    intro rs
    induction rs with
    | nil => intro s; rfl
    | cons r rs ih =>
      intro s
      rw [List.foldl_cons, ih, (checked_context w r.config r.reference r.evidence α s).1]
  simp only [processSlot, advance_time, finalize_unbonding, close_admission, ↓reduceIte]
  rw [hn]

structure DistributedTendermintUnbondingPeriodContractSuite : Prop where
  refinement : ∀ {V : Type} [DecidableEq V] (s : UnbondingState V) h B α,
    toLedger (slashSet s h B α) h = applyCertifiedSet (toLedger s h) h B α
  no_escape : ∀ {V : Type} w (q : Withdrawal V) h τ, h ≤ q.requested → is_timely w h τ
    → τ ≤ q.maturity w
  deadline : ∀ w (s : UnbondingState (Fin 3)) (q : Withdrawal (Fin 3)) h B α,
    s.queue = [q] → q.validator ∈ B → (h, q.validator) ∉ s.processed → h ≤ q.requested →
    s.now = h + w.duration → q.maturity w = s.now →
    (finalize_unbonding w (close_admission (slashSet s h B α))).completed q.validator =
      s.completed q.validator + (1 - α) * q.amount
  conservation : ∀ {n} w α (s : UnbondingState (Fin n)) rs,
    totalValue (processSlot w α s rs) = totalValue s
  nonnegative : ∀ {n} w α (s : UnbondingState (Fin n)) rs,
    WellFormed s → WellFormed (processSlot w α s rs)
  replay : ∀ {n} w (c : Config n) reference e α (s : UnbondingState (Fin n)),
    slash_unbonding w c reference e α (slash_unbonding w c reference e α s) =
      slash_unbonding w c reference e α s
  future_rejected : ∀ {n} w (c : Config n) reference e α (s : UnbondingState (Fin n)),
    s.now < c.height → slash_unbonding w c reference e α s = s
  timely_debit : ∀ {n} w (c : Config n) reference e α (s : UnbondingState (Fin n)) B v,
    attribute_evidence c reference e = .ok B →
    (s.phase = .admission ∧ is_timely w c.height s.now ∧ 0 < α ∧ α ≤ 1) →
    WellFormed s → v ∈ B → (c.height, v) ∉ s.processed → 0 < available s c.height v →
    s.confiscated < (slash_unbonding w c reference e α s).confiscated
  honest_payout : ∀ {n} w α (s : UnbondingState (Fin n)) rs (q : Withdrawal (Fin n)),
    s.queue = [q] → q.maturity w ≤ s.now → (∀ r ∈ rs, QueueSafe s.queue r) →
    (processSlot w α s rs).completed q.validator = s.completed q.validator + q.amount

theorem verification_suite : DistributedTendermintUnbondingPeriodContractSuite :=
  ⟨ledger_refinement, no_escape_theorem, deadline_precedence_theorem, total_value_conservation,
    slot_wellFormed,
    replay_idempotence, no_future_evidence_accepted, timely_slashing_guarantee,
    honest_withdrawal_liveness⟩

end DistributedTendermintUnbondingPeriodContract
