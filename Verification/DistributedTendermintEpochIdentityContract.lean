/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedTendermintUnbondingPeriodContract

/-! Stable subjects across changing local index spaces. Historical configurations and
complete references are trusted inputs; this is not a consensus handover theorem. -/
namespace DistributedTendermintEpochIdentityContract
open Finset DistributedTendermintCoreSafety DistributedTendermintAccountableSafety
open DistributedTendermintSlashingPenaltyContract
open DistributedTendermintSlashingReplayProtection (applyCertifiedSet freshOffenders)
open DistributedTendermintUnbondingPeriodContract

/-- Natural consensus units retain the exact API of module 179; stakeMap embeds them in Q. -/
structure EpochConfig (V : Type*) where
  n : ℕ
  toGlobal : Fin n ↪ V
  weight : Fin n → ℕ
  byzantine : Finset (Fin n)
  firstHeight : ℕ
  lastHeight : ℕ
  ordered : firstHeight ≤ lastHeight

variable {V : Type*} [DecidableEq V]

def EpochConfig.atHeight (c : EpochConfig V) (h : ℕ) : Config c.n :=
  ⟨c.weight, c.byzantine, h⟩

def EpochConfig.activeIds (c : EpochConfig V) : Finset V := univ.map c.toGlobal

def EpochConfig.stakeMap (c : EpochConfig V) (v : V) : ℚ :=
  ∑ i : Fin c.n, if c.toGlobal i = v then (c.weight i : ℚ) else 0

theorem stakeMap_nonnegative (c : EpochConfig V) v : 0 ≤ c.stakeMap v := by
  apply Finset.sum_nonneg
  intro i _
  split <;> positivity

theorem stakeMap_supported (c : EpochConfig V) v (hv : v ∉ c.activeIds) :
    c.stakeMap v = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : c.toGlobal i ≠ v := by
    intro he
    exact hv (Finset.mem_map.mpr ⟨i, mem_univ _, he⟩)
  simp [hi]

def globalBlame (c : EpochConfig V) (B : Finset (Fin c.n)) : Finset V := B.map c.toGlobal

omit [DecidableEq V] in
@[simp] theorem mem_globalBlame (c : EpochConfig V) B v :
    v ∈ globalBlame c B ↔ ∃ i ∈ B, c.toGlobal i = v := by simp [globalBlame]

omit [DecidableEq V] in
@[simp] theorem own_globalBlame (c : EpochConfig V) B i :
    c.toGlobal i ∈ globalBlame c B ↔ i ∈ B := by simp [globalBlame]

omit [DecidableEq V] in
theorem outside_epoch_unaccused (c : EpochConfig V) B v (hv : v ∉ c.activeIds) :
    v ∉ globalBlame c B := by
  intro hm
  obtain ⟨i, _, he⟩ := (mem_globalBlame c B v).mp hm
  exact hv (Finset.mem_map.mpr ⟨i, mem_univ _, he⟩)

/-- Conflicting or duplicate entries are rejected conservatively, never selected by order. -/
abbrev HistoryRegistry (V : Type*) := ℕ → List (EpochConfig V)

def resolveHistory (H : HistoryRegistry V) (h : ℕ) : Option (EpochConfig V) :=
  match H h with
  | [c] => if c.firstHeight ≤ h ∧ h ≤ c.lastHeight then some c else none
  | _ => none

def UnambiguousAt (H : HistoryRegistry V) (h : ℕ) : Prop :=
  ∃ c, H h = [c] ∧ c.firstHeight ≤ h ∧ h ≤ c.lastHeight

omit [DecidableEq V] in
theorem resolve_iff (H : HistoryRegistry V) h c :
    resolveHistory H h = some c ↔ H h = [c] ∧ c.firstHeight ≤ h ∧ h ≤ c.lastHeight := by
  cases hh : H h with
  | nil => simp [resolveHistory, hh]
  | cons a tail =>
    cases tail with
    | nil =>
      by_cases hb : a.firstHeight ≤ h ∧ h ≤ a.lastHeight
      · simp only [resolveHistory, hh, hb, ↓reduceIte, Option.some.injEq,
          List.cons.injEq, and_true]
        constructor
        · rintro rfl; exact ⟨rfl, hb⟩
        · exact fun he => he.1
      · simp only [resolveHistory, hh, hb, ↓reduceIte, List.cons.injEq, and_true]
        constructor
        · intro he; cases he
        · rintro ⟨rfl, hc⟩; exact False.elim (hb hc)
    | cons b rest => simp [resolveHistory, hh]

omit [DecidableEq V] in
theorem unambiguous_history_requirement (H : HistoryRegistry V) h
    (hh : ¬ UnambiguousAt H h) : resolveHistory H h = none := by
  cases he : resolveHistory H h with
  | none => rfl
  | some c => exact False.elim (hh ⟨c, (resolve_iff H h c).mp he⟩)

omit [DecidableEq V] in
theorem unique_resolution (H : HistoryRegistry V) h a b
    (ha : resolveHistory H h = some a) (hb : resolveHistory H h = some b) : a = b := by
  exact Option.some.inj (ha.symm.trans hb)

structure Payload (n : ℕ) where
  reference : Option (Finset (Vote n))
  evidence : EvidenceView n

/-- Only the local dimension is supplied by the packet, never its identity map or weights. -/
abbrev Packet := (n : ℕ) × Payload n

def checkPacket (c : EpochConfig V) (h : ℕ) (p : Packet) : Option (Finset V) :=
  if hn : p.1 = c.n then
    let input : Payload c.n := hn ▸ p.2
    match attribute_evidence (c.atHeight h) input.reference input.evidence with
    | .error _ => none
    | .ok B => some (globalBlame c B)
  else none

def historicalBlame (H : HistoryRegistry V) (h : ℕ) (p : Packet) : Option (Finset V) :=
  (resolveHistory H h).bind (fun c => checkPacket c h p)

omit [DecidableEq V] in
theorem check_accepted (c : EpochConfig V) h (input : Payload c.n) B
    (hc : attribute_evidence (c.atHeight h) input.reference input.evidence = .ok B) :
    checkPacket c h ⟨c.n, input⟩ = some (globalBlame c B) := by simp [checkPacket, hc]

omit [DecidableEq V] in
theorem wrong_dimension_rejected (c : EpochConfig V) h p (hn : p.1 ≠ c.n) :
    checkPacket c h p = none := by simp [checkPacket, hn]

omit [DecidableEq V] in
theorem historical_accepted (H : HistoryRegistry V) h c (input : Payload c.n) B
    (hh : resolveHistory H h = some c)
    (hc : attribute_evidence (c.atHeight h) input.reference input.evidence = .ok B) :
    historicalBlame H h ⟨c.n, input⟩ = some (globalBlame c B) := by
  simp [historicalBlame, hh, check_accepted c h input B hc]

/-- Funds, pending claims and processed keys use global IDs independently of current members. -/
structure EpochState (V : Type*) where
  current : EpochConfig V
  history : HistoryRegistry V
  ledger : UnbondingState V

def epoch_transition (s : EpochState V) (next : EpochConfig V) : EpochState V :=
  { s with current := next }

omit [DecidableEq V] in
theorem epoch_transition_preserves_obligations (s : EpochState V) next :
    (epoch_transition s next).ledger = s.ledger ∧
    (epoch_transition s next).history = s.history := ⟨rfl, rfl⟩

/-- Same timing and rate guards as module 195; the certified set comes from historicalBlame. -/
def applyHistorical (w : Window) (h : ℕ) (p : Packet) (α : ℚ) (s : EpochState V) : EpochState V :=
  if s.ledger.phase = .admission ∧ is_timely w h s.ledger.now ∧ 0 < α ∧ α ≤ 1 then
    match historicalBlame s.history h p with
    | none => s
    | some B => { s with ledger := slashSet s.ledger h B α }
  else s

theorem apply_accepted (w : Window) h p α (s : EpochState V) B
    (hb : historicalBlame s.history h p = some B)
    (hg : s.ledger.phase = .admission ∧ is_timely w h s.ledger.now ∧ 0 < α ∧ α ≤ 1) :
    applyHistorical w h p α s = { s with ledger := slashSet s.ledger h B α } := by
  simp [applyHistorical, hg, hb]

theorem rejected_noop (w : Window) h p α (s : EpochState V)
    (hb : historicalBlame s.history h p = none) : applyHistorical w h p α s = s := by
  simp [applyHistorical, hb]

theorem missing_or_ambiguous_noop (w : Window) h p α (s : EpochState V)
    (hh : ¬ UnambiguousAt s.history h) : applyHistorical w h p α s = s := by
  apply rejected_noop
  simp [historicalBlame, unambiguous_history_requirement _ _ hh]

theorem invalid_time_noop (w : Window) h p α (s : EpochState V)
    (ht : ¬ is_timely w h s.ledger.now) : applyHistorical w h p α s = s := by
  simp [applyHistorical, ht]

theorem transition_commutes (w : Window) h p α (s : EpochState V) next :
    applyHistorical w h p α (epoch_transition s next) =
      epoch_transition (applyHistorical w h p α s) next := by
  unfold applyHistorical epoch_transition
  split_ifs <;> first | rfl | cases historicalBlame s.history h p <;> rfl

theorem historical_replay (w : Window) h p α (s : EpochState V) :
    applyHistorical w h p α (applyHistorical w h p α s) = applyHistorical w h p α s := by
  by_cases hg : s.ledger.phase = .admission ∧ is_timely w h s.ledger.now ∧ 0 < α ∧ α ≤ 1
  · cases hb : historicalBlame s.history h p with
    | none => simp only [rejected_noop w h p α s hb]
    | some B =>
      rw [apply_accepted w h p α s B hb hg]
      have hb' : historicalBlame
          ({ s with ledger := slashSet s.ledger h B α } : EpochState V).history h p = some B := hb
      have hg' : (slashSet s.ledger h B α).phase = .admission ∧
          is_timely w h (slashSet s.ledger h B α).now ∧ 0 < α ∧ α ≤ 1 := hg
      rw [apply_accepted w h p α { s with ledger := slashSet s.ledger h B α } B hb' hg']
      simp only [replay_set]
  · have he : applyHistorical w h p α s = s := by simp [applyHistorical, hg]
    simp only [he]

theorem inter_epoch_replay (w : Window) h p α (s : EpochState V) next :
    applyHistorical w h p α (epoch_transition (applyHistorical w h p α s) next) =
      epoch_transition (applyHistorical w h p α s) next := by
  rw [transition_commutes, historical_replay]

theorem historical_wellFormed (w : Window) h p α (s : EpochState V)
    (hw : WellFormed s.ledger) : WellFormed (applyHistorical w h p α s).ledger := by
  unfold applyHistorical
  split_ifs with hg
  · cases historicalBlame s.history h p with
    | none => exact hw
    | some B => exact slash_wellFormed _ _ _ _ hw (le_of_lt hg.2.2.1) hg.2.2.2
  · exact hw

theorem historical_conservation [Fintype V] (w : Window) h p α (s : EpochState V) :
    totalValue (applyHistorical w h p α s).ledger = totalValue s.ledger := by
  unfold applyHistorical
  split_ifs
  · cases historicalBlame s.history h p with
    | none => rfl
    | some B => exact slash_conservation _ _ _ _
  · rfl

def ownedQueue (s : UnbondingState V) (v : V) : List (Withdrawal V) :=
  s.queue.filter fun q => q.validator = v

theorem unaccused_queue (qs : List (Withdrawal V)) h B α v (hv : v ∉ B) :
    (slashQueue qs h B α).filter (fun q => q.validator = v) =
      qs.filter (fun q => q.validator = v) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [slashQueue, List.map_cons] at *
    by_cases he : q.validator = v
    · simp [he, hv, ih]
    · by_cases hb : q.validator ∈ B ∧ h ≤ q.requested <;> simp [hb, he, ih]

theorem unaccused_funds (s : UnbondingState V) h B α v (hv : v ∉ B) :
    (slashSet s h B α).active v = s.active v ∧
    ownedQueue (slashSet s h B α) v = ownedQueue s v ∧
    (slashSet s h B α).completed v = s.completed v := by
  have hf : v ∉ freshOffenders (toLedger s h) h B := by simp [hv]
  exact ⟨non_faulty_stake_invariant _ _ _ _ hf, unaccused_queue _ _ _ _ _ hf, rfl⟩

/-- A new subject outside the entire historical membership cannot be charged by its evidence. -/
theorem new_validator_reused_index_safety (w : Window) h α (s : EpochState V)
    (old : EpochConfig V) (input : Payload old.n) B v
    (hh : resolveHistory s.history h = some old)
    (hc : attribute_evidence (old.atHeight h) input.reference input.evidence = .ok B)
    (hv : v ∉ old.activeIds) :
    (applyHistorical w h ⟨old.n, input⟩ α s).ledger.active v = s.ledger.active v ∧
    ownedQueue (applyHistorical w h ⟨old.n, input⟩ α s).ledger v = ownedQueue s.ledger v ∧
    (applyHistorical w h ⟨old.n, input⟩ α s).ledger.completed v = s.ledger.completed v := by
  have hb := historical_accepted s.history h old input B hh hc
  unfold applyHistorical
  split_ifs
  · rw [hb]
    exact unaccused_funds _ _ _ _ _ (outside_epoch_unaccused old B v hv)
  · exact ⟨rfl, rfl, rfl⟩

/-- A reused index alone gives protection when the old certificate accuses that one owner. -/
theorem singleton_reused_index_safety (w : Window) h α (s : EpochState V)
    (old : EpochConfig V) (input : Payload old.n) (k : Fin old.n) v
    (hh : resolveHistory s.history h = some old)
    (hc : attribute_evidence (old.atHeight h) input.reference input.evidence = .ok {k})
    (hv : old.toGlobal k ≠ v) :
    (applyHistorical w h ⟨old.n, input⟩ α s).ledger.active v = s.ledger.active v := by
  have hb := historical_accepted s.history h old input {k} hh hc
  unfold applyHistorical
  split_ifs
  · rw [hb]
    apply (unaccused_funds _ _ _ _ _ ?_).1
    simp [globalBlame, ne_comm.mp hv]
  · rfl

/-- Leaving current membership cannot prevent a valid historical debit of liable held funds. -/
theorem unbonding_slashing_cross_epoch_soundness (w : Window) h α (s : EpochState V)
    next (old : EpochConfig V) (input : Payload old.n) B (i : Fin old.n)
    (hh : resolveHistory s.history h = some old)
    (hc : attribute_evidence (old.atHeight h) input.reference input.evidence = .ok B)
    (hg : s.ledger.phase = .admission ∧ is_timely w h s.ledger.now ∧ 0 < α ∧ α ≤ 1)
    (hw : WellFormed s.ledger) (hi : i ∈ B)
    (hf : (h, old.toGlobal i) ∉ s.ledger.processed)
    (hp : 0 < available s.ledger h (old.toGlobal i)) :
    s.ledger.confiscated <
      (applyHistorical w h ⟨old.n, input⟩ α (epoch_transition s next)).ledger.confiscated := by
  rw [transition_commutes]
  rw [apply_accepted w h _ α s (globalBlame old B)
    (historical_accepted s.history h old input B hh hc) hg]
  exact positive_confiscation s.ledger h (globalBlame old B) α (old.toGlobal i) hw
    ((own_globalBlame old B i).mpr hi) hf hg.2.2.1 hp

/-- Historical validation feeds the inclusive-deadline payout theorem of module 195. -/
theorem historical_deadline_precedence (w : Window) h α (s : EpochState V)
    (old : EpochConfig V) (input : Payload old.n) B (q : Withdrawal V)
    (hh : resolveHistory s.history h = some old)
    (hc : attribute_evidence (old.atHeight h) input.reference input.evidence = .ok B)
    (hg : s.ledger.phase = .admission ∧ is_timely w h s.ledger.now ∧ 0 < α ∧ α ≤ 1)
    (hq : s.ledger.queue = [q]) (hb : q.validator ∈ globalBlame old B)
    (hf : (h, q.validator) ∉ s.ledger.processed) (hl : h ≤ q.requested)
    (ht : s.ledger.now = h + w.duration) (hm : q.maturity w = s.ledger.now) :
    (finalize_unbonding w
      (close_admission (applyHistorical w h ⟨old.n, input⟩ α s).ledger)).completed q.validator =
        s.ledger.completed q.validator + (1 - α) * q.amount := by
  rw [apply_accepted w h _ α s (globalBlame old B)
    (historical_accepted s.history h old input B hh hc) hg]
  exact deadline_precedence_theorem w s.ledger q h (globalBlame old B) α hq hb hf hl ht hm

/-- Reindex both the identity map and local consensus data, leaving the subjects unchanged. -/
def reindex (c : EpochConfig V) (e : Equiv.Perm (Fin c.n)) : EpochConfig V :=
  { c with toGlobal := e.symm.toEmbedding.trans c.toGlobal
           weight := fun i => c.weight (e.symm i)
           byzantine := c.byzantine.map e.toEmbedding }

omit [DecidableEq V] in
theorem permutation_globalBlame (c : EpochConfig V) (e : Equiv.Perm (Fin c.n)) B :
    globalBlame (reindex c e) (B.map e.toEmbedding) = globalBlame c B := by
  ext v
  simp only [globalBlame, reindex, Finset.mem_map]
  constructor
  · rintro ⟨j, ⟨i, hi, rfl⟩, hj⟩
    exact ⟨i, hi, by simpa using hj⟩
  · rintro ⟨i, hi, hv⟩
    exact ⟨e i, ⟨i, hi, rfl⟩, by simpa using hv⟩

theorem identity_permutation_invariance (c : EpochConfig V) (e : Equiv.Perm (Fin c.n))
    (s : UnbondingState V) h B α :
    slashSet s h (globalBlame (reindex c e) (B.map e.toEmbedding)) α =
      slashSet s h (globalBlame c B) α := by rw [permutation_globalBlame]

theorem permutation_stakeMap (c : EpochConfig V) (e : Equiv.Perm (Fin c.n)) v :
    (reindex c e).stakeMap v = c.stakeMap v := by
  exact Equiv.sum_comp e.symm (fun i => if c.toGlobal i = v then (c.weight i : ℚ) else 0)

omit [DecidableEq V] in
theorem historical_honest_unaccused (c : EpochConfig V) h {st : State c.n}
    (hr : Reachable (c.atHeight h) st) e B (i : Fin c.n)
    (hc : attribute_evidence (c.atHeight h) (some st.votes) e = .ok B)
    (hi : i ∉ c.byzantine) : c.toGlobal i ∉ globalBlame c B := by
  simpa using attribution_honest (c.atHeight h) hr e B hc i hi

structure DistributedTendermintEpochIdentityContractSuite : Prop where
  preservation : ∀ {V : Type} (s : EpochState V) next,
    (epoch_transition s next).ledger = s.ledger ∧ (epoch_transition s next).history = s.history
  replay : ∀ {V : Type} [DecidableEq V] w h p α (s : EpochState V) next,
    applyHistorical w h p α (epoch_transition (applyHistorical w h p α s) next) =
      epoch_transition (applyHistorical w h p α s) next
  rejects_ambiguity : ∀ {V : Type} [DecidableEq V] w h p α (s : EpochState V),
    ¬ UnambiguousAt s.history h → applyHistorical w h p α s = s
  permutation : ∀ {V : Type} [DecidableEq V] (c : EpochConfig V) e (s : UnbondingState V) h B α,
    slashSet s h (globalBlame (reindex c e) (B.map e.toEmbedding)) α =
      slashSet s h (globalBlame c B) α
  conservation : ∀ {V : Type} [DecidableEq V] [Fintype V] w h p α (s : EpochState V),
    totalValue (applyHistorical w h p α s).ledger = totalValue s.ledger
  nonnegative : ∀ {V : Type} [DecidableEq V] w h p α (s : EpochState V),
    WellFormed s.ledger → WellFormed (applyHistorical w h p α s).ledger

theorem verification_suite : DistributedTendermintEpochIdentityContractSuite :=
  ⟨epoch_transition_preserves_obligations, inter_epoch_replay, missing_or_ambiguous_noop,
    identity_permutation_invariance, historical_conservation, historical_wellFormed⟩

end DistributedTendermintEpochIdentityContract
