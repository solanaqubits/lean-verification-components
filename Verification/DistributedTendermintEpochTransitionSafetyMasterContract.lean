/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedTendermintHandoverRoundInduction

/-! Composition for one target epoch and decision height. A cross-epoch conflict
alone does not supply attributable historical evidence. The final dichotomy exposes
that coverage premise, and collection remains conditional on admission and held funds. -/
namespace DistributedTendermintEpochTransitionSafetyMasterContract
open Finset DistributedTendermintCoreSafety DistributedTendermintAccountableSafety
open DistributedTendermintEpochIdentityContract
open DistributedTendermintUnbondingPeriodContract
open DistributedTendermintQuorumIntersectionEpochTransitionContract
open DistributedTendermintLockHandoverContract DistributedTendermintHandoverRoundInduction

structure EpochTransitionMasterContext (V : Type) where
  context : Context V
  threshold : Threshold
  faultSet : Finset V
  sourcePolka : Certificate context.old.n
  sourceCommit : Certificate context.old.n
  adopted : V → Option LocalState
  transcript : Transcript context.next.n
  history : HistoryRegistry V
  ledger : UnbondingState V
  window : Window
  rate : ℚ

variable {V : Type} [Fintype V] [DecidableEq V]

abbrev Input (C : EpochTransitionMasterContext V) := Payload C.context.old.n

def initialState (C : EpochTransitionMasterContext V) : EpochState V :=
  ⟨C.context.old, C.history, C.ledger⟩

def debit (C : EpochTransitionMasterContext V) (p : Input C) : EpochState V :=
  applyHistorical C.window C.context.height ⟨C.context.old.n, p⟩ C.rate
    (epoch_transition (initialState C) C.context.next)

/-- Closing admission asserts the supplied slot input is complete; this does not advance time. -/
def settle (w : Window) (s : EpochState V) : EpochState V :=
  { s with ledger := finalize_unbonding w (close_admission s.ledger) }

def pipeline (C : EpochTransitionMasterContext V) (p : Input C) : EpochState V :=
  settle C.window (debit C p)

def Agreement (C : EpochTransitionMasterContext V) : Prop :=
  ∀ r x, Commit C.threshold C.context C.transcript r x → x = C.sourceCommit.value

structure SafetyConditions (C : EpochTransitionMasterContext V) : Prop where
  accepted : Accept C.threshold C.context C.sourcePolka
  normalized : Normalized (epochWeights C.context.next)
  source : C.sourceCommit.epoch = C.context.sourceEpoch ∧
    C.sourceCommit.height = C.context.height ∧ C.sourceCommit.phase = .precommit ∧
    C.sourceCommit.value = C.sourcePolka.value
  quorum : Quorum C.threshold (epochWeights C.context.old)
    (certificateSigners C.context.old C.sourceCommit)
  overlap : Overlap C.threshold (epochWeights C.context.old) (epochWeights C.context.next)
    C.faultSet
  adoption : Adoptions C.context C.faultSet C.sourceCommit C.sourcePolka C.adopted
  prevotes : HonestPrevotes C.threshold C.context C.transcript
    (inheritedSigners C.context C.faultSet C.sourceCommit C.sourcePolka C.adopted)
      C.sourcePolka.value
  precommits : HonestPrecommits C.threshold C.context C.transcript
    (inheritedSigners C.context C.faultSet C.sourceCommit C.sourcePolka C.adopted)

theorem cross_epoch_master_safety_branch (C : EpochTransitionMasterContext V)
    (hs : SafetyConditions C) : Agreement C := by
  intro r x hx
  exact cross_epoch_arbitrary_round_safety C.threshold C.context C.faultSet C.sourcePolka
    C.sourceCommit C.adopted C.transcript hs.accepted hs.normalized hs.source hs.quorum
    hs.overlap hs.adoption hs.prevotes hs.precommits r x hx

/-- Real attribution through module 179 and historical lookup, not an arbitrary guilty set. -/
def AcceptedEvidence (C : EpochTransitionMasterContext V) (p : Input C)
    (B : Finset (Fin C.context.old.n)) : Prop :=
  resolveHistory C.history C.context.height = some C.context.old ∧
  attribute_evidence (C.context.old.atHeight C.context.height) p.reference p.evidence = .ok B

def Admission (C : EpochTransitionMasterContext V) : Prop :=
  C.ledger.phase = .admission ∧ is_timely C.window C.context.height C.ledger.now ∧
  0 < C.rate ∧ C.rate ≤ 1

/-- Positivity concerns current liable holdings, not historical consensus weight. -/
def CollectionReady (C : EpochTransitionMasterContext V) (p : Input C)
    (B : Finset (Fin C.context.old.n)) : Prop :=
  AcceptedEvidence C p B ∧ Admission C ∧ WellFormed C.ledger ∧
  ∃ i ∈ B, (C.context.height, C.context.old.toGlobal i) ∉ C.ledger.processed ∧
    0 < available C.ledger C.context.height (C.context.old.toGlobal i)

omit [Fintype V] in
theorem accepted_debit (C : EpochTransitionMasterContext V) p B
    (he : AcceptedEvidence C p B) (hg : Admission C) :
    (debit C p).ledger = slashSet C.ledger C.context.height (globalBlame C.context.old B) C.rate
      := by
  unfold debit
  rw [transition_commutes]
  rw [apply_accepted C.window C.context.height _ C.rate (initialState C)
    (globalBlame C.context.old B)
    (historical_accepted C.history C.context.height C.context.old p B he.1 he.2) hg]
  rfl

omit [Fintype V] in
theorem cross_epoch_accountable_slashing_branch (C : EpochTransitionMasterContext V) p B
    (hr : CollectionReady C p B) :
    (globalBlame C.context.old B).Nonempty ∧
    C.ledger.confiscated < (pipeline C p).ledger.confiscated := by
  obtain ⟨he, hg, hw, i, hi, hf, hp⟩ := hr
  refine ⟨⟨C.context.old.toGlobal i, (own_globalBlame _ _ _).mpr hi⟩, ?_⟩
  have hpos := unbonding_slashing_cross_epoch_soundness C.window C.context.height C.rate
    (initialState C) C.context.next C.context.old p B i he.1 he.2 hg hw hi hf hp
  simpa only [pipeline, settle, finalize_unbonding, close_admission, ↓reduceIte, initialState,
    debit] using hpos

omit [Fintype V] [DecidableEq V] in
/-- Actual same-configuration fork attribution is available; it is not a cross-epoch extractor. -/
theorem historical_fork_global_blame (old : EpochConfig V) h reference e
    (hs : EvidenceSufficiency (old.atHeight h) reference e) r s x y
    (hx : commit (old.atHeight h) e.votes r x) (hy : commit (old.atHeight h) e.votes s y)
    (hne : x ≠ y) :
    checkPacket old h ⟨old.n, ⟨some reference, e⟩⟩ =
      some (globalBlame old (culprits (old.atHeight h) e.votes)) ∧
    (globalBlame old (culprits (old.atHeight h) e.votes)).Nonempty := by
  obtain ⟨ha, hb⟩ := checked_accountable_safety (old.atHeight h) reference e hs hx hy hne
  refine ⟨check_accepted old h ⟨some reference, e⟩ _ ha, ?_⟩
  have hn : (culprits (old.atHeight h) e.votes).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp [he, Config.mass] at hb
  obtain ⟨i, hi⟩ := hn
  exact ⟨old.toGlobal i, (own_globalBlame _ _ _).mpr hi⟩

/-- Conservation for an individual subject allows a withdrawal to move queue funds to completed. -/
def subjectValue (s : UnbondingState V) (v : V) : ℚ :=
  s.active v + eligibleMass s.queue 0 v + s.completed v

omit [Fintype V] in
theorem eligible_partition (w : Window) (qs : List (Withdrawal V)) τ v :
    eligibleMass (qs.filter (fun q => ¬ q.maturity w ≤ τ)) 0 v +
    eligibleMass (qs.filter (fun q => q.maturity w ≤ τ)) 0 v = eligibleMass qs 0 v := by
  induction qs with
  | nil => simp [eligibleMass]
  | cons q qs ih =>
    by_cases ht : q.maturity w ≤ τ
    · simp [ht, eligibleMass] at ih ⊢; linarith
    · have hn := Nat.lt_of_not_ge ht
      simp [ht, hn, eligibleMass] at ih ⊢; linarith

omit [Fintype V] in
theorem settle_subject_value (w : Window) (s : EpochState V) v :
    subjectValue (settle w s).ledger v = subjectValue s.ledger v := by
  have hp := eligible_partition w s.ledger.queue s.ledger.now v
  simp only [subjectValue, settle, finalize_unbonding, close_admission, ↓reduceIte]
  dsimp [pending, matured]
  linarith

omit [Fintype V] in
theorem eligible_owned_queue (s : UnbondingState V) v :
    eligibleMass (ownedQueue s v) 0 v = eligibleMass s.queue 0 v := by
  unfold ownedQueue
  induction s.queue with
  | nil => simp [eligibleMass]
  | cons q qs ih =>
    by_cases hv : q.validator = v <;> simpa [hv, eligibleMass] using ih

omit [Fintype V] in
/-- Protection is absence from the WHOLE certified set, not inequality with one old index owner. -/
theorem cross_epoch_innocent_index_reuse_protection (C : EpochTransitionMasterContext V) p B v
    (he : AcceptedEvidence C p B) (hv : v ∉ globalBlame C.context.old B) :
    (pipeline C p).ledger.active v = C.ledger.active v ∧
    subjectValue (pipeline C p).ledger v = subjectValue C.ledger v := by
  have hf : (debit C p).ledger.active v = C.ledger.active v ∧
      ownedQueue (debit C p).ledger v = ownedQueue C.ledger v ∧
      (debit C p).ledger.completed v = C.ledger.completed v := by
    by_cases hg : Admission C
    · rw [accepted_debit C p B he hg]
      exact unaccused_funds C.ledger _ _ _ v hv
    · have hd : (debit C p).ledger = C.ledger := by
        have hg' : ¬ ((epoch_transition (initialState C) C.context.next).ledger.phase = .admission ∧
            is_timely C.window C.context.height
              (epoch_transition (initialState C) C.context.next).ledger.now ∧
            0 < C.rate ∧ C.rate ≤ 1) := hg
        simp only [debit, applyHistorical, if_neg hg']
        rfl
      rw [hd]
      exact ⟨rfl, rfl, rfl⟩
  refine ⟨?_, ?_⟩
  · simpa only [pipeline, settle, finalize_unbonding, close_admission, ↓reduceIte] using hf.1
  · rw [pipeline, settle_subject_value]
    have hq := congrArg (fun qs => eligibleMass qs 0 v) hf.2.1
    rw [eligible_owned_queue, eligible_owned_queue] at hq
    simp only [subjectValue, hf.1, hf.2.2, hq]

theorem pipeline_conservation (C : EpochTransitionMasterContext V) p :
    totalValue (pipeline C p).ledger = totalValue C.ledger := by
  unfold pipeline settle
  rw [finalize_conservation, close_conservation]
  exact historical_conservation C.window C.context.height _ C.rate
    (epoch_transition (initialState C) C.context.next)

omit [Fintype V] in
theorem pipeline_wellFormed (C : EpochTransitionMasterContext V) p (hw : WellFormed C.ledger) :
    WellFormed (pipeline C p).ledger := by
  have hd : WellFormed (debit C p).ledger :=
    historical_wellFormed C.window C.context.height ⟨C.context.old.n, p⟩ C.rate
      (epoch_transition (initialState C) C.context.next) hw
  exact finalize_wellFormed C.window (close_admission (debit C p).ledger)
    (close_wellFormed (debit C p).ledger hd)

omit [Fintype V] in
/-- Duplicate submission before closing admission has the same settled result. -/
theorem duplicate_before_settlement (C : EpochTransitionMasterContext V) p :
    settle C.window (applyHistorical C.window C.context.height ⟨C.context.old.n, p⟩ C.rate
      (debit C p)) = pipeline C p := by
  unfold pipeline debit
  rw [historical_replay]

omit [Fintype V] in
/-- After settlement admission is closed; retransmission cannot alter completed withdrawals. -/
theorem duplicate_after_settlement (C : EpochTransitionMasterContext V) p :
    applyHistorical C.window C.context.height ⟨C.context.old.n, p⟩ C.rate (pipeline C p) =
      pipeline C p := by
  simp [applyHistorical, pipeline, settle, finalize_unbonding, close_admission]

theorem cross_epoch_master_value_conservation_and_idempotence (C : EpochTransitionMasterContext V)
  p :
    totalValue (pipeline C p).ledger = totalValue C.ledger ∧
    settle C.window (applyHistorical C.window C.context.height ⟨C.context.old.n, p⟩ C.rate
      (debit C p)) = pipeline C p ∧
    applyHistorical C.window C.context.height ⟨C.context.old.n, p⟩ C.rate (pipeline C p) =
      pipeline C p :=
  ⟨pipeline_conservation C p, duplicate_before_settlement C p, duplicate_after_settlement C p⟩

/-- An explicit external coverage/availability obligation, NOT inferred from quorum intersection. -/
def ConflictCovered (C : EpochTransitionMasterContext V) : Prop :=
  ∀ r x, Commit C.threshold C.context C.transcript r x → x ≠ C.sourceCommit.value →
    ∃ p B, CollectionReady C p B

/-- This is a conditional composition theorem, not unconditional extraction or physical
  collection. -/
theorem cross_epoch_safety_or_slashing_dichotomy (C : EpochTransitionMasterContext V)
    (hcoverage : ConflictCovered C) :
    Agreement C ∨ ∃ p B, CollectionReady C p B ∧ (globalBlame C.context.old B).Nonempty ∧
      C.ledger.confiscated < (pipeline C p).ledger.confiscated := by
  classical
  by_cases ha : Agreement C
  · exact Or.inl ha
  · have hex : ∃ r x, Commit C.threshold C.context C.transcript r x ∧
        x ≠ C.sourceCommit.value := by
      by_contra hn
      apply ha
      intro r x hc
      by_contra hv
      exact hn ⟨r, x, hc, hv⟩
    obtain ⟨r, x, hc, hne⟩ := hex
    obtain ⟨p, B, hr⟩ := hcoverage r x hc hne
    exact Or.inr ⟨p, B, hr, cross_epoch_accountable_slashing_branch C p B hr⟩

omit [Fintype V] in
/-- Late evidence cannot debit; settlement may still pay matured withdrawals. -/
theorem expired_debit_noop (C : EpochTransitionMasterContext V) p
    (ht : C.context.height + C.window.duration < C.ledger.now) :
    (debit C p).ledger = C.ledger := by
  unfold debit
  rw [invalid_time_noop]
  · rfl
  · exact fun h => (not_le_of_gt ht) h.2

omit [Fintype V] in
/-- At the inclusive deadline the actual reduced tranche is paid, not its old face value. -/
theorem master_deadline_payout (C : EpochTransitionMasterContext V) p B (q : Withdrawal V)
    (he : AcceptedEvidence C p B) (hg : Admission C) (hq : C.ledger.queue = [q])
    (hb : q.validator ∈ globalBlame C.context.old B)
    (hf : (C.context.height, q.validator) ∉ C.ledger.processed)
    (hl : C.context.height ≤ q.requested)
    (ht : C.ledger.now = C.context.height + C.window.duration)
    (hm : q.maturity C.window = C.ledger.now) :
    (pipeline C p).ledger.completed q.validator =
      C.ledger.completed q.validator + (1 - C.rate) * q.amount := by
  change (finalize_unbonding C.window (close_admission (debit C p).ledger)).completed
    q.validator = _
  rw [accepted_debit C p B he hg]
  exact deadline_precedence_theorem C.window C.ledger q C.context.height
    (globalBlame C.context.old B) C.rate hq hb hf hl ht hm

omit [Fintype V] in
theorem expired_collection_impossible (C : EpochTransitionMasterContext V) p B
    (ht : C.context.height + C.window.duration < C.ledger.now) : ¬ CollectionReady C p B := by
  intro hr
  exact (not_le_of_gt ht) hr.2.1.2.1.2

theorem uncovered_expired_conflict (C : EpochTransitionMasterContext V) r x
    (hc : Commit C.threshold C.context C.transcript r x) (hv : x ≠ C.sourceCommit.value)
    (ht : C.context.height + C.window.duration < C.ledger.now) : ¬ ConflictCovered C := by
  intro hcov
  obtain ⟨p, B, hr⟩ := hcov r x hc hv
  exact expired_collection_impossible C p B ht hr


structure DistributedTendermintEpochTransitionSafetyMasterContractSuite : Prop where
  safety : ∀ {V : Type} [Fintype V] [DecidableEq V],
    ∀ (C : EpochTransitionMasterContext V)
    (_hs : SafetyConditions C), Agreement C
  slashing : ∀ {V : Type} [Fintype V] [DecidableEq V],
    ∀ (C : EpochTransitionMasterContext V) p B
    (_hr : CollectionReady C p B), (globalBlame C.context.old B).Nonempty ∧
    C.ledger.confiscated < (pipeline C p).ledger.confiscated
  innocent : ∀ {V : Type} [Fintype V] [DecidableEq V],
    ∀ (C : EpochTransitionMasterContext V) p B v
    (_he : AcceptedEvidence C p B) (_hv : v ∉ globalBlame C.context.old B), (pipeline C
      p).ledger.active v = C.ledger.active v ∧
    subjectValue (pipeline C p).ledger v = subjectValue C.ledger v
  conservation : ∀ {V : Type} [Fintype V] [DecidableEq V],
    ∀ (C : EpochTransitionMasterContext V) p, totalValue (pipeline C p).ledger = totalValue
      C.ledger ∧
    settle C.window (applyHistorical C.window C.context.height ⟨C.context.old.n, p⟩ C.rate
      (debit C p)) = pipeline C p ∧
    applyHistorical C.window C.context.height ⟨C.context.old.n, p⟩ C.rate (pipeline C p) =
      pipeline C p
  dichotomy : ∀ {V : Type} [Fintype V] [DecidableEq V],
    ∀ (C : EpochTransitionMasterContext V)
    (_hcoverage : ConflictCovered C), Agreement C ∨ ∃ p B, CollectionReady C p B ∧ (globalBlame
      C.context.old B).Nonempty ∧
      C.ledger.confiscated < (pipeline C p).ledger.confiscated
  nonnegative : ∀ {V : Type} [Fintype V] [DecidableEq V],
    ∀ (C : EpochTransitionMasterContext V) p (_hw : WellFormed C.ledger), WellFormed (pipeline C
      p).ledger
  deadline : ∀ {V : Type} [Fintype V] [DecidableEq V],
    ∀ (C : EpochTransitionMasterContext V) p B (q : Withdrawal V)
    (_he : AcceptedEvidence C p B) (_hg : Admission C) (_hq : C.ledger.queue = [q])
    (_hb : q.validator ∈ globalBlame C.context.old B)
    (_hf : (C.context.height, q.validator) ∉ C.ledger.processed)
    (_hl : C.context.height ≤ q.requested)
    (_ht : C.ledger.now = C.context.height + C.window.duration)
    (_hm : q.maturity C.window = C.ledger.now), (pipeline C p).ledger.completed q.validator =
      C.ledger.completed q.validator + (1 - C.rate) * q.amount

theorem verification_suite : DistributedTendermintEpochTransitionSafetyMasterContractSuite :=
  ⟨cross_epoch_master_safety_branch, cross_epoch_accountable_slashing_branch,
    cross_epoch_innocent_index_reuse_protection,
    cross_epoch_master_value_conservation_and_idempotence,
    cross_epoch_safety_or_slashing_dichotomy, pipeline_wellFormed, master_deadline_payout⟩

end DistributedTendermintEpochTransitionSafetyMasterContract
