/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedTendermintQuorumIntersectionEpochTransitionContract

/-! Conditional fixed-height handover. Certificates contain supplied vote records;
cryptographic authentication and delivery are external. Round-zero agreement is
separate from the local, later-round lock replacement rule. -/
namespace DistributedTendermintLockHandoverContract
open Finset DistributedTendermintCoreSafety
open DistributedTendermintEpochIdentityContract
open DistributedTendermintQuorumIntersectionEpochTransitionContract

inductive Threshold where
  | weak | strict
  deriving DecidableEq, Repr

variable {V : Type} [Fintype V] [DecidableEq V]

def Quorum (m : Threshold) (w : V → ℚ) (S : Finset V) : Prop :=
  match m with
  | .weak => (2 : ℚ) / 3 ≤ mass w S
  | .strict => (2 : ℚ) / 3 < mass w S

instance (m : Threshold) (w : V → ℚ) (S : Finset V) : Decidable (Quorum m w S) := by
  cases m <;> unfold Quorum <;> infer_instance

def Overlap (m : Threshold) (w z : V → ℚ) (B : Finset V) : Prop :=
  match m with
  | .weak => (2 : ℚ) / 3 < honestCommon w z B
  | .strict => (2 : ℚ) / 3 ≤ honestCommon w z B

instance (m : Threshold) (w z : V → ℚ) B : Decidable (Overlap m w z B) := by
  cases m <;> unfold Overlap <;> infer_instance

theorem shared_honest (m : Threshold) (w z : V → ℚ)
    (hw : Normalized w) (hz : Normalized z) B Q R
    (hq : Quorum m w Q) (hr : Quorum m z R) (ho : Overlap m w z B) :
    ∃ u ∈ Q ∩ R, u ∉ B ∧ 0 < w u ∧ 0 < z u := by
  cases m with
  | weak =>
    exact honest_node_in_intersection w z hw hz B Q R (2 / 3) (2 / 3) hq hr
      (by change (2 : ℚ) / 3 < _ at ho; linarith)
  | strict => exact strict_tendermint_intersection w z hw hz B Q R hq hr ho

/-- Vote height/epoch are scoped by this envelope, not by CoreSafety.Vote itself. -/
structure Certificate (n : ℕ) where
  epoch : ℕ
  height : ℕ
  round : ℕ
  value : ℕ
  phase : Phase
  votes : Finset (Vote n)
  deriving DecidableEq

def certificateSigners (c : EpochConfig V) (a : Certificate c.n) : Finset V :=
  (signers a.votes a.phase a.round (some a.value)).map c.toGlobal

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_certificateSigners (c : EpochConfig V) (a : Certificate c.n) u :
    u ∈ certificateSigners c a ↔
      ∃ i, c.toGlobal i = u ∧ ⟨i, a.round, a.phase, some a.value⟩ ∈ a.votes := by
  simp [certificateSigners, signers, and_comm]

structure Context (V : Type) where
  sourceEpoch : ℕ
  targetEpoch : ℕ
  height : ℕ
  old : EpochConfig V
  next : EpochConfig V

/-- The context is trusted configuration input, not authenticated by this predicate. -/
def Accept (m : Threshold) (c : Context V) (a : Certificate c.old.n) : Prop :=
  c.targetEpoch = c.sourceEpoch + 1 ∧ a.epoch = c.sourceEpoch ∧ a.height = c.height ∧
  a.phase = .prevote ∧ c.old.firstHeight ≤ a.height ∧ a.height ≤ c.old.lastHeight ∧
  0 < mass c.old.stakeMap univ ∧ Quorum m (epochWeights c.old) (certificateSigners c.old a)

instance (m : Threshold) (c : Context V) a : Decidable (Accept m c a) := by
  unfold Accept; infer_instance

def checkHandover (m : Threshold) (c : Context V) (a : Certificate c.old.n) : Bool :=
  decide (Accept m c a)

@[simp] theorem check_handover_iff (m : Threshold) (c : Context V) a :
    checkHandover m c a = true ↔ Accept m c a := by simp [checkHandover]

structure LocalState where
  epoch : ℕ
  height : ℕ
  round : ℕ
  value : ℕ
  lockedRound : ℕ
  sourceEpoch : ℕ
  sourceRound : ℕ
  deriving DecidableEq, Repr

/-- A fresh target-round floor; never compare a source round with a target round. -/
def inherited (c : Context V) (a : Certificate c.old.n) : LocalState :=
  ⟨c.targetEpoch, c.height, 0, a.value, 0, c.sourceEpoch, a.round⟩

def adopt (m : Threshold) (c : Context V) (a : Certificate c.old.n) (u : V)
    (s : Option LocalState) : Option LocalState :=
  if Accept m c a ∧ u ∈ c.next.activeIds ∧ (s = none ∨ s = some (inherited c a))
  then some (inherited c a) else s

theorem honest_node_lock_propagation (m : Threshold) (c : Context V) a u
    (ha : Accept m c a) (hu : u ∈ c.next.activeIds) :
    adopt m c a u none = some (inherited c a) := by simp [adopt, ha, hu]

theorem adoption_replay_idempotent (m : Threshold) (c : Context V) a u s :
    adopt m c a u (adopt m c a u s) = adopt m c a u s := by
  unfold adopt
  split <;> simp_all

theorem rejected_handover_noop (m : Threshold) (c : Context V) a u s
    (ha : ¬ Accept m c a) : adopt m c a u s = s := by simp [adopt, ha]

/-- Nil is an abstention and does not release the lock. Both vote phases use this guard. -/
def voteAllowed (s : LocalState) (v : Option ℕ) : Prop := v = none ∨ v = some s.value

instance (s : LocalState) v : Decidable (voteAllowed s v) := by
  unfold voteAllowed; infer_instance

def emit (s : LocalState) (i : Fin n) (p : Phase) (v : Option ℕ) : Option (Vote n) :=
  if voteAllowed s v then some ⟨i, s.round, p, v⟩ else none

theorem emit_sound (s : LocalState) (i : Fin n) p v a (h : emit s i p v = some a) :
    voteAllowed s v ∧ a = ⟨i, s.round, p, v⟩ := by
  unfold emit at h
  split at h <;> simp_all

omit [Fintype V] [DecidableEq V] in
theorem inherited_conflict_rejected (c : Context V) a (i : Fin n) p v
    (hv : v ≠ a.value) : emit (inherited c a) i p (some v) = none := by
  simp [emit, voteAllowed, inherited, hv]

/-- A finite snapshot rule only for round zero; no agreement conclusion is assumed. -/
def RecordAllowed (c : Context V) (states : V → Option LocalState)
    (a : Vote c.next.n) : Prop :=
  match states (c.next.toGlobal a.sender) with
  | none => False
  | some s => s.epoch = c.targetEpoch ∧ s.height = c.height ∧
      s.round = a.round ∧ voteAllowed s a.value

instance (c : Context V) states a : Decidable (RecordAllowed c states a) := by
  unfold RecordAllowed; split <;> infer_instance

def HonestRoundZero (c : Context V) (B : Finset V) (states : V → Option LocalState)
    (votes : Finset (Vote c.next.n)) : Prop :=
  ∀ a ∈ votes, a.round = 0 → c.next.toGlobal a.sender ∉ B → RecordAllowed c states a

instance (c : Context V) B states votes : Decidable (HonestRoundZero c B states votes) := by
  unfold HonestRoundZero; infer_instance

omit [Fintype V] [DecidableEq V] in
theorem record_allowed_state (c : Context V) states a (h : RecordAllowed c states a) :
    ∃ s, states (c.next.toGlobal a.sender) = some s ∧ s.epoch = c.targetEpoch ∧
      s.height = c.height ∧ s.round = a.round ∧ voteAllowed s a.value := by
  unfold RecordAllowed at h
  split at h
  · contradiction
  · exact ⟨_, by assumption, h⟩

/-- The old commit signers adopt the SAME checked handover before target voting. -/
def Adoptions (c : Context V) (B : Finset V) (oldCommit : Certificate c.old.n)
    (a : Certificate c.old.n) (states : V → Option LocalState) : Prop :=
  ∀ u ∈ certificateSigners c.old oldCommit, u ∉ B → u ∈ c.next.activeIds →
    states u = some (inherited c a)

/-- Receipt/adoption is an explicit hypothesis. Intersection cannot deliver a certificate. -/
theorem adoptions_from_execution (m : Threshold) (c : Context V) B oldCommit a
    (ha : Accept m c a) :
    Adoptions c B oldCommit a (fun u => adopt m c a u none) := by
  intro u _ _ hu
  exact honest_node_lock_propagation m c a u ha hu

/-- An old commit and a linked accepted polka protect the same decision height. -/
theorem round_zero_safety_handover (m : Threshold) (c : Context V) B
    (a oldCommit : Certificate c.old.n) (newCommit : Certificate c.next.n)
    (states : V → Option LocalState) (ha : Accept m c a)
    (hn : Normalized (epochWeights c.next))
    (ho : oldCommit.epoch = c.sourceEpoch ∧ oldCommit.height = c.height ∧
      oldCommit.phase = .precommit ∧ oldCommit.value = a.value)
    (hnew : newCommit.epoch = c.targetEpoch ∧ newCommit.height = c.height ∧
      newCommit.phase = .precommit ∧ newCommit.round = 0)
    (hq : Quorum m (epochWeights c.old) (certificateSigners c.old oldCommit))
    (hr : Quorum m (epochWeights c.next) (certificateSigners c.next newCommit))
    (hb : Overlap m (epochWeights c.old) (epochWeights c.next) B)
    (hadopt : Adoptions c B oldCommit a states)
    (hvotes : HonestRoundZero c B states newCommit.votes) :
    newCommit.value = oldCommit.value := by
  have hw := epochWeights_normalized c.old ha.2.2.2.2.2.2.1
  obtain ⟨u, hu, hbu, _, hpos⟩ := shared_honest m _ _ hw hn B _ _ hq hr hb
  have hs := hadopt u (mem_inter.mp hu).1 hbu (epoch_positive_active c.next u hpos)
  obtain ⟨i, hi, hv⟩ := (mem_certificateSigners c.next newCommit u).mp (mem_inter.mp hu).2
  rw [hnew.2.2.2] at hv
  obtain ⟨s, he, _, _, _, hall⟩ := record_allowed_state c states
    ⟨i, 0, newCommit.phase, some newCommit.value⟩
    (hvotes _ hv rfl (hi ▸ hbu))
  rw [hi, hs] at he
  have heq : inherited c a = s := Option.some.inj he
  rw [← heq] at hall
  have hval : newCommit.value = a.value := by simpa [voteAllowed, inherited] using hall
  exact hval.trans ho.2.2.2.symm

/-- Sufficient strict-natural threshold bridge; module 179 uses >2/3, not >=2/3. -/
theorem core_quorum_bridge (c : Config n) Q (ht : 0 < c.total) :
    Quorum .strict (normalize (legacyWeights c)) Q ↔ c.quorum Q :=
  legacy_quorum_equivalence c Q ht

/-- A replacement polka is in the TARGET epoch/height and strictly before the vote round. -/
def MayReplace (m : Threshold) (c : Context V) (s : LocalState)
    (a : Certificate c.next.n) : Prop :=
  s.epoch = c.targetEpoch ∧ s.height = c.height ∧ a.epoch = s.epoch ∧
  a.height = s.height ∧ a.phase = .prevote ∧ 0 < s.round ∧
  s.lockedRound < a.round ∧ a.round < s.round ∧
  0 < mass c.next.stakeMap univ ∧
  Quorum m (epochWeights c.next) (certificateSigners c.next a)

instance (m : Threshold) (c : Context V) s a : Decidable (MayReplace m c s a) := by
  unfold MayReplace; infer_instance

def replaceLock (m : Threshold) (c : Context V) (s : LocalState)
    (a : Certificate c.next.n) : Option LocalState :=
  if MayReplace m c s a then some { s with value := a.value, lockedRound := a.round }
  else none

theorem inductive_lock_change_soundness (m : Threshold) (c : Context V) s a t
    (h : replaceLock m c s a = some t) :
    MayReplace m c s a ∧ t = { s with value := a.value, lockedRound := a.round } := by
  unfold replaceLock at h
  split at h <;> simp_all

theorem round_zero_no_replacement (m : Threshold) (c : Context V) s a (hr : s.round = 0) :
    replaceLock m c s a = none := by simp [replaceLock, MayReplace, hr]

theorem stale_polka_rejected (m : Threshold) (c : Context V) s a
    (hr : a.round ≤ s.lockedRound) : replaceLock m c s a = none := by
  have hn : ¬ MayReplace m c s a := fun h => (not_lt_of_ge hr) h.2.2.2.2.2.2.1
  simp [replaceLock, hn]

theorem future_polka_rejected (m : Threshold) (c : Context V) s a
    (hr : s.round ≤ a.round) : replaceLock m c s a = none := by
  have hn : ¬ MayReplace m c s a := fun h => (not_lt_of_ge hr) h.2.2.2.2.2.2.2.1
  simp [replaceLock, hn]

inductive Action (c : Context V) where
  | advance (round : ℕ)
  | replace (certificate : Certificate c.next.n)

def execute (m : Threshold) (c : Context V) (s : LocalState) : Action c → Option LocalState
  | .advance r => if s.round ≤ r then some { s with round := r } else none
  | .replace a => replaceLock m c s a

/-- Every successful step changing value carries a checked, strictly newer local polka. -/
theorem changed_value_has_certificate (m : Threshold) (c : Context V) s action t
    (he : execute m c s action = some t) (hv : t.value ≠ s.value) :
    ∃ a, MayReplace m c s a ∧ t.value = a.value ∧ s.lockedRound < a.round := by
  cases action with
  | advance r =>
    simp only [execute] at he
    split at he
    · have ht := Option.some.inj he
      subst t
      simp_all
    · simp_all
  | replace a =>
    obtain ⟨ha, rfl⟩ := inductive_lock_change_soundness m c s a t he
    exact ⟨a, ha, rfl, ha.2.2.2.2.2.2.1⟩

theorem step_monotone (m : Threshold) (c : Context V) s action t
    (he : execute m c s action = some t) :
    s.round ≤ t.round ∧ s.lockedRound ≤ t.lockedRound ∧
    t.epoch = s.epoch ∧ t.height = s.height := by
  cases action with
  | advance r =>
    simp only [execute] at he
    split at he
    · have ht := Option.some.inj he
      subst t
      simp_all
    · simp_all
  | replace a =>
    obtain ⟨ha, rfl⟩ := inductive_lock_change_soundness m c s a t he
    exact ⟨le_rfl, ha.2.2.2.2.2.2.1.le, rfl, rfl⟩

inductive Reachable (m : Threshold) (c : Context V) (start : LocalState) : LocalState → Prop
  | initial : Reachable m c start start
  | step {s t} : Reachable m c start s → (a : Action c) →
      execute m c s a = some t → Reachable m c start t

/-- Later steps cannot reset a round and smuggle a replacement back into round zero. -/
theorem reachable_round_zero_value (m : Threshold) (c : Context V) start s
    (hs : Reachable m c start s) (hr : s.round = 0) : s.value = start.value := by
  induction hs with
  | initial => rfl
  | @step s t h a he ih =>
    have hz : s.round = 0 := by have hm := (step_monotone m c s a t he).1; omega
    have eq : t.value = s.value := by
      by_contra hn
      obtain ⟨b, hb, _, _⟩ := changed_value_has_certificate m c s a t he hn
      have hp := hb.2.2.2.2.2.1
      omega
    exact eq.trans (ih hz)

/-- Any changed value in a finite local execution has a checked replacement witness. -/
theorem reachable_changed_value_justified (m : Threshold) (c : Context V) start s
    (hs : Reachable m c start s) (hv : s.value ≠ start.value) :
    ∃ pre a, Reachable m c start pre ∧ MayReplace m c pre a ∧
      s.value = a.value ∧ pre.lockedRound < a.round := by
  induction hs with
  | initial => exact False.elim (hv rfl)
  | @step pre post hp action he ih =>
    by_cases same : post.value = pre.value
    · obtain ⟨q, a, hq, ha, hval, hr⟩ := ih (fun h => hv (same.trans h))
      exact ⟨q, a, hq, ha, same.trans hval, hr⟩
    · obtain ⟨a, ha, hval, hr⟩ := changed_value_has_certificate m c pre action post he same
      exact ⟨pre, a, hp, ha, hval, hr⟩

instance (c : Context V) B oldCommit a states :
    Decidable (Adoptions c B oldCommit a states) := by unfold Adoptions; infer_instance

/-- One honest subject in both epochs, but no handover discipline. -/
abbrev unitConfig : EpochConfig (Fin 1) :=
  ⟨1, Function.Embedding.refl _, fun _ => 1, ∅, 0, 100, by decide⟩

abbrev unitContext : Context (Fin 1) := ⟨0, 1, 5, unitConfig, unitConfig⟩

def unitCertificate (e r : ℕ) (p : Phase) (v : ℕ) : Certificate 1 :=
  ⟨e, 5, r, v, p, {⟨0, r, p, some v⟩}⟩

def omissionStates : Fin 1 → Option LocalState :=
  fun _ => some ⟨1, 5, 0, 9, 0, 1, 0⟩

theorem handover_omission_counterexample :
    Accept .strict unitContext (unitCertificate 0 4 .prevote 7) ∧
    Quorum .strict (epochWeights unitConfig)
      (certificateSigners unitConfig (unitCertificate 0 4 .precommit 7)) ∧
    Quorum .strict (epochWeights unitConfig)
      (certificateSigners unitConfig (unitCertificate 1 0 .precommit 9)) ∧
    Overlap .strict (epochWeights unitConfig) (epochWeights unitConfig) ∅ ∧
    HonestRoundZero unitContext ∅ omissionStates (unitCertificate 1 0 .precommit 9).votes ∧
    ¬ Adoptions unitContext ∅ (unitCertificate 0 4 .precommit 7)
      (unitCertificate 0 4 .prevote 7) omissionStates ∧ (7 : ℕ) ≠ 9 := by decide +kernel

structure DistributedTendermintLockHandoverContractSuite : Prop where
  intersection : ∀ {V : Type} [Fintype V] [DecidableEq V]
    (m : Threshold) (w z : V → ℚ), Normalized w → Normalized z →
    ∀ B Q R, Quorum m w Q → Quorum m z R → Overlap m w z B →
    ∃ u ∈ Q ∩ R, u ∉ B ∧ 0 < w u ∧ 0 < z u
  adoption : ∀ {V : Type} [Fintype V] [DecidableEq V] (m : Threshold) (c : Context V) a u,
    Accept m c a → u ∈ c.next.activeIds → adopt m c a u none = some (inherited c a)
  replacement : ∀ {V : Type} [Fintype V] [DecidableEq V] (m : Threshold) (c : Context V) s a t,
    replaceLock m c s a = some t → MayReplace m c s a ∧
      t = { s with value := a.value, lockedRound := a.round }
  round_zero : ∀ {V : Type} [Fintype V] [DecidableEq V] (m : Threshold) (c : Context V) start s,
    Reachable m c start s → s.round = 0 → s.value = start.value
  history : ∀ {V : Type} [Fintype V] [DecidableEq V] (m : Threshold) (c : Context V) start s,
    Reachable m c start s → s.value ≠ start.value →
    ∃ pre a, Reachable m c start pre ∧ MayReplace m c pre a ∧
      s.value = a.value ∧ pre.lockedRound < a.round
  safety : ∀ {V : Type} [Fintype V] [DecidableEq V] (m : Threshold) (c : Context V) B
    (a oldCommit : Certificate c.old.n) (newCommit : Certificate c.next.n)
    (states : V → Option LocalState) (_ha : Accept m c a)
    (_hn : Normalized (epochWeights c.next))
    (_ho : oldCommit.epoch = c.sourceEpoch ∧ oldCommit.height = c.height ∧
      oldCommit.phase = .precommit ∧ oldCommit.value = a.value)
    (_hnew : newCommit.epoch = c.targetEpoch ∧ newCommit.height = c.height ∧
      newCommit.phase = .precommit ∧ newCommit.round = 0)
    (_hq : Quorum m (epochWeights c.old) (certificateSigners c.old oldCommit))
    (_hr : Quorum m (epochWeights c.next) (certificateSigners c.next newCommit))
    (_hb : Overlap m (epochWeights c.old) (epochWeights c.next) B)
    (_hadopt : Adoptions c B oldCommit a states)
    (_hvotes : HonestRoundZero c B states newCommit.votes),
    newCommit.value = oldCommit.value

theorem verification_suite : DistributedTendermintLockHandoverContractSuite :=
  ⟨shared_honest, honest_node_lock_propagation, inductive_lock_change_soundness,
    reachable_round_zero_value, reachable_changed_value_justified, round_zero_safety_handover⟩

end DistributedTendermintLockHandoverContract
