/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedTendermintLockHandoverContract

/-! Conditional all-round agreement in one fixed target epoch and decision height.
The history rules refer to actual finite vote records, not an assumed agreement.
Authentication, delivery and admissibility of a production execution remain external. -/
namespace DistributedTendermintHandoverRoundInduction
open Finset DistributedTendermintCoreSafety
open DistributedTendermintEpochIdentityContract
open DistributedTendermintQuorumIntersectionEpochTransitionContract
open DistributedTendermintLockHandoverContract

variable {V : Type} [Fintype V] [DecidableEq V]

/-- One trusted epoch/height envelope. Chain identity is fixed externally. -/
structure Transcript (n : ℕ) where
  epoch : ℕ
  height : ℕ
  votes : Finset (Vote n)
  deriving DecidableEq

def Transcript.certificate (H : Transcript n) (p : Phase) (r x : ℕ) : Certificate n :=
  ⟨H.epoch, H.height, r, x, p, H.votes⟩

def Observed (m : Threshold) (c : Context V) (H : Transcript c.next.n)
    (p : Phase) (r x : ℕ) : Prop :=
  H.epoch = c.targetEpoch ∧ H.height = c.height ∧
    Quorum m (epochWeights c.next) (certificateSigners c.next (H.certificate p r x))

instance (m : Threshold) (c : Context V) H p r x : Decidable (Observed m c H p r x) := by
  unfold Observed; infer_instance

abbrev Polka (m : Threshold) (c : Context V) H r x := Observed m c H .prevote r x
abbrev Commit (m : Threshold) (c : Context V) H r x := Observed m c H .precommit r x

def EarlierPolka (m : Threshold) (c : Context V) (H : Transcript c.next.n) (r x : ℕ) : Prop :=
  ∃ t ∈ range r, Polka m c H t x

instance (m : Threshold) (c : Context V) H r x : Decidable (EarlierPolka m c H r x) := by
  unfold EarlierPolka; infer_instance

/-- Every possible target quorum meets the adopted honest anchor set A. -/
def Hits (m : Threshold) (c : Context V) (A : Finset V) : Prop :=
  ∀ Q, Quorum m (epochWeights c.next) Q → ∃ u ∈ A, u ∈ Q

instance (m : Threshold) (c : Context V) A : Decidable (Hits m c A) := by
  unfold Hits; infer_instance

def inheritedSigners (c : Context V) (B : Finset V) (oldCommit a : Certificate c.old.n)
    (states : V → Option LocalState) : Finset V :=
  (certificateSigners c.old oldCommit).filter
    (fun u => u ∉ B ∧ states u = some (inherited c a))

theorem inherited_signers_hit_every_quorum (m : Threshold) (c : Context V) B oldCommit a states
    (ha : Accept m c a) (hn : Normalized (epochWeights c.next))
    (hq : Quorum m (epochWeights c.old) (certificateSigners c.old oldCommit))
    (hb : Overlap m (epochWeights c.old) (epochWeights c.next) B)
    (hadopt : Adoptions c B oldCommit a states) :
    Hits m c (inheritedSigners c B oldCommit a states) := by
  intro Q hQ
  obtain ⟨u, hu, hbu, _, hpos⟩ := shared_honest m _ _
    (epochWeights_normalized c.old ha.2.2.2.2.2.2.1) hn B _ Q hq hQ hb
  have hs := hadopt u (mem_inter.mp hu).1 hbu (epoch_positive_active c.next u hpos)
  exact ⟨u, mem_filter.mpr ⟨(mem_inter.mp hu).1, hbu, hs⟩, (mem_inter.mp hu).2⟩

/-- Nil is ignored. Only anchor signers need the rule for the intersection proof. -/
def HonestPrevotesRule (m : Threshold) (c : Context V) (H : Transcript c.next.n) (v : ℕ) (a : Vote
  c.next.n) : Prop :=
  match a.value with
  | none => True
  | some x => x ≠ v → EarlierPolka m c H a.round x

instance (m : Threshold) (c : Context V) H v a : Decidable (HonestPrevotesRule m c H v a) := by
  unfold HonestPrevotesRule; split <;> infer_instance

def HonestPrevotes (m : Threshold) (c : Context V) (H : Transcript c.next.n)
    (A : Finset V) (v : ℕ) : Prop :=
  ∀ a ∈ H.votes, c.next.toGlobal a.sender ∈ A → a.phase = .prevote →
    HonestPrevotesRule m c H v a

instance (m : Threshold) (c : Context V) H A v : Decidable (HonestPrevotes m c H A v) := by
  unfold HonestPrevotes; infer_instance

/-- Safety needs this implication only; a polka does not force execution of a vote. -/
def HonestPrecommitsRule (m : Threshold) (c : Context V) (H : Transcript c.next.n) (a : Vote
  c.next.n) : Prop :=
  match a.value with
  | none => True
  | some x => Polka m c H a.round x

instance (m : Threshold) (c : Context V) H a : Decidable (HonestPrecommitsRule m c H a) := by
  unfold HonestPrecommitsRule; split <;> infer_instance

def HonestPrecommits (m : Threshold) (c : Context V) (H : Transcript c.next.n)
    (A : Finset V) : Prop :=
  ∀ a ∈ H.votes, c.next.toGlobal a.sender ∈ A → a.phase = .precommit →
    HonestPrecommitsRule m c H a

instance (m : Threshold) (c : Context V) H A : Decidable (HonestPrecommits m c H A) := by
  unfold HonestPrecommits; infer_instance

/-- The weighted condition applies uniformly, without fixing a candidate round or value. -/
theorem observed_anchor_vote (m : Threshold) (c : Context V) H A p r x
    (hh : Hits m c A) (ho : Observed m c H p r x) :
    ∃ i, c.next.toGlobal i ∈ A ∧ (⟨i, r, p, some x⟩ : Vote c.next.n) ∈ H.votes := by
  obtain ⟨u, hu, hq⟩ := hh _ ho.2.2
  obtain ⟨i, hi, hv⟩ := (mem_certificateSigners c.next (H.certificate p r x) u).mp hq
  exact ⟨i, hi ▸ hu, hv⟩

theorem no_conflicting_polka_by_well_founded_induction (m : Threshold) (c : Context V) H A v
    (hh : Hits m c A) (hp : HonestPrevotes m c H A v) :
    ∀ r x, Polka m c H r x → x = v := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro x hx
    by_contra hne
    obtain ⟨i, hi, hv⟩ := observed_anchor_vote m c H A .prevote r x hh hx
    obtain ⟨t, ht, htpolka⟩ := hp ⟨i, r, .prevote, some x⟩ hv hi rfl hne
    exact hne (ih t (mem_range.mp ht) x htpolka)

theorem precommit_requires_polka_lemma (m : Threshold) (c : Context V) H A r x
    (hh : Hits m c A) (hc : HonestPrecommits m c H A) (hcommit : Commit m c H r x) :
    Polka m c H r x := by
  obtain ⟨i, hi, hv⟩ := observed_anchor_vote m c H A .precommit r x hh hcommit
  exact hc ⟨i, r, .precommit, some x⟩ hv hi rfl

theorem all_rounds_agreement (m : Threshold) (c : Context V) H A v
    (hh : Hits m c A) (hp : HonestPrevotes m c H A v)
    (hc : HonestPrecommits m c H A) r x (hcommit : Commit m c H r x) : x = v :=
  no_conflicting_polka_by_well_founded_induction m c H A v hh hp r x
    (precommit_requires_polka_lemma m c H A r x hh hc hcommit)

/-- Links the anchor to the checked source polka and an old commit at the SAME height. -/
theorem cross_epoch_arbitrary_round_safety (m : Threshold) (c : Context V) B
    (a oldCommit : Certificate c.old.n) states (H : Transcript c.next.n)
    (ha : Accept m c a) (hn : Normalized (epochWeights c.next))
    (ho : oldCommit.epoch = c.sourceEpoch ∧ oldCommit.height = c.height ∧
      oldCommit.phase = .precommit ∧ oldCommit.value = a.value)
    (hq : Quorum m (epochWeights c.old) (certificateSigners c.old oldCommit))
    (hb : Overlap m (epochWeights c.old) (epochWeights c.next) B)
    (hadopt : Adoptions c B oldCommit a states)
    (hp : HonestPrevotes m c H (inheritedSigners c B oldCommit a states) a.value)
    (hc : HonestPrecommits m c H (inheritedSigners c B oldCommit a states))
    r x (hcommit : Commit m c H r x) : x = oldCommit.value := by
  have hh := inherited_signers_hit_every_quorum m c B oldCommit a states ha hn hq hb hadopt
  exact (all_rounds_agreement m c H _ a.value hh hp hc r x hcommit).trans ho.2.2.2.symm

theorem round_zero_specialization (m : Threshold) (c : Context V) H A v
    (hh : Hits m c A) (hp : HonestPrevotes m c H A v)
    (hc : HonestPrecommits m c H A) x (hcommit : Commit m c H 0 x) : x = v :=
  all_rounds_agreement m c H A v hh hp hc 0 x hcommit

/-- A transcript cannot justify another height or target epoch by relabeling a round. -/
theorem foreign_context_rejected (m : Threshold) (c : Context V) H p r x
    (h : H.epoch ≠ c.targetEpoch ∨ H.height ≠ c.height) : ¬ Observed m c H p r x := by
  intro ho
  rcases h with he | hh
  · exact he ho.1
  · exact hh ho.2.1

theorem no_earlier_round_zero (m : Threshold) (c : Context V) H x :
    ¬ EarlierPolka m c H 0 x := by simp [EarlierPolka]

/-- Actual certificate records, including their envelope, must occur in this history. -/
def Registered (c : Context V) (H : Transcript c.next.n) (a : Certificate c.next.n) : Prop :=
  a.epoch = H.epoch ∧ a.height = H.height ∧ a.votes ⊆ H.votes

instance (c : Context V) H a : Decidable (Registered c H a) := by
  unfold Registered; infer_instance

theorem registered_replacement_polka (m : Threshold) (c : Context V) H s a
    (hn : Normalized (epochWeights c.next)) (ha : MayReplace m c s a)
    (hreg : Registered c H a) : Polka m c H a.round a.value := by
  rcases ha with ⟨se, sh, ae, ah, ap, _, _, _, _, hq⟩
  refine ⟨hreg.1.symm.trans (ae.trans se), hreg.2.1.symm.trans (ah.trans sh), ?_⟩
  have hsub : certificateSigners c.next a ⊆
      certificateSigners c.next (H.certificate .prevote a.round a.value) := by
    intro u hu
    obtain ⟨i, hi, hv⟩ := (mem_certificateSigners c.next a u).mp hu
    apply (mem_certificateSigners c.next _ u).mpr
    refine ⟨i, hi, ?_⟩
    change (⟨i, a.round, .prevote, some a.value⟩ : Vote c.next.n) ∈ H.votes
    rw [ap] at hv
    exact hreg.2.2 hv
  have hm : mass (epochWeights c.next) (certificateSigners c.next a) ≤
      mass (epochWeights c.next) (certificateSigners c.next
        (H.certificate .prevote a.round a.value)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => hn.1 u)
  cases m with
  | weak => exact le_trans hq hm
  | strict => exact lt_of_lt_of_le hq hm

def RegisteredAction (c : Context V) (H : Transcript c.next.n) : Action c → Prop
  | .advance _ => True
  | .replace a => Registered c H a

instance (c : Context V) H a : Decidable (RegisteredAction c H a) := by
  cases a <;> unfold RegisteredAction <;> infer_instance

/-- Module 198's successful transitions with the additional global-history link. -/
inductive RecordedReachable (m : Threshold) (c : Context V) (H : Transcript c.next.n)
    (start : LocalState) : LocalState → Prop
  | initial : RecordedReachable m c H start start
  | step {s t} : RecordedReachable m c H start s → (a : Action c) →
      RegisteredAction c H a → execute m c s a = some t → RecordedReachable m c H start t

theorem recorded_reachable_refines (m : Threshold) (c : Context V) H start s
    (hs : RecordedReachable m c H start s) : Reachable m c start s := by
  induction hs with
  | initial => exact .initial
  | step _ a _ he ih => exact .step ih a he

/-- A changed value has a same-history polka strictly BEFORE the current round. -/
theorem recorded_value_origin (m : Threshold) (c : Context V) H start s
    (hn : Normalized (epochWeights c.next)) (hs : RecordedReachable m c H start s) :
    s.value = start.value ∨ EarlierPolka m c H s.round s.value := by
  induction hs with
  | initial => exact Or.inl rfl
  | @step pre post hp action hreg he ih =>
    have hm := (step_monotone m c pre action post he).1
    cases action with
    | advance r =>
      have hval : post.value = pre.value := by
        simp only [DistributedTendermintLockHandoverContract.execute] at he
        split at he
        · simpa only using congrArg LocalState.value (Option.some.inj he).symm
        · simp_all
      rcases ih with hi | ⟨t, ht, hpolka⟩
      · exact Or.inl (hval.trans hi)
      · exact Or.inr ⟨t, mem_range.mpr (lt_of_lt_of_le (mem_range.mp ht) hm), hval ▸ hpolka⟩
    | replace a =>
      obtain ⟨ha, rfl⟩ := inductive_lock_change_soundness m c pre a post he
      exact Or.inr ⟨a.round, mem_range.mpr ha.2.2.2.2.2.2.2.1,
        registered_replacement_polka m c H pre a hn ha hreg⟩

/-- The local emission guard plus recorded reachability derives the global prevote rule. -/
theorem recorded_prevote_rule (m : Threshold) (c : Context V) H start s
    (hn : Normalized (epochWeights c.next)) (hs : RecordedReachable m c H start s)
    (i : Fin c.next.n) r x (he : emit s i .prevote (some x) = some ⟨i, r, .prevote, some x⟩)
    (hx : x ≠ start.value) : EarlierPolka m c H r x := by
  obtain ⟨hv, heq⟩ := emit_sound s i .prevote (some x) _ he
  have hval : x = s.value := by simpa [voteAllowed] using hv
  have hr : r = s.round := congrArg Vote.round heq
  rcases recorded_value_origin m c H start s hn hs with hsame | hearlier
  · exact False.elim (hx (hval.trans hsame))
  · simpa only [hr, hval] using hearlier

/-- Dropping precommit certification permits a commit with no polka at all. -/
def bareCommit : Transcript 1 := ⟨1, 5, {⟨0, 3, .precommit, some 9⟩}⟩

/-- With <= in place of < a first conflicting polka can justify itself. -/
def circularHistory : Transcript 1 :=
  ⟨1, 5, {⟨0, 1, .prevote, some 9⟩, ⟨0, 1, .precommit, some 9⟩}⟩

def WeakPrevotesRule (m : Threshold) (c : Context V) (H : Transcript c.next.n) (v : ℕ) (a : Vote
  c.next.n) : Prop :=
  match a.value with
  | none => True
  | some x => x ≠ v → ∃ t ∈ range (a.round + 1), Polka m c H t x

instance (m : Threshold) (c : Context V) H v a : Decidable (WeakPrevotesRule m c H v a) := by
  unfold WeakPrevotesRule; split <;> infer_instance

def WeakPrevotes (m : Threshold) (c : Context V) (H : Transcript c.next.n)
    (A : Finset V) (v : ℕ) : Prop :=
  ∀ a ∈ H.votes, c.next.toGlobal a.sender ∈ A → a.phase = .prevote →
    WeakPrevotesRule m c H v a

instance (m : Threshold) (c : Context V) H A v : Decidable (WeakPrevotes m c H A v) := by
  unfold WeakPrevotes; infer_instance

theorem uncertified_precommit_counterexample :
    Hits .strict unitContext {0} ∧
    HonestPrevotes .strict unitContext bareCommit {0} 7 ∧
    Commit .strict unitContext bareCommit 3 9 ∧
    ¬ Polka .strict unitContext bareCommit 3 9 ∧
    ¬ HonestPrecommits .strict unitContext bareCommit {0} ∧ (9 : ℕ) ≠ 7 := by decide +kernel

theorem nonstrict_round_counterexample :
    Hits .strict unitContext {0} ∧
    WeakPrevotes .strict unitContext circularHistory {0} 7 ∧
    HonestPrecommits .strict unitContext circularHistory {0} ∧
    Commit .strict unitContext circularHistory 1 9 ∧
    ¬ HonestPrevotes .strict unitContext circularHistory {0} 7 ∧ (9 : ℕ) ≠ 7 := by decide +kernel

structure DistributedTendermintHandoverRoundInductionSuite : Prop where
  intersection : ∀ {V : Type} [Fintype V] [DecidableEq V],
    ∀ (m : Threshold) (c : Context V) B oldCommit a states
    (_ha : Accept m c a) (_hn : Normalized (epochWeights c.next))
    (_hq : Quorum m (epochWeights c.old) (certificateSigners c.old oldCommit))
    (_hb : Overlap m (epochWeights c.old) (epochWeights c.next) B)
    (_hadopt : Adoptions c B oldCommit a states), Hits m c (inheritedSigners c B oldCommit a states)
  induction : ∀ {V : Type} [Fintype V] [DecidableEq V],
    ∀ (m : Threshold) (c : Context V) H A v
    (_hh : Hits m c A) (_hp : HonestPrevotes m c H A v), ∀ r x, Polka m c H r x → x = v
  certification : ∀ {V : Type} [Fintype V] [DecidableEq V],
    ∀ (m : Threshold) (c : Context V) H A r x
    (_hh : Hits m c A) (_hc : HonestPrecommits m c H A) (_hcommit : Commit m c H r x), Polka m c H
      r x
  agreement : ∀ {V : Type} [Fintype V] [DecidableEq V],
    ∀ (m : Threshold) (c : Context V) H A v
    (_hh : Hits m c A) (_hp : HonestPrevotes m c H A v)
    (_hc : HonestPrecommits m c H A) r x (_hcommit : Commit m c H r x), x = v
  cross_epoch : ∀ {V : Type} [Fintype V] [DecidableEq V],
    ∀ (m : Threshold) (c : Context V) B
    (a oldCommit : Certificate c.old.n) states (H : Transcript c.next.n)
    (_ha : Accept m c a) (_hn : Normalized (epochWeights c.next))
    (_ho : oldCommit.epoch = c.sourceEpoch ∧ oldCommit.height = c.height ∧
      oldCommit.phase = .precommit ∧ oldCommit.value = a.value)
    (_hq : Quorum m (epochWeights c.old) (certificateSigners c.old oldCommit))
    (_hb : Overlap m (epochWeights c.old) (epochWeights c.next) B)
    (_hadopt : Adoptions c B oldCommit a states)
    (_hp : HonestPrevotes m c H (inheritedSigners c B oldCommit a states) a.value)
    (_hc : HonestPrecommits m c H (inheritedSigners c B oldCommit a states))
    r x (_hcommit : Commit m c H r x), x = oldCommit.value
  origin : ∀ {V : Type} [Fintype V] [DecidableEq V],
    ∀ (m : Threshold) (c : Context V) H start s
    (_hn : Normalized (epochWeights c.next)) (_hs : RecordedReachable m c H start s), s.value =
      start.value ∨ EarlierPolka m c H s.round s.value

theorem verification_suite : DistributedTendermintHandoverRoundInductionSuite :=
  ⟨inherited_signers_hit_every_quorum, no_conflicting_polka_by_well_founded_induction,
    precommit_requires_polka_lemma, all_rounds_agreement, cross_epoch_arbitrary_round_safety,
    recorded_value_origin⟩

end DistributedTendermintHandoverRoundInduction
