/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedTendermintCoreSafety

/-! Fixed-height accountability relative to an authenticated reference transcript.
A partial view cannot certify its own completeness. The reference's authenticity
and completeness are external; no signature algorithm or timeout is modeled. -/
namespace DistributedTendermintAccountableSafety
open Finset DistributedTendermintCoreSafety
open DistributedTendermintCoreSafety.Config
variable {n : ℕ}

/-- Same phase and round, including contradictory nil/block votes. -/
def Equivocation (votes : Finset (Vote n)) (i : Fin n) : Prop :=
  ∃ a ∈ votes, ∃ b ∈ votes, a.sender = i ∧ b.sender = i ∧
    a.round = b.round ∧ a.phase = b.phase ∧ a.value ≠ b.value

/-- Core module 165 requires a polka in the SAME round as the precommit. -/
def InvalidPrecommit (c : Config n) (votes : Finset (Vote n)) (i : Fin n) : Prop :=
  ∃ a ∈ votes, a.sender = i ∧ a.phase = .precommit ∧
    match a.value with
    | none => False
    | some v => ¬ polka c votes a.round v

def HasJustification (c : Config n) (votes : Finset (Vote n)) (lo hi v : ℕ) : Prop :=
  ∃ t ∈ range hi, lo ≤ t ∧ polka c votes t v

def LockViolation (c : Config n) (votes : Finset (Vote n)) (i : Fin n) : Prop :=
  ∃ a ∈ votes, ∃ b ∈ votes, a.sender = i ∧ b.sender = i ∧
    a.phase = .precommit ∧ b.phase = .prevote ∧ a.round < b.round ∧
    match a.value, b.value with
    | some u, some v => u ≠ v ∧ ¬ HasJustification c votes a.round b.round v
    | _, _ => False

def Culprit (c : Config n) (votes : Finset (Vote n)) (i : Fin n) : Prop :=
  Equivocation votes i ∨ InvalidPrecommit c votes i ∨ LockViolation c votes i

instance (votes : Finset (Vote n)) (i : Fin n) : Decidable (Equivocation votes i) := by
  unfold Equivocation; infer_instance
instance (c : Config n) (votes : Finset (Vote n)) (i : Fin n) :
    Decidable (InvalidPrecommit c votes i) := by
  unfold InvalidPrecommit
  have (a : Vote n) : Decidable (match a.value with
      | none => False | some v => ¬ polka c votes a.round v) := by
    cases a.value <;> infer_instance
  infer_instance
instance (c : Config n) (votes : Finset (Vote n)) (lo hi v : ℕ) :
    Decidable (HasJustification c votes lo hi v) := by
  unfold HasJustification; infer_instance
instance (c : Config n) (votes : Finset (Vote n)) (i : Fin n) :
    Decidable (LockViolation c votes i) := by
  unfold LockViolation
  have (a b : Vote n) : Decidable (match a.value, b.value with
      | some u, some v => u ≠ v ∧ ¬ HasJustification c votes a.round b.round v
      | _, _ => False) := by
    cases a.value <;> cases b.value <;> infer_instance
  infer_instance
instance (c : Config n) (votes : Finset (Vote n)) (i : Fin n) :
    Decidable (Culprit c votes i) := by unfold Culprit; infer_instance

/-- This computation never reads c.byzantine. -/
def culprits (c : Config n) (votes : Finset (Vote n)) : Finset (Fin n) :=
  univ.filter (Culprit c votes)

@[simp] theorem mem_culprits (c : Config n) (votes : Finset (Vote n)) (i : Fin n) :
    i ∈ culprits c votes ↔ Culprit c votes i := by simp [culprits]

theorem justification_iff (c : Config n) (votes : Finset (Vote n)) (lo hi v : ℕ) :
    HasJustification c votes lo hi v ↔ ∃ t, lo ≤ t ∧ t < hi ∧ polka c votes t v := by
  constructor
  · rintro ⟨t, ht, hl, hp⟩; exact ⟨t, hl, mem_range.mp ht, hp⟩
  · rintro ⟨t, hl, ht, hp⟩; exact ⟨t, mem_range.mpr ht, hl, hp⟩

theorem clean_precommit (c : Config n) (votes : Finset (Vote n)) (i : Fin n)
    (hi : i ∉ culprits c votes) (r v : ℕ)
    (ha : ⟨i, r, .precommit, some v⟩ ∈ votes) : polka c votes r v := by
  by_contra hp
  exact hi ((mem_culprits c votes i).mpr (Or.inr (Or.inl ⟨_, ha, rfl, rfl, hp⟩)))

/-- Removing exactly the mechanically found violators restores the core history laws. -/
theorem history_outside_culprits (c : Config n) (votes : Finset (Vote n)) :
    History { c with byzantine := culprits c votes } votes := by
  constructor
  · intro i hi r p a b ha hb
    by_contra he
    exact hi ((mem_culprits c votes i).mpr (Or.inl ⟨_, ha, _, hb, rfl, rfl, rfl, rfl, he⟩))
  · intro i hi r v ha
    exact clean_precommit c votes i hi r v ha
  · intro i hi lo u r v ha hb hr
    change ∃ t, lo ≤ t ∧ t < r ∧ polka c votes t v
    by_cases he : u = v
    · subst v
      exact ⟨lo, le_rfl, hr, clean_precommit c votes i hi lo u ha⟩
    · by_contra hn
      have hj : ¬ HasJustification c votes lo r v := by
        simpa only [justification_iff] using hn
      exact hi ((mem_culprits c votes i).mpr
        (Or.inr (Or.inr ⟨_, ha, _, hb, rfl, rfl, rfl, rfl, hr, he, hj⟩)))

/-- Conflicting commits, not a single lock violation, force the strict weight bound. -/
theorem accountable_safety_attribution (c : Config n) (votes : Finset (Vote n))
    {r r' u v : ℕ} (hu : commit c votes r u) (hv : commit c votes r' v) (hne : u ≠ v) :
    c.total < 3 * c.mass (culprits c votes) := by
  by_contra hb
  have hbound : 3 * c.mass (culprits c votes) ≤ c.total := by omega
  exact hne (history_safety { c with byzantine := culprits c votes }
    (history_outside_culprits c votes) hbound hu hv)

/-- An alleged signed envelope; authenticity is established relative to the trusted reference. -/
structure SignedMessage (n : ℕ) where
  height : ℕ
  vote : Vote n
  deriving DecidableEq

structure JustificationEvidence (n : ℕ) where
  height : ℕ
  round : ℕ
  value : ℕ
  signers : Finset (Fin n)
  deriving DecidableEq

structure EvidenceView (n : ℕ) where
  messages : Finset (SignedMessage n)
  justifications : Finset (JustificationEvidence n)
  deriving DecidableEq

def EvidenceView.votes (e : EvidenceView n) : Finset (Vote n) := e.messages.image SignedMessage.vote

def ValidJustification (c : Config n) (votes : Finset (Vote n))
    (e : JustificationEvidence n) : Prop :=
  e.height = c.height ∧ c.quorum e.signers ∧
    ∀ i ∈ e.signers, ⟨i, e.round, .prevote, some e.value⟩ ∈ votes

instance (c : Config n) (votes : Finset (Vote n)) (e : JustificationEvidence n) :
    Decidable (ValidJustification c votes e) := by unfold ValidJustification; infer_instance

theorem valid_justification_polka (c : Config n) (votes : Finset (Vote n))
    (e : JustificationEvidence n) (he : ValidJustification c votes e) :
    polka c votes e.round e.value := by
  have hm : e.signers ⊆ signers votes .prevote e.round (some e.value) := by
    intro i hi; simpa [signers] using he.2.2 i hi
  have := mass_mono c hm
  have hq := he.2.1
  dsimp [polka, quorum] at *
  omega

/-- No allegation can be authenticated by a caller-supplied Boolean completeness flag. -/
def ValidView (c : Config n) (reference : Finset (Vote n)) (e : EvidenceView n) : Prop :=
  (∀ m ∈ e.messages, m.height = c.height) ∧ e.votes ⊆ reference ∧
    ∀ j ∈ e.justifications, ValidJustification c e.votes j

/-- A conservative, finite sufficient coverage contract: all reference prevotes are present.
The reference itself must be authenticated and complete externally. -/
def PrevotesCovered (reference observed : Finset (Vote n)) : Prop :=
  ∀ m ∈ reference, m.phase = .prevote → m ∈ observed

structure EvidenceSufficiency (c : Config n) (reference : Finset (Vote n))
    (e : EvidenceView n) : Prop where
  valid : ValidView c reference e
  covered : PrevotesCovered reference e.votes

instance (c : Config n) (reference : Finset (Vote n)) (e : EvidenceView n) :
    Decidable (ValidView c reference e) := by unfold ValidView; infer_instance
instance (reference observed : Finset (Vote n)) :
    Decidable (PrevotesCovered reference observed) := by
  unfold PrevotesCovered; infer_instance

/-- Prevoting coverage preserves every polka; no global history scan is hidden in blame. -/
theorem polka_of_coverage (c : Config n) {reference observed : Finset (Vote n)}
    (hc : PrevotesCovered reference observed) {r v : ℕ} (hp : polka c reference r v) :
    polka c observed r v := by
  have hm : signers reference .prevote r (some v) ⊆ signers observed .prevote r (some v) := by
    intro i hi
    have hv : ⟨i, r, .prevote, some v⟩ ∈ reference := by simpa [signers] using hi
    have := hc _ hv rfl
    simpa [signers] using this
  have := mass_mono c hm
  dsimp [polka, quorum] at *
  omega

/-- No honest participant in the authenticated reference history is accused by a sufficient view. -/
theorem honest_never_accused (c : Config n) (reference : Finset (Vote n)) (e : EvidenceView n)
    (hs : EvidenceSufficiency c reference e) (hh : History c reference)
    (i : Fin n) (hi : i ∉ c.byzantine) : i ∉ culprits c e.votes := by
  intro hm
  rcases (mem_culprits c e.votes i).mp hm with he | hp | hl
  · rcases he with ⟨a, ha, b, hb, hai, hbi, hr, hp, hv⟩
    apply hv
    apply hh.unique i hi a.round a.phase a.value b.value
    · simpa only [← hai] using hs.valid.2.1 ha
    · simpa only [← hbi, hr, hp] using hs.valid.2.1 hb
  · rcases hp with ⟨a, ha, hai, hp, hv⟩
    cases hvv : a.value with
    | none => simp [hvv] at hv
    | some v =>
      have hb : ¬ polka c e.votes a.round v := by simpa [hvv] using hv
      apply hb
      apply polka_of_coverage c hs.covered
      apply hh.certified i hi a.round v
      have ha' := hs.valid.2.1 ha
      cases a
      simp_all
  · rcases hl with ⟨a, ha, b, hb, hai, hbi, hpa, hpb, hr, hv⟩
    cases hva : a.value with
    | none => simp [hva] at hv
    | some u =>
      cases hvb : b.value with
      | none => simp [hvb] at hv
      | some v =>
        have hv' : u ≠ v ∧ ¬ HasJustification c e.votes a.round b.round v := by
          simpa [hva, hvb] using hv
        have hn := hv'.2
        obtain ⟨t, hle, hlt, ht⟩ := hh.justified i hi a.round u b.round v
          (by have := hs.valid.2.1 ha; cases a; simp_all)
          (by have := hs.valid.2.1 hb; cases b; simp_all) hr
        exact hn ((justification_iff c e.votes _ _ _).mpr
          ⟨t, hle, hlt, polka_of_coverage c hs.covered ht⟩)

theorem reachable_honest_never_accused (c : Config n) {s : State n} (hr : Reachable c s)
    (e : EvidenceView n) (he : EvidenceSufficiency c s.votes e) (i : Fin n)
    (hi : i ∉ c.byzantine) : i ∉ culprits c e.votes :=
  honest_never_accused c s.votes e he (reachable_invariant c hr).history i hi

inductive AttributionError where
  | insufficientEvidence | invalidEvidence
  deriving DecidableEq, Repr

/-- The optional reference is supplied by an external authenticated complete-log service.
This checker verifies relative coverage, not the truth of the service's completeness claim. -/
def attribute_evidence (c : Config n) (reference : Option (Finset (Vote n))) (e : EvidenceView n) :
    Except AttributionError (Finset (Fin n)) :=
  match reference with
  | none => .error .insufficientEvidence
  | some full =>
    if ValidView c full e then
      if PrevotesCovered full e.votes then .ok (culprits c e.votes)
      else .error .insufficientEvidence
    else .error .invalidEvidence

theorem attribute_success_iff (c : Config n) (reference : Finset (Vote n)) (e : EvidenceView n)
    (E : Finset (Fin n)) : attribute_evidence c (some reference) e = .ok E ↔
    EvidenceSufficiency c reference e ∧ culprits c e.votes = E := by
  constructor
  · intro h
    simp only [attribute_evidence] at h
    split_ifs at h with hv hc
    · exact ⟨⟨hv, hc⟩, Except.ok.inj h⟩
  · rintro ⟨⟨hv, hc⟩, rfl⟩
    simp [attribute_evidence, hv, hc]

theorem attribution_honest (c : Config n) {s : State n} (hr : Reachable c s)
    (e : EvidenceView n) (E : Finset (Fin n))
    (he : attribute_evidence c (some s.votes) e = .ok E) (i : Fin n) (hi : i ∉ c.byzantine) :
    i ∉ E := by
  obtain ⟨hs, rfl⟩ := (attribute_success_iff c s.votes e E).mp he
  exact reachable_honest_never_accused c hr e hs i hi

theorem checked_accountable_safety (c : Config n) (reference : Finset (Vote n))
    (e : EvidenceView n) (hs : EvidenceSufficiency c reference e) {r r' u v : ℕ}
    (hu : commit c e.votes r u) (hv : commit c e.votes r' v) (hne : u ≠ v) :
    attribute_evidence c (some reference) e = .ok (culprits c e.votes) ∧
      c.total < 3 * c.mass (culprits c e.votes) :=
  ⟨(attribute_success_iff c reference e _).mpr ⟨hs, rfl⟩,
    accountable_safety_attribution c e.votes hu hv hne⟩

theorem missing_reference_rejected (c : Config n) (e : EvidenceView n) :
    attribute_evidence c none e = .error .insufficientEvidence := rfl

theorem missing_prevotes_rejected (c : Config n) (reference : Finset (Vote n))
    (e : EvidenceView n) (hv : ValidView c reference e) (hc : ¬ PrevotesCovered reference e.votes) :
    attribute_evidence c (some reference) e = .error .insufficientEvidence := by
  simp [attribute_evidence, hv, hc]

theorem invalid_view_rejected (c : Config n) (reference : Finset (Vote n))
    (e : EvidenceView n) (hv : ¬ ValidView c reference e) :
    attribute_evidence c (some reference) e = .error .invalidEvidence := by
  simp [attribute_evidence, hv]

theorem duplicate_accusations_weight (c : Config n) (E : Finset (Fin n)) :
    c.mass (E ∪ E) = c.mass E := by rw [union_self]

theorem duplicate_messages_idempotent (c : Config n) (votes : Finset (Vote n)) :
    culprits c (votes ∪ votes) = culprits c votes := by rw [union_self]

theorem attribution_independent_of_fault_oracle (c : Config n) (b : Finset (Fin n))
    (reference : Option (Finset (Vote n))) (e : EvidenceView n) :
    attribute_evidence { c with byzantine := b } reference e =
      attribute_evidence c reference e := rfl

/-- Concrete message witnesses, independently checkable relative to the sufficient view. -/
inductive Accusation (n : ℕ) where
  | doubleVote (a b : Vote n)
  | uncertifiedPrecommit (a : Vote n)
  | unjustifiedSwitch (a b : Vote n)
  deriving DecidableEq

def Accusation.offender : Accusation n → Fin n
  | .doubleVote a _ | .uncertifiedPrecommit a | .unjustifiedSwitch a _ => a.sender

def ValidAccusation (c : Config n) (votes : Finset (Vote n)) : Accusation n → Prop
  | .doubleVote a b => a ∈ votes ∧ b ∈ votes ∧ a.sender = b.sender ∧
      a.round = b.round ∧ a.phase = b.phase ∧ a.value ≠ b.value
  | .uncertifiedPrecommit a => a ∈ votes ∧ a.phase = .precommit ∧
      match a.value with | none => False | some v => ¬ polka c votes a.round v
  | .unjustifiedSwitch a b => a ∈ votes ∧ b ∈ votes ∧ a.sender = b.sender ∧
      a.phase = .precommit ∧ b.phase = .prevote ∧ a.round < b.round ∧
      match a.value, b.value with
      | some u, some v => u ≠ v ∧ ¬ HasJustification c votes a.round b.round v
      | _, _ => False

instance (c : Config n) (votes : Finset (Vote n)) (a : Accusation n) :
    Decidable (ValidAccusation c votes a) := by
  cases a with
  | doubleVote a b => dsimp only [ValidAccusation]; infer_instance
  | uncertifiedPrecommit a =>
    dsimp only [ValidAccusation]; cases a.value <;> infer_instance
  | unjustifiedSwitch a b =>
    dsimp only [ValidAccusation]; cases a.value <;> cases b.value <;> infer_instance

def accusationCandidates (votes : Finset (Vote n)) : Finset (Accusation n) :=
  (votes ×ˢ votes).image (fun ab => .doubleVote ab.1 ab.2) ∪
  votes.image Accusation.uncertifiedPrecommit ∪
  (votes ×ˢ votes).image (fun ab => .unjustifiedSwitch ab.1 ab.2)

def accusations (c : Config n) (votes : Finset (Vote n)) : Finset (Accusation n) :=
  (accusationCandidates votes).filter (ValidAccusation c votes)

theorem mem_accusations_iff (c : Config n) (votes : Finset (Vote n)) (a : Accusation n) :
    a ∈ accusations c votes ↔ ValidAccusation c votes a := by
  constructor
  · intro h; exact (mem_filter.mp h).2
  · intro h
    apply mem_filter.mpr ⟨?_, h⟩
    cases a with
    | doubleVote a b =>
      exact mem_union.mpr (.inl (mem_union.mpr (.inl
        (mem_image.mpr ⟨(a, b), mem_product.mpr ⟨h.1, h.2.1⟩, rfl⟩))))
    | uncertifiedPrecommit a =>
      exact mem_union.mpr (.inl (mem_union.mpr (.inr (mem_image.mpr ⟨a, h.1, rfl⟩))))
    | unjustifiedSwitch a b =>
      exact mem_union.mpr (.inr (mem_image.mpr ⟨(a, b), mem_product.mpr ⟨h.1, h.2.1⟩, rfl⟩))

/-- Every returned identity has explicit message witnesses; repeated episodes are deduplicated. -/
theorem culprits_eq_accusation_senders (c : Config n) (votes : Finset (Vote n)) :
    culprits c votes = (accusations c votes).image Accusation.offender := by
  ext i
  rw [mem_culprits, mem_image]
  constructor
  · intro h
    rcases h with h | h | h
    · rcases h with ⟨a, ha, b, hb, hai, hbi, hr, hp, hv⟩
      exact ⟨.doubleVote a b, (mem_accusations_iff c votes _).mpr
        ⟨ha, hb, hai.trans hbi.symm, hr, hp, hv⟩, hai⟩
    · rcases h with ⟨a, ha, hai, hp, hv⟩
      exact ⟨.uncertifiedPrecommit a, (mem_accusations_iff c votes _).mpr ⟨ha, hp, hv⟩, hai⟩
    · rcases h with ⟨a, ha, b, hb, hai, hbi, hpa, hpb, hr, hv⟩
      exact ⟨.unjustifiedSwitch a b, (mem_accusations_iff c votes _).mpr
        ⟨ha, hb, hai.trans hbi.symm, hpa, hpb, hr, hv⟩, hai⟩
  · rintro ⟨a, ha, hi⟩
    have hv := (mem_accusations_iff c votes a).mp ha
    cases a with
    | doubleVote a b =>
      exact Or.inl ⟨a, hv.1, b, hv.2.1, hi, hv.2.2.1.symm.trans hi, hv.2.2.2⟩
    | uncertifiedPrecommit a =>
      exact Or.inr (Or.inl ⟨a, hv.1, hi, hv.2⟩)
    | unjustifiedSwitch a b =>
      exact Or.inr (Or.inr ⟨a, hv.1, b, hv.2.1, hi, hv.2.2.1.symm.trans hi, hv.2.2.2⟩)

def canonicalJustification (c : Config n) (votes : Finset (Vote n)) (r v : ℕ) :
    JustificationEvidence n := ⟨c.height, r, v, signers votes .prevote r (some v)⟩

theorem canonical_justification_valid (c : Config n) (votes : Finset (Vote n)) (r v : ℕ)
    (hp : polka c votes r v) : ValidJustification c votes (canonicalJustification c votes r v) := by
  refine ⟨rfl, hp, ?_⟩
  intro i hi
  simpa [canonicalJustification, signers] using hi

/-- A complete reference can itself be packaged as a view, without extra certificates. -/
def completeView (c : Config n) (votes : Finset (Vote n)) : EvidenceView n :=
  ⟨votes.image (fun v => ⟨c.height, v⟩), ∅⟩

@[simp] theorem completeView_votes (c : Config n) (votes : Finset (Vote n)) :
    (completeView c votes).votes = votes := by
  ext v
  simp [EvidenceView.votes, completeView]

theorem complete_view_sufficient (c : Config n) (votes : Finset (Vote n)) :
    EvidenceSufficiency c votes (completeView c votes) := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro m hm
      obtain ⟨v, _, rfl⟩ := mem_image.mp hm
      rfl
    · simp
    · simp [completeView]
  · intro m hm _
    simpa using hm

structure DistributedTendermintAccountableSafetySuite : Prop where
  threshold : ∀ {n} (c : Config n) (votes : Finset (Vote n)) {r r' u v},
    commit c votes r u → commit c votes r' v → u ≠ v →
      c.total < 3 * c.mass (culprits c votes)
  no_framing : ∀ {n} (c : Config n) {s : State n}, Reachable c s →
    ∀ (e : EvidenceView n) (E : Finset (Fin n)),
    attribute_evidence c (some s.votes) e = .ok E → ∀ i, i ∉ c.byzantine → i ∉ E
  witnesses : ∀ {n} (c : Config n) (votes : Finset (Vote n)),
    culprits c votes = (accusations c votes).image Accusation.offender
  checked : ∀ {n} (c : Config n) (reference : Finset (Vote n)) (e : EvidenceView n)
    (E : Finset (Fin n)), attribute_evidence c (some reference) e = .ok E ↔
      EvidenceSufficiency c reference e ∧ culprits c e.votes = E

theorem verification_suite : DistributedTendermintAccountableSafetySuite where
  threshold := accountable_safety_attribution
  no_framing := attribution_honest
  witnesses := culprits_eq_accusation_senders
  checked := attribute_success_iff

end DistributedTendermintAccountableSafety
