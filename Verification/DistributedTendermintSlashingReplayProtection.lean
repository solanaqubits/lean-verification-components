/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedTendermintSlashingPenaltyContract

/-! Sequential rational accounting, once per (configuration height, validator).
The authenticated reference, stable validator identities and persistence are external. -/
namespace DistributedTendermintSlashingReplayProtection
open Finset DistributedTendermintCoreSafety DistributedTendermintAccountableSafety
open DistributedTendermintSlashingPenaltyContract

@[ext] structure SlashingLedgerState (V : Type*) where
  balances : V → ℚ
  confiscated : ℚ
  processed : Finset (ℕ × V)

variable {V : Type*} [DecidableEq V]

def WellFormed (s : SlashingLedgerState V) : Prop :=
  (∀ v, 0 ≤ s.balances v) ∧ 0 ≤ s.confiscated

def freshOffenders (s : SlashingLedgerState V) (h : ℕ) (B : Finset V) : Finset V :=
  B.filter fun v => (h, v) ∉ s.processed

/-- Algebraic internal step. Certification and the rate check are at the public boundary. -/
def applyCertifiedSet (s : SlashingLedgerState V) (h : ℕ) (B : Finset V)
    (α : ℚ) : SlashingLedgerState V :=
  let fresh := freshOffenders s h B
  ⟨stakeSlashing s.balances fresh α,
   s.confiscated + DistributedTendermintSlashingPenaltyContract.confiscated s.balances fresh α,
   s.processed ∪ fresh.image (fun v => (h, v))⟩

@[simp] theorem mem_fresh (s : SlashingLedgerState V) (h : ℕ) (B : Finset V) (v : V) :
    v ∈ freshOffenders s h B ↔ v ∈ B ∧ (h, v) ∉ s.processed := by
  simp [freshOffenders]

@[simp] theorem processed_after (s : SlashingLedgerState V) (h : ℕ) (B : Finset V)
    (α : ℚ) (h' : ℕ) (v : V) :
    (h', v) ∈ (applyCertifiedSet s h B α).processed ↔
      (h', v) ∈ s.processed ∨ h' = h ∧ v ∈ B := by
  simp only [applyCertifiedSet, mem_union, mem_image, mem_fresh, Prod.mk.injEq]
  constructor
  · rintro (hp | ⟨u, ⟨hu, _⟩, he, rfl⟩)
    · exact Or.inl hp
    · exact Or.inr ⟨he.symm, hu⟩
  · rintro (hp | ⟨he, hv⟩)
    · exact Or.inl hp
    · subst h'
      by_cases hp : (h, v) ∈ s.processed
      · exact Or.inl hp
      · exact Or.inr ⟨v, ⟨hv, hp⟩, rfl, rfl⟩

theorem processed_monotone (s : SlashingLedgerState V) (h : ℕ) (B : Finset V) (α : ℚ) :
    s.processed ⊆ (applyCertifiedSet s h B α).processed := by
  intro p hp
  exact (processed_after s h B α p.1 p.2).mpr (Or.inl hp)

theorem no_fresh_noop (s : SlashingLedgerState V) (h : ℕ) (B : Finset V) (α : ℚ)
    (hf : freshOffenders s h B = ∅) : applyCertifiedSet s h B α = s := by
  cases s
  simp_all [applyCertifiedSet, DistributedTendermintSlashingPenaltyContract.confiscated]

@[simp] theorem empty_certificate (s : SlashingLedgerState V) (h : ℕ) (α : ℚ) :
    applyCertifiedSet s h ∅ α = s := by
  apply no_fresh_noop
  simp [freshOffenders]

/-- A second set can contain different evidence; only new keys may change balances. -/
theorem previously_processed_balance (s : SlashingLedgerState V) (h : ℕ) (B : Finset V)
    (α : ℚ) (v : V) (hp : (h, v) ∈ s.processed) :
    (applyCertifiedSet s h B α).balances v = s.balances v := by
  exact non_faulty_stake_invariant _ _ _ _ (by simp [hp])

theorem outside_balance (s : SlashingLedgerState V) (h : ℕ) (B : Finset V)
    (α : ℚ) (v : V) (hv : v ∉ B) :
    (applyCertifiedSet s h B α).balances v = s.balances v := by
  exact non_faulty_stake_invariant _ _ _ _ (by simp [hv])

theorem replay_set (s : SlashingLedgerState V) (h : ℕ) (B : Finset V) (α β : ℚ) :
    applyCertifiedSet (applyCertifiedSet s h B α) h B β = applyCertifiedSet s h B α := by
  apply no_fresh_noop
  ext v
  simp
  tauto

theorem overlapping_certificates_no_double_slash (s : SlashingLedgerState V)
    (h : ℕ) (B₁ B₂ : Finset V) (α β : ℚ) (v : V) (hv : v ∈ B₁) :
    (applyCertifiedSet (applyCertifiedSet s h B₁ α) h B₂ β).balances v =
      (applyCertifiedSet s h B₁ α).balances v := by
  apply previously_processed_balance
  simp [hv]

theorem first_step_keys (s : SlashingLedgerState V) (h : ℕ) (B : Finset V)
    (hp : s.processed = ∅) : freshOffenders s h B = B := by
  ext v
  simp [hp]

theorem matches_stateless_penalty (s : SlashingLedgerState V) (h : ℕ) (B : Finset V)
    (α : ℚ) (hp : s.processed = ∅) :
    (applyCertifiedSet s h B α).balances = stakeSlashing s.balances B α := by
  simp only [applyCertifiedSet, first_step_keys s h B hp]

theorem balances_nonnegative (s : SlashingLedgerState V) (h : ℕ) (B : Finset V)
    (α : ℚ) (hw : WellFormed s) (ha : 0 ≤ α) (ha1 : α ≤ 1) :
    WellFormed (applyCertifiedSet s h B α) := by
  exact ⟨slashing_nonnegative _ _ _ hw.1 ha1,
    add_nonneg hw.2 (confiscated_nonnegative _ _ _ hw.1 ha)⟩

section Finite
variable [Fintype V]

def accountedTotal (s : SlashingLedgerState V) : ℚ := totalStake s.balances + s.confiscated

theorem total_stake_conservation (s : SlashingLedgerState V) (h : ℕ) (B : Finset V)
    (α : ℚ) : accountedTotal (applyCertifiedSet s h B α) = accountedTotal s := by
  have hc := slashing_conservation s.balances (freshOffenders s h B) α
  dsimp [accountedTotal, applyCertifiedSet]
  linarith
end Finite

/-- The public transition derives B using module 179, never trusting a caller's set.
The key uses c.height, which is also checked for every signed evidence envelope. -/
def applySlashingCertificate {n : ℕ} (c : Config n)
    (reference : Option (Finset (Vote n))) (e : EvidenceView n) (α : ℚ)
    (s : SlashingLedgerState (Fin n)) : SlashingLedgerState (Fin n) :=
  if 0 < α ∧ α ≤ 1 then
    match attribute_evidence c reference e with
    | .error _ => s
    | .ok B => applyCertifiedSet s c.height B α
  else s

theorem accepted_certificate {n : ℕ} (c : Config n) reference e α
    (s : SlashingLedgerState (Fin n)) B (hc : attribute_evidence c reference e = .ok B)
    (ha : 0 < α ∧ α ≤ 1) :
    applySlashingCertificate c reference e α s = applyCertifiedSet s c.height B α := by
  simp [applySlashingCertificate, ha, hc]

theorem invalid_certificate_noop {n : ℕ} (c : Config n) reference e α
    (s : SlashingLedgerState (Fin n)) err
    (hc : attribute_evidence c reference e = .error err) :
    applySlashingCertificate c reference e α s = s := by
  simp [applySlashingCertificate, hc]

theorem invalid_rate_noop {n : ℕ} (c : Config n) reference e α
    (s : SlashingLedgerState (Fin n)) (ha : ¬ (0 < α ∧ α ≤ 1)) :
    applySlashingCertificate c reference e α s = s := by
  simp [applySlashingCertificate, ha]

theorem replay_idempotence {n : ℕ} (c : Config n) reference e α
    (s : SlashingLedgerState (Fin n)) :
    applySlashingCertificate c reference e α (applySlashingCertificate c reference e α s) =
      applySlashingCertificate c reference e α s := by
  unfold applySlashingCertificate
  split_ifs
  · cases hc : attribute_evidence c reference e with
    | error err => rfl
    | ok B => exact replay_set s c.height B α α
  · rfl

theorem checked_wellFormed {n : ℕ} (c : Config n) reference e α
    (s : SlashingLedgerState (Fin n)) (hw : WellFormed s) :
    WellFormed (applySlashingCertificate c reference e α s) := by
  unfold applySlashingCertificate
  split_ifs with ha
  · cases attribute_evidence c reference e with
    | error err => exact hw
    | ok B => exact balances_nonnegative s c.height B α hw (le_of_lt ha.1) ha.2
  · exact hw

theorem checked_conservation {n : ℕ} (c : Config n) reference e α
    (s : SlashingLedgerState (Fin n)) :
    accountedTotal (applySlashingCertificate c reference e α s) = accountedTotal s := by
  unfold applySlashingCertificate
  split_ifs
  · cases attribute_evidence c reference e with
    | error err => rfl
    | ok B => exact total_stake_conservation s c.height B α
  · rfl

theorem checked_first_step {n : ℕ} (c : Config n) reference e α
    (s : SlashingLedgerState (Fin n)) B (hc : attribute_evidence c reference e = .ok B)
    (ha : 0 < α ∧ α ≤ 1) (hp : s.processed = ∅) :
    (applySlashingCertificate c reference e α s).balances = stakeSlashing s.balances B α := by
  rw [accepted_certificate c reference e α s B hc ha]
  exact matches_stateless_penalty s c.height B α hp

theorem checked_overlap {n : ℕ} (c : Config n) ref₁ ref₂ e₁ e₂ α β
    (s : SlashingLedgerState (Fin n)) B₁ B₂
    (hc₁ : attribute_evidence c ref₁ e₁ = .ok B₁)
    (hc₂ : attribute_evidence c ref₂ e₂ = .ok B₂)
    (ha : 0 < α ∧ α ≤ 1) (hb : 0 < β ∧ β ≤ 1) (v : Fin n) (hv : v ∈ B₁) :
    (applySlashingCertificate c ref₂ e₂ β
      (applySlashingCertificate c ref₁ e₁ α s)).balances v =
      (applySlashingCertificate c ref₁ e₁ α s).balances v := by
  simp only [accepted_certificate c ref₁ e₁ α s B₁ hc₁ ha,
    accepted_certificate c ref₂ e₂ β _ B₂ hc₂ hb]
  exact overlapping_certificates_no_double_slash s c.height B₁ B₂ α β v hv

theorem checked_same_offenders_noop {n : ℕ} (c : Config n) ref₁ ref₂ e₁ e₂ α β
    (s : SlashingLedgerState (Fin n)) B
    (hc₁ : attribute_evidence c ref₁ e₁ = .ok B)
    (hc₂ : attribute_evidence c ref₂ e₂ = .ok B)
    (ha : 0 < α ∧ α ≤ 1) (hb : 0 < β ∧ β ≤ 1) :
    applySlashingCertificate c ref₂ e₂ β (applySlashingCertificate c ref₁ e₁ α s) =
      applySlashingCertificate c ref₁ e₁ α s := by
  simp only [accepted_certificate c ref₁ e₁ α s B hc₁ ha,
    accepted_certificate c ref₂ e₂ β _ B hc₂ hb]
  exact replay_set s c.height B α β

theorem checked_honest_balance {n : ℕ} (c : Config n) {history : State n}
    (hr : Reachable c history) e α (s : SlashingLedgerState (Fin n))
    (v : Fin n) (hv : v ∉ c.byzantine) :
    (applySlashingCertificate c (some history.votes) e α s).balances v = s.balances v := by
  unfold applySlashingCertificate
  split_ifs
  · cases hc : attribute_evidence c (some history.votes) e with
    | error err => rfl
    | ok B => exact outside_balance s c.height B α v (attribution_honest c hr e B hc v hv)
  · rfl

theorem checked_processed_monotone {n : ℕ} (c : Config n) reference e α
    (s : SlashingLedgerState (Fin n)) :
    s.processed ⊆ (applySlashingCertificate c reference e α s).processed := by
  unfold applySlashingCertificate
  split_ifs
  · cases attribute_evidence c reference e with
    | error err => exact Finset.Subset.refl _
    | ok B => exact processed_monotone s c.height B α
  · exact Finset.Subset.refl _

structure CertificateRequest (n : ℕ) where
  config : Config n
  reference : Option (Finset (Vote n))
  evidence : EvidenceView n

def runCertificates {n : ℕ} (α : ℚ) (s : SlashingLedgerState (Fin n))
    (requests : List (CertificateRequest n)) : SlashingLedgerState (Fin n) :=
  requests.foldl (fun st req =>
    applySlashingCertificate req.config req.reference req.evidence α st) s

theorem run_conservation {n : ℕ} (α : ℚ) (requests : List (CertificateRequest n))
    (s : SlashingLedgerState (Fin n)) :
    accountedTotal (runCertificates α s requests) = accountedTotal s := by
  induction requests generalizing s with
  | nil => rfl
  | cons req rest ih =>
    exact (ih _).trans (checked_conservation req.config req.reference req.evidence α s)

theorem run_wellFormed {n : ℕ} (α : ℚ) (requests : List (CertificateRequest n))
    (s : SlashingLedgerState (Fin n)) (hw : WellFormed s) :
    WellFormed (runCertificates α s requests) := by
  induction requests generalizing s with
  | nil => exact hw
  | cons req rest ih =>
    exact ih _ (checked_wellFormed req.config req.reference req.evidence α s hw)

theorem run_processed_monotone {n : ℕ} (α : ℚ) (requests : List (CertificateRequest n))
    (s : SlashingLedgerState (Fin n)) :
    s.processed ⊆ (runCertificates α s requests).processed := by
  induction requests generalizing s with
  | nil => exact Finset.Subset.refl _
  | cons req rest ih =>
    exact (checked_processed_monotone req.config req.reference req.evidence α s).trans (ih _)

structure DistributedTendermintSlashingReplayProtectionSuite : Prop where
  replay : ∀ {n} (c : Config n) reference e α (s : SlashingLedgerState (Fin n)),
    applySlashingCertificate c reference e α (applySlashingCertificate c reference e α s) =
      applySlashingCertificate c reference e α s
  conservation : ∀ {n} (c : Config n) reference e α (s : SlashingLedgerState (Fin n)),
    accountedTotal (applySlashingCertificate c reference e α s) = accountedTotal s
  nonnegative : ∀ {n} (c : Config n) reference e α (s : SlashingLedgerState (Fin n)),
    WellFormed s → WellFormed (applySlashingCertificate c reference e α s)
  rejected : ∀ {n} (c : Config n) reference e α (s : SlashingLedgerState (Fin n)) err,
    attribute_evidence c reference e = .error err → applySlashingCertificate c reference e α s = s
  overlap : ∀ {n} (s : SlashingLedgerState (Fin n)) h B₁ B₂ α β v, v ∈ B₁ →
    (applyCertifiedSet (applyCertifiedSet s h B₁ α) h B₂ β).balances v =
      (applyCertifiedSet s h B₁ α).balances v
  first_step : ∀ {n} (c : Config n) reference e α (s : SlashingLedgerState (Fin n)) B,
    attribute_evidence c reference e = .ok B → (0 < α ∧ α ≤ 1) → s.processed = ∅ →
    (applySlashingCertificate c reference e α s).balances = stakeSlashing s.balances B α
  sequence : ∀ {n} α (requests : List (CertificateRequest n)) (s : SlashingLedgerState (Fin n)),
    accountedTotal (runCertificates α s requests) = accountedTotal s

theorem verification_suite : DistributedTendermintSlashingReplayProtectionSuite where
  replay := replay_idempotence
  conservation := checked_conservation
  nonnegative := checked_wellFormed
  rejected := invalid_certificate_noop
  overlap := overlapping_certificates_no_double_slash
  first_step := checked_first_step
  sequence := run_conservation

end DistributedTendermintSlashingReplayProtection
