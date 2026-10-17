/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsRangeWitnessExtraction
import Mathlib.Tactic.Abel

/-! Deterministic special soundness of a linear representation protocol.
The additional opening forks used in the Bulletproofs bridge are explicit inputs;
they are not extracted from the existing Bulletproofs TranscriptFamily. -/
namespace CryptoPedersenCommitmentOpeningExtractionContract
open scoped BigOperators

section Linear
variable {F W A : Type*} [Field F] [AddCommGroup W] [Module F W]
  [AddCommGroup A] [Module F A]

/-- Public statement and response only; no original opening is stored. -/
structure Transcript (F W A : Type*) where
  statement : A
  announcement : A
  challenge : F
  response : W

def Verify (L : W →ₗ[F] A) (C : A) (t : Transcript F W A) : Prop :=
  t.statement = C ∧ L t.response = t.announcement + t.challenge • C

def ValidFork (L : W →ₗ[F] A) (C : A) (t₁ t₂ : Transcript F W A) : Prop :=
  Verify L C t₁ ∧ Verify L C t₂ ∧
    t₁.announcement = t₂.announcement ∧ t₁.challenge ≠ t₂.challenge

instance [DecidableEq A] (L : W →ₗ[F] A) (C : A) (t : Transcript F W A) :
    Decidable (Verify L C t) := inferInstanceAs (Decidable
      (t.statement = C ∧ L t.response = t.announcement + t.challenge • C))

instance [DecidableEq F] [DecidableEq A] (L : W →ₗ[F] A) (C : A)
    (t₁ t₂ : Transcript F W A) : Decidable (ValidFork L C t₁ t₂) :=
  inferInstanceAs (Decidable (Verify L C t₁ ∧ Verify L C t₂ ∧
    t₁.announcement = t₂.announcement ∧ t₁.challenge ≠ t₂.challenge))

/-- Total algebraic formula; equal challenges have no correctness guarantee. -/
def extractOpening (t₁ t₂ : Transcript F W A) : W :=
  (t₁.challenge - t₂.challenge)⁻¹ • (t₁.response - t₂.response)

theorem special_soundness (L : W →ₗ[F] A) (C : A) (t₁ t₂ : Transcript F W A)
    (h : ValidFork L C t₁ t₂) : L (extractOpening t₁ t₂) = C := by
  rcases h with ⟨h₁, h₂, ha, hx⟩
  have hd : L (t₁.response - t₂.response) = (t₁.challenge - t₂.challenge) • C := by
    rw [map_sub, h₁.2, h₂.2, ha, sub_smul]
    abel
  rw [extractOpening, map_smul, hd, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hx), one_smul]

def honestTranscript (L : W →ₗ[F] A) (w mask : W) (x : F) : Transcript F W A :=
  ⟨L w, L mask, x, mask + x • w⟩

theorem honest_accepts (L : W →ₗ[F] A) (w mask : W) (x : F) :
    Verify L (L w) (honestTranscript L w mask x) := by
  simp [Verify, honestTranscript]

theorem honest_fork_valid (L : W →ₗ[F] A) (w mask : W) (x₁ x₂ : F)
    (hx : x₁ ≠ x₂) : ValidFork L (L w)
      (honestTranscript L w mask x₁) (honestTranscript L w mask x₂) :=
  ⟨honest_accepts L w mask x₁, honest_accepts L w mask x₂, rfl, hx⟩

/-- Equality to the original witness is for honest responses with a common mask. -/
theorem honest_extracts (L : W →ₗ[F] A) (w mask : W) (x₁ x₂ : F)
    (hx : x₁ ≠ x₂) : extractOpening
      (honestTranscript L w mask x₁) (honestTranscript L w mask x₂) = w := by
  change (x₁ - x₂)⁻¹ • ((mask + x₁ • w) - (mask + x₂ • w)) = w
  rw [add_sub_add_left_eq_sub, ← sub_smul, smul_smul,
    inv_mul_cancel₀ (sub_ne_zero.mpr hx), one_smul]

theorem honest_mask_independent (L : W →ₗ[F] A) (w mask₁ mask₂ : W)
    (x₁ x₂ : F) (hx : x₁ ≠ x₂) :
    extractOpening (honestTranscript L w mask₁ x₁) (honestTranscript L w mask₁ x₂) =
      extractOpening (honestTranscript L w mask₂ x₁) (honestTranscript L w mask₂ x₂) := by
  rw [honest_extracts L w mask₁ x₁ x₂ hx, honest_extracts L w mask₂ x₁ x₂ hx]

inductive OpeningError where
  | statementMismatch | announcementMismatch | equalChallenges | rejectedResponse
  deriving DecidableEq, Repr

def checked_extract [DecidableEq F] [DecidableEq A] (L : W →ₗ[F] A) (C : A)
    (t₁ t₂ : Transcript F W A) : Except OpeningError W :=
  if t₁.statement ≠ C ∨ t₂.statement ≠ C then .error .statementMismatch
  else if t₁.announcement ≠ t₂.announcement then .error .announcementMismatch
  else if t₁.challenge = t₂.challenge then .error .equalChallenges
  else if L t₁.response = t₁.announcement + t₁.challenge • C ∧
      L t₂.response = t₂.announcement + t₂.challenge • C then
    .ok (extractOpening t₁ t₂)
  else .error .rejectedResponse

theorem checked_extract_success_iff [DecidableEq F] [DecidableEq A]
    (L : W →ₗ[F] A) (C : A) (t₁ t₂ : Transcript F W A) (w : W) :
    checked_extract L C t₁ t₂ = .ok w ↔
      ValidFork L C t₁ t₂ ∧ extractOpening t₁ t₂ = w := by
  simp only [checked_extract, ValidFork, Verify]
  split_ifs <;> simp_all
  tauto

theorem checked_extract_sound [DecidableEq F] [DecidableEq A]
    (L : W →ₗ[F] A) (C : A) (t₁ t₂ : Transcript F W A) (w : W)
    (h : checked_extract L C t₁ t₂ = .ok w) : L w = C := by
  obtain ⟨hf, hw⟩ := (checked_extract_success_iff L C t₁ t₂ w).mp h
  rw [← hw]
  exact special_soundness L C t₁ t₂ hf
end Linear

section Pedersen
variable {q n : ℕ} [Fact q.Prime] {A : Type} [AddCommGroup A] [Module (ZMod q) A]

/-- Scalar Pedersen representation, with no generator independence assumption. -/
def scalarMap (G H : A) : (ZMod q × ZMod q) →ₗ[ZMod q] A where
  toFun w := w.1 • G + w.2 • H
  map_add' u v := by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
  map_smul' c w := by simp [smul_add, smul_smul]

def vectorMap (G : Fin n → A) (H : A) :
    ((Fin n → ZMod q) × ZMod q) →ₗ[ZMod q] A where
  toFun w := CryptoCommitmentVectorPedersenGroup.commit_vec G H w.1 w.2
  map_add' u v := by
    simp only [CryptoCommitmentVectorPedersenGroup.commit_vec, Prod.fst_add, Prod.snd_add,
      Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c w := by
    simp [CryptoCommitmentVectorPedersenGroup.commit_vec, smul_add, Finset.smul_sum, smul_smul]

omit [AddCommGroup A] [Module (ZMod q) A] in
theorem scalar_coordinates (t₁ t₂ : Transcript (ZMod q) (ZMod q × ZMod q) A) :
    extractOpening t₁ t₂ =
      ((t₁.response.1 - t₂.response.1) / (t₁.challenge - t₂.challenge),
       (t₁.response.2 - t₂.response.2) / (t₁.challenge - t₂.challenge)) := by
  ext <;> simp [extractOpening, div_eq_mul_inv, mul_comm]

omit [AddCommGroup A] [Module (ZMod q) A] in
theorem vector_coordinates
    (t₁ t₂ : Transcript (ZMod q) ((Fin n → ZMod q) × ZMod q) A) :
    extractOpening t₁ t₂ =
      ((fun i => (t₁.response.1 i - t₂.response.1 i) / (t₁.challenge - t₂.challenge)),
       (t₁.response.2 - t₂.response.2) / (t₁.challenge - t₂.challenge)) := by
  ext <;> simp [extractOpening, div_eq_mul_inv, mul_comm]

theorem scalar_soundness (G H C : A)
    (t₁ t₂ : Transcript (ZMod q) (ZMod q × ZMod q) A)
    (hf : ValidFork (scalarMap G H) C t₁ t₂) :
    (extractOpening t₁ t₂).1 • G + (extractOpening t₁ t₂).2 • H = C :=
  special_soundness (scalarMap G H) C t₁ t₂ hf

theorem vector_soundness (G : Fin n → A) (H C : A)
    (t₁ t₂ : Transcript (ZMod q) ((Fin n → ZMod q) × ZMod q) A)
    (hf : ValidFork (vectorMap G H) C t₁ t₂) :
    CryptoCommitmentVectorPedersenGroup.commit_vec G H
      (extractOpening t₁ t₂).1 (extractOpening t₁ t₂).2 = C :=
  special_soundness (vectorMap G H) C t₁ t₂ hf

theorem scalar_existing_commit [Fintype A] (S : CryptoPedersenHomomorphicSum.Setup q A)
    (w : ZMod q × ZMod q) : scalarMap S.g S.h w =
      CryptoPedersenHomomorphicSum.commit S w.1 w.2 := rfl

/-- A pair collision yields a discrete-log relation, not a hardness theorem. -/
theorem collision_extracts_dlog [Fintype A] (S : CryptoPedersenHomomorphicSum.Setup q A)
    (w₁ w₂ : ZMod q × ZMod q) (hne : w₁ ≠ w₂)
    (hc : scalarMap S.g S.h w₁ = scalarMap S.g S.h w₂) :
    w₁.2 ≠ w₂.2 ∧ S.h = ((w₁.1 - w₂.1) / (w₂.2 - w₁.2)) • S.g := by
  have hm : w₁.1 ≠ w₂.1 := by
    intro he
    have hr : w₁.2 = w₂.2 := by
      apply smul_left_injective (ZMod q) S.h_ne_zero
      exact add_left_cancel (show w₂.1 • S.g + w₁.2 • S.h =
        w₂.1 • S.g + w₂.2 • S.h by simpa only [scalarMap, LinearMap.coe_mk,
          AddHom.coe_mk, he] using hc)
    exact hne (Prod.ext he hr)
  simpa [div_eq_mul_inv] using
    CryptoPedersenHomomorphicSum.dlog_extraction_from_collision S hc hm
end Pedersen

section Bridge
open CryptoBulletproofsInnerProduct CryptoBulletproofsRangeReduction
namespace Range
export CryptoBulletproofsRangeWitnessExtraction
  (OpeningCertificate ValidOpenings TranscriptFamily ValidFamily extract ResultValid
    extraction_soundness)
end Range
variable {q k : ℕ} [Fact q.Prime] {A : Type} [AddCommGroup A] [Module (ZMod q) A]

abbrev VectorOpening (q k : ℕ) := (Vec k (ZMod q) × Vec k (ZMod q)) × ZMod q

def rangeVectorMap (p : Generators q A k) : VectorOpening q k →ₗ[ZMod q] A where
  toFun w := vector_commit p w.1.1 w.1.2 w.2
  map_add' u v := by
    simp only [vector_commit, multiscalar_mul, Prod.fst_add, Prod.snd_add,
      Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c w := by
    simp [vector_commit, multiscalar_mul, smul_add, Finset.smul_sum, smul_smul]

/-- Additional representation-protocol transcripts, not fields of TranscriptFamily. -/
structure OpeningForks (q k : ℕ) (A : Type) where
  a₁ : Transcript (ZMod q) (VectorOpening q k) A
  a₂ : Transcript (ZMod q) (VectorOpening q k) A
  s₁ : Transcript (ZMod q) (VectorOpening q k) A
  s₂ : Transcript (ZMod q) (VectorOpening q k) A
  v₁ : Transcript (ZMod q) (ZMod q × ZMod q) A
  v₂ : Transcript (ZMod q) (ZMod q × ZMod q) A

def ValidOpeningForks (p : Generators q A k) (Ac Sc V : A)
    (forks : OpeningForks q k A) : Prop :=
  ValidFork (rangeVectorMap p) Ac forks.a₁ forks.a₂ ∧
  ValidFork (rangeVectorMap p) Sc forks.s₁ forks.s₂ ∧
  ValidFork (scalarMap p.B p.Hblind) V forks.v₁ forks.v₂

instance [DecidableEq A] (p : Generators q A k) (Ac Sc V : A)
    (forks : OpeningForks q k A) : Decidable (ValidOpeningForks p Ac Sc V forks) :=
  inferInstanceAs (Decidable (ValidFork (rangeVectorMap p) Ac forks.a₁ forks.a₂ ∧
    ValidFork (rangeVectorMap p) Sc forks.s₁ forks.s₂ ∧
    ValidFork (scalarMap p.B p.Hblind) V forks.v₁ forks.v₂))

def extractCertificate (forks : OpeningForks q k A) : Range.OpeningCertificate q k :=
  let a := extractOpening forks.a₁ forks.a₂
  let s := extractOpening forks.s₁ forks.s₂
  let v := extractOpening forks.v₁ forks.v₂
  ⟨a.1.1, a.1.2, s.1.1, s.1.2, a.2, s.2, v.1, v.2⟩

theorem extracted_certificate_valid (p : Generators q A k) (Ac Sc V : A)
    (forks : OpeningForks q k A) (h : ValidOpeningForks p Ac Sc V forks) :
    Range.ValidOpenings p Ac Sc V (extractCertificate forks) := by
  exact ⟨(special_soundness (rangeVectorMap p) Ac forks.a₁ forks.a₂ h.1).symm,
    (special_soundness (rangeVectorMap p) Sc forks.s₁ forks.s₂ h.2.1).symm,
    (special_soundness (scalarMap p.B p.Hblind) V forks.v₁ forks.v₂ h.2.2).symm⟩

/-- Conditional bridge: neither a rewinding algorithm nor extraction of these
additional forks from the original Bulletproofs transcript is asserted. -/
theorem range_extraction_from_opening_forks (p : Generators q A k) (Ac Sc V : A)
    (forks : OpeningForks q k A) (f : Range.TranscriptFamily q A k)
    (ho : ValidOpeningForks p Ac Sc V forks) (hf : Range.ValidFamily p Ac Sc V f)
    (hq : 2 ^ (2 ^ k) < q) :
    Range.ResultValid p V (Range.extract (extractCertificate forks) f) :=
  Range.extraction_soundness p Ac Sc V (extractCertificate forks) f
    (extracted_certificate_valid p Ac Sc V forks ho) hf hq

end Bridge

structure CryptoPedersenCommitmentOpeningExtractionContractSuite : Prop where
  soundness : ∀ {q : ℕ} [Fact q.Prime] {W A : Type} [AddCommGroup W]
    [Module (ZMod q) W] [AddCommGroup A] [Module (ZMod q) A]
    (L : W →ₗ[ZMod q] A) C t₁ t₂,
    ValidFork L C t₁ t₂ → L (extractOpening t₁ t₂) = C
  checked : ∀ {q : ℕ} [Fact q.Prime] {W A : Type} [AddCommGroup W]
    [Module (ZMod q) W] [AddCommGroup A] [Module (ZMod q) A] [DecidableEq A]
    (L : W →ₗ[ZMod q] A) C t₁ t₂ w,
    checked_extract L C t₁ t₂ = .ok w → L w = C
  honest : ∀ {q : ℕ} [Fact q.Prime] {W A : Type} [AddCommGroup W]
    [Module (ZMod q) W] [AddCommGroup A] [Module (ZMod q) A]
    (L : W →ₗ[ZMod q] A) w mask x₁ x₂, x₁ ≠ x₂ →
    extractOpening (honestTranscript L w mask x₁) (honestTranscript L w mask x₂) = w
  collision : ∀ {q : ℕ} [Fact q.Prime] {A : Type} [Fintype A] [AddCommGroup A]
    [Module (ZMod q) A] (S : CryptoPedersenHomomorphicSum.Setup q A)
    (w₁ w₂ : ZMod q × ZMod q), w₁ ≠ w₂ →
    scalarMap S.g S.h w₁ = scalarMap S.g S.h w₂ →
    w₁.2 ≠ w₂.2 ∧ S.h = ((w₁.1 - w₂.1) / (w₂.2 - w₁.2)) • S.g
  composition : ∀ {q k : ℕ} [Fact q.Prime] {A : Type} [AddCommGroup A]
    [Module (ZMod q) A] (p : CryptoBulletproofsRangeReduction.Generators q A k)
    Ac Sc V forks f, ValidOpeningForks p Ac Sc V forks →
    Range.ValidFamily p Ac Sc V f → 2 ^ (2 ^ k) < q →
    Range.ResultValid p V (Range.extract (extractCertificate forks) f)

theorem verification_suite : CryptoPedersenCommitmentOpeningExtractionContractSuite where
  soundness := special_soundness
  checked := checked_extract_sound
  honest := honest_extracts
  collision := collision_extracts_dlog
  composition := range_extraction_from_opening_forks

end CryptoPedersenCommitmentOpeningExtractionContract
