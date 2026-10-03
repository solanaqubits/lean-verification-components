/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoSchnorrSignature
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Elementary finite-matrix forking and scalar extraction

Rows encode fixed pre-challenge state. A uniform row and two independent uniform
challenge labels form the sample space. We count successful ordered pairs with
distinct labels; there is no adaptive oracle, query-index search, runtime model,
or proof of distributional zero knowledge. The general multi-query forking lemma
of Bellare--Neven is not formalized by this elementary matrix bound.
-/

open scoped BigOperators
noncomputable section
namespace CryptoTranscriptForkingLemma
section Counting
variable {Ω C : Type*} [Fintype Ω] [Fintype C]
/-- Successful challenge labels for the fixed row state. -/
def accepted (M : Ω → C → Bool) (ω : Ω) : Finset C := Finset.univ.filter (fun c => M ω c = true)
def rowCount (M : Ω → C → Bool) (ω : Ω) : ℕ := (accepted M ω).card
def successCount (M : Ω → C → Bool) : ℕ := ∑ ω, rowCount M ω
/-- Count ordered, distinct accepting challenge pairs, keeping the row fixed. -/
def forkCount (M : Ω → C → Bool) : ℕ := ∑ ω, (accepted M ω).offDiag.card
def successFraction (M : Ω → C → Bool) : ℝ :=
  (successCount M : ℝ) / ((Fintype.card Ω : ℝ) * Fintype.card C)
def forkFraction (M : Ω → C → Bool) : ℝ :=
  (forkCount M : ℝ) / ((Fintype.card Ω : ℝ) * (Fintype.card C : ℝ)^2)

omit [Fintype Ω] in
lemma row_fork_cast (M : Ω → C → Bool) (ω : Ω) :
    ((accepted M ω).offDiag.card : ℝ) = (rowCount M ω : ℝ)^2 - rowCount M ω := by
  rw [Finset.offDiag_card, Nat.cast_sub (Nat.le_mul_self _)]
  simp [rowCount, pow_two]

lemma fork_cast (M : Ω → C → Bool) :
    (forkCount M : ℝ) = (∑ ω, (rowCount M ω : ℝ)^2) - (successCount M : ℝ) := by
  simp only [forkCount, Nat.cast_sum, row_fork_cast, Finset.sum_sub_distrib, successCount]

lemma count_bound (M : Ω → C → Bool) :
    (successCount M : ℝ)^2 ≤ (Fintype.card Ω : ℝ) * ((forkCount M : ℝ) + successCount M) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun ω => (rowCount M ω : ℝ)) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  have hS : (∑ ω, (rowCount M ω : ℝ)) = (successCount M : ℝ) := by simp [successCount]
  rw [hS] at h
  rw [fork_cast]
  nlinarith

/-- Elementary uniform finite-matrix lower bound, without a rewinding algorithm. -/
theorem forking_elementary_bound [Nonempty Ω] (M : Ω → C → Bool) (hq : 1 < Fintype.card C) :
    successFraction M * (successFraction M - 1 / (Fintype.card C : ℝ)) ≤ forkFraction M := by
  have hn : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  have hq' : 0 < (Fintype.card C : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hq)
  have h := count_bound M
  unfold successFraction forkFraction
  apply (le_div_iff₀ (mul_pos hn (sq_pos_of_pos hq'))).2
  field_simp
  nlinarith
lemma successFraction_nonneg (M : Ω → C → Bool) : 0 ≤ successFraction M :=
  div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

lemma forkFraction_nonneg (M : Ω → C → Bool) : 0 ≤ forkFraction M :=
  div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

lemma successFraction_le_one [Nonempty Ω] (M : Ω → C → Bool)
    (hq : 1 < Fintype.card C) : successFraction M ≤ 1 := by
  have hn : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  have hq' : 0 < (Fintype.card C : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hq)
  have hs : successCount M ≤ Fintype.card Ω * Fintype.card C := by
    calc
      successCount M ≤ ∑ _ : Ω, Fintype.card C :=
        Finset.sum_le_sum (fun ω _ => Finset.card_le_card (Finset.filter_subset _ _))
      _ = _ := by simp
  unfold successFraction
  apply (div_le_one (mul_pos hn hq')).2
  exact_mod_cast hs


/-- Accepted cells of the finite single-challenge experiment. -/
def successOutcomes (M : Ω → C → Bool) : Finset (Σ _ : Ω, C) :=
  Finset.univ.sigma (accepted M)

/-- Accepted ordered pairs in a common row, with the diagonal excluded. -/
def forkOutcomes (M : Ω → C → Bool) : Finset (Σ _ : Ω, C × C) :=
  Finset.univ.sigma fun ω => (accepted M ω).offDiag

theorem successCount_eq_card_outcomes (M : Ω → C → Bool) :
    successCount M = (successOutcomes M).card := by
  simp [successCount, successOutcomes, rowCount]

theorem forkCount_eq_card_outcomes (M : Ω → C → Bool) :
    forkCount M = (forkOutcomes M).card := by
  simp [forkCount, forkOutcomes]

@[simp] theorem mem_forkOutcomes (M : Ω → C → Bool) (ω : Ω) (c1 c2 : C) :
    ⟨ω, (c1, c2)⟩ ∈ forkOutcomes M ↔
      M ω c1 = true ∧ M ω c2 = true ∧ c1 ≠ c2 := by
  simp [forkOutcomes, accepted]

/-- Both challenges are sampled with replacement: equal draws are counted as failure. -/
theorem experiment_space_card :
    Fintype.card (Ω × C × C) = Fintype.card Ω * Fintype.card C ^ 2 := by
  simp [pow_two]

theorem forkFraction_le_one [Nonempty Ω] (M : Ω → C → Bool)
    (hq : 1 < Fintype.card C) : forkFraction M ≤ 1 := by
  have hn : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  have hq' : 0 < (Fintype.card C : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hq)
  have hf : forkCount M ≤ Fintype.card Ω * Fintype.card C ^ 2 := by
    calc
      forkCount M ≤ ∑ _ : Ω, Fintype.card C ^ 2 := by
        apply Finset.sum_le_sum
        intro ω _
        rw [Finset.offDiag_card]
        have ha : (accepted M ω).card ≤ Fintype.card C := Finset.card_le_univ _
        exact (Nat.sub_le _ _).trans (by simpa [pow_two] using Nat.mul_le_mul ha ha)
      _ = _ := by simp
  unfold forkFraction
  apply (div_le_one (mul_pos hn (sq_pos_of_pos hq'))).2
  exact_mod_cast hf

theorem fork_exists_of_positive (M : Ω → C → Bool) (h : 0 < forkFraction M) :
    ∃ ω c1 c2, M ω c1 = true ∧ M ω c2 = true ∧ c1 ≠ c2 := by
  have hf : 0 < forkCount M := by
    by_contra hn
    have hz : forkCount M = 0 := Nat.eq_zero_of_not_pos hn
    simp [forkFraction, hz] at h
  rw [forkCount_eq_card_outcomes] at hf
  obtain ⟨⟨ω, c1, c2⟩, hmem⟩ := Finset.card_pos.mp hf
  exact ⟨ω, c1, c2, (mem_forkOutcomes M ω c1 c2).mp hmem⟩

/-- Success strictly above one accepting challenge per row guarantees a nonempty fork set. -/
theorem fork_exists_above_threshold [Nonempty Ω] (M : Ω → C → Bool)
    (hq : 1 < Fintype.card C)
    (hε : 1 / (Fintype.card C : ℝ) < successFraction M) :
    ∃ ω c1 c2, M ω c1 = true ∧ M ω c2 = true ∧ c1 ≠ c2 := by
  have hq' : 0 < (Fintype.card C : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hq)
  have hs : 0 < successFraction M := lt_trans (one_div_pos.mpr hq') hε
  exact fork_exists_of_positive M
    (lt_of_lt_of_le (mul_pos hs (sub_pos.mpr hε)) (forking_elementary_bound M hq))

end Counting


/-- Scalar response equation over a field; not a cryptographic group implementation. -/
def accepts {K : Type*} [Field K] (G PK R c s : K) : Prop :=
  s * G = R + c * PK

def extractWitness {K : Type*} [Field K] (s1 s2 c1 c2 : K) : K :=
  (s1 - s2) / (c1 - c2)

/-- Two accepted responses at the same commitment and distinct field challenges
construct a witness for the public scalar equation. -/
theorem forking_witness_extractable {K : Type*} [Field K]
    (G PK R c1 c2 s1 s2 : K) (hc : c1 ≠ c2)
    (h1 : accepts G PK R c1 s1) (h2 : accepts G PK R c2 s2) :
    extractWitness s1 s2 c1 c2 * G = PK := by
  have hsub : (s1 - s2) * G = (c1 - c2) * PK := by
    calc
      (s1 - s2) * G = s1 * G - s2 * G := by ring
      _ = (R + c1 * PK) - (R + c2 * PK) := by rw [h1, h2]
      _ = (c1 - c2) * PK := by ring
  calc
    extractWitness s1 s2 c1 c2 * G = ((s1 - s2) * G) / (c1 - c2) := by
      unfold extractWitness
      ring
    _ = ((c1 - c2) * PK) / (c1 - c2) := by rw [hsub]
    _ = PK := mul_div_cancel_left₀ PK (sub_ne_zero.mpr hc)

/-- For a nonzero scalar generator, the compatible witness equals the original scalar key. -/
theorem extracted_witness_eq {K : Type*} [Field K]
    (G x R c1 c2 s1 s2 : K) (hG : G ≠ 0) (hc : c1 ≠ c2)
    (h1 : accepts G (x * G) R c1 s1) (h2 : accepts G (x * G) R c2 s2) :
    extractWitness s1 s2 c1 c2 = x :=
  mul_right_cancel₀ hG (forking_witness_extractable G (x * G) R c1 c2 s1 s2 hc h1 h2)

/-- Compatibility with the existing real-valued Schnorr verifier. -/
theorem extraction_matches_schnorr (setup : CryptoSchnorrSignature.SchnorrSetup)
    (pk R c1 c2 s1 s2 : ℝ) (hc : c1 ≠ c2)
    (h1 : CryptoSchnorrSignature.verify setup pk R c1 s1)
    (h2 : CryptoSchnorrSignature.verify setup pk R c2 s2) :
    CryptoSchnorrSignature.publicKey setup (extractWitness s1 s2 c1 c2) = pk :=
  CryptoSchnorrSignature.schnorr_special_soundness setup pk R c1 c2 s1 s2 hc h1 h2

/-- Fixed row state determines the commitment before the challenge label is chosen. -/
def transcriptMatrix {Ω C K : Type*} [Field K] [DecidableEq K]
    (G PK : K) (commitment : Ω → K) (challenge : C → K) (response : Ω → C → K)
    (ω : Ω) (c : C) : Bool :=
  decide (response ω c * G = commitment ω + challenge c * PK)

/-- A successful distinct-label fork yields a scalar witness when label encoding is injective. -/
theorem transcript_fork_extracts {Ω C K : Type*} [Field K] [DecidableEq K]
    (G PK : K) (commitment : Ω → K) (challenge : C → K) (response : Ω → C → K)
    (hinj : Function.Injective challenge) (ω : Ω) (c1 c2 : C) (hc : c1 ≠ c2)
    (h1 : transcriptMatrix G PK commitment challenge response ω c1 = true)
    (h2 : transcriptMatrix G PK commitment challenge response ω c2 = true) :
    extractWitness (response ω c1) (response ω c2) (challenge c1) (challenge c2) * G = PK := by
  apply forking_witness_extractable G PK (commitment ω) _ _ _ _ (hinj.ne hc)
  · simpa only [transcriptMatrix, decide_eq_true_eq, accepts] using h1
  · simpa only [transcriptMatrix, decide_eq_true_eq, accepts] using h2



/-- Combining finite counting and scalar special soundness. The commitment is fixed
by the row, and injective challenge encoding preserves distinctness. -/
theorem forking_matrix_extracts {Ω C K : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype C] [Field K] [DecidableEq K]
    (G PK : K) (commitment : Ω → K) (challenge : C → K) (response : Ω → C → K)
    (hinj : Function.Injective challenge) (hq : 1 < Fintype.card C)
    (hε : 1 / (Fintype.card C : ℝ) <
      successFraction (transcriptMatrix G PK commitment challenge response)) :
    ∃ ω c1 c2, c1 ≠ c2 ∧
      transcriptMatrix G PK commitment challenge response ω c1 = true ∧
      transcriptMatrix G PK commitment challenge response ω c2 = true ∧
      extractWitness (response ω c1) (response ω c2) (challenge c1) (challenge c2) * G = PK := by
  obtain ⟨ω, c1, c2, h1, h2, hc⟩ := fork_exists_above_threshold _ hq hε
  exact ⟨ω, c1, c2, hc, h1, h2,
    transcript_fork_extracts G PK commitment challenge response hinj ω c1 c2 hc h1 h2⟩

/-- Finite uniform matrix counting and scalar algebra; no ROM security reduction. -/
structure ForkingLemmaFormalSuite : Prop where
  h_count : ∀ {Ω C : Type} [Fintype Ω] [Fintype C] (M : Ω → C → Bool),
    (successCount M : ℝ)^2 ≤ (Fintype.card Ω : ℝ) * ((forkCount M : ℝ) + successCount M)
  h_bound : ∀ {Ω C : Type} [Fintype Ω] [Nonempty Ω] [Fintype C]
    (M : Ω → C → Bool), 1 < Fintype.card C →
    successFraction M * (successFraction M - 1 / (Fintype.card C : ℝ)) ≤ forkFraction M
  h_exists : ∀ {Ω C : Type} [Fintype Ω] [Nonempty Ω] [Fintype C]
    (M : Ω → C → Bool), 1 < Fintype.card C →
    1 / (Fintype.card C : ℝ) < successFraction M →
    ∃ ω c1 c2, M ω c1 = true ∧ M ω c2 = true ∧ c1 ≠ c2
  h_extract : ∀ {K : Type} [Field K] (G PK R c1 c2 s1 s2 : K), c1 ≠ c2 →
    accepts G PK R c1 s1 → accepts G PK R c2 s2 →
    extractWitness s1 s2 c1 c2 * G = PK
  h_original : ∀ {K : Type} [Field K] (G x R c1 c2 s1 s2 : K), G ≠ 0 → c1 ≠ c2 →
    accepts G (x * G) R c1 s1 → accepts G (x * G) R c2 s2 →
    extractWitness s1 s2 c1 c2 = x

  h_matrix : ∀ {Ω C K : Type} [Fintype Ω] [Nonempty Ω] [Fintype C]
    [Field K] [DecidableEq K] (G PK : K) (commitment : Ω → K)
    (challenge : C → K) (response : Ω → C → K),
    Function.Injective challenge → 1 < Fintype.card C →
    1 / (Fintype.card C : ℝ) <
      successFraction (transcriptMatrix G PK commitment challenge response) →
    ∃ ω c1 c2, c1 ≠ c2 ∧
      transcriptMatrix G PK commitment challenge response ω c1 = true ∧
      transcriptMatrix G PK commitment challenge response ω c2 = true ∧
      extractWitness (response ω c1) (response ω c2) (challenge c1) (challenge c2) * G = PK

theorem transcript_forking_master_suite : ForkingLemmaFormalSuite := {
  h_count := count_bound
  h_bound := forking_elementary_bound
  h_exists := fork_exists_above_threshold
  h_extract := forking_witness_extractable
  h_original := extracted_witness_eq
  h_matrix := forking_matrix_extracts
}

end CryptoTranscriptForkingLemma
