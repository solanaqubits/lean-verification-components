import Verification.CryptoTranscriptForkingLemma
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

open CryptoTranscriptForkingLemma

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def mixed (ω : Fin 2) (c : Fin 3) : Bool := decide (c.val < ω.val + 1)
private def constantTwo (_ω : Fin 2) (c : Fin 3) : Bool := decide (c.val < 2)
private def onePerRow (_ω : Fin 2) (c : Fin 3) : Bool := decide (c.val = 0)

-- Exhaustive finite counts; off-diagonal pairs stay in their original row.
example : successCount mixed = 3 ∧ forkCount mixed = 2 := by decide
example : (successOutcomes mixed).card = 3 ∧ (forkOutcomes mixed).card = 2 := by decide

-- Nonuniform row success rates give a strict bound: 1/12 < 1/9.
example : successFraction mixed = 1 / 2 ∧ forkFraction mixed = 1 / 9 ∧
    successFraction mixed * (successFraction mixed - 1 / 3) < forkFraction mixed := by
  have hs : successCount mixed = 3 := by decide
  have hf : forkCount mixed = 2 := by decide
  norm_num [successFraction, forkFraction, hs, hf]

-- Equal row counts attain the elementary bound.
example : successFraction constantTwo = 2 / 3 ∧ forkFraction constantTwo = 2 / 9 := by
  have hs : successCount constantTwo = 4 := by decide
  have hf : forkCount constantTwo = 4 := by decide
  norm_num [successFraction, forkFraction, hs, hf]

example : successFraction constantTwo * (successFraction constantTwo - 1 / 3) =
    forkFraction constantTwo := by
  have hs : successCount constantTwo = 4 := by decide
  have hf : forkCount constantTwo = 4 := by decide
  norm_num [successFraction, forkFraction, hs, hf]

-- The strict existence threshold cannot be weakened to equality.
example : successFraction onePerRow = 1 / 3 ∧ forkCount onePerRow = 0 := by
  have hs : successCount onePerRow = 2 := by decide
  have hf : forkCount onePerRow = 0 := by decide
  norm_num [successFraction, hs, hf]

example : ∃ ω c1 c2, constantTwo ω c1 = true ∧ constantTwo ω c2 = true ∧ c1 ≠ c2 := by
  apply fork_exists_above_threshold constantTwo (by decide)
  have hs : successCount constantTwo = 4 := by decide
  norm_num [successFraction, hs]

-- Independent draws include the failed diagonal; unconditional probability is not one.
example : forkFraction (fun (_ω : Fin 1) (_c : Fin 2) => true) = 1 / 2 := by
  have hf : forkCount (fun (_ω : Fin 1) (_c : Fin 2) => true) = 2 := by decide
  norm_num [forkFraction, hf]

-- Finite-field extraction is actual field division, not division of natural labels.
example : extractWitness (0 : ZMod 5) 3 1 2 = 3 := by
  apply extracted_witness_eq (2 : ZMod 5) 3 4 1 2 0 3
  · decide
  · decide
  · unfold accepts
    decide
  · unfold accepts
    decide

-- Distinct labels alone are insufficient if their field encoding collides.
example :
    transcriptMatrix (1 : ℚ) 1 (fun _ : Fin 1 => 0) (fun _ : Fin 2 => 0)
      (fun _ _ => 0) 0 0 = true ∧
    transcriptMatrix (1 : ℚ) 1 (fun _ : Fin 1 => 0) (fun _ : Fin 2 => 0)
      (fun _ _ => 0) 0 1 = true ∧
    extractWitness (0 : ℚ) 0 0 0 * 1 ≠ 1 := by
  norm_num [transcriptMatrix, extractWitness]

-- End-to-end matrix bridge with an injective encoding and a row-fixed commitment.
example : ∃ ω c1 c2, c1 ≠ c2 ∧
    transcriptMatrix (1 : ℚ) 3 (fun _ : Fin 1 => 4) (fun c : Fin 2 => (c.val : ℚ))
      (fun _ c => 4 + (c.val : ℚ) * 3) ω c1 = true ∧
    transcriptMatrix (1 : ℚ) 3 (fun _ : Fin 1 => 4) (fun c : Fin 2 => (c.val : ℚ))
      (fun _ c => 4 + (c.val : ℚ) * 3) ω c2 = true ∧
    extractWitness (4 + (c1.val : ℚ) * 3) (4 + (c2.val : ℚ) * 3)
      (c1.val : ℚ) (c2.val : ℚ) * 1 = 3 := by
  apply forking_matrix_extracts (1 : ℚ) 3 (fun _ : Fin 1 => 4)
    (fun c : Fin 2 => (c.val : ℚ)) (fun _ c => 4 + (c.val : ℚ) * 3)
  · intro a b h
    apply Fin.ext
    change (a.val : ℚ) = (b.val : ℚ) at h
    exact_mod_cast h
  · decide
  · have hM : transcriptMatrix (1 : ℚ) 3 (fun _ : Fin 1 => 4)
        (fun c : Fin 2 => (c.val : ℚ)) (fun _ c => 4 + (c.val : ℚ) * 3) =
        (fun (_ : Fin 1) (_ : Fin 2) => true) := by
      funext ω c
      simp [transcriptMatrix]
    have hs : successCount
        (transcriptMatrix (1 : ℚ) 3 (fun _ : Fin 1 => 4) (fun c : Fin 2 => (c.val : ℚ))
          (fun _ c => 4 + (c.val : ℚ) * 3)) = 2 := by
      rw [hM]
      decide
    norm_num [successFraction, hs]
