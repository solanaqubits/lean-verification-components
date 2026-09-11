import Verification.CollatzBranchFifteen

set_option linter.style.header false

namespace CollatzDyadicTree32

open CollatzBase CollatzAttractor CollatzParity CollatzBranchFifteen

/-- Coverage of all odd inputs by the six branches. -/
theorem odd_dyadic_complete_partition_32 (n : ℕ) (h : n % 2 = 1) :
    n % 8 = 1 ∨ n % 8 = 5 ∨ n % 8 = 3 ∨
    n % 16 = 7 ∨ n % 32 = 15 ∨ n % 32 = 31 := by
  omega

/-- Branch membership indexed by the six leaves of the tree. -/
def InBranch (n : ℕ) (b : Fin 6) : Prop :=
  match b.val with
  | 0 => n % 8 = 1
  | 1 => n % 8 = 5
  | 2 => n % 8 = 3
  | 3 => n % 16 = 7
  | 4 => n % 32 = 15
  | _ => n % 32 = 31

/-- Two branches containing the same input have the same index. -/
theorem branch_unique (n : ℕ) (a b : Fin 6)
    (ha : InBranch n a) (hb : InBranch n b) : a = b := by
  rcases a with ⟨a, ha_lt⟩
  rcases b with ⟨b, hb_lt⟩
  interval_cases a <;> interval_cases b <;> simp [InBranch] at * <;> omega

/-- The six-step value is odd for residue thirty-one modulo thirty-two. -/
theorem collatz_mod32_thirtyone_stage3 (n : ℕ) (h : n % 32 = 31) :
    ((27 * n + 19) / 8) % 2 = 1 := by omega

/-- Exact eight-step formula for the final branch. -/
theorem collatzIter_eight_mod32_thirtyone (n : ℕ) (h : n % 32 = 31) :
    collatzIter 8 n = (81 * n + 65) / 16 := by
  have hm : n % 16 = 15 := by omega
  have hc : collatzIter 8 n = collatzIter 2 (collatzIter 6 n) := collatzIter_add 6 2 n
  rw [hc, collatzIter_six_mod16_fifteen n hm,
    collatzIter_two_odd _ (collatz_mod32_thirtyone_stage3 n h)]
  omega

/-- The proposed thirty-nine-step value is 167, not five. -/
theorem collatzIter_thirtyone_at_39 : collatzIter 39 31 = 167 := by decide

set_option maxRecDepth 4096 in
/-- Starting at thirty-one, the trajectory reaches five after 101 steps. -/
theorem collatzIter_thirtyone_reaches_five : collatzIter 101 31 = 5 := by decide

/-- The finite-base theorem gives eventual reachability of one. -/
theorem collatz_thirtyone_reaches_one : ∃ m : ℕ, collatzIter m 31 = 1 := by
  apply collatz_reaches_one_if_enters_compact 31 101
  · rw [collatzIter_thirtyone_reaches_five]
    omega
  · rw [collatzIter_thirtyone_reaches_five]

/-- Nonnegative normalized rational weights; not a construction of Haar measure. -/
structure DyadicTreeMeasure32 where
  w_mod8_1 : ℚ
  w_mod8_5 : ℚ
  w_mod8_3 : ℚ
  w_mod16_7 : ℚ
  w_mod32_15 : ℚ
  w_mod32_31 : ℚ
  h_nonneg : 0 ≤ w_mod8_1 ∧ 0 ≤ w_mod8_5 ∧ 0 ≤ w_mod8_3 ∧
    0 ≤ w_mod16_7 ∧ 0 ≤ w_mod32_15 ∧ 0 ≤ w_mod32_31
  h_norm : w_mod8_1 + w_mod8_5 + w_mod8_3 + w_mod16_7 + w_mod32_15 + w_mod32_31 = 1

/-- The specified six weights with explicit proofs of their constraints. -/
def canonicalMeasure32 : DyadicTreeMeasure32 where
  w_mod8_1 := 1 / 4
  w_mod8_5 := 1 / 4
  w_mod8_3 := 1 / 4
  w_mod16_7 := 1 / 8
  w_mod32_15 := 1 / 16
  w_mod32_31 := 1 / 16
  h_nonneg := by norm_num
  h_norm := by norm_num

/-- Normalization of the specified weights. -/
theorem canonical_weights_normalized :
    (1 / 4 : ℚ) + 1 / 4 + 1 / 4 + 1 / 8 + 1 / 16 + 1 / 16 = 1 := by norm_num

def coeff_b1 : ℚ := 3 / 4
def coeff_b5 : ℚ := 3 / 8
def coeff_b3 : ℚ := 9 / 8
def coeff_b7 : ℚ := 27 / 16
def coeff_b15 : ℚ := 81 / 32
def coeff_b31 : ℚ := 81 / 16

/-- Unnormalized contribution from the first four branches. -/
def dominantContribution : ℚ :=
  (1 / 4) * coeff_b1 + (1 / 4) * coeff_b5 +
  (1 / 4) * coeff_b3 + (1 / 8) * coeff_b7

/-- Corrected partial sum; this is not the mean of the entire tree. -/
theorem dominant_branches_mean_drift :
    dominantContribution = 99 / 128 ∧ dominantContribution < 1 := by
  norm_num [dominantContribution, coeff_b1, coeff_b5, coeff_b3, coeff_b7]

/-- Normalizing the partial sum by its total weight gives 99/112. -/
theorem dominant_conditional_mean : dominantContribution / (7 / 8) = 99 / 112 := by
  rw [dominant_branches_mean_drift.1]
  norm_num

/-- The complete weighted sum of the supplied leading coefficients. -/
def fullContribution : ℚ :=
  dominantContribution + (1 / 16) * coeff_b15 + (1 / 16) * coeff_b31

/-- The complete sum exceeds one, so these coefficients do not give contraction. -/
theorem full_weighted_sum_gt_one : fullContribution = 639 / 512 ∧ 1 < fullContribution := by
  norm_num [fullContribution, dominantContribution, coeff_b1, coeff_b5, coeff_b3,
    coeff_b7, coeff_b15, coeff_b31]

#print axioms branch_unique
#print axioms collatzIter_eight_mod32_thirtyone
#print axioms collatz_thirtyone_reaches_one
#print axioms full_weighted_sum_gt_one

end CollatzDyadicTree32
