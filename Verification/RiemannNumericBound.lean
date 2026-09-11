import Verification.RiemannMainTerm

set_option linter.style.header false

namespace RiemannNumericBound

open RiemannBounds RiemannMainTerm

/-- Strict lower bound on the exponential at one. -/
theorem exp_one_gt_two : (2 : ℝ) < Real.exp 1 := by
  have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
  linarith

/-- The exponential addition law gives a strict lower bound at two. -/
theorem exp_two_gt_four : (4 : ℝ) < Real.exp 2 := by
  have h1 := exp_one_gt_two
  have hp := Real.exp_pos (1 : ℝ)
  have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  rw [he]
  nlinarith

/-- The logarithm of four is strictly below two. -/
theorem log_four_lt_two : Real.log 4 < 2 := by
  have h := Real.log_lt_log (by norm_num) exp_two_gt_four
  rwa [Real.log_exp] at h

/-- Bound the exponential at four using a logarithmic bound, without decimal approximations. -/
theorem exp_four_lt_million : Real.exp 4 < (1000000 : ℝ) := by
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have h256 : (4 : ℝ) ≤ Real.log ((2 : ℝ) ^ 8) := by
    rw [Real.log_pow]
    norm_num at h2 ⊢
    linarith
  have hl : (4 : ℝ) < Real.log (1000000 : ℝ) :=
    lt_of_le_of_lt h256 (Real.log_lt_log (by norm_num) (by norm_num))
  have he := Real.exp_lt_exp.mpr hl
  rwa [Real.exp_log (by norm_num : (0 : ℝ) < 1000000)] at he

/-- The logarithm exceeds four for every input at least one million. -/
theorem log_n_gt_four (n : ℕ) (hn : 1000000 ≤ n) :
    4 < Real.log (n : ℝ) := by
  have hlt := lt_of_lt_of_le exp_four_lt_million (nat_cast_ge_million n hn)
  have hl := Real.log_lt_log (Real.exp_pos 4) hlt
  rwa [Real.log_exp] at hl

/-- The iterated logarithm is below half the first logarithm on this domain. -/
theorem log_log_lt_half_log (n : ℕ) (hn : 1000000 ≤ n) :
    Real.log (Real.log (n : ℝ)) < Real.log (n : ℝ) / 2 := by
  have hg := log_n_gt_four n hn
  have hp : (0 : ℝ) < Real.log (n : ℝ) / 4 := by linarith
  have hs := Real.log_le_sub_one_of_pos hp
  have hd : Real.log (Real.log (n : ℝ) / 4) =
      Real.log (Real.log (n : ℝ)) - Real.log 4 :=
    Real.log_div (by linarith) (by norm_num)
  rw [hd] at hs
  have h4 := log_four_lt_two
  linarith

/-- The logarithmic ratio is strictly below one half. -/
theorem log_ratio_lt_half (n : ℕ) (hn : 1000000 ≤ n) :
    Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) < 1 / 2 := by
  have hp : 0 < Real.log (n : ℝ) := by linarith [log_n_gt_four n hn]
  apply (div_lt_iff₀ hp).mpr
  linarith [log_log_lt_half_log n hn]

/-- Explicit lower bound on the prescribed main term. -/
theorem mainTerm_gt_half (n : ℕ) (hn : 1000000 ≤ n) :
    (1 / 2 : ℝ) < mainTerm n := by
  dsimp [mainTerm]
  linarith [log_ratio_lt_half n hn]

/-- The prescribed main term lies strictly between one half and one. -/
theorem mainTerm_in_half_one (n : ℕ) (hn : 1000000 ≤ n) :
    (1 / 2 : ℝ) < mainTerm n ∧ mainTerm n < 1 := by
  exact ⟨mainTerm_gt_half n hn, mainTerm_lt_one n hn⟩

#print axioms exp_four_lt_million
#print axioms mainTerm_in_half_one

end RiemannNumericBound
