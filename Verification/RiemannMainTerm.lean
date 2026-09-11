import Verification.RiemannBounds

set_option linter.style.header false

namespace RiemannMainTerm

open RiemannBounds

/-- The iterated logarithm is strictly smaller than the first logarithm on this domain. -/
theorem log_log_lt_log (n : ℕ) (hn : 1000000 ≤ n) :
    Real.log (Real.log (n : ℝ)) < Real.log (n : ℝ) := by
  have h_pos : 0 < Real.log (n : ℝ) := by linarith [log_n_gt_one n hn]
  have h_le := Real.log_le_sub_one_of_pos h_pos
  linarith

/-- The ratio of the iterated and first logarithms is below one. -/
theorem log_ratio_lt_one (n : ℕ) (hn : 1000000 ≤ n) :
    Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) < 1 := by
  have h_pos : 0 < Real.log (n : ℝ) := by linarith [log_n_gt_one n hn]
  exact (div_lt_one h_pos).mpr (log_log_lt_log n hn)

/-- The logarithmic ratio is positive on the specified domain. -/
theorem log_ratio_pos (n : ℕ) (hn : 1000000 ≤ n) :
    0 < Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
  have h_den : 0 < Real.log (n : ℝ) := by linarith [log_n_gt_one n hn]
  exact div_pos (log_log_n_pos n hn) h_den

/-- The prescribed main term is strictly positive. -/
theorem mainTerm_pos (n : ℕ) (hn : 1000000 ≤ n) :
    0 < mainTerm n := by
  dsimp [mainTerm]
  have h_lt1 := log_ratio_lt_one n hn
  linarith

/-- The prescribed main term is strictly below one. -/
theorem mainTerm_lt_one (n : ℕ) (hn : 1000000 ≤ n) :
    mainTerm n < 1 := by
  dsimp [mainTerm]
  have h_pos := log_ratio_pos n hn
  linarith

/-- The model threshold with calibration constant negative one eighth is below one. -/
theorem kappa_crit_lt_one (n : ℕ) (hn : 1000000 ≤ n) :
    kappaCrit n < 1 := by
  dsimp [kappaCrit, c₀_witness]
  have h_main_lt1 := mainTerm_lt_one n hn
  have h_neg_term : (-1 / 8 : ℝ) / (Real.log (n : ℝ) ^ 2) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) (log_sq_pos n hn)
  linarith

#print axioms mainTerm_pos
#print axioms mainTerm_lt_one
#print axioms kappa_crit_lt_one

end RiemannMainTerm
