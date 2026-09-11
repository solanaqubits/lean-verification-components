import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option linter.style.header false

namespace RiemannBounds

/-- The prescribed logarithmic main term; no variational characterization is asserted. -/
noncomputable def mainTerm (n : ℕ) : ℝ :=
  1 - Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)

/-- The selected calibration constant for this explicit model. -/
noncomputable def c₀_witness : ℝ := -1 / 8

/-- The prescribed model threshold with the selected calibration constant. -/
noncomputable def kappaCrit (n : ℕ) : ℝ :=
  mainTerm n + c₀_witness / (Real.log (n : ℝ) ^ 2)

/-- Transfer the lower bound on the natural input to the reals. -/
theorem nat_cast_ge_million (n : ℕ) (hn : 1000000 ≤ n) :
    (1000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn

/-- Positivity of the input to the first logarithm. -/
theorem real_n_pos (n : ℕ) (hn : 1000000 ≤ n) :
    0 < (n : ℝ) := by
  have h := nat_cast_ge_million n hn
  linarith

/-- The logarithm of an input at least one million exceeds one. -/
theorem log_n_gt_one (n : ℕ) (hn : 1000000 ≤ n) :
    1 < Real.log (n : ℝ) := by
  have hn_real := nat_cast_ge_million n hn
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have h4 : 1 ≤ Real.log ((2 : ℝ) ^ 2) := by
    rw [Real.log_pow]
    norm_num at h2 ⊢
    linarith
  have hlt : (2 : ℝ) ^ 2 < (n : ℝ) := by norm_num; linarith
  exact lt_of_le_of_lt h4 (Real.log_lt_log (by norm_num) hlt)

/-- Positivity of the iterated logarithm on the specified domain. -/
theorem log_log_n_pos (n : ℕ) (hn : 1000000 ≤ n) :
    0 < Real.log (Real.log (n : ℝ)) := by
  exact Real.log_pos (log_n_gt_one n hn)

/-- Strict positivity of the squared logarithmic denominator. -/
theorem log_sq_pos (n : ℕ) (hn : 1000000 ≤ n) :
    0 < (Real.log (n : ℝ)) ^ 2 := by
  have h : 0 < Real.log (n : ℝ) := by linarith [log_n_gt_one n hn]
  positivity

/-- Lower bound for the explicitly defined threshold. -/
theorem kappa_crit_lower_bound (n : ℕ) (hn : 1000000 ≤ n) :
    mainTerm n - (485 / 100 : ℝ) / (Real.log (n : ℝ) ^ 2) ≤ kappaCrit n := by
  unfold kappaCrit c₀_witness
  have h_div : (-485 / 100 : ℝ) / (Real.log (n : ℝ) ^ 2) ≤
      (-1 / 8 : ℝ) / (Real.log (n : ℝ) ^ 2) :=
    div_le_div_of_nonneg_right (by norm_num) (le_of_lt (log_sq_pos n hn))
  simp only [neg_div] at h_div ⊢
  linarith

/-- Upper bound for the explicitly defined threshold. -/
theorem kappa_crit_upper_bound (n : ℕ) (hn : 1000000 ≤ n) :
    kappaCrit n ≤ mainTerm n + (460 / 100 : ℝ) / (Real.log (n : ℝ) ^ 2) := by
  unfold kappaCrit c₀_witness
  have h_div : (-1 / 8 : ℝ) / (Real.log (n : ℝ) ^ 2) ≤
      (460 / 100 : ℝ) / (Real.log (n : ℝ) ^ 2) :=
    div_le_div_of_nonneg_right (by norm_num) (le_of_lt (log_sq_pos n hn))
  linarith

/-- Combined bounds for the specified calibrated formula. -/
theorem kappa_crit_explicit_bounds (n : ℕ) (hn : 1000000 ≤ n) :
    mainTerm n - (485 / 100 : ℝ) / (Real.log (n : ℝ) ^ 2) ≤ kappaCrit n ∧
    kappaCrit n ≤ mainTerm n + (460 / 100 : ℝ) / (Real.log (n : ℝ) ^ 2) := by
  exact ⟨kappa_crit_lower_bound n hn, kappa_crit_upper_bound n hn⟩

#print axioms log_n_gt_one
#print axioms kappa_crit_explicit_bounds

end RiemannBounds
