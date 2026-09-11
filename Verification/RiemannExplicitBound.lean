import Verification.RiemannNumericBound

set_option linter.style.header false

namespace RiemannExplicitBound

open RiemannBounds RiemannMainTerm RiemannNumericBound

/-- The squared logarithmic denominator exceeds sixteen. -/
theorem log_sq_gt_sixteen (n : ℕ) (hn : 1000000 ≤ n) :
    (16 : ℝ) < (Real.log (n : ℝ)) ^ 2 := by
  have h := log_n_gt_four n hn
  nlinarith

/-- The reciprocal squared logarithm is strictly below one sixteenth. -/
theorem inv_log_sq_lt_one_sixteenth (n : ℕ) (hn : 1000000 ≤ n) :
    1 / (Real.log (n : ℝ) ^ 2) < (1 / 16 : ℝ) := by
  apply (div_lt_iff₀ (log_sq_pos n hn)).2
  nlinarith [log_sq_gt_sixteen n hn]

/-- Lower bound on the negative calibration correction. -/
theorem neg_term_gt_neg_one_over_128 (n : ℕ) (hn : 1000000 ≤ n) :
    (-1 / 128 : ℝ) < (-1 / 8 : ℝ) / (Real.log (n : ℝ) ^ 2) := by
  have h := inv_log_sq_lt_one_sixteenth n hn
  have hd : (-1 / 8 : ℝ) / (Real.log (n : ℝ) ^ 2) =
      (-1 / 8 : ℝ) * (1 / (Real.log (n : ℝ) ^ 2)) := by ring
  rw [hd]
  nlinarith

/-- Explicit lower bound for the prescribed calibrated threshold. -/
theorem kappa_crit_gt_sixty_three_over_128 (n : ℕ) (hn : 1000000 ≤ n) :
    (63 / 128 : ℝ) < kappaCrit n := by
  dsimp [kappaCrit, c₀_witness]
  have hm := mainTerm_gt_half n hn
  have hp := neg_term_gt_neg_one_over_128 n hn
  linarith

/-- The prescribed threshold exceeds forty-nine hundredths. -/
theorem kappa_crit_gt_forty_nine_hundredths (n : ℕ) (hn : 1000000 ≤ n) :
    (49 / 100 : ℝ) < kappaCrit n := by
  exact lt_trans (by norm_num : (49 / 100 : ℝ) < 63 / 128)
    (kappa_crit_gt_sixty_three_over_128 n hn)

/-- The prescribed threshold lies strictly between 0.49 and one. -/
theorem kappa_crit_strict_bounds (n : ℕ) (hn : 1000000 ≤ n) :
    (49 / 100 : ℝ) < kappaCrit n ∧ kappaCrit n < 1 := by
  exact ⟨kappa_crit_gt_forty_nine_hundredths n hn, kappa_crit_lt_one n hn⟩

/-- Verified analytic bounds for the explicitly defined logarithmic model.
No identification with a mollifier or independently defined functional extremum is asserted.
-/
structure RiemannFormalSuite : Prop where
  h_log_gt1 : ∀ (n : ℕ), 1000000 ≤ n → 1 < Real.log (n : ℝ)
  h_log_log_pos : ∀ (n : ℕ), 1000000 ≤ n → 0 < Real.log (Real.log (n : ℝ))
  h_main_unit : ∀ (n : ℕ), 1000000 ≤ n → 0 < mainTerm n ∧ mainTerm n < 1
  h_main_half : ∀ (n : ℕ), 1000000 ≤ n → (1 / 2 : ℝ) < mainTerm n
  h_kappa_explicit : ∀ (n : ℕ), 1000000 ≤ n →
    mainTerm n - (485 / 100 : ℝ) / (Real.log (n : ℝ) ^ 2) ≤ kappaCrit n ∧
    kappaCrit n ≤ mainTerm n + (460 / 100 : ℝ) / (Real.log (n : ℝ) ^ 2)
  h_kappa_bounds : ∀ (n : ℕ), 1000000 ≤ n → (49 / 100 : ℝ) < kappaCrit n ∧ kappaCrit n < 1

/-- Assemble the analytic model guarantees using only existing proofs. -/
theorem riemann_master_verification_suite : RiemannFormalSuite := {
  h_log_gt1 := log_n_gt_one
  h_log_log_pos := log_log_n_pos
  h_main_unit := fun n hn => ⟨mainTerm_pos n hn, mainTerm_lt_one n hn⟩
  h_main_half := mainTerm_gt_half
  h_kappa_explicit := kappa_crit_explicit_bounds
  h_kappa_bounds := kappa_crit_strict_bounds
}

#print axioms kappa_crit_gt_sixty_three_over_128
#print axioms riemann_master_verification_suite

end RiemannExplicitBound
