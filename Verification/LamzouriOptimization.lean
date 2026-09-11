import Verification.LamzouriMollifier

set_option linter.style.header false

namespace LamzouriOptimization

open LamzouriMollifier

/-- Convert a quotient bound into an equivalent inequality using the positive denominator. -/
theorem rayleigh_gt_iff (c lam : ℝ) :
    lam < rayleighQuotient c ↔ lam * normFunctional c < spectralFunctional c := by
  exact lt_div_iff₀ (norm_functional_pos c)

theorem norm_functional_at_zero : normFunctional 0 = 1 / 3 := by
  norm_num [normFunctional]

theorem spectral_functional_at_zero : spectralFunctional 0 = 1 / 4 := by
  norm_num [spectralFunctional]

theorem rayleigh_quotient_at_zero : rayleighQuotient 0 = 3 / 4 := by
  norm_num [rayleighQuotient, normFunctional, spectralFunctional]

theorem rayleigh_quotient_at_zero_gt_threshold :
    (6725 / 10000 : ℝ) < rayleighQuotient 0 := by
  rw [rayleigh_quotient_at_zero]
  norm_num

theorem norm_functional_at_two : normFunctional 2 = 4 / 5 := by
  norm_num [normFunctional]

theorem spectral_functional_at_two : spectralFunctional 2 = 247 / 420 := by
  norm_num [spectralFunctional]

theorem rayleigh_quotient_at_two : rayleighQuotient 2 = 247 / 336 := by
  norm_num [rayleighQuotient, normFunctional, spectralFunctional]

theorem rayleigh_quotient_at_two_gt_threshold :
    (6725 / 10000 : ℝ) < rayleighQuotient 2 := by
  rw [rayleigh_quotient_at_two]
  norm_num

/-- The prescribed quotient exceeds the threshold throughout the calibration interval. -/
theorem rayleigh_quotient_gt_threshold_on_interval (c : ℝ) (hc : 0 ≤ c) (_hc2 : c ≤ 2) :
    (6725 / 10000 : ℝ) < rayleighQuotient c := by
  apply (rayleigh_gt_iff c _).2
  dsimp [normFunctional, spectralFunctional]
  nlinarith [sq_nonneg c]

/-- A package of bounds for the prescribed quadratic functions. -/
structure LamzouriFormalSuite : Prop where
  h_norm_pos : ∀ c : ℝ, 0 < normFunctional c
  h_norm_one : normFunctional 1 = 8 / 15
  h_spec_one : spectralFunctional 1 = 11 / 28
  h_rayleigh_zero : rayleighQuotient 0 = 3 / 4
  h_rayleigh_one : rayleighQuotient 1 = 165 / 224
  h_rayleigh_two : rayleighQuotient 2 = 247 / 336
  h_bound_zero : (6725 / 10000 : ℝ) < rayleighQuotient 0
  h_bound_one : (6725 / 10000 : ℝ) < rayleighQuotient 1
  h_bound_two : (6725 / 10000 : ℝ) < rayleighQuotient 2
  h_variational : ∀ c lam : ℝ,
    lam < rayleighQuotient c ↔ lam * normFunctional c < spectralFunctional c
  h_interval : ∀ c : ℝ, 0 ≤ c → c ≤ 2 → (6725 / 10000 : ℝ) < rayleighQuotient c

/-- Assemble the proved algebraic identities and interval bound. -/
theorem lamzouri_master_verification_suite : LamzouriFormalSuite := {
  h_norm_pos := norm_functional_pos
  h_norm_one := norm_functional_at_one
  h_spec_one := spectral_functional_at_one
  h_rayleigh_zero := rayleigh_quotient_at_zero
  h_rayleigh_one := rayleigh_quotient_at_one
  h_rayleigh_two := rayleigh_quotient_at_two
  h_bound_zero := rayleigh_quotient_at_zero_gt_threshold
  h_bound_one := rayleigh_quotient_gt_threshold
  h_bound_two := rayleigh_quotient_at_two_gt_threshold
  h_variational := rayleigh_gt_iff
  h_interval := rayleigh_quotient_gt_threshold_on_interval
}

#print axioms rayleigh_quotient_gt_threshold_on_interval
#print axioms lamzouri_master_verification_suite

end LamzouriOptimization
