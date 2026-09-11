import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option linter.style.header false

noncomputable section

namespace LamzouriMollifier

/-- The prescribed quadratic denominator; its integral representation is not proved here. -/
def normFunctional (c : ℝ) : ℝ :=
  (1 / 3 : ℝ) + c * (1 / 6 : ℝ) + (c ^ 2) * (1 / 30 : ℝ)

/-- The prescribed quadratic numerator; no spectral operator is defined here. -/
def spectralFunctional (c : ℝ) : ℝ :=
  (1 / 4 : ℝ) + c * (7 / 60 : ℝ) + (c ^ 2) * (11 / 420 : ℝ)

/-- Ratio of the two specified quadratic functions. -/
def rayleighQuotient (c : ℝ) : ℝ :=
  spectralFunctional c / normFunctional c

/-- Complete the square in the denominator. -/
theorem norm_functional_eq_sos (c : ℝ) :
    normFunctional c = (1 / 30 : ℝ) * ((c + (5 / 2 : ℝ)) ^ 2 + (15 / 4 : ℝ)) := by
  dsimp [normFunctional]
  ring

/-- The prescribed denominator is positive for every real parameter. -/
theorem norm_functional_pos (c : ℝ) : 0 < normFunctional c := by
  rw [norm_functional_eq_sos]
  positivity

theorem norm_functional_ne_zero (c : ℝ) : normFunctional c ≠ 0 :=
  ne_of_gt (norm_functional_pos c)

/-- Exact denominator at one. -/
theorem norm_functional_at_one : normFunctional 1 = 8 / 15 := by
  norm_num [normFunctional]

/-- Exact numerator at one. -/
theorem spectral_functional_at_one : spectralFunctional 1 = 11 / 28 := by
  norm_num [spectralFunctional]

/-- Exact value of the prescribed ratio at one. -/
theorem rayleigh_quotient_at_one : rayleighQuotient 1 = 165 / 224 := by
  unfold rayleighQuotient
  rw [norm_functional_at_one, spectral_functional_at_one]
  norm_num

/-- The specified ratio exceeds 0.6725; no conclusion about zeta zeros is asserted. -/
theorem rayleigh_quotient_gt_threshold :
    (6725 / 10000 : ℝ) < rayleighQuotient 1 := by
  rw [rayleigh_quotient_at_one]
  norm_num

/-- A stronger numerical lower bound on the same ratio. -/
theorem rayleigh_quotient_gt_seventy_three_percent :
    (73 / 100 : ℝ) < rayleighQuotient 1 := by
  rw [rayleigh_quotient_at_one]
  norm_num

#print axioms norm_functional_pos
#print axioms rayleigh_quotient_at_one
#print axioms rayleigh_quotient_gt_threshold
#print axioms rayleigh_quotient_gt_seventy_three_percent

end LamzouriMollifier
