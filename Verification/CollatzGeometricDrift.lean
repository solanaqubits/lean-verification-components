import Verification.CollatzDyadicTree32

set_option linter.style.header false

namespace CollatzGeometricDrift

open CollatzDyadicTree32

/-! Exact exponent arithmetic for the specified finite rational weight model.
No Haar-measure identification or stochastic transition law is asserted here.
-/

def pow3_b1 : ℚ := 1
def pow2_b1 : ℚ := 2

def pow3_b5 : ℚ := 1
def pow2_b5 : ℚ := 3

def pow3_b3 : ℚ := 2
def pow2_b3 : ℚ := 3

def pow3_b7 : ℚ := 3
def pow2_b7 : ℚ := 4

def pow3_b15 : ℚ := 4
def pow2_b15 : ℚ := 5

def pow3_b31 : ℚ := 4
def pow2_b31 : ℚ := 4

/-- Weighted exponent of 3 under the specified six weights. -/
def expected_pow3 : ℚ :=
  (1 / 4 : ℚ) * pow3_b1 +
  (1 / 4 : ℚ) * pow3_b5 +
  (1 / 4 : ℚ) * pow3_b3 +
  (1 / 8 : ℚ) * pow3_b7 +
  (1 / 16 : ℚ) * pow3_b15 +
  (1 / 16 : ℚ) * pow3_b31

theorem expected_pow3_eq : expected_pow3 = 15 / 8 := by
  norm_num [expected_pow3, pow3_b1, pow3_b5, pow3_b3, pow3_b7, pow3_b15, pow3_b31]

/-- Weighted exponent of 2 under the specified six weights. -/
def expected_pow2 : ℚ :=
  (1 / 4 : ℚ) * pow2_b1 +
  (1 / 4 : ℚ) * pow2_b5 +
  (1 / 4 : ℚ) * pow2_b3 +
  (1 / 8 : ℚ) * pow2_b7 +
  (1 / 16 : ℚ) * pow2_b15 +
  (1 / 16 : ℚ) * pow2_b31

theorem expected_pow2_eq : expected_pow2 = 49 / 16 := by
  norm_num [expected_pow2, pow2_b1, pow2_b5, pow2_b3, pow2_b7, pow2_b15, pow2_b31]

/-- Exact integer comparison underlying the coefficient product bound. -/
theorem collatz_tree32_integer_drift_strict_contraction :
    (3 : ℕ) ^ 30 < (2 : ℕ) ^ 49 := by
  decide

/-- This ratio is the sixteenth power of the weighted geometric mean. -/
theorem collatz_tree32_rational_drift_ratio_bound :
    ((3 : ℚ) ^ 30) / ((2 : ℚ) ^ 49) < 1 ∧
    ((3 : ℚ) ^ 30) / ((2 : ℚ) ^ 49) < 37 / 100 := by
  constructor <;> norm_num

/-- Product of the existing branch coefficients, with weights multiplied by sixteen. -/
def coefficientProduct16 : ℚ :=
  coeff_b1 ^ 4 * coeff_b5 ^ 4 * coeff_b3 ^ 4 *
  coeff_b7 ^ 2 * coeff_b15 * coeff_b31

/-- Link the integer-exponent product to the actual coefficients from the tree module. -/
theorem coefficient_product_eq :
    coefficientProduct16 = (3 : ℚ) ^ 30 / (2 : ℚ) ^ 49 := by
  norm_num [coefficientProduct16, coeff_b1, coeff_b5, coeff_b3,
    coeff_b7, coeff_b15, coeff_b31]

/-- The scaled-weight coefficient product is positive and strictly below one. -/
theorem coefficient_product_bounds :
    0 < coefficientProduct16 ∧ coefficientProduct16 < 1 := by
  rw [coefficient_product_eq]
  constructor
  · norm_num
  · exact collatz_tree32_rational_drift_ratio_bound.1

#print axioms expected_pow3_eq
#print axioms expected_pow2_eq
#print axioms collatz_tree32_integer_drift_strict_contraction
#print axioms coefficient_product_bounds

end CollatzGeometricDrift
