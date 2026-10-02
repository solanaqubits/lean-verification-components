import Verification.QuantumStandardQuantumLimit
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt

open QuantumStandardQuantumLimit

-- Unequal coefficients put the optimizer at I=2, rather than the symmetric I=1.
example : noiseVariance 4 1 2 = 2 * Real.sqrt (4 * 1) := by
  norm_num [noiseVariance]

example : noiseVariance 4 1 1 > noiseVariance 4 1 2 := by
  norm_num [noiseVariance]

example (I : ℝ) (hI : 0 < I) : noiseVariance 4 1 I = 4 ↔ I = 2 := by
  have h := noiseVariance_unique_min 4 1 I (by norm_num) (by norm_num) hI
  norm_num at h
  exact h

-- Tight calibration: hbar=4, mass=frequency=1, A*B=4.
example (I : ℝ) (hI : 0 < I) : (2 : ℝ) ≤ Real.sqrt (noiseVariance 4 1 I) := by
  have h := sql_standard_deviation_bound 4 1 I 4 1 1
    (by norm_num) (by norm_num) hI (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  norm_num at h ⊢
  exact h

-- Positive physical labels alone do not give the claimed SQL-shaped bound.
example : (6 / (2 * 1 * 1) : ℝ) ^ 2 > 4 * 1 ∧
    noiseVariance 4 1 2 < 6 / (1 * 1) := by
  norm_num [noiseVariance]

-- Zero and negative intensities are outside the optimization domain.
-- Lean's total division at zero must not be mistaken for a physical limit.
example : noiseVariance 1 1 0 < 2 * Real.sqrt (1 * 1) := by
  norm_num [noiseVariance]
example : noiseVariance 1 1 (-1) < 2 * Real.sqrt (1 * 1) := by
  norm_num [noiseVariance]
