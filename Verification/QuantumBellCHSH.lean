/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Deterministic CHSH algebra and a scalar comparison value

The classical statements concern four jointly assigned signs and a two-term
convex mixture. The number `2 * sqrt 2` is defined, not derived from quantum
observables: no quantum attainability or universal operator bound is proved.
-/

noncomputable section

namespace QuantumBellCHSH

/-- A prescribed binary outcome. -/
def IsSpinMeasurement (s : ℝ) : Prop := s = 1 ∨ s = -1

def chshExpr (a0 a1 b0 b1 : ℝ) : ℝ :=
  a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1

theorem chsh_factorization (a0 a1 b0 b1 : ℝ) :
    chshExpr a0 a1 b0 b1 = a0 * (b0 + b1) + a1 * (b0 - b1) := by
  dsimp [chshExpr]
  ring

/-- Every joint assignment of four signs gives exactly one of the two extrema. -/
theorem chsh_classical_deterministic_values (a0 a1 b0 b1 : ℝ)
    (ha0 : IsSpinMeasurement a0) (ha1 : IsSpinMeasurement a1)
    (hb0 : IsSpinMeasurement b0) (hb1 : IsSpinMeasurement b1) :
    chshExpr a0 a1 b0 b1 = 2 ∨ chshExpr a0 a1 b0 b1 = -2 := by
  rcases ha0 with rfl | rfl <;> rcases ha1 with rfl | rfl <;>
    rcases hb0 with rfl | rfl <;> rcases hb1 with rfl | rfl <;> norm_num [chshExpr]

/-- Absolute equality is for deterministic assignments, not arbitrary mixtures. -/
theorem chsh_classical_bound (a0 a1 b0 b1 : ℝ)
    (ha0 : IsSpinMeasurement a0) (ha1 : IsSpinMeasurement a1)
    (hb0 : IsSpinMeasurement b0) (hb1 : IsSpinMeasurement b1) :
    |chshExpr a0 a1 b0 b1| = 2 ∧ chshExpr a0 a1 b0 b1 ≤ 2 := by
  rcases chsh_classical_deterministic_values a0 a1 b0 b1 ha0 ha1 hb0 hb1 with h | h
  all_goals rw [h]; norm_num

/-- Upper bound for a convex mixture of two scalars with upper bound two. -/
theorem chsh_convex_ensemble_bound (w1 w2 c1 c2 : ℝ)
    (hw1_nonneg : 0 ≤ w1) (hw2_nonneg : 0 ≤ w2)
    (h_weights : w1 + w2 = 1) (hc1_le : c1 ≤ 2) (hc2_le : c2 ≤ 2) :
    w1 * c1 + w2 * c2 ≤ 2 := by
  have h1 := mul_le_mul_of_nonneg_left hc1_le hw1_nonneg
  have h2 := mul_le_mul_of_nonneg_left hc2_le hw2_nonneg
  nlinarith

/-- The named comparison number; not an operator-norm bound in this model. -/
def tsirelsonBound : ℝ := 2 * Real.sqrt 2

/-- Arithmetic separation of the defined comparison number from two. -/
theorem quantum_violates_classical_bound : 2 < tsirelsonBound := by
  have h := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num)
    (show (1 : ℝ) < 2 by norm_num)
  rw [Real.sqrt_one] at h
  dsimp [tsirelsonBound]
  linarith

theorem tsirelson_bound_squared : tsirelsonBound ^ 2 = 8 := by
  dsimp [tsirelsonBound]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- An exact rational lower bound, with no floating-point approximation. -/
theorem quantum_advantage_numerical_lower_bound : (14 / 5 : ℝ) < tsirelsonBound := by
  have hnonneg := Real.sqrt_nonneg (2 : ℝ)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  dsimp [tsirelsonBound]
  nlinarith

structure QuantumBellCHSHFormalSuite : Prop where
  h_factorization : ∀ (a0 a1 b0 b1 : ℝ),
    chshExpr a0 a1 b0 b1 = a0 * (b0 + b1) + a1 * (b0 - b1)
  h_det_values : ∀ (a0 a1 b0 b1 : ℝ),
    IsSpinMeasurement a0 → IsSpinMeasurement a1 →
    IsSpinMeasurement b0 → IsSpinMeasurement b1 →
    chshExpr a0 a1 b0 b1 = 2 ∨ chshExpr a0 a1 b0 b1 = -2
  h_class_bound : ∀ (a0 a1 b0 b1 : ℝ),
    IsSpinMeasurement a0 → IsSpinMeasurement a1 →
    IsSpinMeasurement b0 → IsSpinMeasurement b1 →
    |chshExpr a0 a1 b0 b1| = 2 ∧ chshExpr a0 a1 b0 b1 ≤ 2
  h_ensemble : ∀ (w1 w2 c1 c2 : ℝ),
    0 ≤ w1 → 0 ≤ w2 → w1 + w2 = 1 → c1 ≤ 2 → c2 ≤ 2 →
    w1 * c1 + w2 * c2 ≤ 2
  h_qm_violation : 2 < tsirelsonBound
  h_tsirelson_sq : tsirelsonBound ^ 2 = 8
  h_advantage_num : (14 / 5 : ℝ) < tsirelsonBound

/-- Registry of deterministic classical bounds and scalar square-root identities. -/
theorem quantum_bell_chsh_master_verification_suite : QuantumBellCHSHFormalSuite := {
  h_factorization := chsh_factorization
  h_det_values := chsh_classical_deterministic_values
  h_class_bound := chsh_classical_bound
  h_ensemble := chsh_convex_ensemble_bound
  h_qm_violation := quantum_violates_classical_bound
  h_tsirelson_sq := tsirelson_bound_squared
  h_advantage_num := quantum_advantage_numerical_lower_bound
}

end QuantumBellCHSH
