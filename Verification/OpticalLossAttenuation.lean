/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# OpticalLossAttenuation

Properties of a prescribed constant-coefficient exponential attenuation model.
-/

namespace SolarisOptics

open Real

/-- Constant scalar attenuation model. Consistent length units for alpha and z are assumed
by the physical interpretation; there is no material or waveguide geometry model. -/
structure AttenuatingWaveguide where
  i0 : ℝ
  alpha : ℝ

noncomputable def optical_intensity (w : AttenuatingWaveguide) (z : ℝ) : ℝ :=
  w.i0 * exp (-w.alpha * z)

theorem intensity_at_zero (w : AttenuatingWaveguide) : optical_intensity w 0 = w.i0 := by
  simp [optical_intensity]

/-- Cascade identity for segments sharing the same constant attenuation coefficient. -/
theorem intensity_cascade (w : AttenuatingWaveguide) (z1 z2 : ℝ) :
    optical_intensity w (z1 + z2) = optical_intensity w z1 * exp (-w.alpha * z2) := by
  simp [optical_intensity, mul_add, exp_add, mul_assoc]

theorem intensity_strictly_decreasing (w : AttenuatingWaveguide)
    (h_i0 : 0 < w.i0) (h_alpha : 0 < w.alpha) (z1 z2 : ℝ) (h_lt : z1 < z2) :
    optical_intensity w z2 < optical_intensity w z1 := by
  dsimp [optical_intensity]
  have h_arg : -w.alpha * z2 < -w.alpha * z1 := by nlinarith
  exact mul_lt_mul_of_pos_left (exp_lt_exp.mpr h_arg) h_i0

/-- Nonnegative intensity and no gain along a nonnegative distance for nonnegative loss. -/
theorem intensity_bounds (w : AttenuatingWaveguide) (z : ℝ)
    (h_i0 : 0 ≤ w.i0) (h_alpha : 0 ≤ w.alpha) (hz : 0 ≤ z) :
    0 ≤ optical_intensity w z ∧ optical_intensity w z ≤ w.i0 := by
  have h_exp : exp (-w.alpha * z) ≤ 1 := by
    apply exp_le_one_iff.mpr
    nlinarith
  constructor
  · exact mul_nonneg h_i0 (le_of_lt (exp_pos _))
  · simpa [optical_intensity] using mul_le_mul_of_nonneg_left h_exp h_i0

structure OpticalLossSuite : Prop where
  h_zero : ∀ w, optical_intensity w 0 = w.i0
  h_cascade : ∀ w z1 z2,
    optical_intensity w (z1 + z2) = optical_intensity w z1 * exp (-w.alpha * z2)
  h_decay : ∀ w, 0 < w.i0 → 0 < w.alpha → ∀ z1 z2, z1 < z2 →
    optical_intensity w z2 < optical_intensity w z1
  h_bounds : ∀ w z, 0 ≤ w.i0 → 0 ≤ w.alpha → 0 ≤ z →
    0 ≤ optical_intensity w z ∧ optical_intensity w z ≤ w.i0

theorem optical_loss_master_suite : OpticalLossSuite := {
  h_zero := intensity_at_zero
  h_cascade := intensity_cascade
  h_decay := intensity_strictly_decreasing
  h_bounds := intensity_bounds
}

end SolarisOptics
