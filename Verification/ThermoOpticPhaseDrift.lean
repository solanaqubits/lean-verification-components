/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# ThermoOpticPhaseDrift

Properties of a prescribed linear thermo-optic phase model.
-/

namespace SolarisThermoOptics

/-- Parameters of a prescribed linear, constant-coefficient phase model.
No material calibration or thermal dynamics are inferred from these scalars. -/
structure PhaseShifterParams where
  k0 : ℝ
  dndT : ℝ
  length : ℝ

def phase_drift (p : PhaseShifterParams) (delta_T : ℝ) : ℝ :=
  p.k0 * p.dndT * p.length * delta_T

theorem phase_drift_add (p : PhaseShifterParams) (dT1 dT2 : ℝ) :
    phase_drift p (dT1 + dT2) = phase_drift p dT1 + phase_drift p dT2 := by
  dsimp [phase_drift]
  ring

/-- A scalar error bound, not a proof of statistical or optical coherence. -/
theorem phase_drift_bounded (p : PhaseShifterParams) (delta_T tol : ℝ)
    (h_tol : |delta_T| ≤ tol) :
    |phase_drift p delta_T| ≤ |p.k0 * p.dndT * p.length| * tol := by
  dsimp [phase_drift]
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left h_tol (abs_nonneg _)

theorem phase_drift_zero (p : PhaseShifterParams) : phase_drift p 0 = 0 := by
  simp [phase_drift]

/-- Any temperature change gives zero drift if the coefficient is zero. -/
theorem phase_drift_zero_coefficient (p : PhaseShifterParams) (delta_T : ℝ)
    (hc : p.k0 * p.dndT * p.length = 0) : phase_drift p delta_T = 0 := by
  simp [phase_drift, hc]

/-- Temperature tolerance sufficient for a specified phase-error budget. -/
theorem phase_drift_within_budget (p : PhaseShifterParams) (delta_T tol budget : ℝ)
    (h_tol : |delta_T| ≤ tol) (h_budget : |p.k0 * p.dndT * p.length| * tol ≤ budget) :
    |phase_drift p delta_T| ≤ budget :=
  le_trans (phase_drift_bounded p delta_T tol h_tol) h_budget

/-- With a nonzero phase coefficient, the phase budget is equivalent to a temperature bound.
For negative budgets both inequalities are impossible; physical budgets are nonnegative. -/
theorem phase_budget_iff_temperature_bound (p : PhaseShifterParams) (delta_T budget : ℝ)
    (hc : p.k0 * p.dndT * p.length ≠ 0) :
    |phase_drift p delta_T| ≤ budget ↔
      |delta_T| ≤ budget / |p.k0 * p.dndT * p.length| := by
  rw [le_div_iff₀ (abs_pos.mpr hc)]
  simp [phase_drift, abs_mul, mul_comm, mul_left_comm]

structure ThermoOpticSuite : Prop where
  h_linear : ∀ p dT1 dT2, phase_drift p (dT1 + dT2) = phase_drift p dT1 + phase_drift p dT2
  h_bound : ∀ p dT tol, |dT| ≤ tol → |phase_drift p dT| ≤ |p.k0 * p.dndT * p.length| * tol
  h_zero : ∀ p, phase_drift p 0 = 0
  h_zero_coefficient : ∀ p dT, p.k0 * p.dndT * p.length = 0 → phase_drift p dT = 0
  h_budget : ∀ p dT tol budget, |dT| ≤ tol → |p.k0 * p.dndT * p.length| * tol ≤ budget →
    |phase_drift p dT| ≤ budget
  h_threshold : ∀ p dT budget, p.k0 * p.dndT * p.length ≠ 0 →
    (|phase_drift p dT| ≤ budget ↔ |dT| ≤ budget / |p.k0 * p.dndT * p.length|)

theorem thermo_optic_master_suite : ThermoOpticSuite := {
  h_linear := phase_drift_add
  h_bound := phase_drift_bounded
  h_zero := phase_drift_zero
  h_zero_coefficient := phase_drift_zero_coefficient
  h_budget := phase_drift_within_budget
  h_threshold := phase_budget_iff_temperature_bound
}

end SolarisThermoOptics
