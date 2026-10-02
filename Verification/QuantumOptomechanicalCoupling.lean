/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Prescribed scalar optomechanical coupling

Energies are expressed in units of ħ; x denotes displacement divided by x_zpf.
The force below is conjugate to this normalized coordinate, not an SI force.
There are no creation/annihilation operators or equations for quantum noise.
The positive rate 4g²/κ is prescribed; deriving it from detuned cavity dynamics
or proving its approximation regime is outside the model. Its usual red-sideband
interpretation requires resolved sidebands and weak coupling, not κ ≫ ω_m.
-/

namespace QuantumOptomechanicalCoupling

noncomputable section

structure OptomechanicalParams where
  omega_c : ℝ
  omega_m : ℝ
  g0 : ℝ
  gamma_m : ℝ
  kappa : ℝ
  h_omega_c : 0 < omega_c
  h_omega_m : 0 < omega_m
  h_g0 : 0 < g0
  h_gamma_m : 0 < gamma_m
  h_kappa : 0 < kappa

/-- Scalar free-mode energy in ħ units, with zero-point offsets omitted. -/
def free_energy (p : OptomechanicalParams) (n_c n_m : ℝ) : ℝ :=
  p.omega_c * n_c + p.omega_m * n_m

def interaction_energy (p : OptomechanicalParams) (n_c x : ℝ) : ℝ :=
  -p.g0 * n_c * x

/-- Generalized force in the normalized coordinate; multiply by ħ/x_zpf for SI force. -/
def radiation_force (p : OptomechanicalParams) (n_c : ℝ) : ℝ :=
  p.g0 * n_c

/-- Affine frequency model, not a globally positive frequency for arbitrary displacement. -/
def cavity_frequency_shift (p : OptomechanicalParams) (x : ℝ) : ℝ :=
  p.omega_c - p.g0 * x

theorem free_energy_nonneg (p : OptomechanicalParams) (n_c n_m : ℝ)
    (hc : 0 ≤ n_c) (hm : 0 ≤ n_m) : 0 ≤ free_energy p n_c n_m :=
  add_nonneg (mul_nonneg (le_of_lt p.h_omega_c) hc)
    (mul_nonneg (le_of_lt p.h_omega_m) hm)

theorem optomechanical_force_nonneg (p : OptomechanicalParams) (n_c : ℝ) (hn : 0 ≤ n_c) :
    0 ≤ radiation_force p n_c :=
  mul_nonneg (le_of_lt p.h_g0) hn

theorem optomechanical_force_pos (p : OptomechanicalParams) (n_c : ℝ) (hn : 0 < n_c) :
    0 < radiation_force p n_c := mul_pos p.h_g0 hn

theorem radiation_force_strict_pos (p : OptomechanicalParams) (n_c : ℝ) (hn : 0 < n_c) :
    0 < radiation_force p n_c := optomechanical_force_pos p n_c hn

theorem radiation_force_strict_mono (p : OptomechanicalParams) (n1 n2 : ℝ)
    (hn : n1 < n2) : radiation_force p n1 < radiation_force p n2 :=
  mul_lt_mul_of_pos_left hn p.h_g0

theorem interaction_energy_hasDerivAt (p : OptomechanicalParams) (n_c x : ℝ) :
    HasDerivAt (interaction_energy p n_c) (-radiation_force p n_c) x := by
  change HasDerivAt (fun y : ℝ => -p.g0 * n_c * y) (-(p.g0 * n_c)) x
  simpa using
    (hasDerivAt_id x).const_mul (-p.g0 * n_c)

theorem radiation_force_eq_neg_deriv (p : OptomechanicalParams) (n_c x : ℝ) :
    radiation_force p n_c = -deriv (interaction_energy p n_c) x := by
  rw [(interaction_energy_hasDerivAt p n_c x).deriv, neg_neg]

/-- Frequency differences, rather than the offset frequency itself, are linear. -/
theorem frequency_shift_difference (p : OptomechanicalParams) (x1 x2 : ℝ) :
    cavity_frequency_shift p x2 - cavity_frequency_shift p x1 = -p.g0 * (x2 - x1) := by
  dsimp [cavity_frequency_shift]
  ring

/-- The frequency offset from omega_c is additive in normalized displacement. -/
theorem frequency_shift_linear (p : OptomechanicalParams) (x1 x2 : ℝ) :
    cavity_frequency_shift p (x1 + x2) - p.omega_c =
      (cavity_frequency_shift p x1 - p.omega_c) +
      (cavity_frequency_shift p x2 - p.omega_c) := by
  dsimp [cavity_frequency_shift]
  ring

theorem frequency_shift_strictly_decreasing (p : OptomechanicalParams) (x1 x2 : ℝ)
    (hx : x1 < x2) : cavity_frequency_shift p x2 < cavity_frequency_shift p x1 := by
  exact sub_lt_sub_left (mul_lt_mul_of_pos_left hx p.h_g0) p.omega_c

theorem total_energy_dispersion (p : OptomechanicalParams) (n_c n_m x : ℝ) :
    free_energy p n_c n_m + interaction_energy p n_c x =
      cavity_frequency_shift p x * n_c + p.omega_m * n_m := by
  dsimp [free_energy, interaction_energy, cavity_frequency_shift]
  ring

/-- Prescribed positive-branch rate; g is the enhanced coupling, independent of g0 here. -/
def optical_damping (p : OptomechanicalParams) (g : ℝ) : ℝ :=
  4 * g ^ 2 / p.kappa

def effective_damping (p : OptomechanicalParams) (gamma_opt : ℝ) : ℝ :=
  p.gamma_m + gamma_opt

theorem optical_damping_nonneg (p : OptomechanicalParams) (g : ℝ) :
    0 ≤ optical_damping p g :=
  div_nonneg (mul_nonneg (by norm_num) (sq_nonneg g)) (le_of_lt p.h_kappa)

theorem optical_damping_pos (p : OptomechanicalParams) (g : ℝ) (hg : g ≠ 0) :
    0 < optical_damping p g :=
  div_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hg)) p.h_kappa

/-- Positive added damping increases the rate; this does not assert thermal cooling. -/
theorem dynamical_backaction_cooling (p : OptomechanicalParams) (gamma_opt : ℝ)
    (h : 0 < gamma_opt) : p.gamma_m < effective_damping p gamma_opt :=
  lt_add_of_pos_right _ h

/-- Strict enhancement requires nonzero enhanced coupling. No temperature is modeled. -/
theorem dynamical_backaction_damping (p : OptomechanicalParams) (g : ℝ) (hg : g ≠ 0) :
    p.gamma_m < effective_damping p (optical_damping p g) :=
  dynamical_backaction_cooling p _ (optical_damping_pos p g hg)

theorem zero_coupling_damping (p : OptomechanicalParams) :
    effective_damping p (optical_damping p 0) = p.gamma_m := by
  simp [effective_damping, optical_damping]

theorem red_branch_stable (p : OptomechanicalParams) (g : ℝ) :
    0 < effective_damping p (optical_damping p g) :=
  add_pos_of_pos_of_nonneg p.h_gamma_m (optical_damping_nonneg p g)

/-- Exact algebraic positivity criterion; not full coupled-system stability. -/
theorem stability_criterion_iff (p : OptomechanicalParams) (gamma_opt : ℝ) :
    0 < effective_damping p gamma_opt ↔ -p.gamma_m < gamma_opt := by
  dsimp [effective_damping]
  constructor <;> intro h <;> linarith

theorem stability_criterion (p : OptomechanicalParams) (gamma_opt : ℝ)
    (h : -p.gamma_m < gamma_opt) : 0 < effective_damping p gamma_opt :=
  (stability_criterion_iff p gamma_opt).mpr h

/-- Threshold for a prescribed negative-branch rate, with no detuning dynamics assumed. -/
theorem blue_branch_stability_iff (p : OptomechanicalParams) (g : ℝ) :
    0 < effective_damping p (-optical_damping p g) ↔ 4 * g ^ 2 < p.gamma_m * p.kappa := by
  have h : 0 < effective_damping p (-optical_damping p g) ↔
      optical_damping p g < p.gamma_m := by
    dsimp [effective_damping]
    constructor <;> intro h <;> linarith
  rw [h]
  exact div_lt_iff₀ p.h_kappa

/-- A stipulated scalar relaxation envelope; not the full mechanical displacement equation. -/
def relaxation_envelope (p : OptomechanicalParams) (gamma_opt initial t : ℝ) : ℝ :=
  initial * Real.exp (-effective_damping p gamma_opt * t)

theorem stable_envelope_decreases (p : OptomechanicalParams) (gamma_opt initial t1 t2 : ℝ)
    (h_stable : -p.gamma_m < gamma_opt) (h_initial : 0 < initial) (h_time : t1 < t2) :
    relaxation_envelope p gamma_opt initial t2 < relaxation_envelope p gamma_opt initial t1 := by
  have h_rate := stability_criterion p gamma_opt h_stable
  have h_arg : -effective_damping p gamma_opt * t2 < -effective_damping p gamma_opt * t1 := by
    nlinarith
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr h_arg) h_initial

/-- At zero total rate the stipulated envelope is constant, not exponentially growing. -/
theorem threshold_envelope_constant (p : OptomechanicalParams) (initial t : ℝ) :
    relaxation_envelope p (-p.gamma_m) initial t = initial := by
  simp [relaxation_envelope, effective_damping]

structure OptomechanicalCouplingFormalSuite : Prop where
  h_force_nonneg : ∀ p n, 0 ≤ n → 0 ≤ radiation_force p n
  h_force_pos : ∀ p n, 0 < n → 0 < radiation_force p n
  h_force_mono : ∀ p n1 n2, n1 < n2 → radiation_force p n1 < radiation_force p n2
  h_force_derivative : ∀ p n x, radiation_force p n = -deriv (interaction_energy p n) x
  h_frequency : ∀ p x1 x2,
    cavity_frequency_shift p x2 - cavity_frequency_shift p x1 = -p.g0 * (x2 - x1)
  h_frequency_additive : ∀ p x1 x2,
    cavity_frequency_shift p (x1 + x2) - p.omega_c =
      (cavity_frequency_shift p x1 - p.omega_c) +
      (cavity_frequency_shift p x2 - p.omega_c)
  h_positive_damping : ∀ p gamma_opt,
    0 < gamma_opt → p.gamma_m < effective_damping p gamma_opt
  h_energy : ∀ p n_c n_m x, free_energy p n_c n_m + interaction_energy p n_c x =
    cavity_frequency_shift p x * n_c + p.omega_m * n_m
  h_damping : ∀ p g, g ≠ 0 → p.gamma_m < effective_damping p (optical_damping p g)
  h_stability : ∀ p gamma_opt, 0 < effective_damping p gamma_opt ↔ -p.gamma_m < gamma_opt
  h_blue_threshold : ∀ p g,
    0 < effective_damping p (-optical_damping p g) ↔ 4 * g ^ 2 < p.gamma_m * p.kappa
  h_envelope : ∀ p gamma_opt initial t1 t2,
    -p.gamma_m < gamma_opt → 0 < initial → t1 < t2 →
    relaxation_envelope p gamma_opt initial t2 < relaxation_envelope p gamma_opt initial t1

theorem quantum_optomechanical_coupling_master_suite : OptomechanicalCouplingFormalSuite := {
  h_force_nonneg := optomechanical_force_nonneg
  h_force_pos := optomechanical_force_pos
  h_force_mono := radiation_force_strict_mono
  h_force_derivative := radiation_force_eq_neg_deriv
  h_frequency := frequency_shift_difference
  h_frequency_additive := frequency_shift_linear
  h_positive_damping := dynamical_backaction_cooling
  h_energy := total_energy_dispersion
  h_damping := dynamical_backaction_damping
  h_stability := stability_criterion_iff
  h_blue_threshold := blue_branch_stability_iff
  h_envelope := stable_envelope_decreases
}

end

end QuantumOptomechanicalCoupling
