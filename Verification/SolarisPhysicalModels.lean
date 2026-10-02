/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# SolarisPhysicalModels

Analytical identities and conditional bounds for idealized physical models.
-/

open Real MeasureTheory

noncomputable section

namespace SolarisOptics

/-- The mean of a nonconstant integer-frequency cosine over a full period is zero. -/
theorem integral_integer_cos_eq_zero (k : ℤ) (hk : k ≠ 0) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos ((k : ℝ) * θ)) = 0 := by
  have hk_real : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [intervalIntegral.integral_comp_mul_left _ hk_real, integral_cos]
  have hsin : Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 := by
    have harg : (k : ℝ) * (2 * Real.pi) = ((k * 2 : ℤ) : ℝ) * Real.pi := by
      push_cast
      ring
    rw [harg, Real.sin_int_mul_pi]
  simp [hsin]

/-- Orthogonality of real cosine functions requires different frequencies up to sign.
This integral alone does not model propagation or a waveguide transformation. -/
theorem oam_mode_orthogonality_preserved (m1 m2 : ℤ)
    (h_diff : m1 ≠ m2) (h_not_neg : m1 ≠ -m2) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.cos ((m1 : ℝ) * θ) * Real.cos ((m2 : ℝ) * θ)) = 0 := by
  have hsub : m1 - m2 ≠ 0 := sub_ne_zero.mpr h_diff
  have hadd : m1 + m2 ≠ 0 := by omega
  have hident : (fun θ : ℝ => Real.cos ((m1 : ℝ) * θ) * Real.cos ((m2 : ℝ) * θ)) =
      (fun θ : ℝ => (Real.cos (((m1 - m2 : ℤ) : ℝ) * θ) +
        Real.cos (((m1 + m2 : ℤ) : ℝ) * θ)) / 2) := by
    funext θ
    have h := Real.two_mul_cos_mul_cos ((m1 : ℝ) * θ) ((m2 : ℝ) * θ)
    push_cast
    rw [sub_mul, add_mul]
    linarith
  have hi (k : ℤ) : IntervalIntegrable (fun θ : ℝ => Real.cos ((k : ℝ) * θ))
      volume 0 (2 * Real.pi) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  rw [hident, intervalIntegral.integral_div,
    intervalIntegral.integral_add (hi (m1 - m2)) (hi (m1 + m2)),
    integral_integer_cos_eq_zero (m1 - m2) hsub, integral_integer_cos_eq_zero (m1 + m2) hadd]
  norm_num

/-- Distinct signed indices 1 and -1 are a counterexample to the original cosine claim. -/
theorem opposite_cosine_modes_counterexample :
    (1 : ℤ) ≠ -1 ∧
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.cos ((1 : ℤ) * θ) * Real.cos ((-1 : ℤ) * θ)) = Real.pi := by
  constructor
  · decide
  · simp only [Int.cast_one, Int.cast_neg, one_mul, neg_mul, Real.cos_neg]
    simp_rw [← pow_two]
    rw [integral_cos_sq]
    simp [Real.sin_two_pi]

end SolarisOptics

namespace SolarisOptics

/-- A supplied linear isometry preserves orthogonality.
The waveguide transformation is not derived from Maxwell's equations here. -/
theorem orthogonality_preserved_by_linear_isometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : E →ₗᵢ[ℂ] E) (u v : E) (h_orth : inner (𝕜 := ℂ) u v = 0) :
    inner (𝕜 := ℂ) (U u) (U v) = 0 := by
  rw [U.inner_map_map, h_orth]

/-- Conditional dimensionless phase-error budget. The bound 0.012 is an input calibration
hypothesis, not a consequence of the index/radius thresholds or a zero-noise theorem. -/
theorem adiabatic_oam_phase_stability
    (phase_error : ℝ → ℝ → ℝ)
    (h_calibration : ∀ n r : ℝ, 1 < n → 15e-6 ≤ r → |phase_error n r| ≤ 0.012)
    (n_eff curvature_radius : ℝ) (h_pos : 1 < n_eff)
    (h_curv : 15e-6 ≤ curvature_radius) :
    |phase_error n_eff curvature_radius| < 0.05 := by
  have h := h_calibration n_eff curvature_radius h_pos h_curv
  linarith

end SolarisOptics

namespace SolarisSpinPhotonics

/-- An assumed unitary transformation preserves squared norm exactly.
This does not construct a YIG coupling operator or incorporate damping. -/
theorem energy_preserved_by_unitary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : E ≃ₗᵢ[ℂ] E) (state : E) : ‖U state‖ ^ 2 = ‖state‖ ^ 2 := by
  rw [U.norm_map]

/-- Conditional loss budget: the actual loss is an input linked to alpha*g by h_model.
No identification with a physical energy or Gilbert damping law is derived here. -/
theorem magnon_photon_loss_bound
    (coupling_g damping_alpha energy_loss : ℝ)
    (h_g_pos : 0 < coupling_g) (h_alpha_small : damping_alpha < 1e-4)
    (h_nonneg : 0 ≤ energy_loss) (h_model : energy_loss ≤ damping_alpha * coupling_g) :
    0 ≤ energy_loss ∧ energy_loss < 1e-4 * coupling_g := by
  constructor
  · exact h_nonneg
  · exact lt_of_le_of_lt h_model (mul_lt_mul_of_pos_right h_alpha_small h_g_pos)

end SolarisSpinPhotonics

namespace SolarisPackaging

/-- Scalar thermal-mismatch stress proxy. Its adequacy as a constitutive law is not proved. -/
def thermalStressProxy (delta_alpha delta_temp joint_modulus : ℝ) : ℝ :=
  |delta_alpha * delta_temp * joint_modulus|

/-- Exact evaluation of the stated scalar proxy, in Pa when the inputs use consistent SI units. -/
theorem thermal_stress_proxy_value : thermalStressProxy 2.2e-6 223.0 20.0e9 = 9812000 := by
  norm_num [thermalStressProxy]

/-- Conditional safety of an actual stress explicitly equated to the scalar proxy.
This is not a derivation of von Mises stress or a verification of a physical joint. -/
theorem cryo_packaging_stress_safety
    (delta_alpha delta_temp joint_modulus yield_strength actual_stress : ℝ)
    (h_da : delta_alpha = 2.2e-6) (h_dt : delta_temp = 223.0)
    (h_G : joint_modulus = 20.0e9) (h_yield : yield_strength = 275.0e6)
    (h_model : actual_stress = thermalStressProxy delta_alpha delta_temp joint_modulus) :
    actual_stress = 9812000 ∧ 0 ≤ actual_stress ∧
      actual_stress < yield_strength ∧ actual_stress ≤ 50.0e6 := by
  subst delta_alpha
  subst delta_temp
  subst joint_modulus
  subst yield_strength
  rw [thermal_stress_proxy_value] at h_model
  rw [h_model]
  norm_num

end SolarisPackaging
