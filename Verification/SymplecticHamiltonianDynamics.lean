import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option linter.style.header false
noncomputable section

namespace SymplecticHamiltonianDynamics

structure PhasePoint where
  q : ℝ
  p : ℝ

structure OscillatorParams where
  m : ℝ
  k : ℝ
  h : ℝ
  hm_pos : 0 < m
  hk_pos : 0 < k
  hh_pos : 0 < h

/-- Drift followed by kick, the specified symplectic Euler step. -/
def symplecticStep (params : OscillatorParams) (pt : PhasePoint) : PhasePoint :=
  let q_next := pt.q + (params.h / params.m) * pt.p
  ⟨q_next, pt.p - params.h * params.k * q_next⟩

/-- Prescribed entries of the linear update matrix. -/
def jacobian11 (_ : OscillatorParams) : ℝ := 1
def jacobian12 (params : OscillatorParams) : ℝ := params.h / params.m
def jacobian21 (params : OscillatorParams) : ℝ := -(params.h * params.k)
def jacobian22 (params : OscillatorParams) : ℝ := 1 - params.h ^ 2 * params.k / params.m

def jacobianDet (params : OscillatorParams) : ℝ :=
  jacobian11 params * jacobian22 params - jacobian12 params * jacobian21 params

theorem symplectic_jacobian_det_one (params : OscillatorParams) : jacobianDet params = 1 := by
  dsimp [jacobianDet, jacobian11, jacobian12, jacobian21, jacobian22]
  ring

theorem symplectic_form_preserved (params : OscillatorParams) :
    jacobian11 params * jacobian22 params - jacobian12 params * jacobian21 params = 1 :=
  symplectic_jacobian_det_one params

def shadowEnergy (params : OscillatorParams) (pt : PhasePoint) : ℝ :=
  (1 / 2 : ℝ) * params.k * pt.q ^ 2 +
  (1 / (2 * params.m)) * pt.p ^ 2 +
  (params.h * params.k / (2 * params.m)) * pt.q * pt.p

theorem shadow_energy_conserved (params : OscillatorParams) (pt : PhasePoint) :
    shadowEnergy params (symplecticStep params pt) = shadowEnergy params pt := by
  dsimp [shadowEnergy, symplecticStep]
  have hm : params.m ≠ 0 := ne_of_gt params.hm_pos
  field_simp
  ring

theorem shadow_energy_square_completion (params : OscillatorParams) (pt : PhasePoint) :
    2 * shadowEnergy params pt =
    params.k * (pt.q + params.h / (2 * params.m) * pt.p) ^ 2 +
    (1 / params.m) * (1 - params.h ^ 2 * params.k / (4 * params.m)) * pt.p ^ 2 := by
  dsimp [shadowEnergy]
  ring

theorem shadow_energy_nonneg (params : OscillatorParams) (pt : PhasePoint)
    (h_stab : params.h ^ 2 * params.k < 4 * params.m) : 0 ≤ shadowEnergy params pt := by
  have hc := shadow_energy_square_completion params pt
  have hd : 0 < 4 * params.m := by linarith [params.hm_pos]
  have hf := (div_lt_one hd).mpr h_stab
  have hp : 0 < 1 - params.h ^ 2 * params.k / (4 * params.m) := by linarith
  have h1 : 0 ≤ params.k * (pt.q + params.h / (2 * params.m) * pt.p) ^ 2 :=
    mul_nonneg params.hk_pos.le (sq_nonneg _)
  have h2 : 0 ≤ (1 / params.m) *
      (1 - params.h ^ 2 * params.k / (4 * params.m)) * pt.p ^ 2 :=
    mul_nonneg (mul_nonneg (one_div_pos.mpr params.hm_pos).le hp.le) (sq_nonneg _)
  linarith

structure SymplecticDynamicsFormalSuite : Prop where
  h_det_one : ∀ params, jacobianDet params = 1
  h_form_preserve : ∀ params,
    jacobian11 params * jacobian22 params - jacobian12 params * jacobian21 params = 1
  h_energy_conserv : ∀ params pt,
    shadowEnergy params (symplecticStep params pt) = shadowEnergy params pt
  h_energy_decomp : ∀ params pt, 2 * shadowEnergy params pt =
    params.k * (pt.q + params.h / (2 * params.m) * pt.p) ^ 2 +
    (1 / params.m) * (1 - params.h ^ 2 * params.k / (4 * params.m)) * pt.p ^ 2
  h_energy_nonneg : ∀ params pt,
    params.h ^ 2 * params.k < 4 * params.m → 0 ≤ shadowEnergy params pt

theorem symplectic_dynamics_master_verification_suite : SymplecticDynamicsFormalSuite := {
  h_det_one := symplectic_jacobian_det_one
  h_form_preserve := symplectic_form_preserved
  h_energy_conserv := shadow_energy_conserved
  h_energy_decomp := shadow_energy_square_completion
  h_energy_nonneg := shadow_energy_nonneg
}

#print axioms symplectic_dynamics_master_verification_suite

end SymplecticHamiltonianDynamics
