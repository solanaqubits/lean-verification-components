import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false

namespace QuantumNoCloningTheorem

/-- Roots of a supplied real overlap equation; no unitary or tensor model is assumed. -/
theorem cloning_overlap_quadratic (x : ℝ)
    (h_cloned_inner_product : x = x ^ 2) :
    x = 0 ∨ x = 1 := by
  have h_alg : x * (x - 1) = 0 := by
    nlinarith [h_cloned_inner_product]
  rcases mul_eq_zero.mp h_alg with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- The supplied equation is impossible for real scalars strictly between zero and one. -/
theorem no_cloning_for_non_orthogonal_distinct (x : ℝ)
    (hx_pos : 0 < x) (hx_lt_one : x < 1) :
    x ≠ x ^ 2 := by
  intro h_eq
  rcases cloning_overlap_quadratic x h_eq with h | h
  · linarith
  · linarith

/-- Zero satisfies the equation; this does not construct a cloning operator. -/
theorem orthogonal_states_admit_quadratic (x : ℝ) (h_ortho : x = 0) :
    x = x ^ 2 := by
  rw [h_ortho]
  ring

/-- One satisfies the equation; this does not construct a cloning operator. -/
theorem identical_states_admit_quadratic (x : ℝ) (h_ident : x = 1) :
    x = x ^ 2 := by
  rw [h_ident]
  ring

structure QuantumNoCloningFormalSuite : Prop where
  h_quad_roots : ∀ x : ℝ, x = x ^ 2 → x = 0 ∨ x = 1
  h_no_cloning : ∀ x : ℝ, 0 < x → x < 1 → x ≠ x ^ 2
  h_ortho_admit : ∀ x : ℝ, x = 0 → x = x ^ 2
  h_ident_admit : ∀ x : ℝ, x = 1 → x = x ^ 2

/-- Registry of the scalar quadratic consequences. -/
theorem quantum_no_cloning_master_verification_suite : QuantumNoCloningFormalSuite := {
  h_quad_roots := cloning_overlap_quadratic
  h_no_cloning := no_cloning_for_non_orthogonal_distinct
  h_ortho_admit := orthogonal_states_admit_quadratic
  h_ident_admit := identical_states_admit_quadratic
}

end QuantumNoCloningTheorem
