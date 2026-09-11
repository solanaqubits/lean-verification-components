import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

set_option linter.style.header false
noncomputable section

namespace QuantumDeutschJozsa

def IsConstant (f : Bool → Bool) : Prop := f false = f true
def IsBalanced (f : Bool → Bool) : Prop := f false ≠ f true

theorem boolean_func_classification (f : Bool → Bool) : IsConstant f ∨ IsBalanced f := by
  exact em (f false = f true)

theorem constant_not_balanced (f : Bool → Bool) : ¬ (IsConstant f ∧ IsBalanced f) := by
  rintro ⟨hc, hb⟩
  exact hb hc

def phaseSign (b : Bool) : ℝ := if b then -1 else 1

/-- Prescribed closed-form amplitude; no circuit or query counter is defined. -/
def amp0 (f : Bool → Bool) : ℝ := (phaseSign (f false) + phaseSign (f true)) / 2
def amp1 (f : Bool → Bool) : ℝ := (phaseSign (f false) - phaseSign (f true)) / 2

theorem total_probability_is_one (f : Bool → Bool) : (amp0 f) ^ 2 + (amp1 f) ^ 2 = 1 := by
  cases h0 : f false <;> cases h1 : f true <;> norm_num [amp0, amp1, phaseSign, h0, h1]

theorem constant_function_yields_zero (f : Bool → Bool) (h : IsConstant f) :
    (amp0 f) ^ 2 = 1 ∧ (amp1 f) ^ 2 = 0 := by
  cases h0 : f false <;> cases h1 : f true <;>
    simp_all [IsConstant, amp0, amp1, phaseSign]

theorem balanced_function_yields_one (f : Bool → Bool) (h : IsBalanced f) :
    (amp0 f) ^ 2 = 0 ∧ (amp1 f) ^ 2 = 1 := by
  cases h0 : f false <;> cases h1 : f true <;>
    simp_all [IsBalanced, amp0, amp1, phaseSign]
  norm_num

theorem constant_iff_amp0_sq_one (f : Bool → Bool) : IsConstant f ↔ (amp0 f) ^ 2 = 1 := by
  cases h0 : f false <;> cases h1 : f true <;>
    norm_num [IsConstant, amp0, phaseSign, h0, h1]

theorem balanced_iff_amp1_sq_one (f : Bool → Bool) : IsBalanced f ↔ (amp1 f) ^ 2 = 1 := by
  cases h0 : f false <;> cases h1 : f true <;>
    norm_num [IsBalanced, amp1, phaseSign, h0, h1]

structure QuantumDeutschJozsaFormalSuite : Prop where
  h_classify : ∀ f, IsConstant f ∨ IsBalanced f
  h_disjoint : ∀ f, ¬ (IsConstant f ∧ IsBalanced f)
  h_prob_norm : ∀ f, (amp0 f) ^ 2 + (amp1 f) ^ 2 = 1
  h_constant_res : ∀ f, IsConstant f → (amp0 f) ^ 2 = 1 ∧ (amp1 f) ^ 2 = 0
  h_balanced_res : ∀ f, IsBalanced f → (amp0 f) ^ 2 = 0 ∧ (amp1 f) ^ 2 = 1
  h_constant_iff : ∀ f, IsConstant f ↔ (amp0 f) ^ 2 = 1
  h_balanced_iff : ∀ f, IsBalanced f ↔ (amp1 f) ^ 2 = 1

theorem quantum_deutsch_jozsa_master_verification_suite : QuantumDeutschJozsaFormalSuite := {
  h_classify := boolean_func_classification
  h_disjoint := constant_not_balanced
  h_prob_norm := total_probability_is_one
  h_constant_res := constant_function_yields_zero
  h_balanced_res := balanced_function_yields_one
  h_constant_iff := constant_iff_amp0_sq_one
  h_balanced_iff := balanced_iff_amp1_sq_one
}

#print axioms quantum_deutsch_jozsa_master_verification_suite

end QuantumDeutschJozsa
