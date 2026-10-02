/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# CryptoR1CSConstraintSystem

Algebraic and conditional invariants; see the theorem hypotheses and knowledge card for scope.
-/

noncomputable section
namespace CryptoR1CSConstraintSystem

/-! Four-coordinate real constraint identities; no proof system or circuit compiler. -/
structure Witness4 where
  one : ℝ
  x : ℝ
  y : ℝ
  z : ℝ
  h_one : one = 1

structure LinComb4 where
  w_one : ℝ
  w_x : ℝ
  w_y : ℝ
  w_z : ℝ

def evalLinComb (lc : LinComb4) (s : Witness4) : ℝ :=
  lc.w_one * s.one + lc.w_x * s.x + lc.w_y * s.y + lc.w_z * s.z

structure R1CSConstraint where
  a : LinComb4
  b : LinComb4
  c : LinComb4

def isSatisfied (con : R1CSConstraint) (s : Witness4) : Prop :=
  evalLinComb con.a s * evalLinComb con.b s = evalLinComb con.c s

def mulConstraint : R1CSConstraint :=
  ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩⟩

theorem r1cs_mul_gate_soundness (s : Witness4) :
    isSatisfied mulConstraint s ↔ s.x * s.y = s.z := by
  simp [isSatisfied, mulConstraint, evalLinComb]

def booleanConstraint : R1CSConstraint :=
  ⟨⟨0, 1, 0, 0⟩, ⟨1, -1, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩

theorem r1cs_boolean_gate_soundness (s : Witness4) :
    isSatisfied booleanConstraint s ↔ (s.x = 0 ∨ s.x = 1) := by
  simp only [isSatisfied, booleanConstraint, evalLinComb, s.h_one,
    zero_mul, one_mul, zero_add, add_zero, neg_one_mul]
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right; linarith
  · rintro (h | h)
    · exact Or.inl h
    · right; linarith

def addConstraint : R1CSConstraint :=
  ⟨⟨0, 1, 1, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩⟩

theorem r1cs_add_gate_soundness (s : Witness4) :
    isSatisfied addConstraint s ↔ s.x + s.y = s.z := by
  simp [isSatisfied, addConstraint, evalLinComb, s.h_one]

def addLinComb (lc1 lc2 : LinComb4) : LinComb4 :=
  ⟨lc1.w_one + lc2.w_one, lc1.w_x + lc2.w_x, lc1.w_y + lc2.w_y, lc1.w_z + lc2.w_z⟩

theorem eval_lin_comb_add (lc1 lc2 : LinComb4) (s : Witness4) :
    evalLinComb (addLinComb lc1 lc2) s = evalLinComb lc1 s + evalLinComb lc2 s := by
  dsimp [evalLinComb, addLinComb]
  ring

def smulLinComb (k : ℝ) (lc : LinComb4) : LinComb4 :=
  ⟨k * lc.w_one, k * lc.w_x, k * lc.w_y, k * lc.w_z⟩

theorem eval_lin_comb_smul (k : ℝ) (lc : LinComb4) (s : Witness4) :
    evalLinComb (smulLinComb k lc) s = k * evalLinComb lc s := by
  dsimp [evalLinComb, smulLinComb]
  ring

structure CryptoR1CSFormalSuite : Prop where
  h_mul_gate : ∀ (s : Witness4), isSatisfied mulConstraint s ↔ s.x * s.y = s.z
  h_bool_gate : ∀ (s : Witness4), isSatisfied booleanConstraint s ↔ (s.x = 0 ∨ s.x = 1)
  h_add_gate : ∀ (s : Witness4), isSatisfied addConstraint s ↔ s.x + s.y = s.z
  h_eval_add : ∀ (lc1 lc2 : LinComb4) (s : Witness4),
    evalLinComb (addLinComb lc1 lc2) s = evalLinComb lc1 s + evalLinComb lc2 s
  h_eval_smul : ∀ (k : ℝ) (lc : LinComb4) (s : Witness4),
    evalLinComb (smulLinComb k lc) s = k * evalLinComb lc s

theorem crypto_r1cs_master_verification_suite : CryptoR1CSFormalSuite := {
  h_mul_gate := r1cs_mul_gate_soundness
  h_bool_gate := r1cs_boolean_gate_soundness
  h_add_gate := r1cs_add_gate_soundness
  h_eval_add := eval_lin_comb_add
  h_eval_smul := eval_lin_comb_smul
}

end CryptoR1CSConstraintSystem
