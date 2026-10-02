/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# CryptoSumcheckProtocol

Algebraic and conditional invariants; see the theorem hypotheses and knowledge card for scope.
-/

noncomputable section
namespace CryptoSumcheckProtocol

/-! Honest two-variable Sumcheck identities over ℝ; no randomized verifier or soundness game. -/
structure Poly2ML where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

def evalML (p : Poly2ML) (x1 x2 : ℝ) : ℝ :=
  p.a + p.b * x1 + p.c * x2 + p.d * x1 * x2

def hypercubeSum (p : Poly2ML) : ℝ :=
  evalML p 0 0 + evalML p 0 1 + evalML p 1 0 + evalML p 1 1

def round1Poly (p : Poly2ML) (x1 : ℝ) : ℝ := evalML p x1 0 + evalML p x1 1

def round2Poly (p : Poly2ML) (r1 x2 : ℝ) : ℝ := evalML p r1 x2

theorem sumcheck_round1_sum (p : Poly2ML) :
    round1Poly p 0 + round1Poly p 1 = hypercubeSum p := by
  dsimp [round1Poly, hypercubeSum]
  ring

theorem sumcheck_round2_reduction (p : Poly2ML) (r1 : ℝ) :
    round2Poly p r1 0 + round2Poly p r1 1 = round1Poly p r1 := by
  rfl

theorem sumcheck_final_eval (p : Poly2ML) (r1 r2 : ℝ) :
    round2Poly p r1 r2 = evalML p r1 r2 := by
  rfl

theorem sumcheck_round1_is_affine (p : Poly2ML) (x1 : ℝ) :
    round1Poly p x1 = (2 * p.a + p.c) + (2 * p.b + p.d) * x1 := by
  dsimp [round1Poly, evalML]
  ring

structure CryptoSumcheckFormalSuite : Prop where
  h_round1_sum : ∀ (p : Poly2ML), round1Poly p 0 + round1Poly p 1 = hypercubeSum p
  h_round2_reduc : ∀ (p : Poly2ML) (r1 : ℝ),
    round2Poly p r1 0 + round2Poly p r1 1 = round1Poly p r1
  h_final_eval : ∀ (p : Poly2ML) (r1 r2 : ℝ), round2Poly p r1 r2 = evalML p r1 r2
  h_affine_deg : ∀ (p : Poly2ML) (x1 : ℝ),
    round1Poly p x1 = (2 * p.a + p.c) + (2 * p.b + p.d) * x1

theorem crypto_sumcheck_master_verification_suite : CryptoSumcheckFormalSuite := {
  h_round1_sum := sumcheck_round1_sum
  h_round2_reduc := sumcheck_round2_reduction
  h_final_eval := sumcheck_final_eval
  h_affine_deg := sumcheck_round1_is_affine
}

end CryptoSumcheckProtocol
