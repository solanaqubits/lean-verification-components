/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# CryptoGroth16SNARK

Algebraic and conditional invariants; see the theorem hypotheses and knowledge card for scope.
-/

noncomputable section
namespace CryptoGroth16SNARK

/-! Scalar verification-equation identities, without a witness relation or ZK game. -/
structure Groth16Setup where
  alpha : ℝ
  beta : ℝ
  gamma : ℝ
  delta : ℝ
  h_gamma_ne : gamma ≠ 0
  h_delta_ne : delta ≠ 0

def pairing (P Q : ℝ) : ℝ := P * Q

structure Proof where
  a : ℝ
  b : ℝ
  c : ℝ

def verifyGroth16 (setup : Groth16Setup) (xPub : ℝ) (π : Proof) : Prop :=
  pairing π.a π.b = pairing setup.alpha setup.beta +
    pairing xPub setup.gamma + pairing π.c setup.delta

def computeProverC (setup : Groth16Setup) (xPub a b : ℝ) : ℝ :=
  (a * b - setup.alpha * setup.beta - xPub * setup.gamma) / setup.delta

/-- Solving for C yields an accepted triple for every real input. -/
theorem groth16_honest_completeness (setup : Groth16Setup) (xPub a b : ℝ) :
    let proof : Proof := ⟨a, b, computeProverC setup xPub a b⟩
    verifyGroth16 setup xPub proof := by
  dsimp [verifyGroth16, pairing, computeProverC]
  rw [div_mul_cancel₀ _ setup.h_delta_ne]
  ring

/-- Deterministic construction; no random sampling or distributional simulation. -/
def simulateProof (setup : Groth16Setup) (xPub a b : ℝ) : Proof :=
  ⟨a, b, (a * b - setup.alpha * setup.beta - xPub * setup.gamma) / setup.delta⟩

/-- Acceptance only, not a proof of zero knowledge. -/
theorem groth16_zk_simulation (setup : Groth16Setup) (xPub a b : ℝ) :
    verifyGroth16 setup xPub (simulateProof setup xPub a b) :=
  groth16_honest_completeness setup xPub a b

/-- Difference identity for accepted triples sharing A and B, not proof aggregation. -/
theorem groth16_public_input_linearity (setup : Groth16Setup) (x1 x2 a b c1 c2 : ℝ)
    (h1 : verifyGroth16 setup x1 ⟨a, b, c1⟩)
    (h2 : verifyGroth16 setup x2 ⟨a, b, c2⟩) :
    c1 - c2 = ((x2 - x1) * setup.gamma) / setup.delta := by
  apply (eq_div_iff setup.h_delta_ne).mpr
  dsimp [verifyGroth16, pairing] at h1 h2
  nlinarith only [h1, h2]

structure CryptoGroth16FormalSuite : Prop where
  h_completeness : ∀ (setup : Groth16Setup) (xPub a b : ℝ),
    verifyGroth16 setup xPub ⟨a, b, computeProverC setup xPub a b⟩
  h_zk_sim : ∀ (setup : Groth16Setup) (xPub a b : ℝ),
    verifyGroth16 setup xPub (simulateProof setup xPub a b)
  h_linearity : ∀ (setup : Groth16Setup) (x1 x2 a b c1 c2 : ℝ),
    verifyGroth16 setup x1 ⟨a, b, c1⟩ → verifyGroth16 setup x2 ⟨a, b, c2⟩ →
    c1 - c2 = ((x2 - x1) * setup.gamma) / setup.delta

theorem crypto_groth16_master_verification_suite : CryptoGroth16FormalSuite := {
  h_completeness := groth16_honest_completeness
  h_zk_sim := groth16_zk_simulation
  h_linearity := groth16_public_input_linearity
}

end CryptoGroth16SNARK
