/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Scalar two-signer, two-nonce aggregation identities

This is the algebraic core suggested by MuSig2, not an implementation or security
proof of BIP 327. All keys and nonces are real scalars. Weights, the nonce
coefficient, and the challenge are supplied parameters, not modeled hashes.
The restricted rogue-key lemma excludes one naive subtraction when its weights
are distinct; it does not establish resistance against arbitrary chosen keys.
-/

namespace CryptoMuSig2Aggregation

noncomputable section

/-- Nonzero scalar generator; this does not model a finite cryptographic group. -/
structure MuSig2Setup where
  g : ℝ
  hg_ne : g ≠ 0

def publicKey (setup : MuSig2Setup) (x : ℝ) : ℝ := x * setup.g

def computeAggKey (mu1 mu2 pk1 pk2 : ℝ) : ℝ := mu1 * pk1 + mu2 * pk2

/-- Each signer contributes two public nonces; all signers use the same b. -/
def aggregateNonce (r11 r12 r21 r22 b : ℝ) : ℝ :=
  (r11 + r21) + b * (r12 + r22)

def partialSig (r1 r2 b c mu x : ℝ) : ℝ := r1 + b * r2 + c * mu * x

def aggSig (s1 s2 : ℝ) : ℝ := s1 + s2

/-- Verification of a supplied partial signature for supplied public values. -/
def verifyPartial (g pk r1 r2 b c mu s : ℝ) : Prop :=
  s * g = (r1 + b * r2) + c * mu * pk

def verifyAggregate (g pk nonce c s : ℝ) : Prop := s * g = nonce + c * pk

/-- Honest partial signatures satisfy their scalar verification equation. -/
theorem musig2_partial_sig_relation (g r1 r2 b c mu x : ℝ) :
    partialSig r1 r2 b c mu x * g =
      (r1 * g + b * (r2 * g)) + c * mu * (x * g) := by
  dsimp [partialSig]
  ring

/-- Assembly of any two accepted partial signatures with common b and c. -/
theorem musig2_linearity_homomorphism (g mu1 mu2 pk1 pk2 r11 r12 r21 r22 b c s1 s2 : ℝ)
    (h1 : verifyPartial g pk1 r11 r12 b c mu1 s1)
    (h2 : verifyPartial g pk2 r21 r22 b c mu2 s2) :
    verifyAggregate g (computeAggKey mu1 mu2 pk1 pk2)
      (aggregateNonce r11 r12 r21 r22 b) c (aggSig s1 s2) := by
  dsimp [verifyPartial] at h1 h2
  dsimp [verifyAggregate, computeAggKey, aggregateNonce, aggSig]
  calc
    (s1 + s2) * g = s1 * g + s2 * g := by ring
    _ = ((r11 + b * r12) + c * mu1 * pk1) +
        ((r21 + b * r22) + c * mu2 * pk2) := by rw [h1, h2]
    _ = (r11 + r21 + b * (r12 + r22)) + c * (mu1 * pk1 + mu2 * pk2) := by ring

/-- Perfect algebraic completeness for honestly generated two-signer contributions. -/
theorem musig2_aggregation_completeness (setup : MuSig2Setup)
    (mu1 mu2 x1 x2 r11 r12 r21 r22 b c : ℝ) :
    aggSig (partialSig r11 r12 b c mu1 x1) (partialSig r21 r22 b c mu2 x2) * setup.g =
      aggregateNonce (r11 * setup.g) (r12 * setup.g) (r21 * setup.g) (r22 * setup.g) b +
        c * computeAggKey mu1 mu2 (publicKey setup x1) (publicKey setup x2) := by
  exact musig2_linearity_homomorphism setup.g mu1 mu2 _ _ _ _ _ _ b c _ _
    (musig2_partial_sig_relation setup.g r11 r12 b c mu1 x1)
    (musig2_partial_sig_relation setup.g r21 r22 b c mu2 x2)

/-- Fixed weights distribute over addition of the two public-key components. -/
theorem weighted_key_add (mu1 mu2 pk1 pk2 qk1 qk2 : ℝ) :
    computeAggKey mu1 mu2 (pk1 + qk1) (pk2 + qk2) =
      computeAggKey mu1 mu2 pk1 pk2 + computeAggKey mu1 mu2 qk1 qk2 := by
  dsimp [computeAggKey]
  ring

/-- A partial response is linear in its secret inputs with session parameters fixed. -/
theorem partial_sig_add (r1 r2 q1 q2 b c mu x y : ℝ) :
    partialSig (r1 + q1) (r2 + q2) b c mu (x + y) =
      partialSig r1 r2 b c mu x + partialSig q1 q2 b c mu y := by
  dsimp [partialSig]
  ring

/-- Exact residual left by the particular naive subtraction pk2 - pk1. -/
theorem rogue_key_expansion (mu1 mu2 pk1 pk2 : ℝ) :
    computeAggKey mu1 mu2 pk1 (pk2 - pk1) = (mu1 - mu2) * pk1 + mu2 * pk2 := by
  dsimp [computeAggKey]
  ring

/-- A restricted algebraic barrier, not a reduction to hash-collision resistance. -/
theorem musig2_rogue_key_barrier (mu1 mu2 pk1 pk2 : ℝ)
    (hmu : mu1 ≠ mu2) (hpk : pk1 ≠ 0) :
    computeAggKey mu1 mu2 pk1 (pk2 - pk1) ≠ mu2 * pk2 := by
  rw [rogue_key_expansion]
  have hn : (mu1 - mu2) * pk1 ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hmu) hpk
  intro heq
  apply hn
  linarith

/-- Equal weights permit the naive cancellation: the distinctness premise matters. -/
theorem equal_weights_cancel (mu pk1 pk2 : ℝ) :
    computeAggKey mu mu pk1 (pk2 - pk1) = mu * pk2 := by
  rw [rogue_key_expansion]
  ring

/-- Arbitrary fixed scalar weights alone do not prevent a chosen target aggregate key.
Real MuSig2 coefficients depend on the key list; that dependence is not modeled here. -/
theorem fixed_weights_allow_target_key (mu1 mu2 pk1 target : ℝ) (hmu2 : mu2 ≠ 0) :
    computeAggKey mu1 mu2 pk1 ((target - mu1 * pk1) / mu2) = target := by
  dsimp [computeAggKey]
  rw [mul_comm mu2, div_mul_cancel₀ _ hmu2]
  ring

/-- Public scalar keys reveal their secret by division in this real-valued model. -/
theorem public_key_reveals_scalar (setup : MuSig2Setup) (x : ℝ) :
    publicKey setup x / setup.g = x := by
  exact mul_div_cancel_right₀ x setup.hg_ne

structure MuSig2AggregationFormalSuite : Prop where
  h_partial : ∀ g r1 r2 b c mu x : ℝ,
    partialSig r1 r2 b c mu x * g = (r1 * g + b * (r2 * g)) + c * mu * (x * g)
  h_complete : ∀ (setup : MuSig2Setup) (mu1 mu2 x1 x2 r11 r12 r21 r22 b c : ℝ),
    aggSig (partialSig r11 r12 b c mu1 x1) (partialSig r21 r22 b c mu2 x2) * setup.g =
      aggregateNonce (r11 * setup.g) (r12 * setup.g) (r21 * setup.g) (r22 * setup.g) b +
        c * computeAggKey mu1 mu2 (publicKey setup x1) (publicKey setup x2)
  h_assemble : ∀ g mu1 mu2 pk1 pk2 r11 r12 r21 r22 b c s1 s2 : ℝ,
    verifyPartial g pk1 r11 r12 b c mu1 s1 →
    verifyPartial g pk2 r21 r22 b c mu2 s2 →
    verifyAggregate g (computeAggKey mu1 mu2 pk1 pk2)
      (aggregateNonce r11 r12 r21 r22 b) c (aggSig s1 s2)
  h_barrier : ∀ mu1 mu2 pk1 pk2 : ℝ, mu1 ≠ mu2 → pk1 ≠ 0 →
    computeAggKey mu1 mu2 pk1 (pk2 - pk1) ≠ mu2 * pk2
  h_expansion : ∀ mu1 mu2 pk1 pk2 : ℝ,
    computeAggKey mu1 mu2 pk1 (pk2 - pk1) = (mu1 - mu2) * pk1 + mu2 * pk2
  h_key_add : ∀ mu1 mu2 pk1 pk2 qk1 qk2 : ℝ,
    computeAggKey mu1 mu2 (pk1 + qk1) (pk2 + qk2) =
      computeAggKey mu1 mu2 pk1 pk2 + computeAggKey mu1 mu2 qk1 qk2
  h_partial_add : ∀ r1 r2 q1 q2 b c mu x y : ℝ,
    partialSig (r1 + q1) (r2 + q2) b c mu (x + y) =
      partialSig r1 r2 b c mu x + partialSig q1 q2 b c mu y
  h_target_key : ∀ mu1 mu2 pk1 target : ℝ, mu2 ≠ 0 →
    computeAggKey mu1 mu2 pk1 ((target - mu1 * pk1) / mu2) = target
  h_scalar_recovery : ∀ (setup : MuSig2Setup) (x : ℝ), publicKey setup x / setup.g = x

theorem crypto_musig2_aggregation_master_suite : MuSig2AggregationFormalSuite := {
  h_partial := musig2_partial_sig_relation
  h_complete := musig2_aggregation_completeness
  h_assemble := musig2_linearity_homomorphism
  h_barrier := musig2_rogue_key_barrier
  h_expansion := rogue_key_expansion
  h_key_add := weighted_key_add
  h_partial_add := partial_sig_add
  h_target_key := fixed_weights_allow_target_key
  h_scalar_recovery := public_key_reveals_scalar
}

end

end CryptoMuSig2Aggregation
