/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoShamirSecretSharing

/-!
# Scalar Feldman verification for a degree-at-most-one polynomial

Coefficient commitments and share verification are modeled by multiplication in
ℝ, not exponentiation in a finite cryptographic group. Nonzero scaling makes
verification equivalent to equality with the committed polynomial's evaluation.
This proves consistency with fixed commitments, not dealer honesty or secrecy.
Indeed the public constant commitment reveals the secret by division in this model.
-/

namespace CryptoFeldmanVSS

noncomputable section

structure FeldmanSetup where
  g : ℝ
  hg_ne : g ≠ 0

/-- Reuse the existing degree-at-most-one Shamir polynomial and its interpolation. -/
abbrev PolyLinear := CryptoShamirSecretSharing.Shamir2Polynomial

def share (p : PolyLinear) (x : ℝ) : ℝ :=
  CryptoShamirSecretSharing.share p x

structure CoefficientCommitments where
  a0 : ℝ
  a1 : ℝ

def commitments (setup : FeldmanSetup) (p : PolyLinear) : CoefficientCommitments :=
  ⟨p.secret * setup.g, p.slope * setup.g⟩

/-- Scalar consistency equation for supplied public commitments and a share. -/
def verifyShare (g a0 a1 x value : ℝ) : Prop :=
  value * g = a0 + x * a1

theorem feldman_vss_honest_completeness (setup : FeldmanSetup) (p : PolyLinear) (x : ℝ) :
    verifyShare setup.g (commitments setup p).a0 (commitments setup p).a1 x (share p x) := by
  dsimp [verifyShare, commitments, share, CryptoShamirSecretSharing.share,
    CryptoShamirSecretSharing.evalPoly]
  ring

/-- Nonzero scaling is injective: verification fixes the value at the supplied coordinate. -/
theorem feldman_vss_cheating_detection
    (setup : FeldmanSetup) (p : PolyLinear) (x value : ℝ) :
    verifyShare setup.g (commitments setup p).a0 (commitments setup p).a1 x value ↔
      value = share p x := by
  constructor
  · intro h
    have honest := feldman_vss_honest_completeness setup p x
    exact mul_right_cancel₀ setup.hg_ne (h.trans honest.symm)
  · intro h
    rw [h]
    exact feldman_vss_honest_completeness setup p x

theorem feldman_vss_rejects_inconsistent_share
    (setup : FeldmanSetup) (p : PolyLinear) (x value : ℝ) (h : value ≠ share p x) :
    ¬ verifyShare setup.g (commitments setup p).a0 (commitments setup p).a1 x value := by
  intro hv
  exact h ((feldman_vss_cheating_detection setup p x value).mp hv)

/-- Committing a Lagrange combination equals combining the scalar commitments. -/
theorem commitment_lagrange_linear (g x1 y1 x2 y2 : ℝ) :
    CryptoShamirSecretSharing.reconstructSecret x1 y1 x2 y2 * g =
      CryptoShamirSecretSharing.lagrangeWeight1 x1 x2 * (y1 * g) +
      CryptoShamirSecretSharing.lagrangeWeight2 x1 x2 * (y2 * g) := by
  dsimp [CryptoShamirSecretSharing.reconstructSecret]
  ring

/-- Two distinct coordinates reconstruct the public constant coefficient commitment. -/
theorem feldman_vss_reconstruction_homomorphism
    (setup : FeldmanSetup) (p : PolyLinear) (x1 x2 : ℝ) (h_diff : x1 ≠ x2) :
    CryptoShamirSecretSharing.lagrangeWeight1 x1 x2 * (share p x1 * setup.g) +
      CryptoShamirSecretSharing.lagrangeWeight2 x1 x2 * (share p x2 * setup.g) =
        (commitments setup p).a0 := by
  rw [← commitment_lagrange_linear]
  change CryptoShamirSecretSharing.reconstructSecret x1
    (CryptoShamirSecretSharing.share p x1) x2
    (CryptoShamirSecretSharing.share p x2) * setup.g = p.secret * setup.g
  rw [CryptoShamirSecretSharing.shamir_reconstruction_correct p x1 x2 h_diff]

/-- Accepted shares at distinct coordinates reconstruct the committed polynomial's secret. -/
theorem feldman_vss_verified_reconstruction
    (setup : FeldmanSetup) (p : PolyLinear) (x1 y1 x2 y2 : ℝ) (h_diff : x1 ≠ x2)
    (h1 : verifyShare setup.g (commitments setup p).a0 (commitments setup p).a1 x1 y1)
    (h2 : verifyShare setup.g (commitments setup p).a0 (commitments setup p).a1 x2 y2) :
    CryptoShamirSecretSharing.reconstructSecret x1 y1 x2 y2 = p.secret := by
  rw [(feldman_vss_cheating_detection setup p x1 y1).mp h1,
    (feldman_vss_cheating_detection setup p x2 y2).mp h2]
  exact CryptoShamirSecretSharing.shamir_reconstruction_correct p x1 x2 h_diff

/-- Explicit model boundary: real scalar commitments do not hide the secret. -/
theorem scalar_commitment_reveals_secret (setup : FeldmanSetup) (p : PolyLinear) :
    (commitments setup p).a0 / setup.g = p.secret := by
  exact mul_div_cancel_right₀ p.secret setup.hg_ne

structure FeldmanVSSFormalSuite : Prop where
  h_completeness : ∀ (setup : FeldmanSetup) (p : PolyLinear) (x : ℝ),
    verifyShare setup.g (commitments setup p).a0 (commitments setup p).a1 x (share p x)
  h_detection : ∀ (setup : FeldmanSetup) (p : PolyLinear) (x value : ℝ),
    verifyShare setup.g (commitments setup p).a0 (commitments setup p).a1 x value ↔
      value = share p x
  h_reconstruction : ∀ (setup : FeldmanSetup) (p : PolyLinear) (x1 x2 : ℝ), x1 ≠ x2 →
    CryptoShamirSecretSharing.lagrangeWeight1 x1 x2 * (share p x1 * setup.g) +
      CryptoShamirSecretSharing.lagrangeWeight2 x1 x2 * (share p x2 * setup.g) =
        (commitments setup p).a0
  h_verified_reconstruction : ∀ (setup : FeldmanSetup) (p : PolyLinear) (x1 y1 x2 y2 : ℝ),
    x1 ≠ x2 →
    verifyShare setup.g (commitments setup p).a0 (commitments setup p).a1 x1 y1 →
    verifyShare setup.g (commitments setup p).a0 (commitments setup p).a1 x2 y2 →
    CryptoShamirSecretSharing.reconstructSecret x1 y1 x2 y2 = p.secret

theorem crypto_feldman_vss_master_suite : FeldmanVSSFormalSuite := {
  h_completeness := feldman_vss_honest_completeness
  h_detection := feldman_vss_cheating_detection
  h_reconstruction := feldman_vss_reconstruction_homomorphism
  h_verified_reconstruction := feldman_vss_verified_reconstruction
}

end

end CryptoFeldmanVSS
