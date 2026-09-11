import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option linter.style.header false
noncomputable section

namespace CryptoKZGCommitment

def evalPoly2 (c0 c1 c2 x : ℝ) : ℝ := c0 + c1 * x + c2 * x ^ 2
def evalQuotient2 (c1 c2 z x : ℝ) : ℝ := (c1 + c2 * z) + c2 * x

theorem poly2_division_identity (c0 c1 c2 z x : ℝ) :
    evalPoly2 c0 c1 c2 x - evalPoly2 c0 c1 c2 z = (x - z) * evalQuotient2 c1 c2 z x := by
  dsimp [evalPoly2, evalQuotient2]
  ring

def evalPoly3 (c0 c1 c2 c3 x : ℝ) : ℝ := c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3
def evalQuotient3 (c1 c2 c3 z x : ℝ) : ℝ :=
  (c1 + c2 * z + c3 * z ^ 2) + (c2 + c3 * z) * x + c3 * x ^ 2

theorem poly3_division_identity (c0 c1 c2 c3 z x : ℝ) :
    evalPoly3 c0 c1 c2 c3 x - evalPoly3 c0 c1 c2 c3 z =
      (x - z) * evalQuotient3 c1 c2 c3 z x := by
  dsimp [evalPoly3, evalQuotient3]
  ring

def linearCombinationCommit (alpha beta c1 c2 : ℝ) : ℝ := alpha * c1 + beta * c2

theorem kzg_commitment_linearity (alpha beta c0 c1 c2 d0 d1 d2 s : ℝ) :
    evalPoly2 (alpha * c0 + beta * d0) (alpha * c1 + beta * d1) (alpha * c2 + beta * d2) s =
    linearCombinationCommit alpha beta (evalPoly2 c0 c1 c2 s) (evalPoly2 d0 d1 d2 s) := by
  dsimp [evalPoly2, linearCombinationCommit]
  ring

/-- Scalar bilinear model, without source groups or cryptographic assumptions. -/
def pairingMap (kappa a b : ℝ) : ℝ := a * b * kappa

theorem pairing_bilinear_left (kappa a1 a2 b : ℝ) :
    pairingMap kappa (a1 + a2) b = pairingMap kappa a1 b + pairingMap kappa a2 b := by
  dsimp [pairingMap]
  ring

theorem pairing_bilinear_right (kappa a b1 b2 : ℝ) :
    pairingMap kappa a (b1 + b2) = pairingMap kappa a b1 + pairingMap kappa a b2 := by
  dsimp [pairingMap]
  ring

theorem kzg_pairing_verification_correct (c0 c1 c2 c3 z s kappa : ℝ) :
    let C := evalPoly3 c0 c1 c2 c3 s
    let v := evalPoly3 c0 c1 c2 c3 z
    let pi := evalQuotient3 c1 c2 c3 z s
    pairingMap kappa (C - v) 1 = pairingMap kappa pi (s - z) := by
  dsimp [pairingMap]
  rw [poly3_division_identity]
  ring

/-- Cancellation determines a scalar quotient; it does not establish evaluation binding. -/
theorem kzg_quotient_soundness (C v pi s z kappa : ℝ)
    (h_kappa : kappa ≠ 0) (h_sz : s - z ≠ 0)
    (h_pair : pairingMap kappa (C - v) 1 = pairingMap kappa pi (s - z)) :
    pi = (C - v) / (s - z) := by
  have hp : (C - v) * kappa = (pi * (s - z)) * kappa := by
    simpa [pairingMap] using h_pair
  have hc : C - v = pi * (s - z) := mul_right_cancel₀ h_kappa hp
  exact (eq_div_iff h_sz).mpr hc.symm

structure CryptoKZGFormalSuite : Prop where
  h_poly2_div : ∀ c0 c1 c2 z x,
    evalPoly2 c0 c1 c2 x - evalPoly2 c0 c1 c2 z = (x - z) * evalQuotient2 c1 c2 z x
  h_poly3_div : ∀ c0 c1 c2 c3 z x,
    evalPoly3 c0 c1 c2 c3 x - evalPoly3 c0 c1 c2 c3 z =
      (x - z) * evalQuotient3 c1 c2 c3 z x
  h_linearity : ∀ alpha beta c0 c1 c2 d0 d1 d2 s,
    evalPoly2 (alpha * c0 + beta * d0) (alpha * c1 + beta * d1) (alpha * c2 + beta * d2) s =
    linearCombinationCommit alpha beta (evalPoly2 c0 c1 c2 s) (evalPoly2 d0 d1 d2 s)
  h_pair_left : ∀ kappa a1 a2 b,
    pairingMap kappa (a1 + a2) b = pairingMap kappa a1 b + pairingMap kappa a2 b
  h_pair_right : ∀ kappa a b1 b2,
    pairingMap kappa a (b1 + b2) = pairingMap kappa a b1 + pairingMap kappa a b2
  h_kzg_complete : ∀ c0 c1 c2 c3 z s kappa,
    let C := evalPoly3 c0 c1 c2 c3 s
    let v := evalPoly3 c0 c1 c2 c3 z
    let pi := evalQuotient3 c1 c2 c3 z s
    pairingMap kappa (C - v) 1 = pairingMap kappa pi (s - z)
  h_kzg_sound : ∀ C v pi s z kappa, kappa ≠ 0 → s - z ≠ 0 →
    pairingMap kappa (C - v) 1 = pairingMap kappa pi (s - z) → pi = (C - v) / (s - z)

theorem crypto_kzg_master_verification_suite : CryptoKZGFormalSuite := {
  h_poly2_div := poly2_division_identity
  h_poly3_div := poly3_division_identity
  h_linearity := kzg_commitment_linearity
  h_pair_left := pairing_bilinear_left
  h_pair_right := pairing_bilinear_right
  h_kzg_complete := kzg_pairing_verification_correct
  h_kzg_sound := kzg_quotient_soundness
}

#print axioms crypto_kzg_master_verification_suite

end CryptoKZGCommitment
