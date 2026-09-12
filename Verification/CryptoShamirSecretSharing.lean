import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false
noncomputable section

namespace CryptoShamirSecretSharing

/-- Degree-at-most-one polynomial; no distribution on the slope is assumed. -/
structure Shamir2Polynomial where
  secret : ℝ
  slope : ℝ

def evalPoly (p : Shamir2Polynomial) (x : ℝ) : ℝ :=
  p.secret + p.slope * x

/-- Evaluation at a supplied coordinate. Nonzero coordinates are required for privacy. -/
def share (p : Shamir2Polynomial) (x_i : ℝ) : ℝ := evalPoly p x_i

theorem poly_eval_zero (p : Shamir2Polynomial) : evalPoly p 0 = p.secret := by
  dsimp [evalPoly]
  ring

def lagrangeWeight1 (x1 x2 : ℝ) : ℝ := x2 / (x2 - x1)
def lagrangeWeight2 (x1 x2 : ℝ) : ℝ := -x1 / (x2 - x1)

theorem lagrange_weights_sum_one (x1 x2 : ℝ) (h_diff : x1 ≠ x2) :
    lagrangeWeight1 x1 x2 + lagrangeWeight2 x1 x2 = 1 := by
  dsimp [lagrangeWeight1, lagrangeWeight2]
  have h_sub : x2 - x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h_diff)
  calc
    x2 / (x2 - x1) + -x1 / (x2 - x1) = (x2 - x1) / (x2 - x1) := by ring
    _ = 1 := div_self h_sub

def reconstructSecret (x1 y1 x2 y2 : ℝ) : ℝ :=
  lagrangeWeight1 x1 x2 * y1 + lagrangeWeight2 x1 x2 * y2

theorem shamir_reconstruction_correct
    (p : Shamir2Polynomial) (x1 x2 : ℝ) (h_diff : x1 ≠ x2) :
    reconstructSecret x1 (share p x1) x2 (share p x2) = p.secret := by
  dsimp [reconstructSecret, share, evalPoly, lagrangeWeight1, lagrangeWeight2]
  field_simp [sub_ne_zero.mpr (Ne.symm h_diff)]
  ring

/-- Algebraic compatibility with every candidate secret, not probabilistic secrecy. -/
theorem shamir_single_share_perfect_secrecy
    (x1 y1 candidate_secret : ℝ) (hx1 : x1 ≠ 0) :
    let candidate_slope := (y1 - candidate_secret) / x1
    let p' : Shamir2Polynomial := ⟨candidate_secret, candidate_slope⟩
    share p' x1 = y1 := by
  dsimp [share, evalPoly]
  field_simp [hx1]
  ring

/-- For a fixed candidate secret and nonzero coordinate, the compatible slope is unique. -/
theorem shamir_single_share_unique_slope
    (x y candidate_secret : ℝ) (hx : x ≠ 0) :
    ∃! a : ℝ, share ⟨candidate_secret, a⟩ x = y := by
  refine ⟨(y - candidate_secret) / x,
    shamir_single_share_perfect_secrecy x y candidate_secret hx, ?_⟩
  intro a ha
  dsimp [share, evalPoly] at ha
  apply (eq_div_iff hx).mpr
  exact eq_sub_of_add_eq' ha

structure CryptoShamirFormalSuite : Prop where
  h_eval_zero : ∀ p : Shamir2Polynomial, evalPoly p 0 = p.secret
  h_weight_sum : ∀ x1 x2 : ℝ, x1 ≠ x2 →
    lagrangeWeight1 x1 x2 + lagrangeWeight2 x1 x2 = 1
  h_reconstruct : ∀ (p : Shamir2Polynomial) (x1 x2 : ℝ), x1 ≠ x2 →
    reconstructSecret x1 (share p x1) x2 (share p x2) = p.secret
  h_secrecy : ∀ x1 y1 candidate_secret : ℝ, x1 ≠ 0 →
    let candidate_slope := (y1 - candidate_secret) / x1
    let p' : Shamir2Polynomial := ⟨candidate_secret, candidate_slope⟩
    share p' x1 = y1
  h_unique_slope : ∀ x y candidate_secret : ℝ, x ≠ 0 →
    ∃! a : ℝ, share ⟨candidate_secret, a⟩ x = y

theorem crypto_shamir_master_verification_suite : CryptoShamirFormalSuite := {
  h_eval_zero := poly_eval_zero
  h_weight_sum := lagrange_weights_sum_one
  h_reconstruct := shamir_reconstruction_correct
  h_secrecy := shamir_single_share_perfect_secrecy
  h_unique_slope := shamir_single_share_unique_slope
}

end CryptoShamirSecretSharing
