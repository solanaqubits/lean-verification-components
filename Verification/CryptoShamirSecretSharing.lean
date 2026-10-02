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

/-- Alternate polynomial name; original record fields remain secret and slope. -/
abbrev PolyLinear := Shamir2Polynomial
abbrev Shamir2Polynomial.s (p : Shamir2Polynomial) : ℝ := p.secret
abbrev Shamir2Polynomial.a (p : Shamir2Polynomial) : ℝ := p.slope
abbrev lagrange0_1 := lagrangeWeight1

def lagrange0_2 (x1 x2 : ℝ) : ℝ := x1 / (x1 - x2)

theorem lagrange0_2_eq_weight2 (x1 x2 : ℝ) :
    lagrange0_2 x1 x2 = lagrangeWeight2 x1 x2 := by
  dsimp [lagrange0_2, lagrangeWeight2]
  rw [show x1 - x2 = -(x2 - x1) by ring, div_neg, neg_div]

theorem lagrange_basis_sum_one (x1 x2 : ℝ) (h_diff : x1 ≠ x2) :
    lagrange0_1 x1 x2 + lagrange0_2 x1 x2 = 1 := by
  rw [lagrange0_2_eq_weight2]
  exact lagrange_weights_sum_one x1 x2 h_diff

theorem shamir_2_of_n_reconstruction (p : PolyLinear) (x1 x2 : ℝ) (h_diff : x1 ≠ x2) :
    let y1 := evalPoly p x1
    let y2 := evalPoly p x2
    reconstructSecret x1 y1 x2 y2 = p.s :=
  shamir_reconstruction_correct p x1 x2 h_diff

/-- Compatibility with a candidate secret, not equality of probability distributions. -/
theorem shamir_single_share_hiding (s' x1 y1 : ℝ) (hx1_ne : x1 ≠ 0) :
    let a' := (y1 - s') / x1
    let p' : PolyLinear := ⟨s', a'⟩
    evalPoly p' x1 = y1 := shamir_single_share_perfect_secrecy x1 y1 s' hx1_ne

theorem shamir_homomorphic_add (p1 p2 : PolyLinear) (x : ℝ) :
    evalPoly p1 x + evalPoly p2 x = evalPoly ⟨p1.s + p2.s, p1.a + p2.a⟩ x := by
  dsimp [evalPoly, Shamir2Polynomial.s, Shamir2Polynomial.a]
  ring

structure CryptoShamirSecretSharingFormalSuite : Prop where
  h_basis_sum : ∀ (x1 x2 : ℝ), x1 ≠ x2 → lagrange0_1 x1 x2 + lagrange0_2 x1 x2 = 1
  h_reconstruct : ∀ (p : PolyLinear) (x1 x2 : ℝ), x1 ≠ x2 →
    reconstructSecret x1 (evalPoly p x1) x2 (evalPoly p x2) = p.s
  h_privacy : ∀ (s' x1 y1 : ℝ), x1 ≠ 0 → evalPoly ⟨s', (y1 - s') / x1⟩ x1 = y1
  h_homo_add : ∀ (p1 p2 : PolyLinear) (x : ℝ),
    evalPoly p1 x + evalPoly p2 x = evalPoly ⟨p1.s + p2.s, p1.a + p2.a⟩ x

theorem crypto_shamir_secret_sharing_master_verification_suite :
    CryptoShamirSecretSharingFormalSuite := {
  h_basis_sum := lagrange_basis_sum_one
  h_reconstruct := shamir_2_of_n_reconstruction
  h_privacy := shamir_single_share_hiding
  h_homo_add := shamir_homomorphic_add
}

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

  h_additive_suite : CryptoShamirSecretSharingFormalSuite

theorem crypto_shamir_master_verification_suite : CryptoShamirFormalSuite := {
  h_additive_suite := crypto_shamir_secret_sharing_master_verification_suite
  h_eval_zero := poly_eval_zero
  h_weight_sum := lagrange_weights_sum_one
  h_reconstruct := shamir_reconstruction_correct
  h_secrecy := shamir_single_share_perfect_secrecy
  h_unique_slope := shamir_single_share_unique_slope
}

end CryptoShamirSecretSharing
