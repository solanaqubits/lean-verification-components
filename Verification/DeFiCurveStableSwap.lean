import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false
noncomputable section

namespace DeFiCurveStableSwap

/-- Positive reserves and invariant parameter, with nonnegative amplification.
This structure does not assume that the residual is zero. -/
structure StableSwap2Pool where
  A : ℝ
  D : ℝ
  x : ℝ
  y : ℝ
  hA_nonneg : 0 ≤ A
  hD_pos : 0 < D
  hx_pos : 0 < x
  hy_pos : 0 < y

/-- Static two-asset residual in the specified amplification convention. -/
def stableswapInvariant (A D x y : ℝ) : ℝ :=
  4 * A * (x + y) + D - (4 * A * D + D ^ 3 / (4 * x * y))

theorem stableswap_balanced_equilibrium (A D : ℝ) (_hD : D ≠ 0) :
    stableswapInvariant A D (D / 2) (D / 2) = 0 := by
  dsimp [stableswapInvariant]
  field_simp [_hD]
  ring

/-- The constant-product condition is sufficient at zero amplification. -/
theorem stableswap_zero_amplification_constant_product (D x y : ℝ)
    (_hx : x ≠ 0) (_hy : y ≠ 0) (h_prod : 4 * x * y = D ^ 2) (_hD : D ≠ 0) :
    stableswapInvariant 0 D x y = 0 := by
  dsimp [stableswapInvariant]
  rw [h_prod]
  field_simp [_hD]
  ring

/-- Both directions of the zero-amplification criterion, excluding zero D. -/
theorem stableswap_zero_amplification_iff (D x y : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hD : D ≠ 0) :
    stableswapInvariant 0 D x y = 0 ↔ 4 * x * y = D ^ 2 := by
  constructor
  · intro h
    have hden : 4 * x * y ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hx) hy
    have heq : D = D ^ 3 / (4 * x * y) := by
      simpa only [stableswapInvariant, mul_zero, zero_mul, zero_add, sub_eq_zero] using h
    have hm : D * (4 * x * y) = D * D ^ 2 := by
      calc D * (4 * x * y) = D ^ 3 := (eq_div_iff hden).mp heq
           _ = D * D ^ 2 := by ring
    exact mul_left_cancel₀ hD hm
  · intro h
    exact stableswap_zero_amplification_constant_product D x y hx hy h hD

/-- Simultaneous sum and product balance; no large-amplification limit is asserted. -/
theorem stableswap_simultaneous_sum_product (A D x y : ℝ)
    (h_sum : x + y = D) (h_prod : 4 * x * y = D ^ 2) (_hD : D ≠ 0) :
    stableswapInvariant A D x y = 0 := by
  dsimp [stableswapInvariant]
  rw [h_sum, h_prod]
  field_simp [_hD]
  ring

theorem stableswap_scale_homogeneity (A D x y lambda : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hlam : lambda ≠ 0) :
    stableswapInvariant A (lambda * D) (lambda * x) (lambda * y) =
      lambda * stableswapInvariant A D x y := by
  dsimp [stableswapInvariant]
  field_simp [hx, hy, hlam]

structure DeFiCurveStableSwapFormalSuite : Prop where
  h_balanced_eq : ∀ A D, D ≠ 0 → stableswapInvariant A D (D / 2) (D / 2) = 0
  h_zero_A_cp : ∀ D x y, x ≠ 0 → y ≠ 0 → 4 * x * y = D ^ 2 → D ≠ 0 →
    stableswapInvariant 0 D x y = 0
  h_zero_A_iff : ∀ D x y, x ≠ 0 → y ≠ 0 → D ≠ 0 →
    (stableswapInvariant 0 D x y = 0 ↔ 4 * x * y = D ^ 2)
  h_sum_prod_eq : ∀ A D x y, x + y = D → 4 * x * y = D ^ 2 → D ≠ 0 →
    stableswapInvariant A D x y = 0
  h_homogeneity : ∀ A D x y lambda, x ≠ 0 → y ≠ 0 → lambda ≠ 0 →
    stableswapInvariant A (lambda * D) (lambda * x) (lambda * y) =
      lambda * stableswapInvariant A D x y

theorem defi_curve_stableswap_master_verification_suite : DeFiCurveStableSwapFormalSuite := {
  h_balanced_eq := stableswap_balanced_equilibrium
  h_zero_A_cp := stableswap_zero_amplification_constant_product
  h_zero_A_iff := stableswap_zero_amplification_iff
  h_sum_prod_eq := stableswap_simultaneous_sum_product
  h_homogeneity := stableswap_scale_homogeneity
}

#print axioms defi_curve_stableswap_master_verification_suite

end DeFiCurveStableSwap
