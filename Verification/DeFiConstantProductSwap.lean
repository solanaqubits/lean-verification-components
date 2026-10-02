/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# DeFiConstantProductSwap

Algebraic and conditional invariants; see the theorem hypotheses and knowledge card for scope.
-/

noncomputable section
namespace DeFiConstantProductSwap

/-! Exact real-arithmetic swap identities, without integer rounding or execution semantics. -/
structure PoolState where
  x : ℝ
  y : ℝ
  gamma : ℝ
  hx_pos : 0 < x
  hy_pos : 0 < y
  hgamma_pos : 0 < gamma
  hgamma_le_one : gamma ≤ 1

def getAmountOut (p : PoolState) (dx : ℝ) : ℝ :=
  (p.y * p.gamma * dx) / (p.x + p.gamma * dx)
def remainingY (p : PoolState) (dx : ℝ) : ℝ := p.y - getAmountOut p dx

theorem swap_effective_invariant (p : PoolState) (dx : ℝ) (hdx_pos : 0 < dx) :
    (p.x + p.gamma * dx) * remainingY p dx = p.x * p.y := by
  have hd := ne_of_gt (add_pos p.hx_pos (mul_pos p.hgamma_pos hdx_pos))
  dsimp [remainingY, getAmountOut]
  field_simp [hd]
  ring

theorem remaining_y_formula (p : PoolState) (dx : ℝ) (hdx_pos : 0 < dx) :
    remainingY p dx = (p.x * p.y) / (p.x + p.gamma * dx) := by
  have hd := ne_of_gt (add_pos p.hx_pos (mul_pos p.hgamma_pos hdx_pos))
  apply (eq_div_iff hd).mpr
  simpa [mul_comm] using swap_effective_invariant p dx hdx_pos

theorem remaining_y_pos (p : PoolState) (dx : ℝ) (hdx_pos : 0 < dx) :
    0 < remainingY p dx := by
  rw [remaining_y_formula p dx hdx_pos]
  exact div_pos (mul_pos p.hx_pos p.hy_pos)
    (add_pos p.hx_pos (mul_pos p.hgamma_pos hdx_pos))

theorem amount_out_lt_reserve_y (p : PoolState) (dx : ℝ) (hdx_pos : 0 < dx) :
    getAmountOut p dx < p.y := by
  exact sub_pos.mp (remaining_y_pos p dx hdx_pos)

theorem real_invariant_strictly_grows (p : PoolState) (dx : ℝ)
    (hdx_pos : 0 < dx) (h_fee : p.gamma < 1) :
    p.x * p.y < (p.x + dx) * remainingY p dx := by
  have hdx : p.gamma * dx < dx := by
    simpa using mul_lt_mul_of_pos_right h_fee hdx_pos
  rw [← swap_effective_invariant p dx hdx_pos]
  have hsum : p.x + p.gamma * dx < p.x + dx := by linarith only [hdx]
  exact mul_lt_mul_of_pos_right hsum (remaining_y_pos p dx hdx_pos)

theorem get_amount_out_strict_mono (p : PoolState) (dx1 dx2 : ℝ)
    (hdx1_pos : 0 < dx1) (h_lt : dx1 < dx2) :
    getAmountOut p dx1 < getAmountOut p dx2 := by
  have hd1 := add_pos p.hx_pos (mul_pos p.hgamma_pos hdx1_pos)
  have hd2 := add_pos p.hx_pos (mul_pos p.hgamma_pos (lt_trans hdx1_pos h_lt))
  dsimp [getAmountOut]
  rw [div_lt_div_iff₀ hd1 hd2]
  have hterm := mul_lt_mul_of_pos_left h_lt (mul_pos (mul_pos p.hx_pos p.hy_pos) p.hgamma_pos)
  nlinarith only [hterm]

structure DeFiConstantProductSwapFormalSuite : Prop where
  h_invariant_eff : ∀ (p : PoolState) (dx : ℝ), 0 < dx →
    (p.x + p.gamma * dx) * remainingY p dx = p.x * p.y
  h_remaining_form : ∀ (p : PoolState) (dx : ℝ), 0 < dx →
    remainingY p dx = (p.x * p.y) / (p.x + p.gamma * dx)
  h_out_lt_reserve : ∀ (p : PoolState) (dx : ℝ), 0 < dx → getAmountOut p dx < p.y
  h_rem_pos : ∀ (p : PoolState) (dx : ℝ), 0 < dx → 0 < remainingY p dx
  h_k_grows : ∀ (p : PoolState) (dx : ℝ), 0 < dx → p.gamma < 1 →
    p.x * p.y < (p.x + dx) * remainingY p dx
  h_out_mono : ∀ (p : PoolState) (dx1 dx2 : ℝ), 0 < dx1 → dx1 < dx2 →
    getAmountOut p dx1 < getAmountOut p dx2

theorem defi_constant_product_swap_master_verification_suite :
    DeFiConstantProductSwapFormalSuite := {
  h_invariant_eff := swap_effective_invariant
  h_remaining_form := remaining_y_formula
  h_out_lt_reserve := amount_out_lt_reserve_y
  h_rem_pos := remaining_y_pos
  h_k_grows := real_invariant_strictly_grows
  h_out_mono := get_amount_out_strict_mono
}

end DeFiConstantProductSwap
