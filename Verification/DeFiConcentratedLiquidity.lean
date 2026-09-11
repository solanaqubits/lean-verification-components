import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false
noncomputable section

namespace DeFiConcentratedLiquidity

/-- Positive liquidity and a price strictly inside the prescribed range. -/
structure RangePosition where
  L : ℝ
  sqrtP : ℝ
  sqrtPl : ℝ
  sqrtPu : ℝ
  hL_pos : 0 < L
  hP_pos : 0 < sqrtP
  hPl_pos : 0 < sqrtPl
  hPu_pos : 0 < sqrtPu
  hPl_lt_P : sqrtPl < sqrtP
  hP_lt_Pu : sqrtP < sqrtPu

def virtualX (L sqrtP : ℝ) : ℝ := L / sqrtP
def virtualY (L sqrtP : ℝ) : ℝ := L * sqrtP

theorem virtual_reserves_product_eq_L_sq (L sqrtP : ℝ) (hP : sqrtP ≠ 0) :
    virtualX L sqrtP * virtualY L sqrtP = L ^ 2 := by
  dsimp [virtualX, virtualY]
  field_simp

def realX (pos : RangePosition) : ℝ := pos.L * (1 / pos.sqrtP - 1 / pos.sqrtPu)
def realY (pos : RangePosition) : ℝ := pos.L * (pos.sqrtP - pos.sqrtPl)

theorem realX_pos (pos : RangePosition) : 0 < realX pos := by
  exact mul_pos pos.hL_pos
    (sub_pos.mpr (one_div_lt_one_div_of_lt pos.hP_pos pos.hP_lt_Pu))

theorem realY_pos (pos : RangePosition) : 0 < realY pos :=
  mul_pos pos.hL_pos (sub_pos.mpr pos.hPl_lt_P)

theorem real_reserves_shifted_product_eq_L_sq (pos : RangePosition) :
    (realX pos + pos.L / pos.sqrtPu) * (realY pos + pos.L * pos.sqrtPl) = pos.L ^ 2 := by
  have hx : realX pos + pos.L / pos.sqrtPu = virtualX pos.L pos.sqrtP := by
    dsimp [realX, virtualX]
    ring
  have hy : realY pos + pos.L * pos.sqrtPl = virtualY pos.L pos.sqrtP := by
    dsimp [realY, virtualY]
    ring
  rw [hx, hy]
  exact virtual_reserves_product_eq_L_sq _ _ (ne_of_gt pos.hP_pos)

def deltaY (L sqrtP sqrtP_next : ℝ) : ℝ := L * (sqrtP_next - sqrtP)
def deltaX (L sqrtP sqrtP_next : ℝ) : ℝ := L * (1 / sqrtP_next - 1 / sqrtP)

theorem deltaY_pos_of_price_increase (L sqrtP sqrtP_next : ℝ)
    (hL : 0 < L) (h_inc : sqrtP < sqrtP_next) : 0 < deltaY L sqrtP sqrtP_next :=
  mul_pos hL (sub_pos.mpr h_inc)

theorem deltaX_pos_of_price_decrease (L sqrtP sqrtP_next : ℝ)
    (hL : 0 < L) (h_next_pos : 0 < sqrtP_next) (h_dec : sqrtP_next < sqrtP) :
    0 < deltaX L sqrtP sqrtP_next :=
  mul_pos hL (sub_pos.mpr (one_div_lt_one_div_of_lt h_next_pos h_dec))

structure DeFiConcentratedLiquidityFormalSuite : Prop where
  h_virt_prod : ∀ L sqrtP, sqrtP ≠ 0 → virtualX L sqrtP * virtualY L sqrtP = L ^ 2
  h_realX_pos : ∀ pos, 0 < realX pos
  h_realY_pos : ∀ pos, 0 < realY pos
  h_shifted_eq : ∀ pos,
    (realX pos + pos.L / pos.sqrtPu) * (realY pos + pos.L * pos.sqrtPl) = pos.L ^ 2
  h_deltaY_pos : ∀ L sqrtP sqrtP_next, 0 < L → sqrtP < sqrtP_next →
    0 < deltaY L sqrtP sqrtP_next
  h_deltaX_pos : ∀ L sqrtP sqrtP_next, 0 < L → 0 < sqrtP_next → sqrtP_next < sqrtP →
    0 < deltaX L sqrtP sqrtP_next

theorem defi_concentrated_liquidity_master_verification_suite :
    DeFiConcentratedLiquidityFormalSuite := {
  h_virt_prod := virtual_reserves_product_eq_L_sq
  h_realX_pos := realX_pos
  h_realY_pos := realY_pos
  h_shifted_eq := real_reserves_shifted_product_eq_L_sq
  h_deltaY_pos := deltaY_pos_of_price_increase
  h_deltaX_pos := deltaX_pos_of_price_decrease
}

#print axioms defi_concentrated_liquidity_master_verification_suite

end DeFiConcentratedLiquidity
