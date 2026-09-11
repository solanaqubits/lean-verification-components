import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false

noncomputable section

namespace DeFiAMMInvariants

/-- Exact real-valued output; gamma is the fraction of input used for pricing. -/
def swapOutputY (rx ry gamma dx : ℝ) : ℝ :=
  ry * (gamma * dx) / (rx + gamma * dx)

def newRx (rx dx : ℝ) : ℝ := rx + dx
def newRy (rx ry gamma dx : ℝ) : ℝ := ry - swapOutputY rx ry gamma dx
def newK (rx ry gamma dx : ℝ) : ℝ := newRx rx dx * newRy rx ry gamma dx

theorem output_pos (rx ry gamma dx : ℝ)
    (hrx : 0 < rx) (hry : 0 < ry) (hg : 0 < gamma) (hdx : 0 < dx) :
    0 < swapOutputY rx ry gamma dx := by
  unfold swapOutputY
  positivity

theorem output_lt_reserve (rx ry gamma dx : ℝ)
    (hrx : 0 < rx) (hry : 0 < ry) (hg : 0 < gamma) (hdx : 0 < dx) :
    swapOutputY rx ry gamma dx < ry := by
  unfold swapOutputY
  have hd : 0 < rx + gamma * dx := by positivity
  apply (div_lt_iff₀ hd).mpr
  nlinarith [mul_pos hrx hry]

theorem newRy_pos (rx ry gamma dx : ℝ)
    (hrx : 0 < rx) (hry : 0 < ry) (hg : 0 < gamma) (hdx : 0 < dx) :
    0 < newRy rx ry gamma dx :=
  sub_pos.mpr (output_lt_reserve rx ry gamma dx hrx hry hg hdx)

theorem newRy_eq (rx ry gamma dx : ℝ) (hd : rx + gamma * dx ≠ 0) :
    newRy rx ry gamma dx = rx * ry / (rx + gamma * dx) := by
  unfold newRy swapOutputY
  field_simp
  ring

theorem constant_product_zero_fee (rx ry dx : ℝ) (hrx : 0 < rx) (hdx : 0 < dx) :
    newK rx ry 1 dx = rx * ry := by
  unfold newK newRx
  rw [newRy_eq rx ry 1 dx (by positivity)]
  simp only [one_mul]
  field_simp

/-- Retaining the fee in the input reserve makes the reserve product nondecreasing. -/
theorem invariant_monotone_with_fee (rx ry gamma dx : ℝ)
    (hrx : 0 < rx) (hry : 0 < ry) (hg_pos : 0 < gamma) (hg_le : gamma ≤ 1) (hdx : 0 < dx) :
    rx * ry ≤ newK rx ry gamma dx := by
  have hd : 0 < rx + gamma * dx := by positivity
  unfold newK newRx
  rw [newRy_eq rx ry gamma dx (ne_of_gt hd), ← mul_div_assoc]
  apply (le_div_iff₀ hd).mpr
  have hh : gamma * dx ≤ dx := by nlinarith
  have hk : 0 < rx * ry := mul_pos hrx hry
  nlinarith [mul_le_mul_of_nonneg_left hh (le_of_lt hk)]

theorem price_slippage (rx ry gamma dx : ℝ)
    (hrx : 0 < rx) (hry : 0 < ry) (hg_pos : 0 < gamma) (hg_le : gamma ≤ 1) (hdx : 0 < dx) :
    swapOutputY rx ry gamma dx / dx < ry / rx := by
  have hd : 0 < rx + gamma * dx := by positivity
  have he : swapOutputY rx ry gamma dx / dx = ry * gamma / (rx + gamma * dx) := by
    unfold swapOutputY
    field_simp
  rw [he]
  apply (div_lt_div_iff₀ hd hrx).mpr
  have h1 : gamma * rx ≤ rx := by nlinarith
  have h2 : gamma * rx < rx + gamma * dx := by nlinarith [mul_pos hg_pos hdx]
  nlinarith [mul_lt_mul_of_pos_left h2 hry]

theorem output_strictly_monotonic (rx ry gamma dx1 dx2 : ℝ)
    (hrx : 0 < rx) (hry : 0 < ry) (hg_pos : 0 < gamma)
    (hdx1 : 0 < dx1) (hlt : dx1 < dx2) :
    swapOutputY rx ry gamma dx1 < swapOutputY rx ry gamma dx2 := by
  have hx2 : 0 < dx2 := lt_trans hdx1 hlt
  have hd1 : 0 < rx + gamma * dx1 := by positivity
  have hd2 : 0 < rx + gamma * dx2 := by positivity
  unfold swapOutputY
  apply (div_lt_div_iff₀ hd1 hd2).mpr
  have hp : 0 < ry * gamma * rx * (dx2 - dx1) :=
    mul_pos (mul_pos (mul_pos hry hg_pos) hrx) (sub_pos.mpr hlt)
  nlinarith

structure DeFiAMMFormalSuite : Prop where
  h_output_pos : ∀ (rx ry gamma dx : ℝ), 0 < rx → 0 < ry → 0 < gamma → 0 < dx →
    0 < swapOutputY rx ry gamma dx
  h_output_lt_res : ∀ (rx ry gamma dx : ℝ), 0 < rx → 0 < ry → 0 < gamma → 0 < dx →
    swapOutputY rx ry gamma dx < ry
  h_new_ry_pos : ∀ (rx ry gamma dx : ℝ), 0 < rx → 0 < ry → 0 < gamma → 0 < dx →
    0 < newRy rx ry gamma dx
  h_k_exact_zero_fee : ∀ (rx ry dx : ℝ), 0 < rx → 0 < dx → newK rx ry 1 dx = rx * ry
  h_k_growth_fee : ∀ (rx ry gamma dx : ℝ), 0 < rx → 0 < ry → 0 < gamma → gamma ≤ 1 → 0 < dx →
    rx * ry ≤ newK rx ry gamma dx
  h_slippage : ∀ (rx ry gamma dx : ℝ), 0 < rx → 0 < ry → 0 < gamma → gamma ≤ 1 → 0 < dx →
    swapOutputY rx ry gamma dx / dx < ry / rx
  h_monotone_out : ∀ (rx ry gamma dx1 dx2 : ℝ),
    0 < rx → 0 < ry → 0 < gamma → 0 < dx1 → dx1 < dx2 →
    swapOutputY rx ry gamma dx1 < swapOutputY rx ry gamma dx2

theorem defi_amm_master_verification_suite : DeFiAMMFormalSuite := {
  h_output_pos := output_pos
  h_output_lt_res := output_lt_reserve
  h_new_ry_pos := newRy_pos
  h_k_exact_zero_fee := constant_product_zero_fee
  h_k_growth_fee := invariant_monotone_with_fee
  h_slippage := price_slippage
  h_monotone_out := output_strictly_monotonic
}

#print axioms defi_amm_master_verification_suite

end DeFiAMMInvariants
