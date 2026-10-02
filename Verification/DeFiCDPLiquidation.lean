import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option linter.style.header false
noncomputable section

namespace DeFiCDPLiquidation

/-- A scalar position with positive collateral, debt, price and threshold. -/
structure CDP where
  collateral : ℝ
  debt : ℝ
  price : ℝ
  liquidationThreshold : ℝ
  h_coll_pos : 0 < collateral
  h_debt_pos : 0 < debt
  h_price_pos : 0 < price
  h_thresh_pos : 0 < liquidationThreshold
  h_thresh_le_one : liquidationThreshold ≤ 1

def collateralValue (c : CDP) : ℝ := c.collateral * c.price

def healthFactor (c : CDP) : ℝ :=
  c.collateral * c.price * c.liquidationThreshold / c.debt

/-- Threshold coverage in this model, not protocol-wide solvency. -/
def isSolvent (c : CDP) : Prop := 1 ≤ healthFactor c

def isLiquidatable (c : CDP) : Prop := healthFactor c < 1

theorem solvency_iff_le (c : CDP) :
    isSolvent c ↔ c.debt ≤ c.collateral * c.price * c.liquidationThreshold := by
  exact one_le_div₀ c.h_debt_pos

theorem liquidatable_iff_lt (c : CDP) :
    isLiquidatable c ↔ c.collateral * c.price * c.liquidationThreshold < c.debt := by
  exact div_lt_one₀ c.h_debt_pos

/-- Strict improvement for partial repayment with the collateral numerator fixed. -/
theorem health_factor_improves_on_pure_repay
    (c : CDP) (repay : ℝ) (h_repay_pos : 0 < repay) (h_repay_lt : repay < c.debt) :
    healthFactor c < c.collateral * c.price * c.liquidationThreshold / (c.debt - repay) := by
  have h_num_pos : 0 < c.collateral * c.price * c.liquidationThreshold :=
    mul_pos (mul_pos c.h_coll_pos c.h_price_pos) c.h_thresh_pos
  have h_denom_sub : 0 < c.debt - repay := by linarith
  have h_denom_lt : c.debt - repay < c.debt := by linarith
  exact div_lt_div_of_pos_left h_num_pos h_denom_sub h_denom_lt

/-- A valuation identity; repayment and penalty are arbitrary real inputs. -/
theorem liquidator_seized_collateral_value
    (repayAmount penalty price : ℝ) (h_price_pos : 0 < price) :
    let seizedCollateral := repayAmount * (1 + penalty) / price
    seizedCollateral * price = repayAmount * (1 + penalty) := by
  exact div_mul_cancel₀ (repayAmount * (1 + penalty)) (ne_of_gt h_price_pos)

structure DeFiCDPLiquidationFormalSuite : Prop where
  h_solvency_iff : ∀ (c : CDP),
    isSolvent c ↔ c.debt ≤ c.collateral * c.price * c.liquidationThreshold
  h_liquidatable_iff : ∀ (c : CDP),
    isLiquidatable c ↔ c.collateral * c.price * c.liquidationThreshold < c.debt
  h_repay_improves : ∀ (c : CDP) (repay : ℝ), 0 < repay → repay < c.debt →
    healthFactor c < c.collateral * c.price * c.liquidationThreshold / (c.debt - repay)
  h_seized_val : ∀ (repay penalty price : ℝ), 0 < price →
    (repay * (1 + penalty) / price) * price = repay * (1 + penalty)

theorem defi_cdp_liquidation_master_verification_suite : DeFiCDPLiquidationFormalSuite := {
  h_solvency_iff := solvency_iff_le
  h_liquidatable_iff := liquidatable_iff_lt
  h_repay_improves := health_factor_improves_on_pure_repay
  h_seized_val := liquidator_seized_collateral_value
}

end DeFiCDPLiquidation
