import Mathlib.Data.Real.Basic

set_option linter.style.header false
noncomputable section

namespace DeFiLendingCDP

/-- A static single-collateral position; the threshold is a liquidation threshold. -/
structure CDPPosition where
  collateralAmount : ℝ
  collateralPrice : ℝ
  debtAmount : ℝ
  liqThreshold : ℝ
  hCollateral_nonneg : 0 ≤ collateralAmount
  hPrice_pos : 0 < collateralPrice
  hDebt_pos : 0 < debtAmount
  hThreshold_pos : 0 < liqThreshold
  hThreshold_le_one : liqThreshold ≤ 1

def collateralValue (cdp : CDPPosition) : ℝ :=
  cdp.collateralAmount * cdp.collateralPrice

def adjustedCollateral (cdp : CDPPosition) : ℝ :=
  collateralValue cdp * cdp.liqThreshold

def healthFactor (cdp : CDPPosition) : ℝ :=
  adjustedCollateral cdp / cdp.debtAmount

/-- Coverage according to the model's threshold, not a protocol-wide solvency claim. -/
def IsSolvent (cdp : CDPPosition) : Prop := 1 ≤ healthFactor cdp

def IsLiquidatable (cdp : CDPPosition) : Prop := healthFactor cdp < 1

theorem health_factor_nonneg (cdp : CDPPosition) : 0 ≤ healthFactor cdp :=
  div_nonneg (mul_nonneg (mul_nonneg cdp.hCollateral_nonneg
    (le_of_lt cdp.hPrice_pos)) (le_of_lt cdp.hThreshold_pos)) (le_of_lt cdp.hDebt_pos)

theorem solvency_iff_adjusted_ge_debt (cdp : CDPPosition) :
    IsSolvent cdp ↔ cdp.debtAmount ≤ adjustedCollateral cdp := by
  exact (one_le_div cdp.hDebt_pos)

theorem liquidatable_iff_adjusted_lt_debt (cdp : CDPPosition) :
    IsLiquidatable cdp ↔ adjustedCollateral cdp < cdp.debtAmount := by
  exact (div_lt_one cdp.hDebt_pos)

theorem health_factor_strict_mono_price (C P1 P2 D T : ℝ)
    (hC : 0 < C) (hP : P1 < P2) (hD : 0 < D) (hT : 0 < T) :
    (C * P1 * T) / D < (C * P2 * T) / D :=
  div_lt_div_of_pos_right (mul_lt_mul_of_pos_right
    (mul_lt_mul_of_pos_left hP hC) hT) hD

theorem health_factor_strict_anti_mono_debt (C P D1 D2 T : ℝ)
    (hC : 0 < C) (hP : 0 < P) (hT : 0 < T) (hD : D1 < D2) (hD1_pos : 0 < D1) :
    (C * P * T) / D2 < (C * P * T) / D1 :=
  div_lt_div_of_pos_left (mul_pos (mul_pos hC hP) hT) hD1_pos hD

/-- An uncapped algebraic quote, without a position update or feasibility check. -/
def seizedCollateralAmount (deltaDebt price bonus : ℝ) : ℝ :=
  (deltaDebt * (1 + bonus)) / price

theorem liquidation_seized_value (deltaDebt price bonus : ℝ) (hPrice : price ≠ 0) :
    seizedCollateralAmount deltaDebt price bonus * price = deltaDebt * (1 + bonus) :=
  div_mul_cancel₀ _ hPrice

structure DeFiLendingCDPFormalSuite : Prop where
  h_hf_nonneg : ∀ cdp, 0 ≤ healthFactor cdp
  h_solvency_iff : ∀ cdp, IsSolvent cdp ↔ cdp.debtAmount ≤ adjustedCollateral cdp
  h_liquidate_iff : ∀ cdp, IsLiquidatable cdp ↔ adjustedCollateral cdp < cdp.debtAmount
  h_price_mono : ∀ C P1 P2 D T : ℝ, 0 < C → P1 < P2 → 0 < D → 0 < T →
    (C * P1 * T) / D < (C * P2 * T) / D
  h_debt_mono : ∀ C P D1 D2 T : ℝ, 0 < C → 0 < P → 0 < T → D1 < D2 → 0 < D1 →
    (C * P * T) / D2 < (C * P * T) / D1
  h_seize_val : ∀ deltaDebt price bonus, price ≠ 0 →
    seizedCollateralAmount deltaDebt price bonus * price = deltaDebt * (1 + bonus)

theorem defi_lending_cdp_master_verification_suite : DeFiLendingCDPFormalSuite := {
  h_hf_nonneg := health_factor_nonneg
  h_solvency_iff := solvency_iff_adjusted_ge_debt
  h_liquidate_iff := liquidatable_iff_adjusted_lt_debt
  h_price_mono := health_factor_strict_mono_price
  h_debt_mono := health_factor_strict_anti_mono_debt
  h_seize_val := liquidation_seized_value
}

#print axioms defi_lending_cdp_master_verification_suite

end DeFiLendingCDP
