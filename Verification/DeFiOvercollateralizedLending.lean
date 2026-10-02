/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar overcollateralized lending with two asset prices

Positive balances, fixed prices and a threshold strictly between zero and one.
These results do not model lending-contract execution or oracle behavior.
-/

noncomputable section

namespace DeFiOvercollateralizedLending

structure LendingPosition where
  collateral : ℝ
  debt : ℝ
  priceC : ℝ
  priceD : ℝ
  lt : ℝ
  h_c_pos : 0 < collateral
  h_d_pos : 0 < debt
  h_pc_pos : 0 < priceC
  h_pd_pos : 0 < priceD
  h_lt_pos : 0 < lt
  h_lt_lt_one : lt < 1

def collateralValue (p : LendingPosition) : ℝ := p.collateral * p.priceC

def debtValue (p : LendingPosition) : ℝ := p.debt * p.priceD

def healthFactor (p : LendingPosition) : ℝ := collateralValue p * p.lt / debtValue p

/-- Threshold safety in the scalar position model. -/
def isSafe (p : LendingPosition) : Prop := 1 ≤ healthFactor p

/-- Below the liquidation threshold, not necessarily debt exceeding collateral value. -/
def isLiquidatable (p : LendingPosition) : Prop := healthFactor p < 1

theorem collateral_value_pos (p : LendingPosition) : 0 < collateralValue p :=
  mul_pos p.h_c_pos p.h_pc_pos

theorem debt_value_pos (p : LendingPosition) : 0 < debtValue p :=
  mul_pos p.h_d_pos p.h_pd_pos

theorem health_factor_pos (p : LendingPosition) : 0 < healthFactor p :=
  div_pos (mul_pos (collateral_value_pos p) p.h_lt_pos) (debt_value_pos p)

/-- Threshold safety implies strict value coverage because the threshold is below one. -/
theorem safe_position_strictly_solvent (p : LendingPosition) (h_safe : isSafe p) :
    debtValue p < collateralValue p := by
  have h_ineq : debtValue p ≤ collateralValue p * p.lt :=
    (one_le_div₀ (debt_value_pos p)).mp h_safe
  have h_lt := mul_lt_mul_of_pos_left p.h_lt_lt_one (collateral_value_pos p)
  linarith

/-- Deposit at unchanged debt, prices and threshold. -/
def depositCollateral (p : LendingPosition) (dc : ℝ) (hdc : 0 < dc) : LendingPosition := {
  p with
  collateral := p.collateral + dc
  h_c_pos := add_pos p.h_c_pos hdc
}

theorem add_collateral_increases_hf (p : LendingPosition) (dc : ℝ) (hdc : 0 < dc) :
    healthFactor p < healthFactor (depositCollateral p dc hdc) := by
  dsimp [healthFactor, depositCollateral, collateralValue, debtValue]
  apply (div_lt_div_iff_of_pos_right (debt_value_pos p)).mpr
  have h_gain := mul_pos (mul_pos hdc p.h_pc_pos) p.h_lt_pos
  nlinarith

/-- Add positive debt at fixed collateral and prices; no borrowing admission check. -/
def borrowMore (p : LendingPosition) (dd : ℝ) (hdd : 0 < dd) : LendingPosition := {
  p with
  debt := p.debt + dd
  h_d_pos := add_pos p.h_d_pos hdd
}

theorem borrow_more_decreases_hf (p : LendingPosition) (dd : ℝ) (hdd : 0 < dd) :
    healthFactor (borrowMore p dd hdd) < healthFactor p := by
  dsimp [healthFactor, borrowMore, collateralValue, debtValue]
  have h_num_pos := mul_pos (collateral_value_pos p) p.h_lt_pos
  have h_den_lt : p.debt * p.priceD < (p.debt + dd) * p.priceD := by
    have h_gain := mul_pos hdd p.h_pd_pos
    nlinarith
  exact div_lt_div_of_pos_left h_num_pos (debt_value_pos p) h_den_lt

/-- Defined transfer amount; no execution or repayment-cap predicate is attached. -/
def seizedCollateral (p : LendingPosition) (repaidDebt bonus : ℝ) : ℝ :=
  repaidDebt * p.priceD * (1 + bonus) / p.priceC

theorem liquidation_seized_collateral_value (p : LendingPosition) (repaidDebt bonus : ℝ) :
    seizedCollateral p repaidDebt bonus * p.priceC = repaidDebt * p.priceD * (1 + bonus) := by
  exact div_mul_cancel₀ _ (ne_of_gt p.h_pc_pos)

/-- Conditional coverage; safety alone does not supply the bonus-inclusive premise.
Nonnegative bonus is retained in the interface but not needed for this inequality. -/
theorem full_liquidation_collateral_sufficient (p : LendingPosition) (bonus : ℝ)
    (_h_bonus_nonneg : 0 ≤ bonus)
    (h_covered : debtValue p * (1 + bonus) ≤ collateralValue p) :
    seizedCollateral p p.debt bonus ≤ p.collateral := by
  exact (div_le_iff₀ p.h_pc_pos).mpr h_covered

structure DeFiOvercollateralizedLendingFormalSuite : Prop where
  h_hf_pos : ∀ p : LendingPosition, 0 < healthFactor p
  h_solvency : ∀ p : LendingPosition, isSafe p → debtValue p < collateralValue p
  h_deposit_mono : ∀ (p : LendingPosition) (dc : ℝ) (hdc : 0 < dc),
    healthFactor p < healthFactor (depositCollateral p dc hdc)
  h_borrow_mono : ∀ (p : LendingPosition) (dd : ℝ) (hdd : 0 < dd),
    healthFactor (borrowMore p dd hdd) < healthFactor p
  h_seized_val : ∀ (p : LendingPosition) (repaidDebt bonus : ℝ),
    seizedCollateral p repaidDebt bonus * p.priceC = repaidDebt * p.priceD * (1 + bonus)
  h_full_liq_cov : ∀ (p : LendingPosition) (bonus : ℝ), 0 ≤ bonus →
    debtValue p * (1 + bonus) ≤ collateralValue p →
    seizedCollateral p p.debt bonus ≤ p.collateral

/-- Registry of conditional scalar health and collateral-coverage results. -/
theorem defi_overcollateralized_lending_master_suite :
    DeFiOvercollateralizedLendingFormalSuite := {
  h_hf_pos := health_factor_pos
  h_solvency := safe_position_strictly_solvent
  h_deposit_mono := add_collateral_increases_hf
  h_borrow_mono := borrow_more_decreases_hf
  h_seized_val := liquidation_seized_collateral_value
  h_full_liq_cov := full_liquidation_collateral_sufficient
}

end DeFiOvercollateralizedLending
