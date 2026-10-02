/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar flash-loan reserve accounting

Exact real arithmetic for a prescribed repayment formula. This does not model
EIP-3156 callbacks, token transfers, transaction execution or revert behavior.
-/

noncomputable section

namespace DeFiFlashLoan

/-- A positive reserve and a nonnegative proportional fee rate. -/
structure FlashPool where
  reserve : ℝ
  feeRate : ℝ
  h_reserve_pos : 0 < reserve
  h_fee_nonneg : 0 ≤ feeRate

/-- The model sets the maximum loan equal to the reserve. -/
def maxFlashLoan (p : FlashPool) : ℝ := p.reserve

def flashFee (p : FlashPool) (amount : ℝ) : ℝ := amount * p.feeRate

def totalRepayment (p : FlashPool) (amount : ℝ) : ℝ :=
  amount + flashFee p amount

def postExecutionReserve (p : FlashPool) (amount actualRepaid : ℝ) : ℝ :=
  p.reserve - amount + actualRepaid

/-- The chosen maximum is bounded by the reserve; admission is not modeled. -/
theorem max_flash_loan_le_reserve (p : FlashPool) : maxFlashLoan p ≤ p.reserve :=
  le_refl _

/-- Full repayment preserves the initial reserve and adds the specified fee. -/
theorem flash_loan_solvency_invariant (p : FlashPool) (amount : ℝ)
    (h_amt_nonneg : 0 ≤ amount) :
    let repaid := totalRepayment p amount
    let newReserve := postExecutionReserve p amount repaid
    newReserve = p.reserve + flashFee p amount ∧ p.reserve ≤ newReserve := by
  dsimp [postExecutionReserve, totalRepayment, flashFee]
  have h_fee_nonneg := mul_nonneg h_amt_nonneg p.h_fee_nonneg
  constructor
  · ring
  · linarith

/-- Reserve growth for positive amount and rate, conditional on full repayment. -/
theorem lp_yield_strict_growth (p : FlashPool) (amount : ℝ)
    (h_amt_pos : 0 < amount) (h_fee_pos : 0 < p.feeRate) :
    let repaid := totalRepayment p amount
    p.reserve < postExecutionReserve p amount repaid := by
  dsimp [postExecutionReserve, totalRepayment, flashFee]
  have h_gain := mul_pos h_amt_pos h_fee_pos
  linarith

/-- Underpayment falls below the fee-inclusive target, not necessarily the initial reserve. -/
theorem underpayment_depletes_pool (p : FlashPool) (amount repaid : ℝ)
    (h_underpay : repaid < totalRepayment p amount) :
    postExecutionReserve p amount repaid < p.reserve + flashFee p amount := by
  dsimp [postExecutionReserve, totalRepayment, flashFee] at *
  linarith

theorem flash_fee_additive (p : FlashPool) (a1 a2 : ℝ) :
    flashFee p (a1 + a2) = flashFee p a1 + flashFee p a2 := by
  dsimp [flashFee]
  ring

structure DeFiFlashLoanFormalSuite : Prop where
  h_max_loan : ∀ p : FlashPool, maxFlashLoan p ≤ p.reserve
  h_solvency : ∀ (p : FlashPool) (amount : ℝ), 0 ≤ amount →
    postExecutionReserve p amount (totalRepayment p amount) = p.reserve + flashFee p amount ∧
    p.reserve ≤ postExecutionReserve p amount (totalRepayment p amount)
  h_lp_growth : ∀ (p : FlashPool) (amount : ℝ), 0 < amount → 0 < p.feeRate →
    p.reserve < postExecutionReserve p amount (totalRepayment p amount)
  h_underpay : ∀ (p : FlashPool) (amount repaid : ℝ), repaid < totalRepayment p amount →
    postExecutionReserve p amount repaid < p.reserve + flashFee p amount
  h_fee_add : ∀ (p : FlashPool) (a1 a2 : ℝ),
    flashFee p (a1 + a2) = flashFee p a1 + flashFee p a2

/-- Registry of scalar reserve and fee identities. -/
theorem defi_flash_loan_master_suite : DeFiFlashLoanFormalSuite := {
  h_max_loan := max_flash_loan_le_reserve
  h_solvency := flash_loan_solvency_invariant
  h_lp_growth := lp_yield_strict_growth
  h_underpay := underpayment_depletes_pool
  h_fee_add := flash_fee_additive
}

end DeFiFlashLoan
