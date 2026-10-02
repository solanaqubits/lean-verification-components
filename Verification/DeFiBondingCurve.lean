/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Linear bonding-curve accounting

The reserve is a prescribed quadratic polynomial, not an integral defined here.
Balance identities do not model contract execution, admissible burns or fees.
-/

noncomputable section

namespace DeFiBondingCurve

structure CurveParams where
  m : ℝ
  b : ℝ
  hm_pos : 0 < m
  hb_nonneg : 0 ≤ b

def spotPrice (p : CurveParams) (s : ℝ) : ℝ := p.m * s + p.b

/-- Prescribed reserve polynomial; no calculus theorem is asserted. -/
def reserve (p : CurveParams) (s : ℝ) : ℝ := (1 / 2) * p.m * s ^ 2 + p.b * s

def mintCost (p : CurveParams) (s ds : ℝ) : ℝ := reserve p (s + ds) - reserve p s

def burnRefund (p : CurveParams) (s ds : ℝ) : ℝ := reserve p s - reserve p (s - ds)

def avgMintPrice (p : CurveParams) (s ds : ℝ) : ℝ := mintCost p s ds / ds

theorem mint_cost_formula (p : CurveParams) (s ds : ℝ) :
    mintCost p s ds = p.m * s * ds + (1 / 2) * p.m * ds ^ 2 + p.b * ds := by
  dsimp [mintCost, reserve]
  ring

theorem burn_refund_formula (p : CurveParams) (s ds : ℝ) :
    burnRefund p s ds = p.m * s * ds - (1 / 2) * p.m * ds ^ 2 + p.b * ds := by
  dsimp [burnRefund, reserve]
  ring

/-- Adding the prescribed cost yields the prescribed new reserve. -/
theorem solvency_mint (p : CurveParams) (s ds : ℝ) :
    reserve p s + mintCost p s ds = reserve p (s + ds) := by
  dsimp [mintCost]
  ring

/-- Accounting identity; there is no check that the burned amount is available. -/
theorem solvency_burn (p : CurveParams) (s ds : ℝ) :
    reserve p s - burnRefund p s ds = reserve p (s - ds) := by
  dsimp [burnRefund]
  ring

/-- Same-curve, fee-free mint followed by burning precisely the minted amount. -/
theorem round_trip_conservation (p : CurveParams) (s ds : ℝ) :
    burnRefund p (s + ds) ds = mintCost p s ds := by
  simp [burnRefund, mintCost]

theorem avg_price_formula (p : CurveParams) (s ds : ℝ) (hds_ne : ds ≠ 0) :
    avgMintPrice p s ds = spotPrice p s + (1 / 2) * p.m * ds := by
  dsimp [avgMintPrice, spotPrice, mintCost, reserve]
  field_simp [hds_ne]
  ring

theorem spot_lt_avg_price (p : CurveParams) (s ds : ℝ) (hds_pos : 0 < ds) :
    spotPrice p s < avgMintPrice p s ds := by
  rw [avg_price_formula p s ds (ne_of_gt hds_pos)]
  have h_slip : 0 < (1 / 2) * p.m * ds :=
    mul_pos (mul_pos (by norm_num) p.hm_pos) hds_pos
  linarith

theorem spot_price_strict_mono (p : CurveParams) (s1 s2 : ℝ) (h_lt : s1 < s2) :
    spotPrice p s1 < spotPrice p s2 := by
  dsimp [spotPrice]
  have h_mul := mul_lt_mul_of_pos_left h_lt p.hm_pos
  linarith

theorem reserve_strict_mono (p : CurveParams) (s1 s2 : ℝ)
    (hs1_nonneg : 0 ≤ s1) (h_lt : s1 < s2) : reserve p s1 < reserve p s2 := by
  have h_sq : s1 ^ 2 < s2 ^ 2 := by nlinarith
  have hm_half : 0 < (1 / 2) * p.m := mul_pos (by norm_num) p.hm_pos
  have h_term1 := mul_lt_mul_of_pos_left h_sq hm_half
  have h_term2 := mul_le_mul_of_nonneg_left (le_of_lt h_lt) p.hb_nonneg
  dsimp [reserve]
  linarith

structure DeFiBondingCurveFormalSuite : Prop where
  h_mint_form : ∀ (p : CurveParams) (s ds : ℝ),
    mintCost p s ds = p.m * s * ds + (1 / 2) * p.m * ds ^ 2 + p.b * ds
  h_burn_form : ∀ (p : CurveParams) (s ds : ℝ),
    burnRefund p s ds = p.m * s * ds - (1 / 2) * p.m * ds ^ 2 + p.b * ds
  h_solv_mint : ∀ (p : CurveParams) (s ds : ℝ),
    reserve p s + mintCost p s ds = reserve p (s + ds)
  h_solv_burn : ∀ (p : CurveParams) (s ds : ℝ),
    reserve p s - burnRefund p s ds = reserve p (s - ds)
  h_round_trip : ∀ (p : CurveParams) (s ds : ℝ),
    burnRefund p (s + ds) ds = mintCost p s ds
  h_avg_price : ∀ (p : CurveParams) (s ds : ℝ), ds ≠ 0 →
    avgMintPrice p s ds = spotPrice p s + (1 / 2) * p.m * ds
  h_price_slip : ∀ (p : CurveParams) (s ds : ℝ), 0 < ds →
    spotPrice p s < avgMintPrice p s ds
  h_price_mono : ∀ (p : CurveParams) (s1 s2 : ℝ), s1 < s2 →
    spotPrice p s1 < spotPrice p s2
  h_reserve_mono : ∀ (p : CurveParams) (s1 s2 : ℝ), 0 ≤ s1 → s1 < s2 →
    reserve p s1 < reserve p s2

/-- Registry of polynomial accounting and monotonicity results. -/
theorem defi_bonding_curve_master_suite : DeFiBondingCurveFormalSuite := {
  h_mint_form := mint_cost_formula
  h_burn_form := burn_refund_formula
  h_solv_mint := solvency_mint
  h_solv_burn := solvency_burn
  h_round_trip := round_trip_conservation
  h_avg_price := avg_price_formula
  h_price_slip := spot_lt_avg_price
  h_price_mono := spot_price_strict_mono
  h_reserve_mono := reserve_strict_mono
}

end DeFiBondingCurve
