/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DeFiLendingLiquidationHealthFactor
import Verification.DeFiKinkedInterestRateUtilization
import Verification.DeFiLendingCompoundInterestIndex
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Liquidation reference accounting at fixed prices and index. Debt - asset reserves
and collateral - asset treasury are separate ledgers. No economic solvency claim. -/
namespace DeFiLendingLiquidationAccounting
open scoped BigOperators
open DeFiLendingCompoundInterestIndex

namespace HF
abbrev Position := DeFiLendingLiquidationHealthFactor.Position
end HF

def c_base (r pd pc : ℚ) : ℚ := r * pd / pc
def c_bonus (r pd pc beta : ℚ) : ℚ := beta * c_base r pd pc
def c_seize (r pd pc beta : ℚ) : ℚ := c_base r pd pc + c_bonus r pd pc beta
def c_fee (r pd pc beta phi : ℚ) : ℚ := phi * c_bonus r pd pc beta
def c_liq (r pd pc beta phi : ℚ) : ℚ := c_base r pd pc + (1 - phi) * c_bonus r pd pc beta

theorem collateral_seize_split_identity (r pd pc beta phi : ℚ) :
    c_liq r pd pc beta phi + c_fee r pd pc beta phi = c_seize r pd pc beta := by
  simp only [c_liq, c_fee, c_seize]; ring

theorem collateral_components_positive (r pd pc beta phi : ℚ)
    (hr : 0 < r) (hd : 0 < pd) (hc : 0 < pc) (hb : 0 ≤ beta)
    (hf : 0 ≤ phi) (hf' : phi ≤ 1) :
    0 < c_base r pd pc ∧ 0 ≤ c_bonus r pd pc beta ∧
    0 ≤ c_fee r pd pc beta phi ∧ 0 < c_liq r pd pc beta phi := by
  have hbase : 0 < c_base r pd pc := div_pos (mul_pos hr hd) hc
  have hbonus : 0 ≤ c_bonus r pd pc beta := mul_nonneg hb hbase.le
  exact ⟨hbase, hbonus, mul_nonneg hf hbonus,
    add_pos_of_pos_of_nonneg hbase (mul_nonneg (sub_nonneg.mpr hf') hbonus)⟩

theorem fee_zero (r pd pc beta : ℚ) :
    c_fee r pd pc beta 0 = 0 ∧ c_liq r pd pc beta 0 = c_seize r pd pc beta := by
  simp [c_fee, c_liq, c_seize]

theorem fee_one (r pd pc beta : ℚ) :
    c_fee r pd pc beta 1 = c_bonus r pd pc beta ∧ c_liq r pd pc beta 1 = c_base r pd pc := by
  simp [c_fee, c_liq]

theorem bonus_zero (r pd pc phi : ℚ) :
    c_bonus r pd pc 0 = 0 ∧ c_fee r pd pc 0 phi = 0 ∧ c_liq r pd pc 0 phi = c_base r pd pc := by
  simp [c_bonus, c_fee, c_liq]

theorem full_repay_iff_close_factor_one (B alpha : ℚ) (hB : 0 < B) (ha : alpha ≤ 1) :
    B ≤ alpha * B ↔ alpha = 1 := by
  constructor
  · intro h
    nlinarith
  · intro h; simp [h]

structure Parameters where
  debtPrice : ℚ
  collateralPrice : ℚ
  threshold : ℚ
  closeFactor : ℚ
  bonus : ℚ
  feeFraction : ℚ
  deriving DecidableEq, Repr

def Parameters.Valid (p : Parameters) : Prop :=
  0 < p.debtPrice ∧ 0 < p.collateralPrice ∧ 0 < p.threshold ∧ p.threshold ≤ 1 ∧
  0 < p.closeFactor ∧ p.closeFactor ≤ 1 ∧ 0 ≤ p.bonus ∧ 0 ≤ p.feeFraction ∧ p.feeFraction ≤ 1
instance (p : Parameters) : Decidable p.Valid := inferInstanceAs (Decidable (_ ∧ _))

/-- Debt is in the common numeraire, not in debt - token units. -/
def valued_position (p : Parameters) (C B : ℚ) : HF.Position 1 :=
  { quantity := fun _ => C, price := fun _ => p.collateralPrice,
    lt := fun _ => p.threshold, ltv := fun _ => 0, debt := p.debtPrice * B }

theorem valued_position_valid (p : Parameters) (C B : ℚ) (hp : p.Valid)
    (hC : 0 ≤ C) (hB : 0 ≤ B) : (valued_position p C B).Valid := by
  exact ⟨mul_nonneg hp.1.le hB, fun _ => ⟨hC, hp.2.1, le_rfl, hp.2.2.1.le, hp.2.2.2.1⟩⟩

theorem valued_position_liquidatable (p : Parameters) (C B : ℚ) :
    DeFiLendingLiquidationHealthFactor.liquidatable (valued_position p C B) ↔
      0 < p.debtPrice * B ∧ p.threshold * (p.collateralPrice * C) < p.debtPrice * B := by
  simp [DeFiLendingLiquidationHealthFactor.liquidatable,
    DeFiLendingLiquidationHealthFactor.weightedValue, valued_position]

theorem seize_bridge (p : Parameters) (C B r : ℚ) :
    c_seize r p.debtPrice p.collateralPrice p.bonus =
      DeFiLendingLiquidationHealthFactor.seize (valued_position p C B) 0
        (p.debtPrice * r) p.bonus := by
  simp only [c_seize, c_bonus, c_base, DeFiLendingLiquidationHealthFactor.seize, valued_position]
  ring

structure LiquidationState (n : ℕ) where
  pool : PoolState n
  collateral : Fin n → ℚ
  liquidatorCollateral : ℚ
  treasuryCollateral : ℚ

def LiquidationState.Valid {n : ℕ} (s : LiquidationState n) : Prop :=
  s.pool.Valid ∧ (∀ i, 0 ≤ s.collateral i) ∧
    0 ≤ s.liquidatorCollateral ∧ 0 ≤ s.treasuryCollateral
instance {n : ℕ} (s : LiquidationState n) : Decidable s.Valid := by
  unfold LiquidationState.Valid; infer_instance

def admissible {n : ℕ} (s : LiquidationState n) (p : Parameters) (i : Fin n) (r : ℚ) : Prop :=
  s.Valid ∧ p.Valid ∧ 0 < r ∧ r ≤ borrower_debt (s.pool.scaled i) s.pool.index ∧
  r ≤ p.closeFactor * borrower_debt (s.pool.scaled i) s.pool.index ∧
  DeFiLendingLiquidationHealthFactor.liquidatable
    (valued_position p (s.collateral i) (borrower_debt (s.pool.scaled i) s.pool.index)) ∧
  c_seize r p.debtPrice p.collateralPrice p.bonus ≤ s.collateral i
instance {n : ℕ} (s : LiquidationState n) (p : Parameters) (i : Fin n) (r : ℚ) :
    Decidable (admissible s p i r) := by unfold admissible; infer_instance

def liquidate {n : ℕ} (s : LiquidationState n) (p : Parameters) (i : Fin n) (r : ℚ) :
    LiquidationState n :=
  { pool := transfer_debt s.pool i (-r)
    collateral := fun j => s.collateral j - if j = i then c_seize r p.debtPrice p.collateralPrice
        p.bonus else 0
    liquidatorCollateral := s.liquidatorCollateral + c_liq r p.debtPrice p.collateralPrice p.bonus
        p.feeFraction
    treasuryCollateral := s.treasuryCollateral + c_fee r p.debtPrice p.collateralPrice p.bonus
        p.feeFraction }

def execute {n : ℕ} (s : LiquidationState n) (p : Parameters) (i : Fin n) (r : ℚ) :
    Option (LiquidationState n) := if admissible s p i r then some (liquidate s p i r) else none

theorem execute_iff {n : ℕ} (s t : LiquidationState n) (p : Parameters) (i : Fin n) (r : ℚ) :
    execute s p i r = some t ↔ admissible s p i r ∧ t = liquidate s p i r := by
  unfold execute; split_ifs with h <;> simp_all [eq_comm]

theorem scaled_debt_sum_preserved {n : ℕ} (s : PoolState n) (i : Fin n) (r : ℚ)
    (hI : s.index ≠ 0) :
    ((∑ j, (transfer_debt s i (-r)).scaled j) * s.index) = s.debt - r := by
  simpa [PoolState.debt, total_debt_from_scaled, transfer_debt, sub_eq_add_neg] using
      transfer_debt_total s i (-r) hI

theorem shares_update {n : ℕ} (s : PoolState n) (i : Fin n) (r : ℚ) :
    (transfer_debt s i (-r)).scaled i = s.scaled i - r / s.index ∧
    ∀ j, j ≠ i → (transfer_debt s i (-r)).scaled j = s.scaled j := by
  constructor
  · simp [transfer_debt, neg_div, sub_eq_add_neg]
  · intro j hj; simp [transfer_debt, hj]

theorem debt_pool_balance_preserved {n : ℕ} (s : PoolState n) (i : Fin n) (r : ℚ)
    (hI : s.index ≠ 0) (hb : s.Balanced) : (transfer_debt s i (-r)).Balanced :=
  transfer_preserves_balance s i (-r) hI hb

theorem net_accounting_assets_invariant {n : ℕ} (s : PoolState n) (i : Fin n) (r : ℚ)
    (hI : s.index ≠ 0) :
    net_accounting_assets (transfer_debt s i (-r)).cash (transfer_debt s i (-r)).debt
      (transfer_debt s i (-r)).reserves = net_accounting_assets s.cash s.debt s.reserves := by
  rw [transfer_debt_total s i (-r) hI]
  simp [net_accounting_assets, transfer_debt]; ring

theorem collateral_asset_conservation {n : ℕ} (s : LiquidationState n) (p : Parameters)
    (i : Fin n) (r : ℚ) :
    (liquidate s p i r).collateral i + (liquidate s p i r).liquidatorCollateral +
      (liquidate s p i r).treasuryCollateral =
        s.collateral i + s.liquidatorCollateral + s.treasuryCollateral := by
  simp only [liquidate, ite_true]
  have := collateral_seize_split_identity r p.debtPrice p.collateralPrice p.bonus p.feeFraction
  linarith

theorem liquidation_invariants {n : ℕ} (s : LiquidationState n) (p : Parameters) (i : Fin n) (r : ℚ)
    (h : admissible s p i r) (hb : s.pool.Balanced) :
    (liquidate s p i r).Valid ∧ (liquidate s p i r).pool.Balanced ∧
    (liquidate s p i r).pool.debt = s.pool.debt - r ∧
    (liquidate s p i r).pool.reserves = s.pool.reserves ∧
    (liquidate s p i r).pool.liabilities = s.pool.liabilities ∧
    (liquidate s p i r).pool.index = s.pool.index := by
  rcases h with ⟨hs, hp, hr, hd, _, _, hc⟩
  have hrep : RepayStep s.pool (transfer_debt s.pool i (-r)) i r := ⟨hs.1, hr.le, hd, rfl⟩
  have hinv := repay_step_invariants hrep hb
  have hpos := collateral_components_positive r _ _ _ _ hr hp.1 hp.2.1
    hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2
  refine ⟨⟨hinv.1, ?_, add_nonneg hs.2.2.1 hpos.2.2.2.le, add_nonneg hs.2.2.2 hpos.2.2.1⟩,
    hinv.2.1, hinv.2.2.2, rfl, rfl, rfl⟩
  intro j
  dsimp [liquidate]
  by_cases hj : j = i
  · subst j; simpa using sub_nonneg.mpr hc
  · simpa [hj] using hs.2.1 j

/-- Actual post - settlement HF, with prices and threshold fixed. -/
def health (C B pd pc ell : ℚ) : ℚ := ell * (pc * C) / (pd * B)

theorem health_after_normal_form (C B pd pc ell beta r : ℚ) (hd : pd ≠ 0) (hc : pc ≠ 0) :
    health (C - c_seize r pd pc beta) (B - r) pd pc ell =
      (ell * (pc * C) - ell * ((1 + beta) * (pd * r))) / (pd * B - pd * r) := by
  unfold health c_seize c_bonus c_base
  field_simp

theorem health_nondecreasing_iff (C B pd pc ell beta r : ℚ)
    (hd : 0 < pd) (hc : 0 < pc) (hr : 0 < r) (hB : r < B) :
    health C B pd pc ell ≤ health (C - c_seize r pd pc beta) (B - r) pd pc ell ↔
      ell * (1 + beta) ≤ health C B pd pc ell := by
  rw [health_after_normal_form C B pd pc ell beta r (ne_of_gt hd) (ne_of_gt hc)]
  exact DeFiLendingLiquidationHealthFactor.health_nondecreases_iff _ _ _ _ _
    (mul_pos hd hr) (by nlinarith)

theorem health_decreases_iff (C B pd pc ell beta r : ℚ)
    (hd : 0 < pd) (hc : 0 < pc) (hr : 0 < r) (hB : r < B) :
    health (C - c_seize r pd pc beta) (B - r) pd pc ell < health C B pd pc ell ↔
      health C B pd pc ell < ell * (1 + beta) := by
  exact not_le.symm.trans ((not_congr (health_nondecreasing_iff C B pd pc ell beta r hd hc hr
      hB)).trans not_le)

theorem health_two_regimes :
    health 120 100 1 1 (3 / 4) < health (120 - c_seize 20 1 1 (1 / 10)) 80 1 1 (3 / 4) ∧
    health (100 - c_seize 20 1 1 (1 / 10)) 80 1 1 (3 / 4) < health 100 100 1 1 (3 / 4) ∧
    health 120 100 1 1 (3 / 4) < 1 := by norm_num [health, c_seize, c_bonus, c_base]

/-- Smallest token units are used throughout. pd / pc includes the token - decimal
conversion; both prices share the same numeraire scale. Factors and index use W. -/
structure DiscreteParameters where
  scale : ℕ
  debtPrice : ℕ
  collateralPrice : ℕ
  threshold : ℕ
  closeFactor : ℕ
  bonus : ℕ
  feeFraction : ℕ
  deriving DecidableEq, Repr

structure IntegerState (n : ℕ) where
  cash : ℕ
  debt : ℕ
  reserves : ℕ
  liabilities : ℕ
  index : ℕ
  scaled : Fin n → ℕ
  collateral : Fin n → ℕ
  liquidatorCollateral : ℕ
  treasuryCollateral : ℕ
  deriving DecidableEq, Repr

def base_int (p : DiscreteParameters) (r : ℕ) : ℕ := r * p.debtPrice / p.collateralPrice
def bonus_int (p : DiscreteParameters) (r : ℕ) : ℕ := p.bonus * base_int p r / p.scale
def seize_int (p : DiscreteParameters) (r : ℕ) : ℕ := base_int p r + bonus_int p r
def fee_int (p : DiscreteParameters) (r : ℕ) : ℕ := p.feeFraction * bonus_int p r / p.scale
def liq_int (p : DiscreteParameters) (r : ℕ) : ℕ := seize_int p r - fee_int p r

def displayed_debt {n : ℕ} (s : IntegerState n) (p : DiscreteParameters) (i : Fin n) : ℕ :=
  individual_int p.scale s.index (s.scaled i)

/-- Partial repayments burn floor(r * W / I) shares. Full displayed repayment clears
all shares. The latter has a separate, explicitly bounded rounding residual. -/
def shares_burn (W I b r : ℕ) : ℕ := if r = b * I / W then b else r * W / I

def integer_admissible {n : ℕ} (s : IntegerState n) (p : DiscreteParameters) (i : Fin n) (r : ℕ) :
    Prop :=
  0 < p.scale ∧ 0 < s.index ∧ 0 < p.debtPrice ∧ 0 < p.collateralPrice ∧
  0 < p.threshold ∧ p.threshold ≤ p.scale ∧ 0 < p.closeFactor ∧ p.closeFactor ≤ p.scale ∧
  p.feeFraction ≤ p.scale ∧ 0 < r ∧ r ≤ displayed_debt s p i ∧ r ≤ s.debt ∧
  r ≤ p.closeFactor * displayed_debt s p i / p.scale ∧
  p.threshold * (p.collateralPrice * s.collateral i) < p.scale * (p.debtPrice * displayed_debt s p
      i) ∧
  seize_int p r ≤ s.collateral i
instance {n : ℕ} (s : IntegerState n) (p : DiscreteParameters) (i : Fin n) (r : ℕ) :
    Decidable (integer_admissible s p i r) := by unfold integer_admissible; infer_instance

def liquidate_int {n : ℕ} (s : IntegerState n) (p : DiscreteParameters) (i : Fin n) (r : ℕ) :
    IntegerState n :=
  { s with cash := s.cash + r, debt := s.debt - r
           scaled := fun j => s.scaled j - if j = i then shares_burn p.scale s.index (s.scaled i) r
               else 0
           collateral := fun j => s.collateral j - if j = i then seize_int p r else 0
           liquidatorCollateral := s.liquidatorCollateral + liq_int p r
           treasuryCollateral := s.treasuryCollateral + fee_int p r }

def execute_int {n : ℕ} (s : IntegerState n) (p : DiscreteParameters) (i : Fin n) (r : ℕ) :
    Option (IntegerState n) := if integer_admissible s p i r then some (liquidate_int s p i r) else
        none

theorem execute_int_iff {n : ℕ} (s t : IntegerState n) (p : DiscreteParameters) (i : Fin n) (r : ℕ)
    :
    execute_int s p i r = some t ↔ integer_admissible s p i r ∧ t = liquidate_int s p i r := by
  unfold execute_int; split_ifs with h <;> simp_all [eq_comm]

theorem execute_int_rejects {n : ℕ} (s : IntegerState n) (p : DiscreteParameters) (i : Fin n) (r :
    ℕ) :
    execute_int s p i r = none ↔ ¬ integer_admissible s p i r := by
  unfold execute_int; split_ifs <;> simp_all

theorem fee_int_le_bonus (p : DiscreteParameters) (r : ℕ) (hW : 0 < p.scale)
    (hf : p.feeFraction ≤ p.scale) : fee_int p r ≤ bonus_int p r :=
  reserve_split_le p.scale p.feeFraction (bonus_int p r) hW hf

theorem integer_collateral_split (p : DiscreteParameters) (r : ℕ) (hW : 0 < p.scale)
    (hf : p.feeFraction ≤ p.scale) : liq_int p r + fee_int p r = seize_int p r := by
  have h := fee_int_le_bonus p r hW hf
  dsimp [liq_int, seize_int]
  omega

theorem shares_burn_le (W I b r : ℕ) (hW : 0 < W) (hI : 0 < I) (hr : r ≤ b * I / W) :
    shares_burn W I b r ≤ b := by
  unfold shares_burn
  split_ifs
  · exact le_rfl
  · have hm := (Nat.le_div_iff_mul_le hW).mp hr
    apply (Nat.div_le_iff_le_mul_add_pred hI).mpr
    nlinarith

theorem full_repayment_clears_shares (W I b : ℕ) :
    b - shares_burn W I b (b * I / W) = 0 := by simp [shares_burn]

theorem integer_debt_balance {n : ℕ} (s : IntegerState n) (p : DiscreteParameters) (i : Fin n) (r :
    ℕ)
    (hr : r ≤ s.debt) (hb : s.cash + s.debt = s.reserves + s.liabilities) :
    (liquidate_int s p i r).cash + (liquidate_int s p i r).debt =
      (liquidate_int s p i r).reserves + (liquidate_int s p i r).liabilities := by
  dsimp [liquidate_int]; omega

theorem integer_collateral_conservation {n : ℕ} (s : IntegerState n) (p : DiscreteParameters)
    (i : Fin n) (r : ℕ) (hW : 0 < p.scale) (hf : p.feeFraction ≤ p.scale)
    (hc : seize_int p r ≤ s.collateral i) :
    (liquidate_int s p i r).collateral i + (liquidate_int s p i r).liquidatorCollateral +
      (liquidate_int s p i r).treasuryCollateral =
      s.collateral i + s.liquidatorCollateral + s.treasuryCollateral := by
  simp only [liquidate_int, ite_true]
  have := integer_collateral_split p r hW hf
  omega

theorem execute_int_invariants {n : ℕ} (s t : IntegerState n) (p : DiscreteParameters) (i : Fin n)
    (r : ℕ)
    (h : execute_int s p i r = some t) :
    integer_admissible s p i r ∧
    (s.cash + s.debt = s.reserves + s.liabilities → t.cash + t.debt = t.reserves + t.liabilities) ∧
    t.collateral i + t.liquidatorCollateral + t.treasuryCollateral =
      s.collateral i + s.liquidatorCollateral + s.treasuryCollateral ∧
    t.reserves = s.reserves ∧ t.liabilities = s.liabilities ∧ t.index = s.index ∧
    t.scaled i ≤ s.scaled i ∧
    (∀ j, j ≠ i → t.scaled j = s.scaled j ∧ t.collateral j = s.collateral j) := by
  rcases (execute_int_iff s t p i r).mp h with ⟨hg, rfl⟩
  refine ⟨hg, ?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
  · exact integer_debt_balance s p i r hg.2.2.2.2.2.2.2.2.2.2.2.1
  · exact integer_collateral_conservation s p i r hg.1 hg.2.2.2.2.2.2.2.2.1
      hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · exact Nat.sub_le _ _
  · intro j hj; simp [liquidate_int, hj]

/-- All bounds below concern the specified arithmetic, not machine overflow. -/
theorem base_int_error (p : DiscreteParameters) (r : ℕ) :
    0 ≤ (r : ℚ) * p.debtPrice / p.collateralPrice - base_int p r ∧
    (r : ℚ) * p.debtPrice / p.collateralPrice - base_int p r < 1 := by
  have h := DeFiKinkedInterestRateUtilization.floor_div_bounds (r * p.debtPrice) p.collateralPrice
  dsimp [base_int]; push_cast at h
  constructor <;> linarith [h.1, h.2]

theorem bonus_int_error (p : DiscreteParameters) (r : ℕ) :
    0 ≤ (p.bonus : ℚ) * base_int p r / p.scale - bonus_int p r ∧
    (p.bonus : ℚ) * base_int p r / p.scale - bonus_int p r < 1 := by
  exact reserve_floor_error p.scale p.bonus (base_int p r)

theorem fee_int_error (p : DiscreteParameters) (r : ℕ) :
    0 ≤ (p.feeFraction : ℚ) * bonus_int p r / p.scale - fee_int p r ∧
    (p.feeFraction : ℚ) * bonus_int p r / p.scale - fee_int p r < 1 :=
  reserve_floor_error p.scale p.feeFraction (bonus_int p r)

theorem seize_int_error (p : DiscreteParameters) (r : ℕ) :
    0 ≤ c_seize r p.debtPrice p.collateralPrice ((p.bonus : ℚ) / p.scale) - seize_int p r ∧
    c_seize r p.debtPrice p.collateralPrice ((p.bonus : ℚ) / p.scale) - seize_int p r <
      2 + (p.bonus : ℚ) / p.scale := by
  have hbase := base_int_error p r
  have hbonus := bonus_int_error p r
  have hβ : 0 ≤ (p.bonus : ℚ) / p.scale := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have he : c_seize r p.debtPrice p.collateralPrice ((p.bonus : ℚ) / p.scale) - seize_int p r =
      (1 + (p.bonus : ℚ) / p.scale) * ((r : ℚ) * p.debtPrice / p.collateralPrice - base_int p r) +
      ((p.bonus : ℚ) * base_int p r / p.scale - bonus_int p r) := by
    simp only [c_seize, c_bonus, c_base, seize_int, Nat.cast_add]; ring
  rw [he]
  constructor
  · exact add_nonneg (mul_nonneg (by linarith) hbase.1) hbonus.1
  · nlinarith [mul_nonneg hβ (sub_nonneg.mpr hbase.2.le)]

theorem partial_shares_rounding (W I b r : ℕ) (hW : 0 < W) (hI : 0 < I)
    (hr : r ≤ b * I / W) (hne : r ≠ b * I / W) :
    0 ≤ ((b - shares_burn W I b r : ℕ):ℚ) - ((b : ℚ) - (r : ℚ) * W / I) ∧
    ((b - shares_burn W I b r : ℕ):ℚ) - ((b : ℚ) - (r : ℚ) * W / I) < 1 := by
  have hb := shares_burn_le W I b r hW hI hr
  have h := DeFiKinkedInterestRateUtilization.floor_div_bounds (r * W) I
  rw [Nat.cast_sub hb]
  simp only [shares_burn, if_neg hne]
  push_cast at h
  constructor <;> linarith [h.1, h.2]

theorem full_shares_rounding (W I b : ℕ) (hW : 0 < W) (hI : 0 < I) :
    0 ≤ (b : ℚ) - ((b * I / W : ℕ):ℚ) * W / I ∧
    (b : ℚ) - ((b * I / W : ℕ):ℚ) * W / I < (W : ℚ) / I := by
  have h := DeFiKinkedInterestRateUtilization.floor_div_bounds (b * I) W
  have hw : (0 : ℚ) < W := by exact_mod_cast hW
  have hi : (0 : ℚ) < I := by exact_mod_cast hI
  push_cast at h
  have he : (b : ℚ) - ((b * I / W : ℕ):ℚ) * W / I =
      ((b : ℚ) * I / W - ((b * I / W : ℕ):ℚ)) * ((W : ℚ) / I) := by
    field_simp
  rw [he]
  constructor
  · exact mul_nonneg (sub_nonneg.mpr h.1) (div_pos hw hi).le
  · nlinarith [mul_pos (show 0 < 1 - ((b : ℚ) * I / W - ((b * I / W : ℕ):ℚ)) by linarith [h.2])
      (div_pos hw hi)]

/-- The ledger / index discrepancy has an exact update law, not an n - 1 bound. -/
theorem ledger_gap_update {n : ℕ} (s : IntegerState n) (p : DiscreteParameters) (i : Fin n) (r : ℕ)
    (hr : r ≤ s.debt) :
    ledger_index_gap (liquidate_int s p i r).debt p.scale s.index (liquidate_int s p i r).scaled =
    ledger_index_gap s.debt p.scale s.index s.scaled + aggregate_int p.scale s.index s.scaled -
      aggregate_int p.scale s.index (liquidate_int s p i r).scaled - (r : ℤ) := by
  simp only [ledger_index_gap, liquidate_int, Nat.cast_sub hr]
  ring

theorem post_liquidation_reconciliation {n : ℕ} (s : IntegerState n) (p : DiscreteParameters)
    (i : Fin n) (r : ℕ) (hW : 0 < p.scale) (hn : 0 < n) :
    recon_dust p.scale s.index (liquidate_int s p i r).scaled ≤ n - 1 ∧
    ((liquidate_int s p i r).debt : ℤ) -
      ∑ j, (individual_int p.scale s.index ((liquidate_int s p i r).scaled j):ℤ) =
      ledger_index_gap (liquidate_int s p i r).debt p.scale s.index (liquidate_int s p i r).scaled +
      recon_dust p.scale s.index (liquidate_int s p i r).scaled :=
  ⟨(recon_dust_bounds _ _ _ hW hn).2, ledger_reconciliation_identity _ _ _ _ hW⟩

/-- The module - 164 admission uses monetary repayment pd * r. -/
theorem admissible_health_factor_bridge {n : ℕ} (s : LiquidationState n) (p : Parameters)
    (i : Fin n) (r : ℚ) (h : admissible s p i r) :
    DeFiLendingLiquidationHealthFactor.admissible
      (valued_position p (s.collateral i) (borrower_debt (s.pool.scaled i) s.pool.index))
      0 (p.debtPrice * r) p.bonus p.closeFactor := by
  rcases h with ⟨hs, hp, hr, hd, hclose, hl, hc⟩
  have hB := mul_nonneg (hs.1.2.2.2.2 i) hs.1.2.2.2.1.le
  refine ⟨valued_position_valid p _ _ hp (hs.2.1 i) hB, hl, mul_pos hp.1 hr, ?_,
    hp.2.2.2.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_left hd hp.1.le
  · change p.debtPrice * r ≤ p.closeFactor * (p.debtPrice * borrower_debt (s.pool.scaled i)
      s.pool.index)
    nlinarith [mul_le_mul_of_nonneg_left hclose hp.1.le]
  · rw [← seize_bridge]; exact hc

theorem rational_execution_spec {n : ℕ} (s t : LiquidationState n) (p : Parameters)
    (i : Fin n) (r : ℚ) (he : execute s p i r = some t) (hb : s.pool.Balanced) :
    t.Valid ∧ t.pool.Balanced ∧ t.pool.debt = s.pool.debt - r ∧
    t.pool.cash = s.pool.cash + r ∧ t.pool.index = s.pool.index ∧
    t.pool.reserves = s.pool.reserves ∧ t.pool.liabilities = s.pool.liabilities ∧
    net_accounting_assets t.pool.cash t.pool.debt t.pool.reserves =
      net_accounting_assets s.pool.cash s.pool.debt s.pool.reserves ∧
    t.collateral i + t.liquidatorCollateral + t.treasuryCollateral =
      s.collateral i + s.liquidatorCollateral + s.treasuryCollateral ∧
    (∀ j, j ≠ i → t.pool.scaled j = s.pool.scaled j ∧ t.collateral j = s.collateral j) := by
  rcases (execute_iff s t p i r).mp he with ⟨hg, rfl⟩
  have h := liquidation_invariants s p i r hg hb
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, rfl, rfl, rfl,
    net_accounting_assets_invariant s.pool i r (ne_of_gt hg.1.1.2.2.2.1),
    collateral_asset_conservation s p i r, ?_⟩
  · simp [liquidate, transfer_debt]
  · intro j hj; simp [liquidate, transfer_debt, hj]

/-- Nonzero rounding and ledger / index discrepancy can occur even for one borrower. -/
theorem rounding_gap_example :
    shares_burn 10 100 1 1 = 0 ∧
    ((1 - shares_burn 10 100 1 1 : ℕ):ℚ) - (1 - (1 : ℚ) * 10 / 100) = 1 / 10 ∧
    ledger_index_gap 9 10 100 (fun _ : Fin 1 => 1) = - 1 ∧
    recon_dust 10 100 (fun _ : Fin 1 => 1) = 0 := by
  norm_num [shares_burn, ledger_index_gap, aggregate_int, recon_dust, individual_int]

structure DeFiLendingLiquidationAccountingSuite : Prop where
  full_close : ∀ (B a : ℚ), 0 < B → a ≤ 1 → (B ≤ a * B ↔ a = 1)
  split : ∀ r pd pc beta phi, c_liq r pd pc beta phi + c_fee r pd pc beta phi = c_seize r pd pc beta
  rational_transition : ∀ n (s : LiquidationState n) p i r, admissible s p i r → s.pool.Balanced →
    (liquidate s p i r).Valid ∧ (liquidate s p i r).pool.Balanced ∧
    (liquidate s p i r).pool.debt = s.pool.debt - r ∧
    (liquidate s p i r).pool.reserves = s.pool.reserves ∧
    (liquidate s p i r).pool.liabilities = s.pool.liabilities ∧
    (liquidate s p i r).pool.index = s.pool.index
  scaled_sum : ∀ n (s : PoolState n) i r, s.index ≠ 0 →
    ((∑ j, (transfer_debt s i (-r)).scaled j) * s.index) = s.debt - r
  collateral_conservation : ∀ n (s : LiquidationState n) p i r,
    (liquidate s p i r).collateral i + (liquidate s p i r).liquidatorCollateral +
      (liquidate s p i r).treasuryCollateral = s.collateral i + s.liquidatorCollateral +
          s.treasuryCollateral
  health_condition : ∀ C B pd pc ell beta r, 0 < pd → 0 < pc → 0 < r → r < B →
    (health C B pd pc ell ≤ health (C - c_seize r pd pc beta) (B - r) pd pc ell ↔
      ell * (1 + beta) ≤ health C B pd pc ell)
  integer_checks : ∀ n (s t : IntegerState n) p i r,
    execute_int s p i r = some t ↔ integer_admissible s p i r ∧ t = liquidate_int s p i r
  integer_collateral : ∀ n (s : IntegerState n) p i r, 0 < p.scale → p.feeFraction ≤ p.scale →
    seize_int p r ≤ s.collateral i →
    (liquidate_int s p i r).collateral i + (liquidate_int s p i r).liquidatorCollateral +
      (liquidate_int s p i r).treasuryCollateral = s.collateral i + s.liquidatorCollateral +
          s.treasuryCollateral
  integer_debt : ∀ n (s : IntegerState n) p i r, r ≤ s.debt →
    s.cash + s.debt = s.reserves + s.liabilities →
    (liquidate_int s p i r).cash + (liquidate_int s p i r).debt =
      (liquidate_int s p i r).reserves + (liquidate_int s p i r).liabilities
  rounding : ∀ W I b r, 0 < W → 0 < I → r ≤ b * I / W → r ≠ b * I / W →
    0 ≤ ((b - shares_burn W I b r : ℕ):ℚ) - ((b : ℚ) - (r : ℚ) * W / I) ∧
    ((b - shares_burn W I b r : ℕ):ℚ) - ((b : ℚ) - (r : ℚ) * W / I) < 1
  full_rounding : ∀ (W I b : ℕ), 0 < W → 0 < I →
    0 ≤ (b : ℚ) - ((b * I / W : ℕ):ℚ) * W / I ∧ (b : ℚ) - ((b * I / W : ℕ):ℚ) * W / I < (W : ℚ) / I

theorem verification_suite : DeFiLendingLiquidationAccountingSuite :=
  ⟨full_repay_iff_close_factor_one, collateral_seize_split_identity, fun _ =>
      liquidation_invariants,
    fun _ => scaled_debt_sum_preserved, fun _ => collateral_asset_conservation,
    health_nondecreasing_iff, fun _ => execute_int_iff, fun _ => integer_collateral_conservation,
    fun _ => integer_debt_balance, partial_shares_rounding, full_shares_rounding⟩

end DeFiLendingLiquidationAccounting
