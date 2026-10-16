/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DeFiLendingLiquidationHealthFactor
import Verification.DeFiKinkedInterestRateUtilization
import Verification.DeFiLendingCompoundInterestIndex
import Verification.DeFiLendingLiquidationAccounting
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! An authorized accounting writeoff, not a proof of economic uncollectibility.
Reserve absorption and supplier loss do not transfer cash or collateral. -/
namespace DeFiLendingBadDebtSocialization
open scoped BigOperators
open DeFiLendingCompoundInterestIndex

/-- An external decision input; no claim about authentication or recoverability. -/
def WriteOffAuthorized (decision : Bool) : Prop := decision = true
instance (a : Bool) : Decidable (WriteOffAuthorized a) := inferInstanceAs (Decidable (_ = _))

def reserve_absorbed (R x : ℚ) : ℚ := min R x
def socialized_haircut (R x : ℚ) : ℚ := x - min R x

theorem loss_split_identity (R x : ℚ) :
    reserve_absorbed R x + socialized_haircut R x = x := by
  simp [reserve_absorbed, socialized_haircut]

theorem socialized_haircut_eq_max (R x : ℚ) : socialized_haircut R x = max (x - R) 0 := by
  unfold socialized_haircut
  by_cases h : R ≤ x
  · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
  · rw [min_eq_right (le_of_not_ge h), max_eq_right (by linarith)]
    ring

theorem loss_bounds (R x : ℚ) (hR : 0 ≤ R) (hx : 0 ≤ x) :
    0 ≤ reserve_absorbed R x ∧ reserve_absorbed R x ≤ R ∧
    0 ≤ socialized_haircut R x ∧ socialized_haircut R x ≤ x := by
  have hm := le_min hR hx
  have hmx := min_le_right R x
  exact ⟨hm, min_le_left _ _, sub_nonneg.mpr hmx, by unfold socialized_haircut; linarith⟩

theorem haircut_zero_iff (R x : ℚ) : socialized_haircut R x = 0 ↔ x ≤ R := by
  rw [socialized_haircut_eq_max]
  constructor
  · intro h; have := le_max_left (x - R) 0; linarith
  · intro h; exact max_eq_right (sub_nonpos.mpr h)

theorem haircut_pos_iff (R x : ℚ) : 0 < socialized_haircut R x ↔ R < x := by
  rw [socialized_haircut_eq_max, lt_max_iff]; simp

theorem haircut_le_liabilities_of_balance (cash B R L x : ℚ)
    (hb : cash + B = R + L) (hc : 0 ≤ cash) (hL : 0 ≤ L) (hx : x ≤ B) :
    socialized_haircut R x ≤ L ∧ 0 ≤ L - socialized_haircut R x := by
  have hh : socialized_haircut R x ≤ L := by
    rw [socialized_haircut_eq_max]; exact max_le (by linarith) hL
  exact ⟨hh, sub_nonneg.mpr hh⟩

theorem balance_sheet_preserved_on_writeoff (cash B R L x : ℚ)
    (hb : cash + B = R + L) :
    cash + (B - x) = (R - reserve_absorbed R x) + (L - socialized_haircut R x) := by
  have := loss_split_identity R x; linarith

theorem net_assets_after_writeoff (cash B R x : ℚ) :
    net_accounting_assets cash (B - x) (R - reserve_absorbed R x) =
      net_accounting_assets cash B R - socialized_haircut R x := by
  simp only [net_accounting_assets, reserve_absorbed, socialized_haircut]; ring

theorem net_assets_preserved_iff_covered_by_reserves (cash B R x : ℚ) :
    net_accounting_assets cash (B - x) (R - reserve_absorbed R x) =
      net_accounting_assets cash B R ↔ x ≤ R := by
  rw [net_assets_after_writeoff, sub_eq_self, haircut_zero_iff]

theorem liabilities_preserved_iff (R L x : ℚ) :
    L - socialized_haircut R x = L ↔ x ≤ R := by rw [sub_eq_self, haircut_zero_iff]

structure State (n : ℕ) where
  pool : PoolState n
  supplierShares : ℚ

def State.Valid {n : ℕ} (s : State n) : Prop := s.pool.Valid ∧ 0 ≤ s.supplierShares
instance {n : ℕ} (s : State n) : Decidable s.Valid := by unfold State.Valid; infer_instance

def admissible {n : ℕ} (a : Bool) (s : State n) (i : Fin n) (x : ℚ) : Prop :=
  WriteOffAuthorized a ∧ s.Valid ∧ 0 ≤ x ∧ x ≤ borrower_debt (s.pool.scaled i) s.pool.index ∧
  borrower_debt (s.pool.scaled i) s.pool.index ≤ s.pool.debt ∧
  socialized_haircut s.pool.reserves x ≤ s.pool.liabilities ∧
  (s.supplierShares = 0 → socialized_haircut s.pool.reserves x = 0)
instance {n : ℕ} (a : Bool) (s : State n) (i : Fin n) (x : ℚ) :
    Decidable (admissible a s i x) := by unfold admissible; infer_instance

def writeoff {n : ℕ} (s : State n) (i : Fin n) (x : ℚ) : State n :=
  { s with pool := { s.pool with
      scaled := (transfer_debt s.pool i (-x)).scaled
      reserves := s.pool.reserves - reserve_absorbed s.pool.reserves x
      liabilities := s.pool.liabilities - socialized_haircut s.pool.reserves x } }

def execute {n : ℕ} (a : Bool) (s : State n) (i : Fin n) (x : ℚ) : Option (State n) :=
  if admissible a s i x then some (writeoff s i x) else none

theorem execute_iff {n : ℕ} (a : Bool) (s t : State n) (i : Fin n) (x : ℚ) :
    execute a s i x = some t ↔ admissible a s i x ∧ t = writeoff s i x := by
  unfold execute; split_ifs <;> simp_all [eq_comm]

theorem execute_rejects {n : ℕ} (a : Bool) (s : State n) (i : Fin n) (x : ℚ) :
    execute a s i x = none ↔ ¬ admissible a s i x := by
  unfold execute; split_ifs <;> simp_all

theorem cash_unchanged_on_writeoff {n : ℕ} (s : State n) (i : Fin n) (x : ℚ) :
    (writeoff s i x).pool.cash = s.pool.cash := rfl

theorem fixed_index_and_supplier_shares {n : ℕ} (s : State n) (i : Fin n) (x : ℚ) :
    (writeoff s i x).pool.index = s.pool.index ∧
    (writeoff s i x).supplierShares = s.supplierShares := ⟨rfl, rfl⟩

theorem scaled_update {n : ℕ} (s : State n) (i : Fin n) (x : ℚ) :
    (writeoff s i x).pool.scaled i = s.pool.scaled i - x / s.pool.index ∧
    ∀ j, j ≠ i → (writeoff s i x).pool.scaled j = s.pool.scaled j :=
  DeFiLendingLiquidationAccounting.shares_update s.pool i x

theorem scaled_debt_consistency_on_writeoff {n : ℕ} (s : State n) (i : Fin n) (x : ℚ)
    (hi : s.pool.index ≠ 0) : (writeoff s i x).pool.debt = s.pool.debt - x :=
  DeFiLendingLiquidationAccounting.scaled_debt_sum_preserved s.pool i x hi

theorem writeoff_valid {n : ℕ} (a : Bool) (s : State n) (i : Fin n) (x : ℚ)
    (h : admissible a s i x) : (writeoff s i x).Valid := by
  rcases h with ⟨_, ⟨hs, hS⟩, _, hx, _, hL, _⟩
  refine ⟨⟨hs.1, sub_nonneg.mpr (min_le_left _ _), sub_nonneg.mpr hL, hs.2.2.2.1, ?_⟩, hS⟩
  intro j
  obtain ⟨he, ho⟩ := scaled_update s i x
  by_cases hj : j = i
  · subst j; rw [he]; exact sub_nonneg.mpr ((div_le_iff₀ hs.2.2.2.1).mpr hx)
  · rw [ho j hj]; exact hs.2.2.2.2 j

theorem writeoff_balance {n : ℕ} (s : State n) (i : Fin n) (x : ℚ)
    (hi : s.pool.index ≠ 0) (hb : s.pool.Balanced) : (writeoff s i x).pool.Balanced := by
  unfold PoolState.Balanced
  rw [scaled_debt_consistency_on_writeoff s i x hi]
  exact balance_sheet_preserved_on_writeoff _ _ _ _ _ hb

theorem writeoff_assets {n : ℕ} (s : State n) (i : Fin n) (x : ℚ)
    (hi : s.pool.index ≠ 0) :
    net_accounting_assets (writeoff s i x).pool.cash (writeoff s i x).pool.debt
      (writeoff s i x).pool.reserves = net_accounting_assets s.pool.cash s.pool.debt
        s.pool.reserves -
      socialized_haircut s.pool.reserves x := by
  rw [scaled_debt_consistency_on_writeoff s i x hi]
  exact net_assets_after_writeoff _ _ _ _

def lp_exchange_rate (L S : ℚ) : ℚ := L / S

theorem lp_exchange_rate_drop (R L S x : ℚ) :
    lp_exchange_rate L S - lp_exchange_rate (L - socialized_haircut R x) S =
      socialized_haircut R x / S := by unfold lp_exchange_rate; ring

theorem lp_exchange_rate_nonincreasing (R L S x : ℚ) (hS : 0 < S) :
    lp_exchange_rate (L - socialized_haircut R x) S ≤ lp_exchange_rate L S := by
  have hh : 0 ≤ socialized_haircut R x := by rw [socialized_haircut_eq_max]; exact le_max_right _ _
  have := div_nonneg hh hS.le
  linarith [lp_exchange_rate_drop R L S x]

theorem lp_exchange_rate_preserved_iff (R L S x : ℚ) (hS : 0 < S) :
    lp_exchange_rate (L - socialized_haircut R x) S = lp_exchange_rate L S ↔ x ≤ R := by
  unfold lp_exchange_rate
  rw [div_left_inj' (ne_of_gt hS), sub_eq_self, haircut_zero_iff]

theorem execute_invariants {n : ℕ} (a : Bool) (s t : State n) (i : Fin n) (x : ℚ)
    (h : execute a s i x = some t) :
    WriteOffAuthorized a ∧ t.Valid ∧ (s.pool.Balanced → t.pool.Balanced) ∧
    t.pool.debt = s.pool.debt - x ∧ t.pool.cash = s.pool.cash ∧
    t.pool.index = s.pool.index ∧ t.supplierShares = s.supplierShares := by
  obtain ⟨hg, rfl⟩ := (execute_iff a s t i x).mp h
  have hi := ne_of_gt hg.2.1.1.2.2.2.1
  exact ⟨hg.1, writeoff_valid a s i x hg, writeoff_balance s i x hi,
    scaled_debt_consistency_on_writeoff s i x hi, rfl, rfl, rfl⟩

/-- Discrete state reuses module 173's separate debt and collateral registers. -/
structure IntegerState (n : ℕ) where
  pool : DeFiLendingLiquidationAccounting.IntegerState n
  supplierShares : ℕ
  deriving DecidableEq, Repr

def reserve_absorbed_int (R x : ℕ) : ℕ := min R x
def haircut_int (R x : ℕ) : ℕ := x - min R x

/-- A zero writeoff is a no-op, even when positive shares display zero debt. -/
def shares_burn_int (W I b x : ℕ) : ℕ :=
  if x = 0 then 0 else DeFiLendingLiquidationAccounting.shares_burn W I b x

def integer_admissible {n : ℕ} (a : Bool) (W : ℕ) (s : IntegerState n) (i : Fin n) (x : ℕ) : Prop :=
  WriteOffAuthorized a ∧ 0 < W ∧ 0 < s.pool.index ∧
  x ≤ individual_int W s.pool.index (s.pool.scaled i) ∧
  individual_int W s.pool.index (s.pool.scaled i) ≤ s.pool.debt ∧
  haircut_int s.pool.reserves x ≤ s.pool.liabilities ∧
  (s.supplierShares = 0 → haircut_int s.pool.reserves x = 0)
instance {n : ℕ} (a : Bool) (W : ℕ) (s : IntegerState n) (i : Fin n) (x : ℕ) :
    Decidable (integer_admissible a W s i x) := by unfold integer_admissible; infer_instance

def writeoff_int {n : ℕ} (W : ℕ) (s : IntegerState n) (i : Fin n) (x : ℕ) : IntegerState n :=
  { s with pool := { s.pool with
      debt := s.pool.debt - x
      reserves := s.pool.reserves - reserve_absorbed_int s.pool.reserves x
      liabilities := s.pool.liabilities - haircut_int s.pool.reserves x
      scaled := fun j => s.pool.scaled j - if j = i then
        shares_burn_int W s.pool.index (s.pool.scaled i) x else 0 } }

def execute_int {n : ℕ} (a : Bool) (W : ℕ) (s : IntegerState n) (i : Fin n) (x : ℕ) :
    Option (IntegerState n) :=
  if integer_admissible a W s i x then some (writeoff_int W s i x) else none

theorem execute_int_iff {n : ℕ} (a : Bool) (W : ℕ) (s t : IntegerState n) (i : Fin n) (x : ℕ) :
    execute_int a W s i x = some t ↔ integer_admissible a W s i x ∧ t = writeoff_int W s i x := by
  unfold execute_int; split_ifs <;> simp_all [eq_comm]

theorem execute_int_rejects {n : ℕ} (a : Bool) (W : ℕ) (s : IntegerState n) (i : Fin n) (x : ℕ) :
    execute_int a W s i x = none ↔ ¬ integer_admissible a W s i x := by
  unfold execute_int; split_ifs <;> simp_all

theorem integer_loss_split (R x : ℕ) :
    reserve_absorbed_int R x + haircut_int R x = x ∧ reserve_absorbed_int R x ≤ R ∧
    haircut_int R x ≤ x := by unfold reserve_absorbed_int haircut_int; omega

theorem integer_haircut_zero_iff (R x : ℕ) : haircut_int R x = 0 ↔ x ≤ R := by
  unfold haircut_int; omega

theorem integer_haircut_pos_iff (R x : ℕ) : 0 < haircut_int R x ↔ R < x := by
  unfold haircut_int; omega

theorem integer_split_cast (R x : ℕ) :
    (reserve_absorbed_int R x : ℚ) = reserve_absorbed R x ∧
    (haircut_int R x : ℚ) = socialized_haircut R x := by
  simp [reserve_absorbed_int, reserve_absorbed, haircut_int, socialized_haircut,
    Nat.cast_sub (min_le_right R x)]

theorem integer_haircut_le_of_balance (cash B R L x : ℕ)
    (hb : cash + B = R + L) (hx : x ≤ B) : haircut_int R x ≤ L := by
  unfold haircut_int; omega

theorem integer_balance_preserved {n : ℕ} (W : ℕ) (s : IntegerState n) (i : Fin n) (x : ℕ)
    (hx : x ≤ s.pool.debt) (hh : haircut_int s.pool.reserves x ≤ s.pool.liabilities)
    (hb : s.pool.cash + s.pool.debt = s.pool.reserves + s.pool.liabilities) :
    (writeoff_int W s i x).pool.cash + (writeoff_int W s i x).pool.debt =
    (writeoff_int W s i x).pool.reserves + (writeoff_int W s i x).pool.liabilities := by
  have := integer_loss_split s.pool.reserves x
  dsimp [writeoff_int]; omega

theorem integer_assets_drop {n : ℕ} (W : ℕ) (s : IntegerState n) (i : Fin n) (x : ℕ)
    (hx : x ≤ s.pool.debt) :
    ((writeoff_int W s i x).pool.cash : ℤ) + (writeoff_int W s i x).pool.debt -
      (writeoff_int W s i x).pool.reserves =
    (s.pool.cash : ℤ) + s.pool.debt - s.pool.reserves - haircut_int s.pool.reserves x := by
  have h := integer_loss_split s.pool.reserves x
  have he : (reserve_absorbed_int s.pool.reserves x : ℤ) + haircut_int s.pool.reserves x = x := by
    exact_mod_cast h.1
  simp only [writeoff_int, Nat.cast_sub hx, Nat.cast_sub h.2.1]
  linarith

theorem shares_burn_int_le (W I b x : ℕ) (hW : 0 < W) (hI : 0 < I) (hx : x ≤ b * I / W) :
    shares_burn_int W I b x ≤ b := by
  unfold shares_burn_int; split_ifs
  · exact Nat.zero_le _
  · exact DeFiLendingLiquidationAccounting.shares_burn_le W I b x hW hI hx

theorem writeoff_int_zero {n : ℕ} (W : ℕ) (s : IntegerState n) (i : Fin n) :
    writeoff_int W s i 0 = s := by
  simp [writeoff_int, reserve_absorbed_int, haircut_int, shares_burn_int]

theorem writeoff_zero {n : ℕ} (s : State n) (i : Fin n) (hR : 0 ≤ s.pool.reserves) :
    writeoff s i 0 = s := by
  simp [writeoff, transfer_debt, reserve_absorbed, socialized_haircut, min_eq_right hR]

theorem execute_int_invariants {n : ℕ} (a : Bool) (W : ℕ) (s t : IntegerState n)
    (i : Fin n) (x : ℕ) (h : execute_int a W s i x = some t) :
    WriteOffAuthorized a ∧
    (s.pool.cash + s.pool.debt = s.pool.reserves + s.pool.liabilities →
      t.pool.cash + t.pool.debt = t.pool.reserves + t.pool.liabilities) ∧
    t.pool.cash = s.pool.cash ∧ t.pool.index = s.pool.index ∧
    t.supplierShares = s.supplierShares ∧ t.pool.collateral = s.pool.collateral ∧
    t.pool.treasuryCollateral = s.pool.treasuryCollateral ∧
    t.pool.liquidatorCollateral = s.pool.liquidatorCollateral ∧
    t.pool.scaled i ≤ s.pool.scaled i ∧
    (∀ j, j ≠ i → t.pool.scaled j = s.pool.scaled j) := by
  obtain ⟨hg, rfl⟩ := (execute_int_iff a W s t i x).mp h
  refine ⟨hg.1, integer_balance_preserved W s i x (le_trans hg.2.2.2.1 hg.2.2.2.2.1)
    hg.2.2.2.2.2.1, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact Nat.sub_le _ _
  · intro j hj; simp [writeoff_int, hj]

/-- Partial burns round down; zero writeoff also has zero error. -/
theorem partial_scaled_error (W I b x : ℕ) (hW : 0 < W) (hI : 0 < I)
    (hx : x ≤ b * I / W) (hne : x ≠ b * I / W) :
    0 ≤ ((b - shares_burn_int W I b x : ℕ) : ℚ) - ((b : ℚ) - (x : ℚ) * W / I) ∧
    ((b - shares_burn_int W I b x : ℕ) : ℚ) - ((b : ℚ) - (x : ℚ) * W / I) < 1 := by
  by_cases hz : x = 0
  · subst x; simp [shares_burn_int]
  · simpa [shares_burn_int, hz] using
      DeFiLendingLiquidationAccounting.partial_shares_rounding W I b x hW hI hx hne

theorem positive_full_writeoff_clears (W I b : ℕ) (hx : 0 < b * I / W) :
    b - shares_burn_int W I b (b * I / W) = 0 := by
  simp [shares_burn_int, ne_of_gt hx, DeFiLendingLiquidationAccounting.shares_burn]

theorem full_scaled_residual_bound (W I b : ℕ) (hW : 0 < W) (hI : 0 < I) :
    0 ≤ (b : ℚ) - ((b * I / W : ℕ) : ℚ) * W / I ∧
    (b : ℚ) - ((b * I / W : ℕ) : ℚ) * W / I < (W : ℚ) / I :=
  DeFiLendingLiquidationAccounting.full_shares_rounding W I b hW hI

/-- Undefined without issued supplier shares; do not interpret Nat division by zero as a price. -/
def lp_exchange_rate_int (W L S : ℕ) : Option ℕ := if S = 0 then none else some (L * W / S)

theorem lp_exchange_rate_int_zero (W L : ℕ) : lp_exchange_rate_int W L 0 = none := by
  simp [lp_exchange_rate_int]

theorem lp_rate_floor_error (W L S : ℕ) :
    0 ≤ (L : ℚ) * W / S - (L * W / S : ℕ) ∧
    (L : ℚ) * W / S - (L * W / S : ℕ) < 1 := by
  have h := DeFiKinkedInterestRateUtilization.floor_div_bounds (L * W) S
  push_cast at h
  constructor <;> linarith [h.1, h.2]

theorem lp_rate_int_nonincreasing (W L S h : ℕ) :
    (L - h) * W / S ≤ L * W / S := Nat.div_le_div_right (Nat.mul_le_mul_right W (Nat.sub_le L h))

/-- The difference of two rounded prices has signed error strictly between -1 and 1. -/
theorem lp_rate_drop_error (W L S h : ℕ) (hh : h ≤ L) :
    -1 < ((L * W / S : ℕ) : ℚ) - (( (L - h) * W / S : ℕ) : ℚ) - (h : ℚ) * W / S ∧
    ((L * W / S : ℕ) : ℚ) - (((L - h) * W / S : ℕ) : ℚ) - (h : ℚ) * W / S < 1 := by
  have h₁ := lp_rate_floor_error W L S
  have h₂ := lp_rate_floor_error W (L - h) S
  rw [Nat.cast_sub hh] at h₂
  have he : ((L : ℚ) - h) * W / S = (L : ℚ) * W / S - (h : ℚ) * W / S := by ring
  rw [he] at h₂
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

theorem ledger_gap_update {n : ℕ} (W : ℕ) (s : IntegerState n) (i : Fin n) (x : ℕ)
    (hx : x ≤ s.pool.debt) :
    ledger_index_gap (writeoff_int W s i x).pool.debt W s.pool.index (writeoff_int W s i
      x).pool.scaled =
    ledger_index_gap s.pool.debt W s.pool.index s.pool.scaled +
      aggregate_int W s.pool.index s.pool.scaled -
      aggregate_int W s.pool.index (writeoff_int W s i x).pool.scaled - (x : ℤ) := by
  simp only [ledger_index_gap, writeoff_int, Nat.cast_sub hx]; ring

theorem post_writeoff_reconciliation {n : ℕ} (W : ℕ) (s : IntegerState n) (i : Fin n) (x : ℕ)
    (hW : 0 < W) (hn : 0 < n) :
    recon_dust W s.pool.index (writeoff_int W s i x).pool.scaled ≤ n - 1 ∧
    ((writeoff_int W s i x).pool.debt : ℤ) -
      ∑ j, (individual_int W s.pool.index ((writeoff_int W s i x).pool.scaled j) : ℤ) =
      ledger_index_gap (writeoff_int W s i x).pool.debt W s.pool.index (writeoff_int W s i
        x).pool.scaled +
      recon_dust W s.pool.index (writeoff_int W s i x).pool.scaled :=
  ⟨(recon_dust_bounds _ _ _ hW hn).2, ledger_reconciliation_identity _ _ _ _ hW⟩


theorem rejects_unauthorized {n : ℕ} (s : State n) (i : Fin n) (x : ℚ) :
    execute false s i x = none := by simp [execute, admissible, WriteOffAuthorized]

theorem integer_rejects_unauthorized {n : ℕ} (W : ℕ) (s : IntegerState n) (i : Fin n) (x : ℕ) :
    execute_int false W s i x = none := by simp [execute_int, integer_admissible,
      WriteOffAuthorized]

theorem integer_rejects_no_suppliers {n : ℕ} (a : Bool) (W : ℕ) (s : IntegerState n)
    (i : Fin n) (x : ℕ) (hS : s.supplierShares = 0) (hh : 0 < haircut_int s.pool.reserves x) :
    execute_int a W s i x = none := by
  rw [execute_int_rejects]
  intro h
  have := h.2.2.2.2.2.2 hS
  omega

theorem integer_no_underflow {n : ℕ} (a : Bool) (W : ℕ) (s : IntegerState n) (i : Fin n) (x : ℕ)
    (h : integer_admissible a W s i x) :
    x ≤ s.pool.debt ∧ reserve_absorbed_int s.pool.reserves x ≤ s.pool.reserves ∧
    haircut_int s.pool.reserves x ≤ s.pool.liabilities ∧
    shares_burn_int W s.pool.index (s.pool.scaled i) x ≤ s.pool.scaled i :=
  ⟨le_trans h.2.2.2.1 h.2.2.2.2.1, (integer_loss_split _ _).2.1, h.2.2.2.2.2.1,
    shares_burn_int_le W _ _ x h.2.1 h.2.2.1 h.2.2.2.1⟩

/-- The independent ledger can change when the rounded scaled balance does not. -/
theorem ledger_gap_not_recon_dust :
    shares_burn_int 10 100 1 1 = 0 ∧
    ledger_index_gap 9 10 100 (fun _ : Fin 1 => 1) = -1 ∧
    recon_dust 10 100 (fun _ : Fin 1 => 1) = 0 := by
  norm_num [shares_burn_int, DeFiLendingLiquidationAccounting.shares_burn,
    ledger_index_gap, aggregate_int, recon_dust, individual_int]

structure DeFiLendingBadDebtSocializationSuite : Prop where
  split : ∀ R x, reserve_absorbed R x + socialized_haircut R x = x
  bounds : ∀ R x, 0 ≤ R → 0 ≤ x →
    0 ≤ reserve_absorbed R x ∧ reserve_absorbed R x ≤ R ∧
    0 ≤ socialized_haircut R x ∧ socialized_haircut R x ≤ x
  threshold : ∀ R x, socialized_haircut R x = 0 ↔ x ≤ R
  balance : ∀ cash B R L x, cash + B = R + L →
    cash + (B - x) = (R - reserve_absorbed R x) + (L - socialized_haircut R x)
  coverage : ∀ cash B R L x, cash + B = R + L → 0 ≤ cash → 0 ≤ L → x ≤ B →
    socialized_haircut R x ≤ L ∧ 0 ≤ L - socialized_haircut R x
  assets : ∀ cash B R x,
    net_accounting_assets cash (B - x) (R - reserve_absorbed R x) =
      net_accounting_assets cash B R - socialized_haircut R x
  rational_checks : ∀ n a (s t : State n) i x,
    execute a s i x = some t ↔ admissible a s i x ∧ t = writeoff s i x
  valid_transition : ∀ n a (s : State n) i x, admissible a s i x → (writeoff s i x).Valid
  scaled : ∀ n (s : State n) i x, s.pool.index ≠ 0 →
    (writeoff s i x).pool.debt = s.pool.debt - x
  lp_drop : ∀ R L S x, lp_exchange_rate L S - lp_exchange_rate (L - socialized_haircut R x) S =
    socialized_haircut R x / S
  lp_threshold : ∀ R L S x, 0 < S →
    (lp_exchange_rate (L - socialized_haircut R x) S = lp_exchange_rate L S ↔ x ≤ R)
  integer_checks : ∀ n a W (s t : IntegerState n) i x,
    execute_int a W s i x = some t ↔ integer_admissible a W s i x ∧ t = writeoff_int W s i x
  integer_balance : ∀ n W (s : IntegerState n) i x, x ≤ s.pool.debt →
    haircut_int s.pool.reserves x ≤ s.pool.liabilities →
    s.pool.cash + s.pool.debt = s.pool.reserves + s.pool.liabilities →
    (writeoff_int W s i x).pool.cash + (writeoff_int W s i x).pool.debt =
      (writeoff_int W s i x).pool.reserves + (writeoff_int W s i x).pool.liabilities
  share_rounding : ∀ W I b x, 0 < W → 0 < I → x ≤ b * I / W → x ≠ b * I / W →
    0 ≤ ((b - shares_burn_int W I b x : ℕ) : ℚ) - ((b : ℚ) - (x : ℚ) * W / I) ∧
    ((b - shares_burn_int W I b x : ℕ) : ℚ) - ((b : ℚ) - (x : ℚ) * W / I) < 1
  lp_rounding : ∀ (W L S : ℕ), 0 ≤ (L : ℚ) * W / S - (L * W / S : ℕ) ∧
    (L : ℚ) * W / S - (L * W / S : ℕ) < 1
  rejects_no_suppliers : ∀ n a W (s : IntegerState n) i x,
    s.supplierShares = 0 → 0 < haircut_int s.pool.reserves x → execute_int a W s i x = none

theorem verification_suite : DeFiLendingBadDebtSocializationSuite :=
  ⟨loss_split_identity, loss_bounds, haircut_zero_iff, balance_sheet_preserved_on_writeoff,
    haircut_le_liabilities_of_balance, net_assets_after_writeoff, fun _ => execute_iff,
    fun _ => writeoff_valid, fun _ => scaled_debt_consistency_on_writeoff,
    lp_exchange_rate_drop, lp_exchange_rate_preserved_iff, fun _ => execute_int_iff,
    fun _ => integer_balance_preserved, partial_scaled_error, lp_rate_floor_error,
    fun _ => integer_rejects_no_suppliers⟩

end DeFiLendingBadDebtSocialization
