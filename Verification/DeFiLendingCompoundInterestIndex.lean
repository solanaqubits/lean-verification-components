/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DeFiLendingLiquidationHealthFactor
import Verification.DeFiKinkedInterestRateUtilization
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact accrual accounting and an explicitly rounded reference implementation.
No assertion of recoverability, withdrawal liquidity or deployed-contract refinement. -/
namespace DeFiLendingCompoundInterestIndex
open scoped BigOperators

abbrev Rates := DeFiKinkedInterestRateUtilization.KinkRateParams

def accrue_index (I rate dt : ℚ) : ℚ := I * (1 + rate * dt)

theorem accrue_index_ge (I rate dt : ℚ) (hI : 0 ≤ I) (hr : 0 ≤ rate) (ht : 0 ≤ dt) :
    I ≤ accrue_index I rate dt := by
  have := mul_nonneg hI (mul_nonneg hr ht)
  dsimp [accrue_index]; nlinarith

theorem accrue_index_pos (I rate dt : ℚ) (hI : 0 < I) (hr : 0 ≤ rate) (ht : 0 ≤ dt) :
    0 < accrue_index I rate dt := lt_of_lt_of_le hI (accrue_index_ge _ _ _ hI.le hr ht)

theorem accrue_index_zero_dt (I r : ℚ) : accrue_index I r 0 = I := by simp [accrue_index]
theorem accrue_index_zero_rate (I t : ℚ) : accrue_index I 0 t = I := by simp [accrue_index]

theorem subdivision_identity (I r t₁ t₂ : ℚ) :
    accrue_index (accrue_index I r t₁) r t₂ = 
      accrue_index I r (t₁ + t₂) + I * r ^ 2 * t₁ * t₂ := by
  simp only [accrue_index]; ring

theorem subdivision_compounding_strict_gt (I r t₁ t₂ : ℚ)
    (hI : 0 < I) (hr : 0 < r) (h₁ : 0 < t₁) (h₂ : 0 < t₂) :
    accrue_index I r (t₁ + t₂) < accrue_index (accrue_index I r t₁) r t₂ := by
  rw [subdivision_identity]
  exact lt_add_of_pos_right _ (mul_pos (mul_pos (mul_pos hI (pow_pos hr _)) h₁) h₂)

def accrue_chain (I : ℚ) (steps : List (ℚ × ℚ)) : ℚ :=
  steps.foldl (fun J s => accrue_index J s.1 s.2) I

theorem accrue_chain_product (steps : List (ℚ × ℚ)) (I : ℚ) :
    accrue_chain I steps = I * (steps.map (fun s => 1 + s.1 * s.2)).prod := by
  induction steps generalizing I with
  | nil => simp [accrue_chain]
  | cons s ss ih =>
    simpa [accrue_chain, accrue_index, mul_assoc] using ih (accrue_index I s.1 s.2)

theorem accrue_chain_ge (steps : List (ℚ × ℚ)) (I : ℚ) (hI : 0 ≤ I)
    (hs : ∀ s ∈ steps, 0 ≤ s.1 ∧ 0 ≤ s.2) : I ≤ accrue_chain I steps := by
  induction steps generalizing I with
  | nil => simp [accrue_chain]
  | cons s ss ih =>
    have h := hs s (by simp)
    have hi := accrue_index_ge I s.1 s.2 hI h.1 h.2
    exact hi.trans (ih _ (hI.trans hi) (fun x hx => hs x (by simp [hx])))

def borrower_debt (b I : ℚ) : ℚ := b * I
def total_debt_from_scaled {n : ℕ} (b : Fin n → ℚ) (I : ℚ) : ℚ := (∑ i, b i) * I

theorem sum_borrower_debt_eq_total {n : ℕ} (b : Fin n → ℚ) (I : ℚ) :
    ∑ i, borrower_debt (b i) I = total_debt_from_scaled b I := by
  simp [borrower_debt, total_debt_from_scaled, Finset.sum_mul]

theorem debt_accrual_identity {n : ℕ} (b : Fin n → ℚ) (I r t : ℚ) :
    total_debt_from_scaled b (accrue_index I r t) = 
      total_debt_from_scaled b I + total_debt_from_scaled b I * r * t := by
  simp only [total_debt_from_scaled, accrue_index]; ring

theorem sum_debt_increments {n : ℕ} (b : Fin n → ℚ) (I r t : ℚ) :
    ∑ i, (borrower_debt (b i) (accrue_index I r t) - borrower_debt (b i) I) = 
      total_debt_from_scaled b I * r * t := by
  rw [Finset.sum_sub_distrib, sum_borrower_debt_eq_total, sum_borrower_debt_eq_total,
    debt_accrual_identity]; ring

def net_accounting_assets (cash B R : ℚ) : ℚ := cash + B - R

theorem net_assets_growth_identity (cash B R rho interest : ℚ) :
    net_accounting_assets cash (B + interest) (R + rho * interest) -
      net_accounting_assets cash B R = (1 - rho) * interest := by
  simp only [net_accounting_assets]; ring

theorem net_assets_nondecreasing (cash B R rho r t : ℚ)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (ht : 0 ≤ t) (hρ : rho ≤ 1) :
    net_accounting_assets cash B R ≤
      net_accounting_assets cash (B + B * r * t) (R + rho * (B * r * t)) := by
  have := mul_nonneg (sub_nonneg.mpr hρ) (mul_nonneg (mul_nonneg hB hr) ht)
  rw [← net_assets_growth_identity cash B R rho (B * r * t)] at this
  linarith

theorem balance_sheet_conservation (cash B R L rho interest : ℚ)
    (h : cash + B = R + L) : cash + (B + interest) = (R + rho * interest) + (L + (1 - rho) *
        interest) := by
  linear_combination h

theorem reserve_cash_bound_preserved_iff (cash R rho interest : ℚ) :
    R + rho * interest ≤ cash ↔ rho * interest ≤ cash - R := by constructor <;> intro h <;> linarith

/-- Total debt is derived from shares, avoiding an unproved independent ledger equality. -/
structure PoolState (n : ℕ) where
  cash : ℚ
  reserves : ℚ
  liabilities : ℚ
  index : ℚ
  scaled : Fin n → ℚ

def PoolState.debt {n : ℕ} (s : PoolState n) : ℚ := total_debt_from_scaled s.scaled s.index

def PoolState.Valid {n : ℕ} (s : PoolState n) : Prop :=
  0 ≤ s.cash ∧ 0 ≤ s.reserves ∧ 0 ≤ s.liabilities ∧ 0 < s.index ∧ ∀ i, 0 ≤ s.scaled i

def PoolState.Balanced {n : ℕ} (s : PoolState n) : Prop :=
  s.cash + s.debt = s.reserves + s.liabilities

theorem debt_nonneg {n : ℕ} (s : PoolState n) (h : s.Valid) : 0 ≤ s.debt :=
  mul_nonneg (Finset.sum_nonneg (fun i _ => h.2.2.2.2 i)) h.2.2.2.1.le

def accrue {n : ℕ} (s : PoolState n) (r dt rho : ℚ) : PoolState n :=
  { s with index := accrue_index s.index r dt
           reserves := s.reserves + rho * (s.debt * r * dt)
           liabilities := s.liabilities + (1 - rho) * (s.debt * r * dt) }

/-- Guards describe local input admissibility, not the conservation conclusion. -/
def AccrueStep {n : ℕ} (s s' : PoolState n) (r dt rho : ℚ) : Prop :=
  s.Valid ∧ 0 ≤ r ∧ 0 ≤ dt ∧ 0 ≤ rho ∧ rho ≤ 1 ∧ s' = accrue s r dt rho

theorem accrue_debt {n : ℕ} (s : PoolState n) (r t rho : ℚ) :
    (accrue s r t rho).debt = s.debt + s.debt * r * t := debt_accrual_identity _ _ _ _

theorem accrue_preserves_valid {n : ℕ} (s : PoolState n) (r t rho : ℚ)
    (hs : s.Valid) (hr : 0 ≤ r) (ht : 0 ≤ t) (hρ : 0 ≤ rho) (hρ₁ : rho ≤ 1) :
    (accrue s r t rho).Valid := by
  have hi := mul_nonneg (mul_nonneg (debt_nonneg s hs) hr) ht
  exact ⟨hs.1, add_nonneg hs.2.1 (mul_nonneg hρ hi),
    add_nonneg hs.2.2.1 (mul_nonneg (sub_nonneg.mpr hρ₁) hi),
    accrue_index_pos _ _ _ hs.2.2.2.1 hr ht, hs.2.2.2.2⟩

theorem accrue_preserves_balance {n : ℕ} (s : PoolState n) (r t rho : ℚ)
    (h : s.Balanced) : (accrue s r t rho).Balanced := by
  unfold PoolState.Balanced
  rw [accrue_debt]
  exact balance_sheet_conservation _ _ _ _ _ _ h

theorem accrue_step_invariants {n : ℕ} {s s' : PoolState n} {r t rho : ℚ}
    (h : AccrueStep s s' r t rho) (hb : s.Balanced) :
    s'.Valid ∧ s'.Balanced ∧ s'.cash = s.cash ∧ s'.scaled = s.scaled := by
  rcases h with ⟨hs, hr, ht, hρ, hρ₁, rfl⟩
  exact ⟨accrue_preserves_valid s r t rho hs hr ht hρ hρ₁,
    accrue_preserves_balance s r t rho hb, rfl, rfl⟩

/-- Signed share change; public transition predicates enforce borrowing/repayment guards. -/
def transfer_debt {n : ℕ} (s : PoolState n) (k : Fin n) (amount : ℚ) : PoolState n :=
  { s with cash := s.cash - amount
           scaled := fun i => s.scaled i + if i = k then amount / s.index else 0 }

theorem transfer_debt_total {n : ℕ} (s : PoolState n) (k : Fin n) (a : ℚ)
    (hI : s.index ≠ 0) : (transfer_debt s k a).debt = s.debt + a := by
  simp [PoolState.debt, total_debt_from_scaled, transfer_debt, Finset.sum_add_distrib,
    add_mul, div_mul_cancel₀ _ hI]

def BorrowStep {n : ℕ} (s s' : PoolState n) (k : Fin n) (a : ℚ) : Prop :=
  s.Valid ∧ 0 ≤ a ∧ a ≤ s.cash ∧ s' = transfer_debt s k a

def RepayStep {n : ℕ} (s s' : PoolState n) (k : Fin n) (a : ℚ) : Prop :=
  s.Valid ∧ 0 ≤ a ∧ a ≤ borrower_debt (s.scaled k) s.index ∧ s' = transfer_debt s k (-a)

theorem transfer_preserves_balance {n : ℕ} (s : PoolState n) (k : Fin n) (a : ℚ)
    (hI : s.index ≠ 0) (hb : s.Balanced) : (transfer_debt s k a).Balanced := by
  unfold PoolState.Balanced
  rw [transfer_debt_total s k a hI]
  change s.cash - a + (s.debt + a) = s.reserves + s.liabilities
  dsimp [PoolState.Balanced] at hb
  linarith

theorem borrow_step_invariants {n : ℕ} {s s' : PoolState n} {k : Fin n} {a : ℚ}
    (h : BorrowStep s s' k a) (hb : s.Balanced) :
    s'.Valid ∧ s'.Balanced ∧ s'.index = s.index ∧ s'.debt = s.debt + a := by
  rcases h with ⟨hs, ha, hcash, rfl⟩
  have hi := ne_of_gt hs.2.2.2.1
  refine ⟨?_, transfer_preserves_balance s k a hi hb, rfl, transfer_debt_total s k a hi⟩
  refine ⟨sub_nonneg.mpr hcash, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
  intro i
  dsimp [transfer_debt]
  split_ifs
  · exact add_nonneg (hs.2.2.2.2 i) (div_nonneg ha hs.2.2.2.1.le)
  · simpa using hs.2.2.2.2 i

theorem repay_step_invariants {n : ℕ} {s s' : PoolState n} {k : Fin n} {a : ℚ}
    (h : RepayStep s s' k a) (hb : s.Balanced) :
    s'.Valid ∧ s'.Balanced ∧ s'.index = s.index ∧ s'.debt = s.debt - a := by
  rcases h with ⟨hs, ha, hdebt, rfl⟩
  have hi := ne_of_gt hs.2.2.2.1
  refine ⟨?_, transfer_preserves_balance s k (-a) hi hb, rfl, ?_⟩
  · refine ⟨by change 0 ≤ s.cash - (-a); linarith [hs.1], hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
    intro i
    dsimp [transfer_debt]
    split_ifs with he
    · subst i
      have hd : a / s.index ≤ s.scaled k := (div_le_iff₀ hs.2.2.2.1).mpr hdebt
      rw [neg_div]; linarith
    · simpa using hs.2.2.2.2 i
  · simpa [sub_eq_add_neg] using transfer_debt_total s k (-a) hi

instance {n : ℕ} (s : PoolState n) : Decidable s.Valid := by
  unfold PoolState.Valid; infer_instance

def execute_accrue {n : ℕ} (s : PoolState n) (r t rho : ℚ) : Option (PoolState n) :=
  if s.Valid ∧ 0 ≤ r ∧ 0 ≤ t ∧ 0 ≤ rho ∧ rho ≤ 1 then some (accrue s r t rho) else none

def execute_borrow {n : ℕ} (s : PoolState n) (k : Fin n) (a : ℚ) : Option (PoolState n) :=
  if s.Valid ∧ 0 ≤ a ∧ a ≤ s.cash then some (transfer_debt s k a) else none

def execute_repay {n : ℕ} (s : PoolState n) (k : Fin n) (a : ℚ) : Option (PoolState n) :=
  if s.Valid ∧ 0 ≤ a ∧ a ≤ borrower_debt (s.scaled k) s.index
  then some (transfer_debt s k (-a)) else none

theorem execute_accrue_iff {n : ℕ} (s s' : PoolState n) (r t rho : ℚ) :
    execute_accrue s r t rho = some s' ↔ AccrueStep s s' r t rho := by
  simp only [execute_accrue, AccrueStep]
  split_ifs with h
  · simp only [Option.some.injEq]; tauto
  · tauto

theorem execute_borrow_iff {n : ℕ} (s s' : PoolState n) (k : Fin n) (a : ℚ) :
    execute_borrow s k a = some s' ↔ BorrowStep s s' k a := by
  simp only [execute_borrow, BorrowStep]
  split_ifs with h
  · simp only [Option.some.injEq]; tauto
  · tauto

theorem execute_repay_iff {n : ℕ} (s s' : PoolState n) (k : Fin n) (a : ℚ) :
    execute_repay s k a = some s' ↔ RepayStep s s' k a := by
  simp only [execute_repay, RepayStep]
  split_ifs with h
  · simp only [Option.some.injEq]; tauto
  · tauto

theorem kink_rate_accrual_pos (P : Rates) (I u dt : ℚ) (hI : 0 < I)
    (hu : 0 ≤ u) (ht : 0 ≤ dt) :
    0 < accrue_index I (DeFiKinkedInterestRateUtilization.borrow_rate P u) dt :=
  accrue_index_pos _ _ _ hI (DeFiKinkedInterestRateUtilization.borrow_rate_nonneg P hu) ht

theorem utilization_after_accrual_iff (cash B R rho r t : ℚ)
    (hB : 0 < B + B * r * t) (hA : 0 < cash + (B + B * r * t) - (R + rho * (B * r * t))) :
    DeFiKinkedInterestRateUtilization.utilization cash (B + B * r * t) (R + rho * (B * r * t)) ≤ 1 ↔
      rho * (B * r * t) ≤ cash - R := by
  rw [DeFiKinkedInterestRateUtilization.utilization_le_one_iff hB hA]
  exact reserve_cash_bound_preserved_iff _ _ _ _

theorem utilization_exceeds_one_after_accrual_counterexample :
    (5:ℚ) ≤ 10 ∧ DeFiKinkedInterestRateUtilization.utilization 10 100 5 ≤ 1 ∧
    10 < (5:ℚ) + (1 / 2) * (100 * (1 / 5) * 1) ∧
    1 < DeFiKinkedInterestRateUtilization.utilization 10 120 15 ∧
    0 < net_accounting_assets 10 100 5 ∧
    net_accounting_assets 10 100 5 < net_accounting_assets 10 120 15 := by
  norm_num [DeFiKinkedInterestRateUtilization.utilization,
      DeFiKinkedInterestRateUtilization.denominator, net_accounting_assets]

/-- Positive scale and reserve-factor guard are checked by the executable interface. -/
structure DiscreteState where
  cash : ℕ
  debt : ℕ
  reserves : ℕ
  liabilities : ℕ
  index : ℕ
  deriving DecidableEq, Repr

def interest_floor (W B rate dt : ℕ) : ℕ := B * rate * dt / W
def index_floor (W I rate dt : ℕ) : ℕ := I + I * rate * dt / W

def accrue_discrete (s : DiscreteState) (W rate dt rho : ℕ) : Option DiscreteState :=
  if W = 0 ∨ W < rho ∨ s.index = 0 then none else
    let interest := interest_floor W s.debt rate dt
    let reserve := rho * interest / W
    some {s with debt := s.debt + interest, reserves := s.reserves + reserve,
                 liabilities := s.liabilities + (interest - reserve),
                 index := index_floor W s.index rate dt}

theorem reserve_split_le (W rho interest : ℕ) (hW : 0 < W) (hρ : rho ≤ W) :
    rho * interest / W ≤ interest := by
  apply (Nat.div_le_iff_le_mul_add_pred hW).mpr
  nlinarith

theorem discrete_balance_conservation (s : DiscreteState) (W rate dt rho : ℕ)
    (hW : 0 < W) (hρ : rho ≤ W) (hb : s.cash + s.debt = s.reserves + s.liabilities) :
    s.cash + (s.debt + interest_floor W s.debt rate dt) = 
      (s.reserves + rho * interest_floor W s.debt rate dt / W) + 
      (s.liabilities + (interest_floor W s.debt rate dt - rho * interest_floor W s.debt rate dt /
          W)) := by
  have := reserve_split_le W rho (interest_floor W s.debt rate dt) hW hρ
  omega

theorem accrue_discrete_spec {s s' : DiscreteState} {W rate dt rho : ℕ}
    (h : accrue_discrete s W rate dt rho = some s') :
    0 < W ∧ rho ≤ W ∧ 0 < s'.index ∧ s.index ≤ s'.index ∧
      s.cash = s'.cash ∧ s.debt ≤ s'.debt ∧
      (s.cash + s.debt = s.reserves + s.liabilities → s'.cash + s'.debt = s'.reserves +
          s'.liabilities) := by
  unfold accrue_discrete at h
  split_ifs at h with hg
  · simp only [Option.some.injEq] at h
    subst s'
    have hW : 0 < W := by omega
    have hρ : rho ≤ W := by omega
    refine ⟨hW, hρ, ?_, ?_, rfl, Nat.le_add_right _ _, ?_⟩
    · exact Nat.add_pos_left (show 0 < s.index by omega) _
    · exact Nat.le_add_right _ _
    · exact discrete_balance_conservation s W rate dt rho hW hρ

theorem interest_floor_error (W B r t : ℕ) :
    0 ≤ (B:ℚ) * r * t / W - interest_floor W B r t ∧
      (B:ℚ) * r * t / W - interest_floor W B r t < 1 := by
  have h := DeFiKinkedInterestRateUtilization.floor_div_bounds (B * r * t) W
  dsimp [interest_floor]
  push_cast at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem index_floor_error (W I r t : ℕ) (hW : 0 < W) :
    0 ≤ accrue_index ((I:ℚ) / W) ((r:ℚ) / W) t - (index_floor W I r t:ℚ) / W ∧
      accrue_index ((I:ℚ) / W) ((r:ℚ) / W) t - (index_floor W I r t:ℚ) / W < 1 / (W:ℚ) := by
  have h := interest_floor_error W I r t
  have hw : (0:ℚ) < W := by exact_mod_cast hW
  have he : accrue_index ((I:ℚ) / W) ((r:ℚ) / W) t - (index_floor W I r t:ℚ) / W = 
      ((I:ℚ) * r * t / W - interest_floor W I r t) / W := by
    simp only [accrue_index, index_floor, interest_floor, Nat.cast_add]
    ring
  rw [he]
  exact ⟨div_nonneg h.1 hw.le, (div_lt_div_iff_of_pos_right hw).mpr h.2⟩

theorem reserve_floor_error (W rho interest : ℕ) :
    0 ≤ (rho:ℚ) * interest / W - (rho * interest / W:ℕ) ∧
      (rho:ℚ) * interest / W - (rho * interest / W:ℕ) < 1 := by
  have h := DeFiKinkedInterestRateUtilization.floor_div_bounds (rho * interest) W
  push_cast at h
  constructor <;> linarith [h.1, h.2]

theorem supplier_split_error (W rho interest : ℕ) (hW : 0 < W) (hρ : rho ≤ W) :
    0 ≤ ((interest - rho * interest / W:ℕ):ℚ) - (1 - (rho:ℚ) / W) * interest ∧
      ((interest - rho * interest / W:ℕ):ℚ) - (1 - (rho:ℚ) / W) * interest < 1 := by
  have h := reserve_floor_error W rho interest
  rw [Nat.cast_sub (reserve_split_le W rho interest hW hρ)]
  have he : (interest:ℚ) - (rho * interest / W:ℕ) - (1 - (rho:ℚ) / W) * interest = 
      (rho:ℚ) * interest / W - (rho * interest / W:ℕ) := by ring
  rw [he]
  exact h

theorem ledger_index_gap_counterexample :
    interest_floor 10 10 1 1 = 1 ∧ index_floor 10 1 1 1 = 1 ∧
    (100 * index_floor 10 1 1 1 / 10 : ℕ) = 10 ∧
    10 + interest_floor 10 10 1 1 > 100 * index_floor 10 1 1 1 / 10 := by
  norm_num [interest_floor, index_floor]

def individual_int (W I : ℕ) (b : ℕ) : ℕ := b * I / W
def aggregate_int {n : ℕ} (W I : ℕ) (b : Fin n → ℕ) : ℕ := (∑ i, b i) * I / W
def recon_dust {n : ℕ} (W I : ℕ) (b : Fin n → ℕ) : ℕ :=
  aggregate_int W I b - ∑ i, individual_int W I (b i)

theorem sum_individual_le_aggregate {n : ℕ} (W I : ℕ) (b : Fin n → ℕ) (hW : 0 < W) :
    ∑ i, individual_int W I (b i) ≤ aggregate_int W I b := by
  apply (Nat.le_div_iff_mul_le hW).mpr
  change (∑ i, b i * I / W) * W ≤ (∑ i, b i) * I
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => Nat.div_mul_le_self (b i * I) W)

theorem recon_dust_bounds {n : ℕ} (W I : ℕ) (b : Fin n → ℕ) (hW : 0 < W) (hn : 0 < n) :
    (∑ i, individual_int W I (b i) ≤ aggregate_int W I b) ∧ recon_dust W I b ≤ n - 1 := by
  have hlo := sum_individual_le_aggregate W I b hW
  have hsum : (∑ i, b i * I) < ∑ i, (b i * I / W + 1) * W := by
    apply Finset.sum_lt_sum
    · intro i _; simpa [mul_comm] using (Nat.lt_mul_div_succ (b i * I) hW).le
    · refine ⟨⟨0, hn⟩, Finset.mem_univ _, ?_⟩
      simpa [mul_comm] using Nat.lt_mul_div_succ (b ⟨0, hn⟩ * I) hW
  have he : (∑ i, (b i * I / W + 1) * W) = ((∑ i, individual_int W I (b i)) + n) * W := by
    simp [individual_int, Finset.sum_mul, Finset.sum_add_distrib, add_mul]
  rw [he, ← Finset.sum_mul] at hsum
  have hup : aggregate_int W I b < (∑ i, individual_int W I (b i)) + n :=
    (Nat.div_lt_iff_lt_mul hW).mpr hsum
  refine ⟨hlo, ?_⟩
  dsimp [recon_dust]; omega

theorem recon_dust_empty (W I : ℕ) (b : Fin 0 → ℕ) : recon_dust W I b = 0 := by
  simp [recon_dust, aggregate_int]

theorem recon_dust_nonzero_counterexample :
    aggregate_int 10 15 (fun _ : Fin 2 => 1) = 3 ∧
    (∑ i : Fin 2, individual_int 10 15 ((fun _ : Fin 2 => 1) i)) = 2 ∧
    recon_dust 10 15 (fun _ : Fin 2 => 1) = 1 := by
  norm_num [aggregate_int, individual_int, recon_dust, Fin.sum_univ_two]

/-- Signed discrepancy between an independently accrued ledger and index-derived aggregate.
The n-1 reconciliation bound does not bound this separate discrepancy. -/
def ledger_index_gap {n : ℕ} (B W I : ℕ) (b : Fin n → ℕ) : ℤ :=
  (B:ℤ) - aggregate_int W I b

theorem ledger_reconciliation_identity {n : ℕ} (B W I : ℕ) (b : Fin n → ℕ) (hW : 0 < W) :
    (B:ℤ) - ∑ i, (individual_int W I (b i):ℤ) = 
      ledger_index_gap B W I b + recon_dust W I b := by
  have h := sum_individual_le_aggregate W I b hW
  simp only [ledger_index_gap, recon_dust, Nat.cast_sub h, Nat.cast_sum]
  ring

structure DeFiLendingCompoundInterestIndexSuite : Prop where
  index_positive : ∀ I r t, 0 < I → 0 ≤ r → 0 ≤ t → 0 < accrue_index I r t
  composition : ∀ steps I, accrue_chain I steps = I * (steps.map (fun s => 1 + s.1 * s.2)).prod
  subdivision : ∀ I r t u, 0 < I → 0 < r → 0 < t → 0 < u →
    accrue_index I r (t + u) < accrue_index (accrue_index I r t) r u
  debt_sum : ∀ n (b : Fin n → ℚ) I, (∑ i, borrower_debt (b i) I) = total_debt_from_scaled b I
  accounting : ∀ (c B R L rho d : ℚ), c + B = R + L → c + (B + d) = (R + rho * d) + (L + (1 - rho)
      * d)
  reserve_bound : ∀ (c R rho d : ℚ), R + rho * d ≤ c ↔ rho * d ≤ c - R
  accrue_transition : ∀ n (s s' : PoolState n) r t rho, AccrueStep s s' r t rho →
    s.Balanced → s'.Valid ∧ s'.Balanced ∧ s'.cash = s.cash ∧ s'.scaled = s.scaled
  borrow_transition : ∀ n (s s' : PoolState n) k a, BorrowStep s s' k a →
    s.Balanced → s'.Valid ∧ s'.Balanced ∧ s'.index = s.index ∧ s'.debt = s.debt + a
  repay_transition : ∀ n (s s' : PoolState n) k a, RepayStep s s' k a →
    s.Balanced → s'.Valid ∧ s'.Balanced ∧ s'.index = s.index ∧ s'.debt = s.debt - a
  integer_transition : ∀ s s' W r t rho, accrue_discrete s W r t rho = some s' →
    0 < W ∧ rho ≤ W ∧ 0 < s'.index ∧ s.index ≤ s'.index ∧ s.cash = s'.cash ∧
    s.debt ≤ s'.debt ∧ (s.cash + s.debt = s.reserves + s.liabilities →
      s'.cash + s'.debt = s'.reserves + s'.liabilities)
  rounding : ∀ (W I r t : ℕ), 0 < W →
    0 ≤ accrue_index ((I:ℚ) / W) ((r:ℚ) / W) t - (index_floor W I r t:ℚ) / W ∧
    accrue_index ((I:ℚ) / W) ((r:ℚ) / W) t - (index_floor W I r t:ℚ) / W < 1 / (W:ℚ)
  reconciliation : ∀ n W I (b : Fin n → ℕ), 0 < W → 0 < n →
    (∑ i, individual_int W I (b i) ≤ aggregate_int W I b) ∧ recon_dust W I b ≤ n - 1

theorem verification_suite : DeFiLendingCompoundInterestIndexSuite where
  index_positive := accrue_index_pos
  composition := accrue_chain_product
  subdivision := subdivision_compounding_strict_gt
  debt_sum := fun _ => sum_borrower_debt_eq_total
  accounting := balance_sheet_conservation
  reserve_bound := reserve_cash_bound_preserved_iff
  accrue_transition := fun _ _ _ _ _ _ => accrue_step_invariants
  borrow_transition := fun _ _ _ _ _ => borrow_step_invariants
  repay_transition := fun _ _ _ _ _ => repay_step_invariants
  integer_transition := fun _ _ _ _ _ _ => accrue_discrete_spec
  rounding := index_floor_error
  reconciliation := fun _ => recon_dust_bounds

end DeFiLendingCompoundInterestIndex
