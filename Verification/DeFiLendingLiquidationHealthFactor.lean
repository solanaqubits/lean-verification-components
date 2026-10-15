/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DeFiOvercollateralizedLending
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Lending liquidation with explicit coverage conditions

Exact rational multi-collateral reference accounting. Debt is valued in a common
numeraire. Oracle prices stay fixed during a settlement. No pool-wide solvency,
market execution or deployed protocol correspondence is asserted.
-/
namespace DeFiLendingLiquidationHealthFactor
open scoped BigOperators

structure Position (n : ℕ) where
  quantity : Fin n → ℚ
  price : Fin n → ℚ
  lt : Fin n → ℚ
  ltv : Fin n → ℚ
  debt : ℚ
  deriving DecidableEq

def Position.Valid (p : Position n) : Prop :=
  0 ≤ p.debt ∧ ∀ i, 0 ≤ p.quantity i ∧ 0 < p.price i ∧
    0 ≤ p.ltv i ∧ p.ltv i ≤ p.lt i ∧ p.lt i ≤ 1
instance (p : Position n) : Decidable p.Valid := inferInstanceAs (Decidable (_ ∧ _))

def collateralValue (p : Position n) : ℚ := ∑ i, p.price i * p.quantity i
def weightedValue (p : Position n) : ℚ := ∑ i, p.lt i * (p.price i * p.quantity i)
def borrowLimit (p : Position n) : ℚ := ∑ i, p.ltv i * (p.price i * p.quantity i)
/-- None denotes a debt-free position, not a numeric zero health factor. -/
def healthFactor (p : Position n) : Option ℚ :=
  if p.debt = 0 then none else some (weightedValue p / p.debt)
def liquidatable (p : Position n) : Prop := 0 < p.debt ∧ weightedValue p < p.debt
instance (p : Position n) : Decidable (liquidatable p) := inferInstanceAs (Decidable (_ ∧ _))
def covered (p : Position n) : Prop := p.debt ≤ collateralValue p
instance (p : Position n) : Decidable (covered p) := inferInstanceAs (Decidable (_ ≤ _))

theorem weighted_bounds (p : Position n) (h : p.Valid) :
    0 ≤ borrowLimit p ∧ borrowLimit p ≤ weightedValue p ∧ weightedValue p ≤ collateralValue p := by
  have hc i : 0 ≤ p.price i * p.quantity i := mul_nonneg (h.2 i).2.1.le (h.2 i).1
  refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (h.2 i).2.2.1 (hc i)), ?_, ?_⟩
  · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (h.2 i).2.2.2.1 (hc i))
  · exact Finset.sum_le_sum (fun i _ => mul_le_of_le_one_left (hc i) (h.2 i).2.2.2.2)

theorem debt_free (p : Position n) (h : p.debt = 0) :
    healthFactor p = none ∧ ¬ liquidatable p := by simp [healthFactor, liquidatable, h]

theorem liquidatable_iff_health (p : Position n) (h : 0 < p.debt) :
    liquidatable p ↔ ∃ v, healthFactor p = some v ∧ v < 1 := by
  simp [healthFactor, ne_of_gt h, liquidatable, h, div_lt_one₀ h]

theorem borrowing_admission_safe (p : Position n) (h : p.Valid)
    (hb : p.debt ≤ borrowLimit p) : ¬ liquidatable p ∧ covered p := by
  have hw := weighted_bounds p h
  exact ⟨fun hl => (not_lt_of_ge (hb.trans hw.2.1)) hl.2, hb.trans (hw.2.1.trans hw.2.2)⟩

/-- At fixed balances, thresholds and debt, raising collateral prices raises W. -/
def reprice (p : Position n) (prices : Fin n → ℚ) : Position n := { p with price := prices }

theorem reprice_weighted_mono (p : Position n) (h : p.Valid) (prices : Fin n → ℚ)
    (hp : ∀ i, p.price i ≤ prices i) : weightedValue p ≤ weightedValue (reprice p prices) := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hp i) (h.2 i).1)
    ((h.2 i).2.2.1.trans (h.2 i).2.2.2.1)

theorem reprice_health_mono (p : Position n) (h : p.Valid) (hd : 0 < p.debt)
    (prices : Fin n → ℚ) (hp : ∀ i, p.price i ≤ prices i) :
    weightedValue p / p.debt ≤ weightedValue (reprice p prices) / p.debt :=
  div_le_div_of_nonneg_right (reprice_weighted_mono p h prices hp) hd.le

/-- Algebraic HF difference; hypotheses exclude zero and fully repaid debt. -/
theorem health_change_identity (W B t r β : ℚ) (hB : 0 < B) (hr : r < B) :
    (W - t * ((1 + β) * r)) / (B - r) - W / B =
      r * (W / B - t * (1 + β)) / (B - r) := by
  field_simp [ne_of_gt hB, ne_of_gt (sub_pos.mpr hr)]
  ring

theorem health_improves_iff (W B t r β : ℚ) (hr : 0 < r) (hB : r < B) :
    W / B < (W - t * ((1 + β) * r)) / (B - r) ↔ t * (1 + β) < W / B := by
  have hi := health_change_identity W B t r β (hr.trans hB) hB
  rw [← sub_pos, hi, div_pos_iff_of_pos_right (sub_pos.mpr hB), mul_pos_iff_of_pos_left hr]
  exact sub_pos

theorem health_nondecreases_iff (W B t r β : ℚ) (hr : 0 < r) (hB : r < B) :
    W / B ≤ (W - t * ((1 + β) * r)) / (B - r) ↔ t * (1 + β) ≤ W / B := by
  have hi := health_change_identity W B t r β (hr.trans hB) hB
  rw [← sub_nonneg, hi, le_div_iff₀ (sub_pos.mpr hB), zero_mul,
    mul_nonneg_iff_of_pos_left hr]
  exact sub_nonneg

theorem coverage_gap_identity (C B r β : ℚ) :
    (C - (1 + β) * r) - (B - r) = C - B - β * r := by ring

theorem residual_coverage_iff (C B r β : ℚ) :
    B - r ≤ C - (1 + β) * r ↔ β * r ≤ C - B := by constructor <;> intro h <;> nlinarith

/-- Settlement records actual seized units; admission is a separate check. -/
def settle (p : Position n) (k : Fin n) (r s : ℚ) : Position n :=
  { p with quantity := fun i => p.quantity i - if i = k then s else 0, debt := p.debt - r }

theorem settle_valid (p : Position n) (hp : p.Valid) (k : Fin n) (r s : ℚ)
    (hr : r ≤ p.debt) (hs : s ≤ p.quantity k) : (settle p k r s).Valid := by
  refine ⟨sub_nonneg.mpr hr, fun i => ?_⟩
  refine ⟨?_, (hp.2 i).2⟩
  by_cases hi : i = k
  · subst i; simpa [settle] using sub_nonneg.mpr hs
  · simpa [settle, hi] using (hp.2 i).1

theorem settle_collateral (p : Position n) (k : Fin n) (r s : ℚ) :
    collateralValue (settle p k r s) = collateralValue p - p.price k * s := by
  simp [collateralValue, settle, mul_sub, mul_ite, Finset.sum_sub_distrib]

theorem settle_weighted (p : Position n) (k : Fin n) (r s : ℚ) :
    weightedValue (settle p k r s) = weightedValue p - p.lt k * (p.price k * s) := by
  simp [weightedValue, settle, mul_sub, mul_ite, Finset.sum_sub_distrib]

def seize (p : Position n) (k : Fin n) (r β : ℚ) : ℚ := (1 + β) * r / p.price k

theorem seize_value (p : Position n) (hp : p.Valid) (k : Fin n) (r β : ℚ) :
    p.price k * seize p k r β = (1 + β) * r := by
  exact mul_div_cancel₀ _ (ne_of_gt (hp.2 k).2.1)

def admissible (p : Position n) (k : Fin n) (r β close : ℚ) : Prop :=
  p.Valid ∧ liquidatable p ∧ 0 < r ∧ r ≤ p.debt ∧ 0 ≤ β ∧
    0 < close ∧ close ≤ 1 ∧ r ≤ close * p.debt ∧ seize p k r β ≤ p.quantity k
instance (p : Position n) (k : Fin n) (r β close : ℚ) : Decidable (admissible p k r β close) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Full repayment is a distinct branch; its health factor is None. -/
def execute (p : Position n) (k : Fin n) (r β close : ℚ) : Option (Position n) :=
  if admissible p k r β close then
    if r = p.debt then some (settle p k p.debt (seize p k r β))
    else some (settle p k r (seize p k r β))
  else none

theorem execute_eq (p : Position n) (k : Fin n) (r β close : ℚ) :
    execute p k r β close =
      if admissible p k r β close then some (settle p k r (seize p k r β)) else none := by
  unfold execute
  split <;> simp_all

theorem execute_success_iff (p : Position n) (k : Fin n) (r β close : ℚ) :
    (execute p k r β close).isSome = true ↔ admissible p k r β close := by
  rw [execute_eq]; split <;> simp_all

theorem execute_spec (p t : Position n) (k : Fin n) (r β close : ℚ)
    (he : execute p k r β close = some t) :
    admissible p k r β close ∧ t = settle p k r (seize p k r β) ∧ t.Valid ∧
      collateralValue t = collateralValue p - (1 + β) * r ∧
      weightedValue t = weightedValue p - p.lt k * ((1 + β) * r) := by
  rw [execute_eq] at he
  split at he <;> try contradiction
  rename_i h
  cases Option.some.inj he
  exact ⟨h, rfl, settle_valid p h.1 k r _ h.2.2.2.1 h.2.2.2.2.2.2.2.2,
    by rw [settle_collateral, seize_value p h.1],
    by rw [settle_weighted, seize_value p h.1]⟩

theorem execute_full_repayment (p t : Position n) (k : Fin n) (β close : ℚ)
    (h : execute p k p.debt β close = some t) : healthFactor t = none ∧ ¬ liquidatable t := by
  have ht := (execute_spec p t k p.debt β close h).2.1
  apply debt_free
  rw [ht]
  simp [settle]

theorem execute_coverage_iff (p t : Position n) (k : Fin n) (r β close : ℚ)
    (h : execute p k r β close = some t) : covered t ↔ β * r ≤ collateralValue p - p.debt := by
  have ht := execute_spec p t k r β close h
  unfold covered
  rw [ht.2.2.2.1, ht.2.1]
  exact residual_coverage_iff _ _ _ _

theorem execute_partial_health (p t : Position n) (k : Fin n) (r β close : ℚ)
    (he : execute p k r β close = some t) (hr : r < p.debt) :
    healthFactor t = some ((weightedValue p - p.lt k * ((1 + β) * r)) / (p.debt - r)) ∧
    weightedValue t / t.debt - weightedValue p / p.debt =
      r * (weightedValue p / p.debt - p.lt k * (1 + β)) / (p.debt - r) := by
  have h := execute_spec p t k r β close he
  have hd : t.debt = p.debt - r := by rw [h.2.1]; rfl
  constructor
  · simp [healthFactor, hd, ne_of_gt (sub_pos.mpr hr), h.2.2.2.2]
  · rw [hd, h.2.2.2.2]
    exact health_change_identity _ _ _ _ _ h.1.2.1.1 hr

def executeCovered (p : Position n) (k : Fin n) (r β close : ℚ) : Option (Position n) :=
  if β * r ≤ collateralValue p - p.debt then execute p k r β close else none

theorem executeCovered_spec (p t : Position n) (k : Fin n) (r β close : ℚ)
    (he : executeCovered p k r β close = some t) :
    t.Valid ∧ covered t ∧ collateralValue t - t.debt = collateralValue p - p.debt - β * r := by
  unfold executeCovered at he
  split at he <;> try contradiction
  rename_i hc
  have h := execute_spec p t k r β close he
  refine ⟨h.2.2.1, (execute_coverage_iff p t k r β close he).mpr hc, ?_⟩
  rw [h.2.2.2.1, h.2.1]
  exact coverage_gap_identity _ _ _ _

structure LiquidationStep (n : ℕ) where
  asset : Fin n
  repayment : ℚ
  bonus : ℚ
  close : ℚ

def executeChain (p : Position n) : List (LiquidationStep n) → Option (Position n)
  | [] => some p
  | a :: as => (executeCovered p a.asset a.repayment a.bonus a.close).bind
      (fun t => executeChain t as)

def bonusCost (as : List (LiquidationStep n)) : ℚ :=
  (as.map (fun a => a.bonus * a.repayment)).sum

theorem covered_chain (as : List (LiquidationStep n)) (p t : Position n)
    (hp : p.Valid) (hc : covered p) (he : executeChain p as = some t) :
    t.Valid ∧ covered t ∧
      collateralValue t - t.debt = collateralValue p - p.debt - bonusCost as := by
  induction as generalizing p with
  | nil => cases Option.some.inj he; exact ⟨hp, hc, by simp [bonusCost]⟩
  | cons a as ih =>
    obtain ⟨u, hu, ht⟩ := Option.bind_eq_some_iff.mp he
    have hs := executeCovered_spec p u a.asset a.repayment a.bonus a.close hu
    have hi := ih u hs.1 hs.2.1 ht
    refine ⟨hi.1, hi.2.1, ?_⟩
    rw [hi.2.2, hs.2.2]
    simp [bonusCost]
    ring

/-- The rounding surplus is retained by the borrower, not paid to the liquidator. -/
theorem rounded_coverage (p : Position n) (k : Fin n) (r s β : ℚ)
    (hs : p.price k * s ≤ (1 + β) * r) (hc : β * r ≤ collateralValue p - p.debt) :
    covered (settle p k r s) := by
  unfold covered
  rw [settle_collateral]
  change p.debt - r ≤ collateralValue p - p.price k * s
  nlinarith

theorem rounded_health_lower_bound (p : Position n) (hp : p.Valid) (k : Fin n)
    (r s β : ℚ) (hr : r < p.debt) (hs : p.price k * s ≤ (1 + β) * r) :
    (weightedValue p - p.lt k * ((1 + β) * r)) / (p.debt - r) ≤
      weightedValue (settle p k r s) / (p.debt - r) := by
  rw [settle_weighted]
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hr.le)
  have ht := mul_le_mul_of_nonneg_left hs ((hp.2 k).2.2.1.trans (hp.2 k).2.2.2.1)
  linarith

structure DiscretePosition (n : ℕ) where
  quantity : Fin n → ℕ
  price : Fin n → ℚ
  lt : Fin n → ℚ
  ltv : Fin n → ℚ
  debt : ℕ
  deriving DecidableEq

def DiscretePosition.lift (p : DiscretePosition n) : Position n :=
  ⟨fun i => p.quantity i, p.price, p.lt, p.ltv, p.debt⟩

def DiscretePosition.settle (p : DiscretePosition n) (k : Fin n) (r s : ℕ) : DiscretePosition n :=
  { p with quantity := fun i => p.quantity i - if i = k then s else 0, debt := p.debt - r }

theorem discrete_settle_lift (p : DiscretePosition n) (k : Fin n) (r s : ℕ)
    (hr : r ≤ p.debt) (hs : s ≤ p.quantity k) :
    (p.settle k r s).lift = settle p.lift k r s := by
  have hq : ∀ i, (if i = k then s else 0) ≤ p.quantity i := by
    intro i; split <;> simp_all
  cases p
  simp only [DiscretePosition.settle, DiscretePosition.lift, settle]
  congr 1
  · funext i
    rw [Nat.cast_sub (hq i)]
    simp
  · exact Nat.cast_sub hr

def floorSeizure (p : DiscretePosition n) (k : Fin n) (r : ℕ) (β : ℚ) : ℕ :=
  ⌊seize p.lift k r β⌋₊

def ceilRepayment (p : DiscretePosition n) (k : Fin n) (s : ℕ) (β : ℚ) : ℕ :=
  ⌈p.price k * s / (1 + β)⌉₊

theorem floor_seizure_error (p : DiscretePosition n) (hp : p.lift.Valid)
    (k : Fin n) (r : ℕ) (β : ℚ) (hb : 0 ≤ β) :
    0 ≤ seize p.lift k r β - (floorSeizure p k r β : ℚ) ∧
      seize p.lift k r β - (floorSeizure p k r β : ℚ) < 1 := by
  have hn : 0 ≤ seize p.lift k r β :=
    div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg r)) (hp.2 k).2.1.le
  have hl := Nat.floor_le hn
  have hu := Nat.lt_floor_add_one (seize p.lift k r β)
  exact ⟨sub_nonneg.mpr hl, by dsimp [floorSeizure]; linarith⟩

theorem ceil_repayment_error (p : DiscretePosition n) (hp : p.lift.Valid)
    (k : Fin n) (s : ℕ) (β : ℚ) (hb : 0 ≤ β) :
    0 ≤ (ceilRepayment p k s β : ℚ) - p.price k * s / (1 + β) ∧
      (ceilRepayment p k s β : ℚ) - p.price k * s / (1 + β) < 1 := by
  have hn := div_nonneg (mul_nonneg (hp.2 k).2.1.le (Nat.cast_nonneg s))
    (show 0 ≤ 1 + β by linarith)
  have hl := Nat.le_ceil (p.price k * s / (1 + β))
  have hu := Nat.ceil_lt_add_one hn
  change (⌈p.price k * s / (1 + β)⌉₊ : ℚ) < p.price k * s / (1 + β) + 1 at hu
  exact ⟨sub_nonneg.mpr hl, by dsimp [ceilRepayment]; linarith⟩

theorem ceil_repayment_minimal (p : DiscretePosition n) (k : Fin n) (s r : ℕ)
    (β : ℚ) (hb : 0 ≤ β) :
    ceilRepayment p k s β ≤ r ↔ p.price k * s ≤ (1 + β) * r := by
  rw [ceilRepayment, Nat.ceil_le, div_le_iff₀ (show 0 < 1 + β by linarith)]
  rw [mul_comm (r : ℚ)]

def discreteAdmissible (p : DiscretePosition n) (k : Fin n) (r s : ℕ) (β close : ℚ) : Prop :=
  p.lift.Valid ∧ liquidatable p.lift ∧ 0 < r ∧ r ≤ p.debt ∧ 0 ≤ β ∧
    0 < close ∧ close ≤ 1 ∧ (r : ℚ) ≤ close * p.debt ∧ s ≤ p.quantity k ∧
      p.price k * s ≤ (1 + β) * r
instance (p : DiscretePosition n) (k : Fin n) (r s : ℕ) (β close : ℚ) :
    Decidable (discreteAdmissible p k r s β close) := inferInstanceAs (Decidable (_ ∧ _))

/-- The common executable integer settlement guard checks actual amounts. -/
def executeDiscrete (p : DiscretePosition n) (k : Fin n) (r s : ℕ) (β close : ℚ) :
    Option (DiscretePosition n) :=
  if discreteAdmissible p k r s β close then some (p.settle k r s) else none

def executeFloor (p : DiscretePosition n) (k : Fin n) (r : ℕ) (β close : ℚ) :=
  executeDiscrete p k r (floorSeizure p k r β) β close

def executeCeil (p : DiscretePosition n) (k : Fin n) (s : ℕ) (β close : ℚ) :=
  executeDiscrete p k (ceilRepayment p k s β) s β close

theorem execute_discrete_spec (p t : DiscretePosition n) (k : Fin n) (r s : ℕ) (β close : ℚ)
    (he : executeDiscrete p k r s β close = some t) :
    discreteAdmissible p k r s β close ∧ t.lift = settle p.lift k r s ∧ t.lift.Valid ∧
      (β * r ≤ collateralValue p.lift - p.debt → covered t.lift) := by
  unfold executeDiscrete at he
  split at he <;> try contradiction
  rename_i h
  cases Option.some.inj he
  have ht := discrete_settle_lift p k r s h.2.2.2.1 h.2.2.2.2.2.2.2.2.1
  refine ⟨h, ht, ?_, ?_⟩
  · rw [ht]
    apply settle_valid _ h.1
    · change (r : ℚ) ≤ (p.debt : ℚ)
      exact_mod_cast h.2.2.2.1
    · change (s : ℚ) ≤ (p.quantity k : ℚ)
      exact_mod_cast h.2.2.2.2.2.2.2.2.1
  · intro hc
    rw [ht]
    exact rounded_coverage _ _ _ _ _ h.2.2.2.2.2.2.2.2.2 hc

theorem floor_seizure_value (p : DiscretePosition n) (hp : p.lift.Valid)
    (k : Fin n) (r : ℕ) (β : ℚ) (hb : 0 ≤ β) :
    p.price k * floorSeizure p k r β ≤ (1 + β) * r := by
  have hf := sub_nonneg.mp (floor_seizure_error p hp k r β hb).1
  have hm := mul_le_mul_of_nonneg_left hf (hp.2 k).2.1.le
  rw [seize_value p.lift hp] at hm
  exact hm

theorem ceil_repayment_value (p : DiscretePosition n) (k : Fin n) (s : ℕ) (β : ℚ)
    (hb : 0 ≤ β) : p.price k * s ≤ (1 + β) * ceilRepayment p k s β :=
  (ceil_repayment_minimal p k s _ β hb).mp (le_refl _)

theorem execute_floor_spec (p t : DiscretePosition n) (k : Fin n) (r : ℕ) (β close : ℚ)
    (he : executeFloor p k r β close = some t) :
    t.lift.Valid ∧ (β * r ≤ collateralValue p.lift - p.debt → covered t.lift) :=
  (execute_discrete_spec p t k r _ β close he).2.2

theorem execute_ceil_spec (p t : DiscretePosition n) (k : Fin n) (s : ℕ) (β close : ℚ)
    (he : executeCeil p k s β close = some t) : t.lift.Valid ∧
    (β * ceilRepayment p k s β ≤ collateralValue p.lift - p.debt → covered t.lift) :=
  (execute_discrete_spec p t k _ s β close he).2.2

theorem execute_discrete_full (p t : DiscretePosition n) (k : Fin n) (s : ℕ) (β close : ℚ)
    (he : executeDiscrete p k p.debt s β close = some t) :
    healthFactor t.lift = none ∧ ¬ liquidatable t.lift := by
  have ht := (execute_discrete_spec p t k p.debt s β close he).2.1
  apply debt_free
  rw [ht]
  simp [settle, DiscretePosition.lift]

/-- Exact single-collateral identity, with no claim of unconditional improvement. -/
theorem single_health_change (C B LT r β : ℚ) (hB : 0 < B) (hr : r < B) :
    LT * (C - (1 + β) * r) / (B - r) - LT * C / B =
      r * (LT * C / B - LT * (1 + β)) / (B - r) := by
  rw [mul_sub]
  exact health_change_identity _ _ _ _ _ hB hr

/-- A nonempty rational model, also used for explicit negative regressions. -/
def oneAsset (C B LT LTV : ℚ) : Position 1 :=
  ⟨fun _ => C, fun _ => 1, fun _ => LT, fun _ => LTV, B⟩

theorem liquidation_can_worsen_health :
    let p := oneAsset 100 95 (4/5) (3/4)
    let t := settle p 0 50 (55 : ℚ)
    execute p 0 50 (1/10) 1 = some t ∧
      healthFactor p = some (16/19) ∧ healthFactor t = some (4/5) ∧
      (4/5 : ℚ) < 16/19 := by
  norm_num [oneAsset, execute_eq, admissible, Position.Valid, liquidatable, weightedValue,
    healthFactor, settle, seize]

theorem liquidation_can_create_position_deficit :
    let p := oneAsset 100 95 (4/5) (3/4)
    let t := settle p 0 50 (60 : ℚ)
    covered p ∧ execute p 0 50 (1/5) 1 = some t ∧ ¬ covered t ∧
      executeCovered p 0 50 (1/5) 1 = none := by
  norm_num [oneAsset, executeCovered, execute_eq, admissible, Position.Valid, liquidatable,
    covered, collateralValue, weightedValue, settle, seize]

/-- Positive scalar instances embed in the existing real lending model. -/
def legacyPosition (C B LT : ℚ) (hc : 0 < C) (hb : 0 < B) (ht : 0 < LT) (hu : LT < 1) :
    DeFiOvercollateralizedLending.LendingPosition where
  collateral := C
  debt := B
  priceC := 1
  priceD := 1
  lt := LT
  h_c_pos := by exact_mod_cast hc
  h_d_pos := by exact_mod_cast hb
  h_pc_pos := by norm_num
  h_pd_pos := by norm_num
  h_lt_pos := by exact_mod_cast ht
  h_lt_lt_one := by exact_mod_cast hu

theorem real_health_bridge (C B LT : ℚ) (hc : 0 < C) (hb : 0 < B)
    (ht : 0 < LT) (hu : LT < 1) :
    ((LT * C / B : ℚ) : ℝ) =
      DeFiOvercollateralizedLending.healthFactor (legacyPosition C B LT hc hb ht hu) := by
  simp only [DeFiOvercollateralizedLending.healthFactor,
    DeFiOvercollateralizedLending.collateralValue, DeFiOvercollateralizedLending.debtValue,
    legacyPosition, Rat.cast_div, Rat.cast_mul, mul_one]
  ring

theorem debt_value_health_antitone (p : Position n) (hp : p.Valid) (hB : 0 < p.debt)
    (B : ℚ) (h : p.debt ≤ B) : weightedValue p / B ≤ weightedValue p / p.debt := by
  have hw := weighted_bounds p hp
  exact div_le_div_of_nonneg_left (hw.1.trans hw.2.1) hB h

theorem rounded_health_nondecreases (p : Position n) (hp : p.Valid) (k : Fin n)
    (r s β : ℚ) (hr : 0 < r) (hB : r < p.debt)
    (hs : p.price k * s ≤ (1 + β) * r)
    (hh : p.lt k * (1 + β) ≤ weightedValue p / p.debt) :
    weightedValue p / p.debt ≤ weightedValue (settle p k r s) / (p.debt - r) :=
  ((health_nondecreases_iff _ _ _ _ _ hr hB).mpr hh).trans
    (rounded_health_lower_bound p hp k r s β hB hs)

/-- Optional conservative guard for the integer settlement, separate from admission. -/
def executeDiscreteCovered (p : DiscretePosition n) (k : Fin n) (r s : ℕ) (β close : ℚ) :=
  if β * r ≤ collateralValue p.lift - p.debt then executeDiscrete p k r s β close else none

theorem execute_discrete_covered (p t : DiscretePosition n) (k : Fin n) (r s : ℕ) (β close : ℚ)
    (he : executeDiscreteCovered p k r s β close = some t) : t.lift.Valid ∧ covered t.lift := by
  unfold executeDiscreteCovered at he
  split at he <;> try contradiction
  rename_i hc
  have h := (execute_discrete_spec p t k r s β close he).2.2
  exact ⟨h.1, h.2 hc⟩

structure DeFiLendingLiquidationHealthFactorSuite : Prop where
  debt_zero : ∀ n (p : Position n), p.debt = 0 → healthFactor p = none ∧ ¬ liquidatable p
  threshold : ∀ n (p : Position n), 0 < p.debt →
    (liquidatable p ↔ ∃ v, healthFactor p = some v ∧ v < 1)
  weights : ∀ n (p : Position n), p.Valid →
    0 ≤ borrowLimit p ∧ borrowLimit p ≤ weightedValue p ∧ weightedValue p ≤ collateralValue p
  price_monotone : ∀ n (p : Position n), p.Valid → 0 < p.debt →
    ∀ prices, (∀ i, p.price i ≤ prices i) →
      weightedValue p / p.debt ≤ weightedValue (reprice p prices) / p.debt
  health_identity : ∀ (C B LT r β : ℚ), 0 < B → r < B →
    LT * (C - (1 + β) * r) / (B - r) - LT * C / B =
      r * (LT * C / B - LT * (1 + β)) / (B - r)
  improvement : ∀ (W B t r β : ℚ), 0 < r → r < B →
    (W / B < (W - t * ((1 + β) * r)) / (B - r) ↔ t * (1 + β) < W / B)
  coverage : ∀ (C B r β : ℚ), (B - r ≤ C - (1 + β) * r ↔ β * r ≤ C - B)
  execution : ∀ n (p : Position n) k r β close,
    ((execute p k r β close).isSome = true ↔ admissible p k r β close)
  full_repayment : ∀ n (p t : Position n) k β close,
    execute p k p.debt β close = some t → healthFactor t = none ∧ ¬ liquidatable t
  coverage_guard : ∀ n (p t : Position n) k r β close,
    executeCovered p k r β close = some t → t.Valid ∧ covered t ∧
      collateralValue t - t.debt = collateralValue p - p.debt - β * r
  chain : ∀ n as (p t : Position n), p.Valid → covered p → executeChain p as = some t →
    t.Valid ∧ covered t ∧ collateralValue t - t.debt = collateralValue p - p.debt - bonusCost as
  floor_error : ∀ n (p : DiscretePosition n), p.lift.Valid → ∀ k (r : ℕ) β, 0 ≤ β →
    0 ≤ seize p.lift k r β - (floorSeizure p k r β : ℚ) ∧
      seize p.lift k r β - (floorSeizure p k r β : ℚ) < 1
  ceil_error : ∀ n (p : DiscretePosition n), p.lift.Valid → ∀ k s β, 0 ≤ β →
    0 ≤ (ceilRepayment p k s β : ℚ) - p.price k * s / (1 + β) ∧
      (ceilRepayment p k s β : ℚ) - p.price k * s / (1 + β) < 1
  ceil_minimal : ∀ n (p : DiscretePosition n) k s r β, 0 ≤ β →
    (ceilRepayment p k s β ≤ r ↔ p.price k * s ≤ (1 + β) * r)
  integer_guard : ∀ n (p t : DiscretePosition n) k r s β close,
    executeDiscreteCovered p k r s β close = some t → t.lift.Valid ∧ covered t.lift
  integer_execution : ∀ n (p t : DiscretePosition n) k r s β close,
    executeDiscrete p k r s β close = some t → t.lift.Valid ∧
      (β * r ≤ collateralValue p.lift - p.debt → covered t.lift)

theorem verification_suite : DeFiLendingLiquidationHealthFactorSuite where
  debt_zero := fun _ => debt_free
  threshold := fun _ => liquidatable_iff_health
  weights := fun _ => weighted_bounds
  price_monotone := fun _ => reprice_health_mono
  health_identity := single_health_change
  improvement := health_improves_iff
  coverage := residual_coverage_iff
  execution := fun _ => execute_success_iff
  full_repayment := fun _ => execute_full_repayment
  coverage_guard := fun _ => executeCovered_spec
  chain := fun _ => covered_chain
  floor_error := fun _ => floor_seizure_error
  ceil_error := fun _ => ceil_repayment_error
  ceil_minimal := fun _ => ceil_repayment_minimal
  integer_guard := fun _ => execute_discrete_covered
  integer_execution := fun _ p t k r s β close he =>
    (execute_discrete_spec p t k r s β close he).2.2

end DeFiLendingLiquidationHealthFactor
