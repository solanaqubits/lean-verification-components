/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DeFiLendingLiquidationHealthFactor
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact instantaneous rates, not a solvency or compound-interest model.
The integer reference algorithm uses unbounded naturals and a specified rounding
order; no equivalence to deployed Compound/Aave bytecode is asserted. -/
namespace DeFiKinkedInterestRateUtilization

def denominator (cash borrows reserves : ℚ) : ℚ := cash + borrows - reserves

def utilization (cash borrows reserves : ℚ) : ℚ :=
  if borrows = 0 then 0 else borrows / denominator cash borrows reserves

def ValidPoolState (cash borrows reserves : ℚ) : Prop :=
  0 ≤ cash ∧ 0 ≤ borrows ∧ 0 ≤ reserves ∧ (0 < borrows → 0 < denominator cash borrows reserves)

instance (cash borrows reserves : ℚ) : Decidable (ValidPoolState cash borrows reserves) := by
  unfold ValidPoolState; infer_instance

def checked_utilization (cash borrows reserves : ℚ) : Option ℚ :=
  if ValidPoolState cash borrows reserves then some (utilization cash borrows reserves) else none

theorem utilization_zero (cash reserves : ℚ) : utilization cash 0 reserves = 0 := by
  simp [utilization]

theorem utilization_pos {cash borrows reserves : ℚ} (hb : 0 < borrows)
    (hd : 0 < denominator cash borrows reserves) : 0 < utilization cash borrows reserves := by
  simp only [utilization, if_neg (ne_of_gt hb)]
  exact div_pos hb hd

theorem utilization_nonneg {cash borrows reserves : ℚ}
    (h : ValidPoolState cash borrows reserves) : 0 ≤ utilization cash borrows reserves := by
  by_cases hb : borrows = 0
  · simp [hb, utilization]
  · exact (utilization_pos (lt_of_le_of_ne h.2.1 (Ne.symm hb))
      (h.2.2.2 (lt_of_le_of_ne h.2.1 (Ne.symm hb)))).le

theorem utilization_le_one_iff {cash borrows reserves : ℚ} (hb : 0 < borrows)
    (hd : 0 < denominator cash borrows reserves) :
    utilization cash borrows reserves ≤ 1 ↔ reserves ≤ cash := by
  simp only [utilization, if_neg (ne_of_gt hb), div_le_one hd]
  dsimp [denominator]; constructor <;> intro h <;> linarith

theorem utilization_in_unit_interval {cash borrows reserves : ℚ}
    (h : ValidPoolState cash borrows reserves) (hr : reserves ≤ cash) :
    0 ≤ utilization cash borrows reserves ∧ utilization cash borrows reserves ≤ 1 := by
  refine ⟨utilization_nonneg h, ?_⟩
  by_cases hb : borrows = 0
  · simp [hb, utilization]
  · have hp := lt_of_le_of_ne h.2.1 (Ne.symm hb)
    exact (utilization_le_one_iff hp (h.2.2.2 hp)).mpr hr

theorem checked_utilization_spec (cash borrows reserves u : ℚ) :
    checked_utilization cash borrows reserves = some u ↔
      ValidPoolState cash borrows reserves ∧ u = utilization cash borrows reserves := by
  simp only [checked_utilization]; split <;> simp_all [eq_comm]

theorem utilization_gt_one_counterexample :
    ValidPoolState 10 100 20 ∧ 10 < (20 : ℚ) ∧ utilization 10 100 20 = 10 / 9 ∧
      1 < utilization 10 100 20 := by norm_num [ValidPoolState, denominator, utilization]

structure KinkRateParams where
  base : ℚ
  slope₁ : ℚ
  slope₂ : ℚ
  kink : ℚ
  reserveFactor : ℚ
  base_nonneg : 0 ≤ base
  slope₁_nonneg : 0 ≤ slope₁
  slope₂_nonneg : 0 ≤ slope₂
  kink_pos : 0 < kink
  kink_lt_one : kink < 1
  reserve_nonneg : 0 ≤ reserveFactor
  reserve_le_one : reserveFactor ≤ 1

def borrow_rate (P : KinkRateParams) (u : ℚ) : ℚ :=
  if u ≤ P.kink then P.base + P.slope₁ * u
  else P.base + P.slope₁ * P.kink + P.slope₂ * (u - P.kink)

def supply_rate (P : KinkRateParams) (u : ℚ) : ℚ :=
  u * (1 - P.reserveFactor) * borrow_rate P u

theorem borrow_rate_at_kink (P : KinkRateParams) :
    borrow_rate P P.kink = P.base + P.slope₁ * P.kink ∧
    P.base + P.slope₁ * P.kink + P.slope₂ * (P.kink - P.kink) =
      P.base + P.slope₁ * P.kink := by simp [borrow_rate]

theorem borrow_rate_nonneg (P : KinkRateParams) {u : ℚ} (hu : 0 ≤ u) :
    0 ≤ borrow_rate P u := by
  unfold borrow_rate; split
  · exact add_nonneg P.base_nonneg (mul_nonneg P.slope₁_nonneg hu)
  · exact add_nonneg (add_nonneg P.base_nonneg (mul_nonneg P.slope₁_nonneg P.kink_pos.le))
      (mul_nonneg P.slope₂_nonneg (by linarith))

theorem borrow_rate_monotone (P : KinkRateParams) : Monotone (borrow_rate P) := by
  intro u v huv
  unfold borrow_rate; split <;> split
  · exact add_le_add_right (mul_le_mul_of_nonneg_left huv P.slope₁_nonneg) _
  · have h₁ := mul_nonneg P.slope₁_nonneg (show 0 ≤ P.kink - u by linarith)
    have h₂ := mul_nonneg P.slope₂_nonneg (show 0 ≤ v - P.kink by linarith)
    linarith
  · linarith
  · have := mul_le_mul_of_nonneg_left huv P.slope₂_nonneg
    linarith

/-- Hinge representation also proves continuity when the second slope decreases. -/
theorem borrow_rate_hinge (P : KinkRateParams) (u : ℚ) :
    borrow_rate P u = P.base + P.slope₁ * u +
      (P.slope₂ - P.slope₁) * max (u - P.kink) 0 := by
  by_cases h : u ≤ P.kink
  · simp [borrow_rate, h]
  · rw [borrow_rate, if_neg h, max_eq_left (by linarith : 0 ≤ u - P.kink)]; ring

theorem borrow_rate_continuous (P : KinkRateParams) : Continuous (borrow_rate P) := by
  have he : borrow_rate P = fun u => P.base + P.slope₁ * u +
      (P.slope₂ - P.slope₁) * max (u - P.kink) 0 := funext (borrow_rate_hinge P)
  rw [he]
  exact (continuous_const.add (continuous_const.mul continuous_id)).add
    (continuous_const.mul ((continuous_id.sub continuous_const).max continuous_const))

theorem borrow_rate_max (P : KinkRateParams) (hs : P.slope₁ ≤ P.slope₂) (u : ℚ) :
    borrow_rate P u = max (P.base + P.slope₁ * u)
      (P.base + P.slope₁ * P.kink + P.slope₂ * (u - P.kink)) := by
  unfold borrow_rate; split
  · rw [max_eq_left]; nlinarith [mul_nonneg (sub_nonneg.mpr hs)
      (show 0 ≤ P.kink - u by linarith)]
  · rw [max_eq_right]; nlinarith [mul_nonneg (sub_nonneg.mpr hs)
      (show 0 ≤ u - P.kink by linarith)]

/-- Actual Jensen convexity on all rationals, not just branch agreement. -/
theorem borrow_rate_convex_slope (P : KinkRateParams) (hs : P.slope₁ ≤ P.slope₂) :
    ConvexOn ℚ Set.univ (borrow_rate P) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  simp only [smul_eq_mul]
  rw [borrow_rate_max P hs, max_le_iff]
  have h₁ (t : ℚ) : P.base + P.slope₁ * t ≤ borrow_rate P t := by
    rw [borrow_rate_max P hs]; exact le_max_left _ _
  have h₂ (t : ℚ) : P.base + P.slope₁ * P.kink + P.slope₂ * (t - P.kink) ≤
      borrow_rate P t := by rw [borrow_rate_max P hs]; exact le_max_right _ _
  constructor
  · have h := add_le_add (mul_le_mul_of_nonneg_left (h₁ u) ha)
      (mul_le_mul_of_nonneg_left (h₁ v) hb)
    have he : a * (P.base + P.slope₁ * u) + b * (P.base + P.slope₁ * v) =
        P.base + P.slope₁ * (a*u+b*v) := by
      calc _ = (a+b)*P.base + P.slope₁*(a*u+b*v) := by ring
           _ = _ := by rw [hab]; ring
    rwa [he] at h
  · have h := add_le_add (mul_le_mul_of_nonneg_left (h₂ u) ha)
      (mul_le_mul_of_nonneg_left (h₂ v) hb)
    have he : a * (P.base + P.slope₁ * P.kink + P.slope₂ * (u - P.kink)) +
        b * (P.base + P.slope₁ * P.kink + P.slope₂ * (v - P.kink)) =
        P.base + P.slope₁ * P.kink + P.slope₂ * (a*u+b*v-P.kink) := by
      calc _ = (a+b)*(P.base + P.slope₁*P.kink - P.slope₂*P.kink) +
          P.slope₂*(a*u+b*v) := by ring
           _ = _ := by rw [hab]; ring
    rwa [he] at h

theorem supply_rate_nonneg (P : KinkRateParams) {u : ℚ} (hu : 0 ≤ u) :
    0 ≤ supply_rate P u :=
  mul_nonneg (mul_nonneg hu (sub_nonneg.mpr P.reserve_le_one)) (borrow_rate_nonneg P hu)

theorem supply_rate_monotone (P : KinkRateParams) {u v : ℚ} (hu : 0 ≤ u) (huv : u ≤ v) :
    supply_rate P u ≤ supply_rate P v := by
  exact mul_le_mul (mul_le_mul_of_nonneg_right huv (sub_nonneg.mpr P.reserve_le_one))
    (borrow_rate_monotone P huv) (borrow_rate_nonneg P hu)
    (mul_nonneg (hu.trans huv) (sub_nonneg.mpr P.reserve_le_one))

theorem rate_spread_identity (P : KinkRateParams) (u : ℚ) :
    borrow_rate P u - supply_rate P u =
      borrow_rate P u * (1 - u * (1 - P.reserveFactor)) := by unfold supply_rate; ring

theorem supply_le_borrow_on_unit (P : KinkRateParams) {u : ℚ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ supply_rate P u ∧ supply_rate P u ≤ borrow_rate P u := by
  have hm : u * (1 - P.reserveFactor) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (by linarith [P.reserve_nonneg] : 1 - P.reserveFactor ≤ 1) hu).trans
      (by simpa using hu1)
  exact ⟨supply_rate_nonneg P hu, by
    simpa [supply_rate] using mul_le_mul_of_nonneg_right hm (borrow_rate_nonneg P hu)⟩

theorem strict_spread_iff (P : KinkRateParams) {u : ℚ} (hu : 0 ≤ u) (_hu1 : u ≤ 1) :
    supply_rate P u < borrow_rate P u ↔
      0 < borrow_rate P u ∧ u * (1 - P.reserveFactor) < 1 := by
  have hn := borrow_rate_nonneg P hu
  have he := rate_spread_identity P u
  constructor
  · intro h
    have hp : 0 < borrow_rate P u * (1 - u * (1 - P.reserveFactor)) := by linarith
    have hf := (mul_pos_iff.mp hp).resolve_right (by rintro ⟨h, _⟩; linarith)
    exact ⟨hf.1, by linarith [hf.2]⟩
  · rintro ⟨hb, hf⟩
    have := mul_pos hb (show 0 < 1 - u * (1 - P.reserveFactor) by linarith)
    linarith

theorem spread_zero_at_full_util_zero_reserve (P : KinkRateParams)
    (hr : P.reserveFactor = 0) : supply_rate P 1 = borrow_rate P 1 := by
  simp [supply_rate, hr]

/-- Unbounded natural quotient, incremented exactly when a remainder exists. -/
def ceil_div (a b : ℕ) : ℕ := a / b + if a % b = 0 then 0 else 1

theorem floor_div_bounds (a b : ℕ) :
    ((a / b : ℕ) : ℚ) ≤ (a : ℚ) / b ∧ (a : ℚ) / b < (a / b : ℕ) + 1 := by
  rw [← Nat.floor_div_eq_div (K := ℚ)]
  exact ⟨Nat.floor_le (div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)),
    Nat.lt_floor_add_one _⟩

theorem ceil_div_bounds (a b : ℕ) (hb : 0 < b) :
    (a : ℚ) / b ≤ ceil_div a b ∧ (ceil_div a b : ℚ) < (a : ℚ) / b + 1 := by
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  have hd : (b : ℚ) * (a / b : ℕ) + (a % b : ℕ) = a := by
    exact_mod_cast Nat.div_add_mod a b
  have hr : ((a % b : ℕ) : ℚ) < b := by exact_mod_cast Nat.mod_lt a hb
  unfold ceil_div
  split_ifs with h
  · have he : (a : ℚ) / b = (a / b : ℕ) := by
      apply (div_eq_iff (ne_of_gt hbq)).mpr
      simp only [h, Nat.cast_zero, add_zero] at hd
      nlinarith
    simp [he]
  · have hr0 : (0 : ℚ) < (a % b : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero h
    push_cast
    constructor
    · apply (div_le_iff₀ hbq).mpr; nlinarith
    · have hh : ((a / b : ℕ) : ℚ) < (a : ℚ) / b := by
        apply (lt_div_iff₀ hbq).mpr; nlinarith
      linarith

structure FixedParams where
  scale : ℕ
  base : ℕ
  slope₁ : ℕ
  slope₂ : ℕ
  kink : ℕ
  reserveFactor : ℕ
  scale_pos : 0 < scale
  kink_pos : 0 < kink
  kink_lt_scale : kink < scale
  reserve_le_scale : reserveFactor ≤ scale

def FixedParams.lift (P : FixedParams) : KinkRateParams where
  base := (P.base : ℚ) / P.scale
  slope₁ := (P.slope₁ : ℚ) / P.scale
  slope₂ := (P.slope₂ : ℚ) / P.scale
  kink := (P.kink : ℚ) / P.scale
  reserveFactor := (P.reserveFactor : ℚ) / P.scale
  base_nonneg := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  slope₁_nonneg := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  slope₂_nonneg := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  kink_pos := div_pos (by exact_mod_cast P.kink_pos) (by exact_mod_cast P.scale_pos)
  kink_lt_one := (div_lt_one (by exact_mod_cast P.scale_pos)).mpr
    (by exact_mod_cast P.kink_lt_scale)
  reserve_nonneg := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  reserve_le_one := (div_le_one (by exact_mod_cast P.scale_pos)).mpr
    (by exact_mod_cast P.reserve_le_scale)

/-- One final upward rounding of the entire scaled borrow numerator. -/
def borrow_numerator (P : FixedParams) (u : ℕ) : ℕ :=
  P.base * P.scale + P.slope₁ * min u P.kink + P.slope₂ * (u - P.kink)

def borrow_rate_int (P : FixedParams) (u : ℕ) : ℕ :=
  ceil_div (borrow_numerator P u) P.scale

/-- One downward division, after all three numerator factors are multiplied. -/
def supply_rate_int (P : FixedParams) (u : ℕ) : ℕ :=
  u * (P.scale - P.reserveFactor) * borrow_rate_int P u / (P.scale * P.scale)

theorem borrow_numerator_spec (P : FixedParams) (u : ℕ) :
    (borrow_numerator P u : ℚ) / P.scale =
      P.scale * borrow_rate P.lift ((u : ℚ) / P.scale) := by
  have hw : (P.scale : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt P.scale_pos)
  have hwpos : (0 : ℚ) < P.scale := by exact_mod_cast P.scale_pos
  by_cases h : u ≤ P.kink
  · have hq : (u : ℚ) / P.scale ≤ P.lift.kink :=
      (div_le_div_iff_of_pos_right hwpos).mpr (by exact_mod_cast h)
    rw [borrow_rate, if_pos hq]
    simp only [borrow_numerator, min_eq_left h, Nat.sub_eq_zero_of_le h,
      mul_zero, add_zero, FixedParams.lift, Nat.cast_add, Nat.cast_mul]
    field_simp
  · have hk : P.kink ≤ u := (Nat.le_of_lt (Nat.lt_of_not_ge h))
    have hq : ¬ (u : ℚ) / P.scale ≤ P.lift.kink := by
      change ¬ (u : ℚ) / P.scale ≤ (P.kink : ℚ) / P.scale
      rw [div_le_div_iff_of_pos_right hwpos]; exact_mod_cast h
    rw [borrow_rate, if_neg hq]
    simp only [borrow_numerator, min_eq_right hk, Nat.cast_add, Nat.cast_mul,
      Nat.cast_sub hk, FixedParams.lift]
    field_simp

/-- The normalized borrow error is in [0,1/W). -/
theorem borrow_rate_int_error (P : FixedParams) (u : ℕ) :
    0 ≤ (borrow_rate_int P u : ℚ) / P.scale - borrow_rate P.lift ((u : ℚ) / P.scale) ∧
    (borrow_rate_int P u : ℚ) / P.scale - borrow_rate P.lift ((u : ℚ) / P.scale) <
      1 / P.scale := by
  have h := ceil_div_bounds (borrow_numerator P u) P.scale P.scale_pos
  rw [borrow_numerator_spec] at h
  have hw : (0 : ℚ) < P.scale := by exact_mod_cast P.scale_pos
  change P.scale * borrow_rate P.lift ((u : ℚ) / P.scale) ≤ (borrow_rate_int P u : ℚ) ∧
    (borrow_rate_int P u : ℚ) < P.scale * borrow_rate P.lift ((u : ℚ) / P.scale) + 1 at h
  constructor
  · have hh := (le_div_iff₀ hw).mpr (by nlinarith [h.1] :
        borrow_rate P.lift ((u : ℚ) / P.scale) * P.scale ≤ (borrow_rate_int P u : ℚ))
    linarith
  · have hh := div_lt_div_of_pos_right h.2 hw
    simp only [add_div, mul_div_cancel_left₀ _ (ne_of_gt hw)] at hh
    linarith

theorem supply_rate_int_le_borrow (P : FixedParams) {u : ℕ} (hu : u ≤ P.scale) :
    supply_rate_int P u ≤ borrow_rate_int P u := by
  have hmul : u * (P.scale - P.reserveFactor) ≤ P.scale * P.scale :=
    Nat.mul_le_mul hu (Nat.sub_le _ _)
  unfold supply_rate_int
  apply Nat.div_le_of_le_mul
  nlinarith [Nat.mul_le_mul_right (borrow_rate_int P u) hmul]

/-- Exact bridge for the integer supply numerator, including truncated natural subtraction. -/
theorem supply_numerator_spec (P : FixedParams) (u : ℕ) :
    ((u * (P.scale - P.reserveFactor) * borrow_rate_int P u : ℕ) : ℚ) /
      (P.scale * P.scale : ℕ) =
      ((u : ℚ) / P.scale) * (1 - P.lift.reserveFactor) * borrow_rate_int P u := by
  simp only [Nat.cast_mul, Nat.cast_sub P.reserve_le_scale, FixedParams.lift]
  have hw : (P.scale : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt P.scale_pos
  field_simp

/-- Downward supply error relative to its already rounded borrow-rate input. -/
theorem supply_rate_int_floor_error (P : FixedParams) (u : ℕ) :
    0 ≤ ((u : ℚ) / P.scale) * (1 - P.lift.reserveFactor) *
      ((borrow_rate_int P u : ℚ) / P.scale) - (supply_rate_int P u : ℚ) / P.scale ∧
    ((u : ℚ) / P.scale) * (1 - P.lift.reserveFactor) *
      ((borrow_rate_int P u : ℚ) / P.scale) - (supply_rate_int P u : ℚ) / P.scale <
        1 / P.scale := by
  have h := floor_div_bounds (u * (P.scale - P.reserveFactor) * borrow_rate_int P u)
    (P.scale * P.scale)
  rw [supply_numerator_spec] at h
  change (supply_rate_int P u : ℚ) ≤ _ ∧ _ < (supply_rate_int P u : ℚ) + 1 at h
  have hw : (0 : ℚ) < P.scale := by exact_mod_cast P.scale_pos
  simp only [← mul_div_assoc]
  constructor
  · have hh := div_le_div_of_nonneg_right h.1 hw.le
    linarith
  · have hh := div_lt_div_of_pos_right h.2 hw
    rw [add_div] at hh
    linarith

/-- Net error against the rational curve at quantized utilization is strictly less than one ulp. -/
theorem supply_rate_int_error (P : FixedParams) {u : ℕ} (hu : u ≤ P.scale) :
    -(1 / (P.scale : ℚ)) < (supply_rate_int P u : ℚ) / P.scale -
      supply_rate P.lift ((u : ℚ) / P.scale) ∧
    (supply_rate_int P u : ℚ) / P.scale - supply_rate P.lift ((u : ℚ) / P.scale) <
      1 / P.scale := by
  have hb := borrow_rate_int_error P u
  have hs := supply_rate_int_floor_error P u
  have hw : (0 : ℚ) < P.scale := by exact_mod_cast P.scale_pos
  have hu0 : (0 : ℚ) ≤ (u : ℚ) / P.scale := div_nonneg (Nat.cast_nonneg _) hw.le
  have hu1 : (u : ℚ) / P.scale ≤ 1 := (div_le_one hw).mpr (by exact_mod_cast hu)
  have hf0 : 0 ≤ ((u : ℚ) / P.scale) * (1 - P.lift.reserveFactor) :=
    mul_nonneg hu0 (sub_nonneg.mpr P.lift.reserve_le_one)
  have hf1 : ((u : ℚ) / P.scale) * (1 - P.lift.reserveFactor) ≤ 1 := by
    nlinarith [P.lift.reserve_nonneg, P.lift.reserve_le_one,
      mul_nonneg hu0 P.lift.reserve_nonneg]
  have he0 := mul_nonneg hf0 hb.1
  have he1 := mul_le_mul_of_nonneg_right hf1 hb.1
  dsimp [supply_rate]
  constructor <;> nlinarith

/-- Zero debt is accepted even when the unused denominator is nonpositive. -/
def utilization_int (W cash borrows reserves : ℕ) : Option ℕ :=
  if W = 0 then none
  else if borrows = 0 then some 0
  else if reserves < cash + borrows then some (W * borrows / (cash + borrows - reserves))
  else none

theorem utilization_int_zero (W cash reserves : ℕ) (hW : 0 < W) :
    utilization_int W cash 0 reserves = some 0 := by simp [utilization_int, Nat.ne_of_gt hW]

theorem utilization_int_invalid (W cash borrows reserves : ℕ)
    (hb : borrows ≠ 0) (hd : cash + borrows ≤ reserves) :
    utilization_int W cash borrows reserves = none := by simp [utilization_int, hb, not_lt.mpr hd]

theorem utilization_int_error {W cash borrows reserves u : ℕ} (hW : 0 < W)
    (h : utilization_int W cash borrows reserves = some u) :
    0 ≤ utilization cash borrows reserves - (u : ℚ) / W ∧
    utilization cash borrows reserves - (u : ℚ) / W < 1 / W := by
  have hw : (0 : ℚ) < W := by exact_mod_cast hW
  unfold utilization_int at h
  rw [if_neg (Nat.ne_of_gt hW)] at h
  split_ifs at h with hb hd
  · simp only [Option.some.injEq] at h
    subst u
    simp [hb, utilization, hw]
  · simp only [Option.some.injEq] at h
    subst u
    have hn : reserves ≤ cash + borrows := hd.le
    have he : ((W * borrows : ℕ) : ℚ) / (cash + borrows - reserves : ℕ) =
        W * utilization cash borrows reserves := by
      simp only [utilization, Nat.cast_ne_zero.mpr hb, if_false, denominator,
        Nat.cast_mul, Nat.cast_sub hn, Nat.cast_add]
      ring
    have hf := floor_div_bounds (W * borrows) (cash + borrows - reserves)
    rw [he] at hf
    constructor
    · have hh := (div_le_iff₀ hw).mpr (by nlinarith [hf.1] :
          ((W * borrows / (cash + borrows - reserves) : ℕ) : ℚ) ≤
            utilization cash borrows reserves * W)
      linarith
    · have hh := div_lt_div_of_pos_right hf.2 hw
      rw [add_div] at hh
      have hw0 := ne_of_gt hw
      field_simp at hh ⊢
      nlinarith

/-- Domain guard for the unit-interval rate theorems uses the exact reserve/cash condition. -/
def quote_rates (P : FixedParams) (cash borrows reserves : ℕ) : Option (ℕ × ℕ × ℕ) :=
  if reserves ≤ cash ∨ borrows = 0 then
    (utilization_int P.scale cash borrows reserves).map
      (fun u => (u, borrow_rate_int P u, supply_rate_int P u))
  else none

theorem utilization_int_le_scale {W cash borrows reserves u : ℕ} (hW : 0 < W)
    (hg : reserves ≤ cash ∨ borrows = 0)
    (h : utilization_int W cash borrows reserves = some u) : u ≤ W := by
  have he := (utilization_int_error hW h).1
  have hu : utilization cash borrows reserves ≤ 1 := by
    by_cases hb : borrows = 0
    · simp [hb, utilization]
    · have hr := hg.resolve_right hb
      have hbq : (0 : ℚ) < borrows := by exact_mod_cast Nat.pos_of_ne_zero hb
      have hd : 0 < denominator cash borrows reserves := by
        have hrq : (reserves : ℚ) ≤ cash := by exact_mod_cast hr
        dsimp [denominator]; linarith
      exact (utilization_le_one_iff hbq hd).mpr (by exact_mod_cast hr)
  have hw : (0 : ℚ) < W := by exact_mod_cast hW
  have hq : (u : ℚ) / W ≤ 1 := by linarith
  exact_mod_cast (div_le_one hw).mp hq

theorem quote_rates_spec (P : FixedParams) (cash borrows reserves u rb rs : ℕ) :
    quote_rates P cash borrows reserves = some (u, rb, rs) ↔
      (reserves ≤ cash ∨ borrows = 0) ∧
      utilization_int P.scale cash borrows reserves = some u ∧
      rb = borrow_rate_int P u ∧ rs = supply_rate_int P u := by
  unfold quote_rates
  split_ifs with hg
  · cases h : utilization_int P.scale cash borrows reserves with
    | none => simp [hg]
    | some v => simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
                simp only [hg, true_and]
                constructor
                · rintro ⟨rfl, h₁, h₂⟩; exact ⟨rfl, h₁.symm, h₂.symm⟩
                · rintro ⟨hv, h₁, h₂⟩; cases hv; exact ⟨rfl, h₁.symm, h₂.symm⟩
  · simp [hg]

theorem quote_rates_preserves (P : FixedParams) {cash borrows reserves u rb rs : ℕ}
    (h : quote_rates P cash borrows reserves = some (u, rb, rs)) :
    u ≤ P.scale ∧ rs ≤ rb := by
  obtain ⟨hg, hu, rfl, rfl⟩ := (quote_rates_spec P cash borrows reserves u rb rs).mp h
  have hunit := utilization_int_le_scale P.scale_pos hg hu
  exact ⟨hunit, supply_rate_int_le_borrow P hunit⟩

/-- Uniform slope bound, including an interval crossing the kink. -/
theorem borrow_rate_growth_le (P : KinkRateParams) {u v : ℚ} (h : u ≤ v) :
    borrow_rate P v - borrow_rate P u ≤ max P.slope₁ P.slope₂ * (v - u) := by
  have h₁ := le_max_left P.slope₁ P.slope₂
  have h₂ := le_max_right P.slope₁ P.slope₂
  have hdiff : 0 ≤ v - u := sub_nonneg.mpr h
  unfold borrow_rate
  split <;> split
  · nlinarith [mul_nonneg (sub_nonneg.mpr h₁) hdiff]
  · linarith
  · have hlow : 0 ≤ P.kink - u := by linarith
    have hhigh : 0 ≤ v - P.kink := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr h₁) hlow,
      mul_nonneg (sub_nonneg.mpr h₂) hhigh]
  · nlinarith [mul_nonneg (sub_nonneg.mpr h₂) hdiff]

/-- End-to-end borrow error includes the utilization quantization loss. -/
theorem borrow_rate_total_error (P : FixedParams) {cash borrows reserves u : ℕ}
    (h : utilization_int P.scale cash borrows reserves = some u) :
    -(max P.lift.slope₁ P.lift.slope₂ / P.scale) ≤
      (borrow_rate_int P u : ℚ) / P.scale - borrow_rate P.lift (utilization cash borrows reserves) ∧
    (borrow_rate_int P u : ℚ) / P.scale - borrow_rate P.lift (utilization cash borrows reserves) <
      1 / P.scale := by
  have he := utilization_int_error P.scale_pos h
  have hb := borrow_rate_int_error P u
  have hm := borrow_rate_monotone P.lift (show (u : ℚ) / P.scale ≤
      utilization cash borrows reserves by linarith)
  have hg := borrow_rate_growth_le P.lift (show (u : ℚ) / P.scale ≤
      utilization cash borrows reserves by linarith)
  have hL : 0 ≤ max P.lift.slope₁ P.lift.slope₂ :=
    P.lift.slope₁_nonneg.trans (le_max_left _ _)
  have hl := mul_le_mul_of_nonneg_left he.2.le hL
  simp only [mul_one_div] at hl
  constructor <;> linarith

/-- Instantaneous supply sensitivity at fixed curve and reserve factor. -/
theorem supply_rate_growth_le (P : KinkRateParams) {u v : ℚ}
    (_hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    supply_rate P v - supply_rate P u ≤
      (1 - P.reserveFactor) * (borrow_rate P 1 + max P.slope₁ P.slope₂) * (v - u) := by
  have hb := borrow_rate_monotone P huv
  have hb1 := borrow_rate_monotone P hv
  have hg := borrow_rate_growth_le P huv
  have hdiff := sub_nonneg.mpr huv
  have hmul := mul_le_mul_of_nonneg_left hb1 hdiff
  have hunit := mul_le_mul_of_nonneg_right (huv.trans hv) (sub_nonneg.mpr hb)
  have he : (v-u)*borrow_rate P v + u*(borrow_rate P v-borrow_rate P u) ≤
      (borrow_rate P 1 + max P.slope₁ P.slope₂)*(v-u) := by nlinarith
  have hh := mul_le_mul_of_nonneg_left he (sub_nonneg.mpr P.reserve_le_one)
  dsimp [supply_rate]; nlinarith [hh]

/-- End-to-end supply error: one rounding ulp plus an explicit utilization sensitivity term. -/
theorem supply_rate_total_error (P : FixedParams) {cash borrows reserves u : ℕ}
    (hg : reserves ≤ cash ∨ borrows = 0)
    (h : utilization_int P.scale cash borrows reserves = some u) :
    -((1 - P.lift.reserveFactor) *
        (borrow_rate P.lift 1 + max P.lift.slope₁ P.lift.slope₂) / P.scale + 1 / P.scale) <
      (supply_rate_int P u : ℚ) / P.scale - supply_rate P.lift (utilization cash borrows reserves) ∧
    (supply_rate_int P u : ℚ) / P.scale - supply_rate P.lift (utilization cash borrows reserves) <
      1 / P.scale := by
  have hu := utilization_int_le_scale P.scale_pos hg h
  have he := utilization_int_error P.scale_pos h
  have hs := supply_rate_int_error P hu
  have hw : (0 : ℚ) < P.scale := by exact_mod_cast P.scale_pos
  have hu0 : (0 : ℚ) ≤ (u : ℚ) / P.scale := div_nonneg (Nat.cast_nonneg _) hw.le
  have hU1 : utilization cash borrows reserves ≤ 1 := by
    by_cases hb : borrows = 0
    · simp [hb, utilization]
    · have hr := hg.resolve_right hb
      apply (utilization_le_one_iff (by exact_mod_cast Nat.pos_of_ne_zero hb) ?_).mpr
        (by exact_mod_cast hr)
      have hrq : (reserves : ℚ) ≤ cash := by exact_mod_cast hr
      have hbq : (0 : ℚ) < borrows := by exact_mod_cast Nat.pos_of_ne_zero hb
      dsimp [denominator]; linarith
  have huU : (u : ℚ) / P.scale ≤ utilization cash borrows reserves := by linarith [he.1]
  have hm := supply_rate_monotone P.lift hu0 huU
  have hl := supply_rate_growth_le P.lift hu0 huU hU1
  have hL : 0 ≤ (1-P.lift.reserveFactor) * (borrow_rate P.lift 1 +
      max P.lift.slope₁ P.lift.slope₂) :=
    mul_nonneg (sub_nonneg.mpr P.lift.reserve_le_one)
      (add_nonneg (borrow_rate_nonneg P.lift (by norm_num))
        (P.lift.slope₁_nonneg.trans (le_max_left _ _)))
  have hh := mul_le_mul_of_nonneg_left he.2.le hL
  simp only [mul_one_div] at hh
  constructor <;> linarith

theorem borrow_rate_dominates_linear (P : KinkRateParams) (hs : P.slope₁ ≤ P.slope₂) (u : ℚ) :
    P.base + P.slope₁ * u ≤ borrow_rate P u := by
  rw [borrow_rate_max P hs]; exact le_max_left _ _

theorem before_kink_increment (P : KinkRateParams) {u v : ℚ} (huv : u ≤ v) (hv : v ≤ P.kink) :
    borrow_rate P v - borrow_rate P u = P.slope₁ * (v - u) := by
  simp only [borrow_rate, if_pos hv, if_pos (huv.trans hv)]; ring

theorem after_kink_increment (P : KinkRateParams) {u v : ℚ} (hu : P.kink ≤ u) (huv : u ≤ v) :
    borrow_rate P v - borrow_rate P u = P.slope₂ * (v - u) := by
  unfold borrow_rate
  split <;> split <;> rename_i h₁ h₂
  · have : u = P.kink := by linarith
    have : v = P.kink := by linarith
    simp_all
  · linarith
  · have : u = P.kink := by linarith
    rw [this]; ring
  · ring

theorem rates_at_zero (P : KinkRateParams) :
    borrow_rate P 0 = P.base ∧ supply_rate P 0 = 0 := by
  simp [borrow_rate, P.kink_pos.le, supply_rate]

theorem full_reserve_supply_zero (P : KinkRateParams) (hr : P.reserveFactor = 1) (u : ℚ) :
    supply_rate P u = 0 := by simp [supply_rate, hr]

structure DeFiKinkedInterestRateUtilizationSuite : Prop where
  unit_interval : ∀ cash borrows reserves, ValidPoolState cash borrows reserves → reserves ≤ cash →
    0 ≤ utilization cash borrows reserves ∧ utilization cash borrows reserves ≤ 1
  normalization_iff : ∀ cash borrows reserves, 0 < borrows → 0 < denominator cash borrows reserves →
    (utilization cash borrows reserves ≤ 1 ↔ reserves ≤ cash)
  continuous_curve : ∀ P, Continuous (borrow_rate P)
  monotone_curve : ∀ P, Monotone (borrow_rate P)
  convex_curve : ∀ P, P.slope₁ ≤ P.slope₂ → ConvexOn ℚ Set.univ (borrow_rate P)
  supply_monotone : ∀ P u v, 0 ≤ u → u ≤ v → supply_rate P u ≤ supply_rate P v
  rate_order : ∀ P u, 0 ≤ u → u ≤ 1 → 0 ≤ supply_rate P u ∧ supply_rate P u ≤ borrow_rate P u
  strict_spread : ∀ P u, 0 ≤ u → u ≤ 1 →
    (supply_rate P u < borrow_rate P u ↔ 0 < borrow_rate P u ∧ u * (1 - P.reserveFactor) < 1)
  integer_order : ∀ P u, u ≤ P.scale → supply_rate_int P u ≤ borrow_rate_int P u
  borrow_rounding : ∀ P u,
    0 ≤ (borrow_rate_int P u : ℚ) / P.scale - borrow_rate P.lift ((u : ℚ) / P.scale) ∧
    (borrow_rate_int P u : ℚ) / P.scale - borrow_rate P.lift ((u : ℚ) / P.scale) < 1 / P.scale
  supply_rounding : ∀ P u, u ≤ P.scale →
    -(1 / (P.scale : ℚ)) < (supply_rate_int P u : ℚ) / P.scale -
      supply_rate P.lift ((u : ℚ) / P.scale) ∧
    (supply_rate_int P u : ℚ) / P.scale - supply_rate P.lift ((u : ℚ) / P.scale) < 1 / P.scale
  guarded_quote : ∀ P cash borrows reserves u rb rs,
    quote_rates P cash borrows reserves = some (u, rb, rs) → u ≤ P.scale ∧ rs ≤ rb

theorem verification_suite : DeFiKinkedInterestRateUtilizationSuite where
  unit_interval := fun _ _ _ => utilization_in_unit_interval
  normalization_iff := fun _ _ _ => utilization_le_one_iff
  continuous_curve := borrow_rate_continuous
  monotone_curve := borrow_rate_monotone
  convex_curve := borrow_rate_convex_slope
  supply_monotone := fun _ _ _ => supply_rate_monotone _
  rate_order := fun _ _ => supply_le_borrow_on_unit _
  strict_spread := fun _ _ => strict_spread_iff _
  integer_order := fun _ _ => supply_rate_int_le_borrow _
  borrow_rounding := borrow_rate_int_error
  supply_rounding := fun _ _ => supply_rate_int_error _
  guarded_quote := fun _ _ _ _ _ _ _ => quote_rates_preserves _

end DeFiKinkedInterestRateUtilization
