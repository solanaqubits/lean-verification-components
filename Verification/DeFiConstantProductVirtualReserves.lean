/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DeFiConstantProductSwap
import Verification.DeFiConcentratedLiquidity
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Virtual-reserve constant-product reference model

Fees remain in trading reserves. Fixed offsets, exact rational execution and
natural directed rounding; no external-price, MEV or implementation security claim.
-/
namespace DeFiConstantProductVirtualReserves

structure VirtualReservesState where
  x : ℚ
  y : ℚ
  α : ℚ
  β : ℚ
  hx : 0 ≤ x
  hy : 0 ≤ y
  hα : 0 ≤ α
  hβ : 0 ≤ β
  hX : 0 < x + α
  hY : 0 < y + β
  deriving DecidableEq

def X (s : VirtualReservesState) := s.x + s.α
def Y (s : VirtualReservesState) := s.y + s.β
def invariant (s : VirtualReservesState) := X s * Y s
def d_eff (d γ : ℚ) := (1 - γ) * d
def output_amount (X Y e : ℚ) := Y * e / (X + e)
def quote (s : VirtualReservesState) (d γ : ℚ) := output_amount (X s) (Y s) (d_eff d γ)
def valid_fee (γ : ℚ) : Prop := 0 ≤ γ ∧ γ < 1
instance (γ : ℚ) : Decidable (valid_fee γ) := inferInstanceAs (Decidable (_ ∧ _))

theorem effective_nonneg {d γ : ℚ} (hd : 0 ≤ d) (hg : valid_fee γ) :
    0 ≤ d_eff d γ := mul_nonneg (sub_nonneg.mpr hg.2.le) hd

theorem denominator_pos (s : VirtualReservesState) {e : ℚ} (he : 0 ≤ e) :
    0 < X s + e := add_pos_of_pos_of_nonneg s.hX he

theorem output_nonneg (s : VirtualReservesState) {e : ℚ} (he : 0 ≤ e) :
    0 ≤ output_amount (X s) (Y s) e :=
  div_nonneg (mul_nonneg s.hY.le he) (denominator_pos s he).le

theorem remaining_identity (s : VirtualReservesState) {e : ℚ} (he : 0 ≤ e) :
    Y s - output_amount (X s) (Y s) e = X s * Y s / (X s + e) := by
  unfold output_amount
  field_simp [ne_of_gt (denominator_pos s he)]
  ring

theorem remaining_pos (s : VirtualReservesState) {e : ℚ} (he : 0 ≤ e) :
    0 < Y s - output_amount (X s) (Y s) e := by
  rw [remaining_identity s he]
  exact div_pos (mul_pos s.hX s.hY) (denominator_pos s he)

theorem solvency_criterion_iff (s : VirtualReservesState) {e : ℚ} (he : 0 ≤ e) :
    output_amount (X s) (Y s) e ≤ s.y ↔ s.β * e ≤ s.y * X s := by
  unfold output_amount
  rw [div_le_iff₀ (denominator_pos s he)]
  dsimp [Y]
  constructor <;> intro h <;> nlinarith only [h]

theorem effective_invariant (s : VirtualReservesState) {e : ℚ} (he : 0 ≤ e) :
    (X s + e) * (Y s - output_amount (X s) (Y s) e) = invariant s := by
  rw [remaining_identity s he]
  field_simp [ne_of_gt (denominator_pos s he)]
  rfl

theorem invariant_growth_identity (s : VirtualReservesState) {d γ : ℚ}
    (hd : 0 ≤ d) (hg : valid_fee γ) :
    (s.x + d + s.α) * (s.y - quote s d γ + s.β) =
      invariant s + γ * d * (Y s - quote s d γ) := by
  have h := effective_invariant s (effective_nonneg hd hg)
  change (X s + d_eff d γ) * (Y s - quote s d γ) = invariant s at h
  dsimp [d_eff] at h
  dsimp [X, Y] at h ⊢
  nlinarith only [h]

theorem invariant_nondecreasing (s : VirtualReservesState) {d γ : ℚ}
    (hd : 0 ≤ d) (hg : valid_fee γ) :
    invariant s ≤ (s.x + d + s.α) * (s.y - quote s d γ + s.β) := by
  rw [invariant_growth_identity s hd hg]
  have hr := (remaining_pos s (effective_nonneg hd hg)).le
  exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hg.1 hd) hr)

theorem invariant_exact_conservation (s : VirtualReservesState) {d : ℚ} (hd : 0 ≤ d) :
    (s.x + d + s.α) * (s.y - quote s d 0 + s.β) = invariant s := by
  simpa using invariant_growth_identity s hd (show valid_fee 0 by constructor <;> norm_num)

theorem output_strict_mono (s : VirtualReservesState) {d₁ d₂ γ : ℚ}
    (hg : valid_fee γ) (h₁ : 0 ≤ d₁) (hlt : d₁ < d₂) :
    quote s d₁ γ < quote s d₂ γ := by
  have h₂ : 0 ≤ d₂ := h₁.trans hlt.le
  have hpos : 0 < 1 - γ := sub_pos.mpr hg.2
  have he := mul_lt_mul_of_pos_left hlt hpos
  have ht := mul_lt_mul_of_pos_left he (mul_pos s.hX s.hY)
  unfold quote output_amount
  rw [div_lt_div_iff₀ (denominator_pos s (effective_nonneg h₁ hg))
    (denominator_pos s (effective_nonneg h₂ hg))]
  dsimp [d_eff, X, Y] at *
  nlinarith only [ht]

theorem average_rate_formula (s : VirtualReservesState) {d γ : ℚ}
    (hd : 0 < d) (_hg : valid_fee γ) :
    quote s d γ / d = Y s * (1 - γ) / (X s + d_eff d γ) := by
  unfold quote output_amount d_eff
  field_simp [ne_of_gt hd, ne_of_gt (denominator_pos s (effective_nonneg hd.le _hg))]

theorem price_impact_average_rate (s : VirtualReservesState) {d₁ d₂ γ : ℚ}
    (hg : valid_fee γ) (h₁ : 0 < d₁) (hlt : d₁ < d₂) :
    quote s d₂ γ / d₂ ≤ quote s d₁ γ / d₁ := by
  rw [average_rate_formula s (h₁.trans hlt) hg, average_rate_formula s h₁ hg]
  apply div_le_div_of_nonneg_left (mul_nonneg s.hY.le (sub_nonneg.mpr hg.2.le))
    (denominator_pos s (effective_nonneg h₁.le hg))
  exact add_le_add_right (mul_le_mul_of_nonneg_left hlt.le (sub_nonneg.mpr hg.2.le)) _

/-- A payout no larger than the exact quote preserves the product. -/
theorem rounded_invariant (s : VirtualReservesState) {d γ p : ℚ}
    (hd : 0 ≤ d) (hg : valid_fee γ) (hp : p ≤ quote s d γ) :
    invariant s ≤ (s.x + d + s.α) * (s.y - p + s.β) := by
  apply (invariant_nondecreasing s hd hg).trans
  exact mul_le_mul_of_nonneg_left (by linarith) (by linarith [s.hX])

def swapAxes (s : VirtualReservesState) : VirtualReservesState :=
  ⟨s.y, s.x, s.β, s.α, s.hy, s.hx, s.hβ, s.hα, s.hY, s.hX⟩

@[simp] theorem swapAxes_twice (s : VirtualReservesState) : swapAxes (swapAxes s) = s := rfl
@[simp] theorem swapAxes_invariant (s : VirtualReservesState) :
    invariant (swapAxes s) = invariant s := by dsimp [invariant, X, Y, swapAxes]; ring

def execute_swap_x_to_y (s : VirtualReservesState) (d γ : ℚ) : Option VirtualReservesState :=
  if hd : 0 ≤ d then
    if hg : valid_fee γ then
      if hs : s.β * d_eff d γ ≤ s.y * X s then
        some ⟨s.x + d, s.y - quote s d γ, s.α, s.β,
          add_nonneg s.hx hd,
          sub_nonneg.mpr ((solvency_criterion_iff s (effective_nonneg hd hg)).mpr hs),
          s.hα, s.hβ, by linarith [s.hX],
          by have h := remaining_pos s (effective_nonneg hd hg); dsimp [quote, Y] at *; linarith⟩
      else none
    else none
  else none

theorem execute_success_iff (s : VirtualReservesState) (d γ : ℚ) :
    (execute_swap_x_to_y s d γ).isSome = true ↔
      0 ≤ d ∧ valid_fee γ ∧ s.β * d_eff d γ ≤ s.y * X s := by
  unfold execute_swap_x_to_y
  split <;> simp_all
  split <;> simp_all

theorem execute_preserves (s t : VirtualReservesState) (d γ : ℚ)
    (h : execute_swap_x_to_y s d γ = some t) :
    invariant s ≤ invariant t ∧ t.α = s.α ∧ t.β = s.β := by
  unfold execute_swap_x_to_y at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases Option.some.inj h
  exact ⟨invariant_nondecreasing s ‹0 ≤ d› ‹valid_fee γ›, rfl, rfl⟩

def execute_swap_y_to_x (s : VirtualReservesState) (d γ : ℚ) : Option VirtualReservesState :=
  (execute_swap_x_to_y (swapAxes s) d γ).map swapAxes

theorem symmetric_y_to_x (s t : VirtualReservesState) (d γ : ℚ)
    (h : execute_swap_y_to_x s d γ = some t) : invariant s ≤ invariant t := by
  obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
  simpa using (execute_preserves (swapAxes s) u d γ hu).1

structure SwapStep where
  reverse : Bool
  amount : ℚ
  fee : ℚ

def execute_step (s : VirtualReservesState) (a : SwapStep) :=
  if a.reverse then execute_swap_y_to_x s a.amount a.fee
  else execute_swap_x_to_y s a.amount a.fee

def execute_chain (s : VirtualReservesState) : List SwapStep → Option VirtualReservesState
  | [] => some s
  | a :: as => (execute_step s a).bind (fun t => execute_chain t as)

theorem dynamic_fee_chain_monotone (as : List SwapStep) (s t : VirtualReservesState)
    (h : execute_chain s as = some t) : invariant s ≤ invariant t := by
  induction as generalizing s with
  | nil => cases Option.some.inj h; exact le_refl _
  | cons a as ih =>
    obtain ⟨u, hu, ht⟩ := Option.bind_eq_some_iff.mp h
    have hi : invariant s ≤ invariant u := by
      unfold execute_step at hu
      split at hu
      · exact symmetric_y_to_x s u _ _ hu
      · exact (execute_preserves s u _ _ hu).1
    exact hi.trans (ih u ht)

/-- Gross input for a requested exact payout, with fees retained in reserves. -/
def input_required (s : VirtualReservesState) (o γ : ℚ) :=
  X s * o / ((1 - γ) * (Y s - o))

theorem input_required_nonneg (s : VirtualReservesState) {o γ : ℚ}
    (ho : 0 ≤ o) (hY : o < Y s) (hg : valid_fee γ) :
    0 ≤ input_required s o γ :=
  div_nonneg (mul_nonneg s.hX.le ho) (mul_pos (sub_pos.mpr hg.2) (sub_pos.mpr hY)).le

theorem input_required_iff (s : VirtualReservesState) {o d γ : ℚ}
    (hd : 0 ≤ d) (hY : o < Y s) (hg : valid_fee γ) :
    input_required s o γ ≤ d ↔ o ≤ quote s d γ := by
  unfold input_required quote output_amount
  rw [div_le_iff₀ (mul_pos (sub_pos.mpr hg.2) (sub_pos.mpr hY)),
    le_div_iff₀ (denominator_pos s (effective_nonneg hd hg))]
  dsimp [d_eff]
  constructor <;> intro h <;> nlinarith only [h]

def floor_div_output (s : VirtualReservesState) (d : ℕ) (γ : ℚ) : ℕ := ⌊quote s d γ⌋₊
def ceil_div_input (s : VirtualReservesState) (o : ℕ) (γ : ℚ) : ℕ := ⌈input_required s o γ⌉₊

theorem floor_output_error (s : VirtualReservesState) (d : ℕ) {γ : ℚ}
    (hg : valid_fee γ) :
    0 ≤ quote s d γ - (floor_div_output s d γ : ℚ) ∧
      quote s d γ - (floor_div_output s d γ : ℚ) < 1 := by
  have hl := Nat.floor_le (output_nonneg s (effective_nonneg (Nat.cast_nonneg d) hg))
  have hu := Nat.lt_floor_add_one (quote s d γ)
  exact ⟨sub_nonneg.mpr hl, by dsimp [floor_div_output]; linarith⟩

theorem ceil_input_error (s : VirtualReservesState) (o : ℕ) {γ : ℚ}
    (hg : valid_fee γ) (hY : (o : ℚ) < Y s) :
    0 ≤ (ceil_div_input s o γ : ℚ) - input_required s o γ ∧
      (ceil_div_input s o γ : ℚ) - input_required s o γ < 1 := by
  have hl := Nat.le_ceil (input_required s o γ)
  have hu := Nat.ceil_lt_add_one (input_required_nonneg s (Nat.cast_nonneg o) hY hg)
  exact ⟨sub_nonneg.mpr hl, by dsimp [ceil_div_input]; linarith⟩

theorem ceil_input_minimal (s : VirtualReservesState) (o d : ℕ) {γ : ℚ}
    (hg : valid_fee γ) (hY : (o : ℚ) < Y s) :
    ceil_div_input s o γ ≤ d ↔ (o : ℚ) ≤ quote s d γ := by
  rw [ceil_div_input, Nat.ceil_le]
  exact input_required_iff s (Nat.cast_nonneg d) hY hg

structure DiscreteState where
  x : ℕ
  y : ℕ
  α : ℕ
  β : ℕ
  deriving DecidableEq, Repr

def DiscreteState.Valid (s : DiscreteState) : Prop := 0 < s.x + s.α ∧ 0 < s.y + s.β
instance (s : DiscreteState) : Decidable s.Valid := inferInstanceAs (Decidable (_ ∧ _))

def DiscreteState.lift (s : DiscreteState) (h : s.Valid) : VirtualReservesState :=
  ⟨s.x, s.y, s.α, s.β, Nat.cast_nonneg _, Nat.cast_nonneg _, Nat.cast_nonneg _,
    Nat.cast_nonneg _, by exact_mod_cast h.1, by exact_mod_cast h.2⟩

def DiscreteState.K (s : DiscreteState) := (s.x + s.α) * (s.y + s.β)
def DiscreteState.settle (s : DiscreteState) (d o : ℕ) : DiscreteState :=
  ⟨s.x + d, s.y - o, s.α, s.β⟩

theorem settle_valid (s : DiscreteState) (hs : s.Valid) (d o : ℕ)
    (ho : o ≤ s.y) (hlt : o < s.y + s.β) : (s.settle d o).Valid := by
  dsimp [DiscreteState.Valid, DiscreteState.settle]
  have hx := hs.1
  omega

theorem settle_rounding_guarantee (s : DiscreteState) (hs : s.Valid) (d o : ℕ)
    {γ : ℚ} (hg : valid_fee γ) (ho : o ≤ s.y)
    (hq : (o : ℚ) ≤ quote (s.lift hs) d γ) : s.K ≤ (s.settle d o).K := by
  have h := rounded_invariant (s.lift hs) (Nat.cast_nonneg d) hg hq
  dsimp [DiscreteState.lift, invariant, X, Y] at h
  have he : (s.y : ℚ) - o = ((s.y - o : ℕ) : ℚ) := (Nat.cast_sub ho).symm
  rw [he] at h
  exact_mod_cast h

def discrete_swap_floor (s : DiscreteState) (d : ℕ) (γ : ℚ) : Option DiscreteState :=
  if hs : s.Valid then
    if valid_fee γ ∧ (s.β : ℚ) * d_eff d γ ≤ s.y * X (s.lift hs) then
      some (s.settle d (floor_div_output (s.lift hs) d γ))
    else none
  else none

theorem discrete_floor_accepts (s : DiscreteState) (hs : s.Valid) (d : ℕ) (γ : ℚ)
    (hg : valid_fee γ) (hb : (s.β : ℚ) * d_eff d γ ≤ s.y * X (s.lift hs)) :
    discrete_swap_floor s d γ = some (s.settle d (floor_div_output (s.lift hs) d γ)) := by
  simp [discrete_swap_floor, hs, hg, hb]

theorem discrete_floor_preserves (s t : DiscreteState) (d : ℕ) (γ : ℚ)
    (h : discrete_swap_floor s d γ = some t) :
    t.Valid ∧ s.K ≤ t.K ∧ t.α = s.α ∧ t.β = s.β := by
  unfold discrete_swap_floor at h
  split at h <;> try contradiction
  rename_i hs
  split at h <;> try contradiction
  rename_i hg
  cases Option.some.inj h
  have he := effective_nonneg (Nat.cast_nonneg d) hg.1
  have hq := (floor_output_error (s.lift hs) d hg.1).1
  have hfloor : (floor_div_output (s.lift hs) d γ : ℚ) ≤ quote (s.lift hs) d γ :=
    sub_nonneg.mp hq
  have hsol : quote (s.lift hs) d γ ≤ (s.y : ℚ) :=
    (solvency_criterion_iff (s.lift hs) he).mpr hg.2
  have ho : floor_div_output (s.lift hs) d γ ≤ s.y := by exact_mod_cast hfloor.trans hsol
  have hr := remaining_pos (s.lift hs) he
  have hlt : floor_div_output (s.lift hs) d γ < s.y + s.β := by
    have hh : (floor_div_output (s.lift hs) d γ : ℚ) < (s.y : ℚ) + s.β := by
      change 0 < (s.y : ℚ) + s.β - quote (s.lift hs) d γ at hr
      linarith
    exact_mod_cast hh
  exact ⟨settle_valid s hs d _ ho hlt, settle_rounding_guarantee s hs d _ hg.1 ho hfloor,
    rfl, rfl⟩

/-- Pay exactly o, collecting the least natural gross input sufficient for o. -/
def discrete_swap_ceil (s : DiscreteState) (o : ℕ) (γ : ℚ) : Option DiscreteState :=
  if hs : s.Valid then
    if valid_fee γ ∧ o ≤ s.y ∧ o < s.y + s.β then
      some (s.settle (ceil_div_input (s.lift hs) o γ) o)
    else none
  else none

theorem discrete_ceil_accepts (s : DiscreteState) (hs : s.Valid) (o : ℕ) (γ : ℚ)
    (hg : valid_fee γ) (ho : o ≤ s.y) (hlt : o < s.y + s.β) :
    discrete_swap_ceil s o γ = some (s.settle (ceil_div_input (s.lift hs) o γ) o) := by
  simp [discrete_swap_ceil, hs, hg, ho, hlt]

theorem discrete_ceil_preserves (s t : DiscreteState) (o : ℕ) (γ : ℚ)
    (h : discrete_swap_ceil s o γ = some t) :
    t.Valid ∧ s.K ≤ t.K ∧ t.α = s.α ∧ t.β = s.β := by
  unfold discrete_swap_ceil at h
  split at h <;> try contradiction
  rename_i hs
  split at h <;> try contradiction
  rename_i hg
  cases Option.some.inj h
  have hY : (o : ℚ) < Y (s.lift hs) := by
    dsimp [Y, DiscreteState.lift]
    exact_mod_cast hg.2.2
  have hq := (ceil_input_minimal (s.lift hs) o (ceil_div_input (s.lift hs) o γ) hg.1 hY).mp
    (le_refl _)
  exact ⟨settle_valid s hs _ o hg.2.1 hg.2.2,
    settle_rounding_guarantee s hs _ o hg.1 hg.2.1 hq, rfl, rfl⟩

def DiscreteState.swapAxes (s : DiscreteState) : DiscreteState := ⟨s.y, s.x, s.β, s.α⟩
@[simp] theorem discrete_axes_K (s : DiscreteState) : s.swapAxes.K = s.K := by
  dsimp [DiscreteState.K, DiscreteState.swapAxes]; ring
@[simp] theorem discrete_axes_valid (s : DiscreteState) : s.swapAxes.Valid ↔ s.Valid := by
  exact and_comm

structure DiscreteStep where
  reverse : Bool
  exactOutput : Bool
  amount : ℕ
  fee : ℚ

def discrete_forward (s : DiscreteState) (a : DiscreteStep) :=
  if a.exactOutput then discrete_swap_ceil s a.amount a.fee
  else discrete_swap_floor s a.amount a.fee

def discrete_step (s : DiscreteState) (a : DiscreteStep) :=
  if a.reverse then (discrete_forward s.swapAxes a).map DiscreteState.swapAxes
  else discrete_forward s a

theorem discrete_forward_preserves (s t : DiscreteState) (a : DiscreteStep)
    (h : discrete_forward s a = some t) : t.Valid ∧ s.K ≤ t.K := by
  unfold discrete_forward at h
  split at h
  · exact ⟨(discrete_ceil_preserves s t _ _ h).1, (discrete_ceil_preserves s t _ _ h).2.1⟩
  · exact ⟨(discrete_floor_preserves s t _ _ h).1, (discrete_floor_preserves s t _ _ h).2.1⟩

theorem discrete_step_preserves (s t : DiscreteState) (a : DiscreteStep)
    (h : discrete_step s a = some t) : t.Valid ∧ s.K ≤ t.K := by
  unfold discrete_step at h
  split at h
  · obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
    simpa using discrete_forward_preserves s.swapAxes u a hu
  · exact discrete_forward_preserves s t a h

def discrete_chain (s : DiscreteState) : List DiscreteStep → Option DiscreteState
  | [] => some s
  | a :: as => (discrete_step s a).bind (fun t => discrete_chain t as)

theorem discrete_chain_monotone (as : List DiscreteStep) (s t : DiscreteState)
    (hs : s.Valid) (h : discrete_chain s as = some t) : t.Valid ∧ s.K ≤ t.K := by
  induction as generalizing s with
  | nil => cases Option.some.inj h; exact ⟨hs, le_refl _⟩
  | cons a as ih =>
    obtain ⟨u, hu, ht⟩ := Option.bind_eq_some_iff.mp h
    have hh := discrete_step_preserves s u a hu
    have hi := ih u hh.1 ht
    exact ⟨hi.1, hh.2.trans hi.2⟩

theorem reverse_solvency_criterion (s : VirtualReservesState) {e : ℚ} (he : 0 ≤ e) :
    output_amount (Y s) (X s) e ≤ s.x ↔ s.α * e ≤ s.x * Y s :=
  solvency_criterion_iff (swapAxes s) he

theorem reverse_growth_identity (s : VirtualReservesState) {d γ : ℚ}
    (hd : 0 ≤ d) (hg : valid_fee γ) :
    (s.x - quote (swapAxes s) d γ + s.α) * (s.y + d + s.β) =
      invariant s + γ * d * (X s - quote (swapAxes s) d γ) := by
  simpa [swapAxes, X, Y, invariant, mul_comm] using invariant_growth_identity (swapAxes s) hd hg

theorem strict_growth (s : VirtualReservesState) {d γ : ℚ}
    (hd : 0 < d) (hg : valid_fee γ) (hγ : 0 < γ) :
    invariant s < (s.x + d + s.α) * (s.y - quote s d γ + s.β) := by
  rw [invariant_growth_identity s hd.le hg]
  exact lt_add_of_pos_right _
    (mul_pos (mul_pos hγ hd) (remaining_pos s (effective_nonneg hd.le hg)))

theorem rational_chain_offsets (as : List SwapStep) (s t : VirtualReservesState)
    (h : execute_chain s as = some t) : t.α = s.α ∧ t.β = s.β := by
  induction as generalizing s with
  | nil => cases Option.some.inj h; exact ⟨rfl, rfl⟩
  | cons a as ih =>
    obtain ⟨u, hu, ht⟩ := Option.bind_eq_some_iff.mp h
    have hi : u.α = s.α ∧ u.β = s.β := by
      unfold execute_step at hu
      split at hu
      · obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hu
        have hh := (execute_preserves (swapAxes s) v _ _ hv).2
        exact ⟨hh.2, hh.1⟩
      · exact (execute_preserves s u _ _ hu).2
    have hh := ih u ht
    exact ⟨hh.1.trans hi.1, hh.2.trans hi.2⟩

/-- The effective-reserve rational quote embeds into the earlier real CPMM quote.
Its gamma denotes the effective fraction, whereas this module's gamma is the fee. -/
noncomputable def real_pool (s : VirtualReservesState) (γ : ℚ) (hg : valid_fee γ) :
    DeFiConstantProductSwap.PoolState :=
  ⟨(X s : ℝ), (Y s : ℝ), (1 - γ : ℚ), by exact_mod_cast s.hX,
    by exact_mod_cast s.hY, by exact_mod_cast sub_pos.mpr hg.2,
    by exact_mod_cast (show (1 : ℚ) - γ ≤ 1 by linarith [hg.1])⟩

theorem real_quote_bridge (s : VirtualReservesState) (d γ : ℚ) (hg : valid_fee γ) :
    (quote s d γ : ℝ) = DeFiConstantProductSwap.getAmountOut (real_pool s γ hg) d := by
  simp [quote, output_amount, d_eff, real_pool, DeFiConstantProductSwap.getAmountOut, mul_assoc]

structure DeFiConstantProductVirtualReservesSuite : Prop where
  solvency : ∀ s e, 0 ≤ e →
    (output_amount (X s) (Y s) e ≤ s.y ↔ s.β * e ≤ s.y * X s)
  growth : ∀ s d γ, 0 ≤ d → valid_fee γ →
    (s.x + d + s.α) * (s.y - quote s d γ + s.β) =
      invariant s + γ * d * (Y s - quote s d γ)
  conservation : ∀ s d, 0 ≤ d →
    (s.x + d + s.α) * (s.y - quote s d 0 + s.β) = invariant s
  output_monotone : ∀ s d₁ d₂ γ, valid_fee γ → 0 ≤ d₁ → d₁ < d₂ →
    quote s d₁ γ < quote s d₂ γ
  average_rate : ∀ s d₁ d₂ γ, valid_fee γ → 0 < d₁ → d₁ < d₂ →
    quote s d₂ γ / d₂ ≤ quote s d₁ γ / d₁
  executable_guard : ∀ s d γ, (execute_swap_x_to_y s d γ).isSome = true ↔
    0 ≤ d ∧ valid_fee γ ∧ s.β * d_eff d γ ≤ s.y * X s
  chain : ∀ as s t, execute_chain s as = some t → invariant s ≤ invariant t
  offsets : ∀ as s t, execute_chain s as = some t → t.α = s.α ∧ t.β = s.β
  floor_error : ∀ s (d : ℕ) γ, valid_fee γ →
    0 ≤ quote s d γ - (floor_div_output s d γ : ℚ) ∧
      quote s d γ - (floor_div_output s d γ : ℚ) < 1
  ceil_error : ∀ s (o : ℕ) γ, valid_fee γ → (o : ℚ) < Y s →
    0 ≤ (ceil_div_input s o γ : ℚ) - input_required s o γ ∧
      (ceil_div_input s o γ : ℚ) - input_required s o γ < 1
  minimal_input : ∀ s (o d : ℕ) γ, valid_fee γ → (o : ℚ) < Y s →
    (ceil_div_input s o γ ≤ d ↔ (o : ℚ) ≤ quote s d γ)
  discrete_floor : ∀ s t d γ, discrete_swap_floor s d γ = some t →
    t.Valid ∧ s.K ≤ t.K ∧ t.α = s.α ∧ t.β = s.β
  discrete_ceil : ∀ s t o γ, discrete_swap_ceil s o γ = some t →
    t.Valid ∧ s.K ≤ t.K ∧ t.α = s.α ∧ t.β = s.β
  discrete_chain : ∀ as s t, s.Valid → discrete_chain s as = some t →
    t.Valid ∧ s.K ≤ t.K

theorem verification_suite : DeFiConstantProductVirtualReservesSuite where
  solvency := fun s _ => solvency_criterion_iff s
  growth := fun s _ _ => invariant_growth_identity s
  conservation := fun s _ => invariant_exact_conservation s
  output_monotone := fun s _ _ _ => output_strict_mono s
  average_rate := fun s _ _ _ => price_impact_average_rate s
  executable_guard := execute_success_iff
  chain := dynamic_fee_chain_monotone
  offsets := rational_chain_offsets
  floor_error := fun s d _ => floor_output_error s d
  ceil_error := fun s o _ => ceil_input_error s o
  minimal_input := fun s o d _ => ceil_input_minimal s o d
  discrete_floor := discrete_floor_preserves
  discrete_ceil := discrete_ceil_preserves
  discrete_chain := discrete_chain_monotone

end DeFiConstantProductVirtualReserves
