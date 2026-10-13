/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DeFiConcentratedLiquidity
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Discrete concentrated-liquidity reference arithmetic

Executable Q64.96 reference quantization, directed rounding, maximal budgeted grid
search and position-derived liquidity transitions. No Solidity branch equivalence,
wide-grid efficiency or complete TickMath-driven pool loop is asserted.
-/
namespace DeFiConcentratedLiquidityMath

def scale : ℕ := 2 ^ 96

theorem scale_pos : 0 < scale := by norm_num [scale]

def idealPrice (i : ℤ) : ℚ := (10001 / 10000) ^ i

theorem idealPrice_pos (i : ℤ) : 0 < idealPrice i := by
  unfold idealPrice
  exact zpow_pos (by norm_num) i

def decode (s : ℕ) : ℚ := s / (scale : ℚ)

/-- Executable reference quantizer, not the bit-constant algorithm in TickMath. -/
def sqrtPriceReference (i : ℤ) : ℕ := Nat.sqrt ⌊idealPrice i * (scale : ℚ) ^ 2⌋₊

theorem sqrt_reference_bracket (i : ℤ) :
    (sqrtPriceReference i : ℚ) ^ 2 ≤ idealPrice i * (scale : ℚ) ^ 2 ∧
    idealPrice i * (scale : ℚ) ^ 2 < ((sqrtPriceReference i : ℚ) + 1) ^ 2 := by
  have hp : 0 ≤ idealPrice i * (scale : ℚ) ^ 2 := mul_nonneg (idealPrice_pos i).le (sq_nonneg _)
  have hl := Nat.floor_le hp
  have hu := Nat.lt_floor_add_one (idealPrice i * (scale : ℚ) ^ 2)
  have hs := Nat.sqrt_le' ⌊idealPrice i * (scale : ℚ) ^ 2⌋₊
  have ht := Nat.lt_succ_sqrt' ⌊idealPrice i * (scale : ℚ) ^ 2⌋₊
  constructor
  · exact (by exact_mod_cast hs : (sqrtPriceReference i : ℚ) ^ 2 ≤
      (⌊idealPrice i * (scale : ℚ) ^ 2⌋₊ : ℚ)).trans hl
  · have ht' : (⌊idealPrice i * (scale : ℚ) ^ 2⌋₊ : ℚ) + 1 ≤
        ((sqrtPriceReference i : ℚ) + 1) ^ 2 := by
      exact_mod_cast ht
    exact hu.trans_le ht'

/-- One Q64.96 unit bounds the error of the reference quantizer. -/
theorem sqrt_reference_error (i : ℤ) :
    0 ≤ Real.sqrt (idealPrice i : ℝ) - (decode (sqrtPriceReference i) : ℝ) ∧
    Real.sqrt (idealPrice i : ℝ) - (decode (sqrtPriceReference i) : ℝ) <
      1 / (scale : ℝ) := by
  have h := sqrt_reference_bracket i
  have hp : 0 ≤ (idealPrice i : ℝ) := by exact_mod_cast (idealPrice_pos i).le
  have hs : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have hl : (sqrtPriceReference i : ℝ) ^ 2 ≤ (idealPrice i : ℝ) * (scale : ℝ) ^ 2 := by
    exact_mod_cast h.1
  have hu : (idealPrice i : ℝ) * (scale : ℝ) ^ 2 <
      ((sqrtPriceReference i : ℝ) + 1) ^ 2 := by exact_mod_cast h.2
  have he := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg (idealPrice i : ℝ)
  have h0 : (0 : ℝ) ≤ sqrtPriceReference i := Nat.cast_nonneg _
  have hlow : (sqrtPriceReference i : ℝ) ≤ Real.sqrt (idealPrice i : ℝ) * scale := by
    apply (sq_le_sq₀ h0 (mul_nonneg hn hs.le)).mp
    simpa only [mul_pow, he] using hl
  have hhigh : Real.sqrt (idealPrice i : ℝ) * scale < (sqrtPriceReference i : ℝ) + 1 := by
    apply (sq_lt_sq₀ (mul_nonneg hn hs.le) (by positivity)).mp
    simpa only [mul_pow, he] using hu
  simp only [decode, Rat.cast_div, Rat.cast_natCast]
  constructor
  · exact sub_nonneg.mpr ((div_le_iff₀ hs).mpr hlow)
  · apply (lt_div_iff₀ hs).mpr
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hs)]
    linarith

def mulDivFloor (a b c : ℕ) : ℕ := ⌊(a : ℚ) * b / c⌋₊
def mulDivCeil (a b c : ℕ) : ℕ := ⌈(a : ℚ) * b / c⌉₊

theorem floor_div_formula (a b c : ℕ) : mulDivFloor a b c = a * b / c := by
  unfold mulDivFloor
  rw [← Int.floor_toNat, ← Nat.cast_mul, Rat.floor_natCast_div_natCast]
  rw [Int.ofNat_ediv_ofNat]
  rfl

theorem ceil_div_formula (a b c : ℕ) (hc : 0 < c) :
    mulDivCeil a b c = (a * b + c - 1) / c := by
  apply Nat.le_antisymm
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ (by exact_mod_cast hc : (0 : ℚ) < c)).mpr
    have h := Nat.lt_mul_div_succ (a * b + c - 1) hc
    have h' : a * b ≤ ((a * b + c - 1) / c) * c := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm c] at h
      omega
    exact_mod_cast h'
  · have h := Nat.le_ceil ((a : ℚ) * b / c)
    have h' : a * b ≤ mulDivCeil a b c * c := by
      dsimp [mulDivCeil]
      exact_mod_cast (div_le_iff₀ (by exact_mod_cast hc : (0 : ℚ) < c)).mp h
    apply (Nat.div_le_iff_le_mul_add_pred hc).mpr
    rw [Nat.mul_comm c]
    omega

theorem rounding_bounds (a b c : ℕ) :
    (0 ≤ (mulDivCeil a b c : ℚ) - (a : ℚ) * b / c ∧
      (mulDivCeil a b c : ℚ) - (a : ℚ) * b / c < 1) ∧
    (0 ≤ (a : ℚ) * b / c - mulDivFloor a b c ∧
      (a : ℚ) * b / c - mulDivFloor a b c < 1) := by
  have hn : (0 : ℚ) ≤ (a : ℚ) * b / c := by positivity
  have h1 := Nat.le_ceil ((a : ℚ) * b / c)
  have h2 := Nat.ceil_lt_add_one hn
  have h3 := Nat.floor_le hn
  have h4 := Nat.lt_floor_add_one ((a : ℚ) * b / c)
  dsimp [mulDivCeil, mulDivFloor]
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

def amount0Exact (a b L : ℕ) : ℚ := (L * scale : ℕ) * (b - a : ℕ) / (a * b : ℕ)
def amount1Exact (a b L : ℕ) : ℚ := (L : ℚ) * (b - a : ℕ) / scale

def getAmount0Delta (a b L : ℕ) (roundUp : Bool) : ℕ :=
  if roundUp then mulDivCeil (L * scale) (b - a) (a * b)
  else mulDivFloor (L * scale) (b - a) (a * b)

def getAmount1Delta (a b L : ℕ) (roundUp : Bool) : ℕ :=
  if roundUp then mulDivCeil L (b - a) scale
  else mulDivFloor L (b - a) scale

theorem amount0_rounding (a b L : ℕ) :
    amount0Exact a b L ≤ (getAmount0Delta a b L true : ℚ) ∧
    (getAmount0Delta a b L false : ℚ) ≤ amount0Exact a b L ∧
    (getAmount0Delta a b L true : ℚ) - amount0Exact a b L < 1 ∧
    amount0Exact a b L - (getAmount0Delta a b L false : ℚ) < 1 := by
  have h := rounding_bounds (L * scale) (b - a) (a * b)
  simp only [getAmount0Delta, ↓reduceIte, Bool.false_eq_true] 
  dsimp [amount0Exact, amount1Exact]
  exact ⟨by linarith [h.1.1], by linarith [h.2.1], h.1.2, h.2.2⟩

theorem amount1_rounding (a b L : ℕ) :
    amount1Exact a b L ≤ (getAmount1Delta a b L true : ℚ) ∧
    (getAmount1Delta a b L false : ℚ) ≤ amount1Exact a b L ∧
    (getAmount1Delta a b L true : ℚ) - amount1Exact a b L < 1 ∧
    amount1Exact a b L - (getAmount1Delta a b L false : ℚ) < 1 := by
  have h := rounding_bounds L (b - a) scale
  simp only [getAmount1Delta, ↓reduceIte, Bool.false_eq_true]
  dsimp [amount0Exact, amount1Exact]
  exact ⟨by linarith [h.1.1], by linarith [h.2.1], h.1.2, h.2.2⟩

@[simp] theorem amount0_same (a L : ℕ) (r : Bool) : getAmount0Delta a a L r = 0 := by
  simp [getAmount0Delta, mulDivCeil, mulDivFloor]
@[simp] theorem amount1_same (a L : ℕ) (r : Bool) : getAmount1Delta a a L r = 0 := by
  simp [getAmount1Delta, mulDivCeil, mulDivFloor]
@[simp] theorem amount0_zero (a b : ℕ) (r : Bool) : getAmount0Delta a b 0 r = 0 := by
  simp [getAmount0Delta, mulDivCeil, mulDivFloor]
@[simp] theorem amount1_zero (a b : ℕ) (r : Bool) : getAmount1Delta a b 0 r = 0 := by
  simp [getAmount1Delta, mulDivCeil, mulDivFloor]

inductive SwapMode where
  | exactInput
  | exactOutput
  deriving DecidableEq, Repr

structure SwapParams where
  current : ℕ
  target : ℕ
  liquidity : ℕ
  remaining : ℕ
  feePips : ℕ
  mode : SwapMode
  current_pos : 0 < current
  target_pos : 0 < target
  fee_lt : feePips < 1000000
  deriving Repr

def zeroForOne (p : SwapParams) : Bool := p.target ≤ p.current

def distance (p : SwapParams) : ℕ :=
  if p.target ≤ p.current then p.current - p.target else p.target - p.current

def priceAt (p : SwapParams) (k : ℕ) : ℕ :=
  if p.target ≤ p.current then p.current - k else p.current + k

@[simp] theorem priceAt_zero (p : SwapParams) : priceAt p 0 = p.current := by
  simp [priceAt]

theorem priceAt_target (p : SwapParams) : priceAt p (distance p) = p.target := by
  dsimp [priceAt, distance]
  split <;> omega

theorem priceAt_bounds (p : SwapParams) (k : ℕ) (hk : k ≤ distance p) :
    min p.current p.target ≤ priceAt p k ∧ priceAt p k ≤ max p.current p.target := by
  by_cases h : p.target ≤ p.current
  · simp only [priceAt, distance, h, ↓reduceIte] at *
    omega
  · simp only [priceAt, distance, h, ↓reduceIte] at *
    omega

def inputAt (p : SwapParams) (k : ℕ) : ℕ :=
  if p.target ≤ p.current then getAmount0Delta (priceAt p k) p.current p.liquidity true
  else getAmount1Delta p.current (priceAt p k) p.liquidity true

def outputAt (p : SwapParams) (k : ℕ) : ℕ :=
  if p.target ≤ p.current then getAmount1Delta (priceAt p k) p.current p.liquidity false
  else getAmount0Delta p.current (priceAt p k) p.liquidity false

def feeFor (p : SwapParams) (amountIn : ℕ) : ℕ :=
  mulDivCeil amountIn p.feePips (1000000 - p.feePips)

@[simp] theorem inputAt_zero (p : SwapParams) : inputAt p 0 = 0 := by
  simp [inputAt]
@[simp] theorem outputAt_zero (p : SwapParams) : outputAt p 0 = 0 := by
  simp [outputAt]
@[simp] theorem feeFor_zero (p : SwapParams) : feeFor p 0 = 0 := by
  simp [feeFor, mulDivCeil]

def admissible (p : SwapParams) (k : ℕ) : Prop :=
  match p.mode with
  | .exactInput => inputAt p k + feeFor p (inputAt p k) ≤ p.remaining
  | .exactOutput => outputAt p k ≤ p.remaining

instance (p : SwapParams) (k : ℕ) : Decidable (admissible p k) := by
  unfold admissible
  split <;> infer_instance

theorem zero_admissible (p : SwapParams) : admissible p 0 := by
  unfold admissible
  split <;> simp

def feasibleProgress (p : SwapParams) : Finset ℕ :=
  (Finset.range (distance p + 1)).filter (admissible p)

theorem zero_feasible (p : SwapParams) : 0 ∈ feasibleProgress p := by
  simp [feasibleProgress, zero_admissible]

/-- Exhaustive executable reference search. No gas or asymptotic efficiency claim. -/
def chosenProgress (p : SwapParams) : ℕ :=
  if p.remaining = 0 then 0 else (feasibleProgress p).max' ⟨0, zero_feasible p⟩

theorem chosen_feasible (p : SwapParams) : chosenProgress p ∈ feasibleProgress p := by
  unfold chosenProgress
  split
  · exact zero_feasible p
  · exact Finset.max'_mem _ _

theorem chosen_spec (p : SwapParams) :
    chosenProgress p ≤ distance p ∧ admissible p (chosenProgress p) := by
  have h := chosen_feasible p
  simp only [feasibleProgress, Finset.mem_filter, Finset.mem_range] at h
  exact ⟨by omega, h.2⟩

theorem chosen_maximal (p : SwapParams) (hr : p.remaining ≠ 0) (k : ℕ)
    (hk : k ≤ distance p) (ha : admissible p k) : k ≤ chosenProgress p := by
  simp only [chosenProgress, hr, ↓reduceIte]
  apply Finset.le_max'
  simp only [feasibleProgress, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, ha⟩

structure SwapResult where
  nextPrice : ℕ
  amountIn : ℕ
  amountOut : ℕ
  fee : ℕ
  deriving DecidableEq, Repr

def computeSwapStep (p : SwapParams) : SwapResult :=
  let k := chosenProgress p
  ⟨priceAt p k, inputAt p k, outputAt p k, feeFor p (inputAt p k)⟩

theorem swap_price_bounds (p : SwapParams) :
    min p.current p.target ≤ (computeSwapStep p).nextPrice ∧
    (computeSwapStep p).nextPrice ≤ max p.current p.target :=
  priceAt_bounds p _ (chosen_spec p).1

theorem swap_price_positive (p : SwapParams) : 0 < (computeSwapStep p).nextPrice := by
  have h := (swap_price_bounds p).1
  have h1 := p.current_pos
  have h2 := p.target_pos
  omega

theorem exact_input_budget (p : SwapParams) (hm : p.mode = .exactInput) :
    (computeSwapStep p).amountIn + (computeSwapStep p).fee ≤ p.remaining := by
  have h := (chosen_spec p).2
  simpa only [admissible, hm, computeSwapStep] using h

theorem exact_output_budget (p : SwapParams) (hm : p.mode = .exactOutput) :
    (computeSwapStep p).amountOut ≤ p.remaining := by
  have h := (chosen_spec p).2
  simpa only [admissible, hm, computeSwapStep] using h

theorem swap_zero_remaining (p : SwapParams) (hr : p.remaining = 0) :
    computeSwapStep p = ⟨p.current, 0, 0, 0⟩ := by
  simp [computeSwapStep, chosenProgress, hr]

theorem swap_reaches_affordable_target (p : SwapParams) (hr : p.remaining ≠ 0)
    (ha : admissible p (distance p)) : (computeSwapStep p).nextPrice = p.target := by
  have hk : chosenProgress p = distance p :=
    Nat.le_antisymm (chosen_spec p).1 (chosen_maximal p hr _ le_rfl ha)
  simpa only [computeSwapStep, hk] using priceAt_target p

theorem zero_liquidity_admissible (p : SwapParams) (hL : p.liquidity = 0) (k : ℕ) :
    admissible p k := by
  have hi : inputAt p k = 0 := by simp [inputAt, hL]
  have ho : outputAt p k = 0 := by simp [outputAt, hL]
  unfold admissible
  split <;> simp [hi, ho]

theorem zero_liquidity_transit (p : SwapParams) (hL : p.liquidity = 0)
    (hr : p.remaining ≠ 0) : computeSwapStep p = ⟨p.target, 0, 0, 0⟩ := by
  have ht := swap_reaches_affordable_target p hr (zero_liquidity_admissible p hL _)
  have hi : inputAt p (chosenProgress p) = 0 := by simp [inputAt, hL]
  have ho : outputAt p (chosenProgress p) = 0 := by simp [outputAt, hL]
  change priceAt p (chosenProgress p) = p.target at ht
  simp only [computeSwapStep, ht, hi, ho, feeFor_zero]

/-- Finite positions induce the net tick table; it is not an unconstrained oracle. -/
structure Position where
  lower : ℤ
  upper : ℤ
  amount : ℕ
  ordered : lower < upper
  deriving Repr

def positionLiquidity (p : Position) (i : ℤ) : ℤ :=
  if p.lower ≤ i ∧ i < p.upper then p.amount else 0

def positionNet (p : Position) (i : ℤ) : ℤ :=
  (if p.lower = i then (p.amount : ℤ) else 0) -
    (if p.upper = i then (p.amount : ℤ) else 0)

def activeLiquidity (ps : List Position) (i : ℤ) : ℤ :=
  (ps.map (fun p => positionLiquidity p i)).sum

def tickNet (ps : List Position) (i : ℤ) : ℤ :=
  (ps.map (fun p => positionNet p i)).sum

theorem position_nonneg (p : Position) (i : ℤ) : 0 ≤ positionLiquidity p i := by
  unfold positionLiquidity
  split <;> positivity

theorem active_nonneg (ps : List Position) (i : ℤ) : 0 ≤ activeLiquidity ps i := by
  induction ps with
  | nil => simp [activeLiquidity]
  | cons p ps ih =>
    simp only [activeLiquidity, List.map_cons, List.sum_cons] at *
    exact add_nonneg (position_nonneg p i) ih

theorem position_cross (p : Position) (i : ℤ) :
    positionLiquidity p (i + 1) = positionLiquidity p i + positionNet p (i + 1) := by
  have h := p.ordered
  unfold positionLiquidity positionNet
  split_ifs <;> omega

theorem active_cross (ps : List Position) (i : ℤ) :
    activeLiquidity ps (i + 1) = activeLiquidity ps i + tickNet ps (i + 1) := by
  induction ps with
  | nil => simp [activeLiquidity, tickNet]
  | cons p ps ih =>
    simp only [activeLiquidity, tickNet, List.map_cons, List.sum_cons] at *
    rw [position_cross, ih]
    ring

def crossTick (L : ℕ) (net : ℤ) (down : Bool) : ℤ :=
  if down then (L : ℤ) - net else (L : ℤ) + net

theorem cross_right_nonnegative (ps : List Position) (i : ℤ) :
    crossTick (activeLiquidity ps i).toNat (tickNet ps (i + 1)) false =
      activeLiquidity ps (i + 1) ∧
    0 ≤ crossTick (activeLiquidity ps i).toNat (tickNet ps (i + 1)) false := by
  have he : crossTick (activeLiquidity ps i).toNat (tickNet ps (i + 1)) false =
      activeLiquidity ps (i + 1) := by
    simp only [crossTick, Bool.false_eq_true, ↓reduceIte,
      Int.toNat_of_nonneg (active_nonneg ps i)]
    exact (active_cross ps i).symm
  exact ⟨he, he.symm ▸ active_nonneg ps (i + 1)⟩

theorem cross_left_nonnegative (ps : List Position) (i : ℤ) :
    crossTick (activeLiquidity ps i).toNat (tickNet ps i) true =
      activeLiquidity ps (i - 1) ∧
    0 ≤ crossTick (activeLiquidity ps i).toNat (tickNet ps i) true := by
  have h := active_cross ps (i - 1)
  have he : crossTick (activeLiquidity ps i).toNat (tickNet ps i) true =
      activeLiquidity ps (i - 1) := by
    simp only [crossTick, ↓reduceIte, Int.toNat_of_nonneg (active_nonneg ps i)]
    have hh : i - 1 + 1 = i := by omega
    rw [hh] at h
    omega
  exact ⟨he, he.symm ▸ active_nonneg ps (i - 1)⟩

structure TickState where
  tick : ℤ
  liquidity : ℕ
  deriving DecidableEq, Repr

def ValidTickState (ps : List Position) (s : TickState) : Prop :=
  (s.liquidity : ℤ) = activeLiquidity ps s.tick

def crossBoundary (ps : List Position) (s : TickState) (down : Bool) : TickState :=
  if down then ⟨s.tick - 1, (crossTick s.liquidity (tickNet ps s.tick) true).toNat⟩
  else ⟨s.tick + 1, (crossTick s.liquidity (tickNet ps (s.tick + 1)) false).toNat⟩

theorem cross_boundary_preserves (ps : List Position) (s : TickState)
    (hv : ValidTickState ps s) (down : Bool) :
    ValidTickState ps (crossBoundary ps s down) := by
  have hL : s.liquidity = (activeLiquidity ps s.tick).toNat := by
    rw [← hv]
    simp
  cases down
  · simp only [crossBoundary, Bool.false_eq_true, ↓reduceIte, ValidTickState]
    rw [hL, (cross_right_nonnegative ps s.tick).1,
      Int.toNat_of_nonneg (active_nonneg ps (s.tick + 1))]
  · simp only [crossBoundary, ↓reduceIte, ValidTickState]
    rw [hL, (cross_left_nonnegative ps s.tick).1,
      Int.toNat_of_nonneg (active_nonneg ps (s.tick - 1))]

def crossTrace (ps : List Position) : TickState → List Bool → TickState
  | s, [] => s
  | s, down :: ds => crossTrace ps (crossBoundary ps s down) ds

theorem cross_trace_preserves (ps : List Position) (ds : List Bool) (s : TickState)
    (hv : ValidTickState ps s) : ValidTickState ps (crossTrace ps s ds) := by
  induction ds generalizing s with
  | nil => exact hv
  | cons d ds ih => exact ih _ (cross_boundary_preserves ps s hv d)

/-- The signed changes telescope along the actual sequence of boundary states. -/
def traceDelta (ps : List Position) : TickState → List Bool → ℤ
  | _, [] => 0
  | s, d :: ds =>
    (if d then -tickNet ps s.tick else tickNet ps (s.tick + 1)) +
      traceDelta ps (crossBoundary ps s d) ds

theorem boundary_delta (ps : List Position) (s : TickState)
    (hv : ValidTickState ps s) (d : Bool) :
    ((crossBoundary ps s d).liquidity : ℤ) = (s.liquidity : ℤ) +
      (if d then -tickNet ps s.tick else tickNet ps (s.tick + 1)) := by
  have h := cross_boundary_preserves ps s hv d
  have hx := active_cross ps s.tick
  have hy := active_cross ps (s.tick - 1)
  change (s.liquidity : ℤ) = _ at hv
  cases d <;> simp only [crossBoundary, Bool.false_eq_true, ↓reduceIte, ValidTickState] at *
  · omega
  · have hh : s.tick - 1 + 1 = s.tick := by omega
    rw [hh] at hy
    omega

theorem cross_trace_telescope (ps : List Position) (ds : List Bool) (s : TickState)
    (hv : ValidTickState ps s) :
    ((crossTrace ps s ds).liquidity : ℤ) = s.liquidity + traceDelta ps s ds := by
  induction ds generalizing s with
  | nil => simp [crossTrace, traceDelta]
  | cons d ds ih =>
    simp only [crossTrace, traceDelta]
    rw [ih _ (cross_boundary_preserves ps s hv d), boundary_delta ps s hv d]
    ring

/-- Returning across the same boundary restores the position-derived state. -/
theorem crossing_round_trip (ps : List Position) (s : TickState)
    (hv : ValidTickState ps s) : crossTrace ps s [false, true] = s := by
  have h := cross_trace_preserves ps [false, true] s hv
  have ht : (crossTrace ps s [false, true]).tick = s.tick := by
    simp [crossTrace, crossBoundary]
  have hl : (crossTrace ps s [false, true]).liquidity = s.liquidity := by
    unfold ValidTickState at *
    rw [ht, ← hv] at h
    exact_mod_cast h
  cases s
  cases he : crossTrace ps _ [false, true]
  simp_all

theorem amount0_rational_bridge (a b L : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    amount0Exact a b L = (L : ℚ) * (1 / decode a - 1 / decode b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  have hs : (scale : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt scale_pos)
  simp only [amount0Exact, decode, Nat.cast_mul, Nat.cast_sub hab]
  field_simp

theorem amount1_rational_bridge (a b L : ℕ) (hab : a ≤ b) :
    amount1Exact a b L = (L : ℚ) * (decode b - decode a) := by
  simp only [amount1Exact, decode, Nat.cast_sub hab]
  ring

theorem amount1_real_bridge (a b L : ℕ) (hab : a ≤ b) :
    (amount1Exact a b L : ℝ) =
      DeFiConcentratedLiquidity.deltaY L (decode a : ℝ) (decode b : ℝ) := by
  rw [amount1_rational_bridge a b L hab]
  simp [DeFiConcentratedLiquidity.deltaY]

theorem amount0_real_bridge (a b L : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    (amount0Exact a b L : ℝ) =
      DeFiConcentratedLiquidity.deltaX L (decode b : ℝ) (decode a : ℝ) := by
  rw [amount0_rational_bridge a b L ha hab]
  simp [DeFiConcentratedLiquidity.deltaX]

def inputExactAt (p : SwapParams) (k : ℕ) : ℚ :=
  if p.target ≤ p.current then amount0Exact (priceAt p k) p.current p.liquidity
  else amount1Exact p.current (priceAt p k) p.liquidity

def outputExactAt (p : SwapParams) (k : ℕ) : ℚ :=
  if p.target ≤ p.current then amount1Exact (priceAt p k) p.current p.liquidity
  else amount0Exact p.current (priceAt p k) p.liquidity

theorem swap_input_rounds_up (p : SwapParams) :
    inputExactAt p (chosenProgress p) ≤ ((computeSwapStep p).amountIn : ℚ) ∧
    ((computeSwapStep p).amountIn : ℚ) - inputExactAt p (chosenProgress p) < 1 := by
  dsimp [computeSwapStep, inputAt, inputExactAt]
  split
  · exact ⟨(amount0_rounding _ _ _).1, (amount0_rounding _ _ _).2.2.1⟩
  · exact ⟨(amount1_rounding _ _ _).1, (amount1_rounding _ _ _).2.2.1⟩

theorem swap_output_rounds_down (p : SwapParams) :
    ((computeSwapStep p).amountOut : ℚ) ≤ outputExactAt p (chosenProgress p) ∧
    outputExactAt p (chosenProgress p) - ((computeSwapStep p).amountOut : ℚ) < 1 := by
  dsimp [computeSwapStep, outputAt, outputExactAt]
  split
  · exact ⟨(amount1_rounding _ _ _).2.1, (amount1_rounding _ _ _).2.2.2⟩
  · exact ⟨(amount0_rounding _ _ _).2.1, (amount0_rounding _ _ _).2.2.2⟩

def availableInput (p : SwapParams) : ℕ :=
  mulDivFloor p.remaining (1000000 - p.feePips) 1000000

/-- The fee-inclusive budget is equivalent to the usual fee-discounted input budget. -/
theorem fee_budget_iff (p : SwapParams) (a : ℕ) :
    a + feeFor p a ≤ p.remaining ↔ a ≤ availableInput p := by
  have hd : 0 < 1000000 - p.feePips := by have := p.fee_lt; omega
  have hd' : (0 : ℚ) < (1000000 - p.feePips : ℕ) := by exact_mod_cast hd
  have hdcast : ((1000000 - p.feePips : ℕ) : ℚ) = 1000000 - p.feePips := by
    rw [Nat.cast_sub (Nat.le_of_lt p.fee_lt)]
    norm_num
  have hav : a ≤ availableInput p ↔ (a : ℚ) ≤
      (p.remaining : ℚ) * (1000000 - p.feePips : ℕ) / 1000000 := by
    exact Nat.le_floor_iff (by positivity)
  rw [hav]
  constructor
  · intro h
    have hc := Nat.le_ceil ((a : ℚ) * p.feePips / (1000000 - p.feePips : ℕ))
    have hq : (a : ℚ) + (feeFor p a : ℚ) ≤ p.remaining := by exact_mod_cast h
    have hh : (a : ℚ) * p.feePips / (1000000 - p.feePips : ℕ) ≤ p.remaining - a := by
      change (a : ℚ) * p.feePips / (1000000 - p.feePips : ℕ) ≤ (feeFor p a : ℚ) at hc
      linarith
    have hx := (div_le_iff₀ hd').mp hh
    rw [hdcast] at *
    apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 1000000)).mpr
    nlinarith
  · intro h
    have ha : a ≤ p.remaining := by
      have hdle : ((1000000 - p.feePips : ℕ) : ℚ) ≤ 1000000 := by
        exact_mod_cast (Nat.sub_le 1000000 p.feePips)
      have hn : (0 : ℚ) ≤ p.remaining := Nat.cast_nonneg _
      have hx := (le_div_iff₀ (by norm_num : (0 : ℚ) < 1000000)).mp h
      have hq : (a : ℚ) ≤ p.remaining := by nlinarith
      exact_mod_cast hq
    have hf : feeFor p a ≤ p.remaining - a := by
      apply Nat.ceil_le.mpr
      apply (div_le_iff₀ hd').mpr
      rw [Nat.cast_sub ha, hdcast]
      have hx := (le_div_iff₀ (by norm_num : (0 : ℚ) < 1000000)).mp h
      rw [hdcast] at hx
      nlinarith
    omega

/-- Sum of actual fee-inclusive charges, with each remaining budget computed by subtraction. -/
def spendTrace : List SwapParams → ℕ → ℕ
  | [], _ => 0
  | p :: ps, budget =>
    let step := computeSwapStep {p with remaining := budget, mode := .exactInput}
    let spent := step.amountIn + step.fee
    spent + spendTrace ps (budget - spent)

theorem spend_trace_budget (ps : List SwapParams) (budget : ℕ) : spendTrace ps budget ≤ budget := by
  induction ps generalizing budget with
  | nil => simp [spendTrace]
  | cons p ps ih =>
    have h := exact_input_budget {p with remaining := budget, mode := .exactInput} rfl
    have ht := ih (budget -
      ((computeSwapStep {p with remaining := budget, mode := .exactInput}).amountIn +
      (computeSwapStep {p with remaining := budget, mode := .exactInput}).fee))
    dsimp [spendTrace]
    dsimp at h
    omega

/-- A boundary is consumed only from its appropriate side and only after being reached. -/
def crossAt (ps : List Position) (s : TickState) (boundary : ℤ)
    (down reached : Bool) : TickState :=
  if reached && (if down then s.tick = boundary else s.tick + 1 = boundary)
  then crossBoundary ps s down else s

theorem cross_at_preserves (ps : List Position) (s : TickState)
    (hv : ValidTickState ps s) (b : ℤ) (d reached : Bool) :
    ValidTickState ps (crossAt ps s b d reached) := by
  unfold crossAt
  split_ifs <;> first | exact cross_boundary_preserves ps s hv d | exact hv

theorem cross_at_idempotent (ps : List Position) (s : TickState) (b : ℤ) (d : Bool) :
    crossAt ps (crossAt ps s b d true) b d true = crossAt ps s b d true := by
  cases d
  · by_cases h : s.tick + 1 = b
    · simp [crossAt, crossBoundary, h]
    · simp [crossAt, h]
  · by_cases h : s.tick = b
    · simp [crossAt, crossBoundary, h]
    · simp [crossAt, h]

def crossAfterSwap (ps : List Position) (s : TickState) (b : ℤ) (p : SwapParams) : TickState :=
  crossAt ps s b (zeroForOne p) ((computeSwapStep p).nextPrice == p.target)

theorem cross_after_swap_preserves (ps : List Position) (s : TickState)
    (hv : ValidTickState ps s) (b : ℤ) (p : SwapParams) :
    ValidTickState ps (crossAfterSwap ps s b p) :=
  cross_at_preserves ps s hv b _ _

theorem unreached_boundary_unchanged (ps : List Position) (s : TickState) (b : ℤ)
    (p : SwapParams) (h : (computeSwapStep p).nextPrice ≠ p.target) :
    crossAfterSwap ps s b p = s := by
  simp [crossAfterSwap, crossAt, h]

structure DeFiConcentratedLiquidityMathSuite : Prop where
  quantization : ∀ i, 0 ≤ Real.sqrt (idealPrice i : ℝ) -
    (decode (sqrtPriceReference i) : ℝ) ∧
    Real.sqrt (idealPrice i : ℝ) - (decode (sqrtPriceReference i) : ℝ) < 1 / (scale : ℝ)
  floor_formula : ∀ a b c, mulDivFloor a b c = a * b / c
  ceil_formula : ∀ a b c, 0 < c → mulDivCeil a b c = (a * b + c - 1) / c
  rounding : ∀ a b c,
    (0 ≤ (mulDivCeil a b c : ℚ) - (a : ℚ) * b / c ∧
      (mulDivCeil a b c : ℚ) - (a : ℚ) * b / c < 1) ∧
    (0 ≤ (a : ℚ) * b / c - mulDivFloor a b c ∧
      (a : ℚ) * b / c - mulDivFloor a b c < 1)
  input_budget : ∀ p, p.mode = .exactInput →
    (computeSwapStep p).amountIn + (computeSwapStep p).fee ≤ p.remaining
  output_budget : ∀ p, p.mode = .exactOutput → (computeSwapStep p).amountOut ≤ p.remaining
  fee_discount : ∀ p a, a + feeFor p a ≤ p.remaining ↔ a ≤ availableInput p
  price_bounds : ∀ p, min p.current p.target ≤ (computeSwapStep p).nextPrice ∧
    (computeSwapStep p).nextPrice ≤ max p.current p.target
  maximal : ∀ p, p.remaining ≠ 0 → ∀ k, k ≤ distance p →
    admissible p k → k ≤ chosenProgress p
  no_undercollection : ∀ p, inputExactAt p (chosenProgress p) ≤
    ((computeSwapStep p).amountIn : ℚ)
  no_overpayment : ∀ p, ((computeSwapStep p).amountOut : ℚ) ≤
    outputExactAt p (chosenProgress p)
  tick_trace : ∀ ps ds s, ValidTickState ps s → ValidTickState ps (crossTrace ps s ds)
  tick_telescope : ∀ ps ds s, ValidTickState ps s →
    ((crossTrace ps s ds).liquidity : ℤ) = s.liquidity + traceDelta ps s ds
  trace_budget : ∀ ps budget, spendTrace ps budget ≤ budget
  no_double_cross : ∀ ps s b d,
    crossAt ps (crossAt ps s b d true) b d true = crossAt ps s b d true
  real_bridge : ∀ a b L, 0 < a → a ≤ b → (amount0Exact a b L : ℝ) =
    DeFiConcentratedLiquidity.deltaX L (decode b : ℝ) (decode a : ℝ)

theorem verification_suite : DeFiConcentratedLiquidityMathSuite := {
  quantization := sqrt_reference_error
  floor_formula := floor_div_formula
  ceil_formula := ceil_div_formula
  rounding := rounding_bounds
  input_budget := exact_input_budget
  output_budget := exact_output_budget
  fee_discount := fee_budget_iff
  price_bounds := swap_price_bounds
  maximal := chosen_maximal
  no_undercollection := fun p => (swap_input_rounds_up p).1
  no_overpayment := fun p => (swap_output_rounds_down p).1
  tick_trace := cross_trace_preserves
  tick_telescope := cross_trace_telescope
  trace_budget := spend_trace_budget
  no_double_cross := cross_at_idempotent
  real_bridge := amount0_real_bridge
}

end DeFiConcentratedLiquidityMath
