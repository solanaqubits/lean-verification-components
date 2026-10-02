import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false
noncomputable section

namespace DeFiConcentratedLiquidity

/-- Positive liquidity and a price strictly inside the prescribed range. -/
structure RangePosition where
  L : ℝ
  sqrtP : ℝ
  sqrtPl : ℝ
  sqrtPu : ℝ
  hL_pos : 0 < L
  hP_pos : 0 < sqrtP
  hPl_pos : 0 < sqrtPl
  hPu_pos : 0 < sqrtPu
  hPl_lt_P : sqrtPl < sqrtP
  hP_lt_Pu : sqrtP < sqrtPu

def virtualX (L sqrtP : ℝ) : ℝ := L / sqrtP
def virtualY (L sqrtP : ℝ) : ℝ := L * sqrtP

theorem virtual_reserves_product_eq_L_sq (L sqrtP : ℝ) (hP : sqrtP ≠ 0) :
    virtualX L sqrtP * virtualY L sqrtP = L ^ 2 := by
  dsimp [virtualX, virtualY]
  field_simp

def realX (pos : RangePosition) : ℝ := pos.L * (1 / pos.sqrtP - 1 / pos.sqrtPu)
def realY (pos : RangePosition) : ℝ := pos.L * (pos.sqrtP - pos.sqrtPl)

theorem realX_pos (pos : RangePosition) : 0 < realX pos := by
  exact mul_pos pos.hL_pos
    (sub_pos.mpr (one_div_lt_one_div_of_lt pos.hP_pos pos.hP_lt_Pu))

theorem realY_pos (pos : RangePosition) : 0 < realY pos :=
  mul_pos pos.hL_pos (sub_pos.mpr pos.hPl_lt_P)

theorem real_reserves_shifted_product_eq_L_sq (pos : RangePosition) :
    (realX pos + pos.L / pos.sqrtPu) * (realY pos + pos.L * pos.sqrtPl) = pos.L ^ 2 := by
  have hx : realX pos + pos.L / pos.sqrtPu = virtualX pos.L pos.sqrtP := by
    dsimp [realX, virtualX]
    ring
  have hy : realY pos + pos.L * pos.sqrtPl = virtualY pos.L pos.sqrtP := by
    dsimp [realY, virtualY]
    ring
  rw [hx, hy]
  exact virtual_reserves_product_eq_L_sq _ _ (ne_of_gt pos.hP_pos)

def deltaY (L sqrtP sqrtP_next : ℝ) : ℝ := L * (sqrtP_next - sqrtP)
def deltaX (L sqrtP sqrtP_next : ℝ) : ℝ := L * (1 / sqrtP_next - 1 / sqrtP)

theorem deltaY_pos_of_price_increase (L sqrtP sqrtP_next : ℝ)
    (hL : 0 < L) (h_inc : sqrtP < sqrtP_next) : 0 < deltaY L sqrtP sqrtP_next :=
  mul_pos hL (sub_pos.mpr h_inc)

theorem deltaX_pos_of_price_decrease (L sqrtP sqrtP_next : ℝ)
    (hL : 0 < L) (h_next_pos : 0 < sqrtP_next) (h_dec : sqrtP_next < sqrtP) :
    0 < deltaX L sqrtP sqrtP_next :=
  mul_pos hL (sub_pos.mpr (one_div_lt_one_div_of_lt h_next_pos h_dec))

/-- Positive liquidity and ordinary price endpoints; preserves the older root-price API. -/
structure PriceRangePosition where
  L : ℝ
  pa : ℝ
  pb : ℝ
  hL_pos : 0 < L
  hpa_pos : 0 < pa
  hpa_lt_pb : pa < pb

theorem pb_pos (r : PriceRangePosition) : 0 < r.pb :=
  lt_trans r.hpa_pos r.hpa_lt_pb

theorem sqrt_pa_lt_sqrt_pb (r : PriceRangePosition) : Real.sqrt r.pa < Real.sqrt r.pb :=
  Real.sqrt_lt_sqrt (le_of_lt r.hpa_pos) r.hpa_lt_pb

theorem sqrt_pa_pos (r : PriceRangePosition) : 0 < Real.sqrt r.pa :=
  Real.sqrt_pos.mpr r.hpa_pos

theorem sqrt_pb_pos (r : PriceRangePosition) : 0 < Real.sqrt r.pb :=
  Real.sqrt_pos.mpr (pb_pos r)

/-- Unclamped real formula; outside the range it need not be nonnegative. -/
def amountX (L p pb : ℝ) : ℝ := L * (1 / Real.sqrt p - 1 / Real.sqrt pb)

def amountY (L p pa : ℝ) : ℝ := L * (Real.sqrt p - Real.sqrt pa)

theorem amount_x_zero_at_upper (r : PriceRangePosition) : amountX r.L r.pb r.pb = 0 := by
  simp [amountX]

theorem amount_y_zero_at_lower (r : PriceRangePosition) : amountY r.L r.pa r.pa = 0 := by
  simp [amountY]

def maxDeltaX (r : PriceRangePosition) : ℝ :=
  r.L * (1 / Real.sqrt r.pa - 1 / Real.sqrt r.pb)

def maxDeltaY (r : PriceRangePosition) : ℝ := r.L * (Real.sqrt r.pb - Real.sqrt r.pa)

theorem max_delta_x_pos (r : PriceRangePosition) : 0 < maxDeltaX r :=
  mul_pos r.hL_pos (sub_pos.mpr
    (one_div_lt_one_div_of_lt (sqrt_pa_pos r) (sqrt_pa_lt_sqrt_pb r)))

theorem max_delta_y_pos (r : PriceRangePosition) : 0 < maxDeltaY r :=
  mul_pos r.hL_pos (sub_pos.mpr (sqrt_pa_lt_sqrt_pb r))

def shiftedVirtualX (realAmount L pb : ℝ) : ℝ := realAmount + L / Real.sqrt pb

def shiftedVirtualY (realAmount L pa : ℝ) : ℝ := realAmount + L * Real.sqrt pa

/-- Algebraic identity for any positive p, not a piecewise reserve model outside the range. -/
theorem virtual_reserves_product (r : PriceRangePosition) (p : ℝ) (hp_pos : 0 < p) :
    shiftedVirtualX (amountX r.L p r.pb) r.L r.pb *
      shiftedVirtualY (amountY r.L p r.pa) r.L r.pa = r.L ^ 2 := by
  have hx : shiftedVirtualX (amountX r.L p r.pb) r.L r.pb = virtualX r.L (Real.sqrt p) := by
    dsimp [shiftedVirtualX, amountX, virtualX]
    ring
  have hy : shiftedVirtualY (amountY r.L p r.pa) r.L r.pa = virtualY r.L (Real.sqrt p) := by
    dsimp [shiftedVirtualY, amountY, virtualY]
    ring
  rw [hx, hy]
  exact virtual_reserves_product_eq_L_sq _ _ (ne_of_gt (Real.sqrt_pos.mpr hp_pos))

/-- Positive liquidity with ordered positive root-price endpoints. -/
structure RangePool where
  L : ℝ
  sa : ℝ
  sb : ℝ
  hL : 0 < L
  hsa : 0 < sa
  hab : sa < sb

theorem sb_pos (p : RangePool) : 0 < p.sb := lt_trans p.hsa p.hab

/-- Unclamped formula: s is not constrained to the prescribed range. -/
def realReserveX (p : RangePool) (s : ℝ) : ℝ := p.L * (1 / s - 1 / p.sb)

def realReserveY (p : RangePool) (s : ℝ) : ℝ := p.L * (s - p.sa)

def virtReserveX (p : RangePool) (s : ℝ) : ℝ := realReserveX p s + p.L / p.sb

def virtReserveY (p : RangePool) (s : ℝ) : ℝ := realReserveY p s + p.L * p.sa

theorem virt_x_eq (p : RangePool) (s : ℝ) : virtReserveX p s = p.L / s := by
  dsimp [virtReserveX, realReserveX]
  ring

theorem virt_y_eq (p : RangePool) (s : ℝ) : virtReserveY p s = p.L * s := by
  dsimp [virtReserveY, realReserveY]
  ring

theorem concentrated_virtual_product (p : RangePool) (s : ℝ) (hs_pos : 0 < s) :
    virtReserveX p s * virtReserveY p s = p.L ^ 2 := by
  rw [virt_x_eq, virt_y_eq]
  exact virtual_reserves_product_eq_L_sq p.L s (ne_of_gt hs_pos)

theorem uniswap_v3_invariant_identity (p : RangePool) (s : ℝ) (hs_pos : 0 < s) :
    (realReserveX p s + p.L / p.sb) * (realReserveY p s + p.L * p.sa) = p.L ^ 2 :=
  concentrated_virtual_product p s hs_pos

theorem boundary_at_sa_y_zero (p : RangePool) : realReserveY p p.sa = 0 := by
  simp [realReserveY]

theorem boundary_at_sa_x_pos (p : RangePool) : 0 < realReserveX p p.sa :=
  mul_pos p.hL (sub_pos.mpr (one_div_lt_one_div_of_lt p.hsa p.hab))

theorem boundary_at_sb_x_zero (p : RangePool) : realReserveX p p.sb = 0 := by
  simp [realReserveX]

theorem boundary_at_sb_y_pos (p : RangePool) : 0 < realReserveY p p.sb :=
  mul_pos p.hL (sub_pos.mpr p.hab)

/-- Pointwise comparison of the formula, not a token-transfer execution theorem. -/
theorem reserve_x_strictly_decreases (p : RangePool) (s1 s2 : ℝ)
    (hs1_pos : 0 < s1) (h_lt : s1 < s2) : realReserveX p s2 < realReserveX p s1 := by
  exact mul_lt_mul_of_pos_left
    (sub_lt_sub_right (one_div_lt_one_div_of_lt hs1_pos h_lt) (1 / p.sb)) p.hL

theorem reserve_y_strictly_increases (p : RangePool) (s1 s2 : ℝ) (h_lt : s1 < s2) :
    realReserveY p s1 < realReserveY p s2 :=
  mul_lt_mul_of_pos_left (sub_lt_sub_right h_lt p.sa) p.hL

/-- Positive-offset comparison; not a market-depth or economic-return guarantee. -/
theorem capital_savings_x (p : RangePool) (s : ℝ) :
    realReserveX p s < virtReserveX p s := by
  dsimp [virtReserveX]
  have hterm := div_pos p.hL (sb_pos p)
  linarith

/-- Positive-offset comparison, including inputs outside the price range. -/
theorem capital_savings_y (p : RangePool) (s : ℝ) :
    realReserveY p s < virtReserveY p s := by
  dsimp [virtReserveY]
  have hterm := mul_pos p.hL p.hsa
  linarith

structure DeFiConcentratedLiquidityFormalSuite : Prop where
  h_virt_x_eq : ∀ (p : RangePool) (s : ℝ), virtReserveX p s = p.L / s
  h_virt_y_eq : ∀ (p : RangePool) (s : ℝ), virtReserveY p s = p.L * s
  h_invariant : ∀ (p : RangePool) (s : ℝ), 0 < s →
    (realReserveX p s + p.L / p.sb) * (realReserveY p s + p.L * p.sa) = p.L ^ 2
  h_bound_sa_y : ∀ p : RangePool, realReserveY p p.sa = 0
  h_bound_sa_x : ∀ p : RangePool, 0 < realReserveX p p.sa
  h_bound_sb_x : ∀ p : RangePool, realReserveX p p.sb = 0
  h_bound_sb_y : ∀ p : RangePool, 0 < realReserveY p p.sb
  h_mono_x : ∀ (p : RangePool) (s1 s2 : ℝ), 0 < s1 → s1 < s2 →
    realReserveX p s2 < realReserveX p s1
  h_mono_y : ∀ (p : RangePool) (s1 s2 : ℝ), s1 < s2 →
    realReserveY p s1 < realReserveY p s2
  h_cap_x : ∀ (p : RangePool) (s : ℝ), realReserveX p s < virtReserveX p s
  h_cap_y : ∀ (p : RangePool) (s : ℝ), realReserveY p s < virtReserveY p s
  h_virt_prod : ∀ L sqrtP, sqrtP ≠ 0 → virtualX L sqrtP * virtualY L sqrtP = L ^ 2
  h_realX_pos : ∀ pos, 0 < realX pos
  h_realY_pos : ∀ pos, 0 < realY pos
  h_shifted_eq : ∀ pos,
    (realX pos + pos.L / pos.sqrtPu) * (realY pos + pos.L * pos.sqrtPl) = pos.L ^ 2
  h_deltaY_pos : ∀ L sqrtP sqrtP_next, 0 < L → sqrtP < sqrtP_next →
    0 < deltaY L sqrtP sqrtP_next
  h_deltaX_pos : ∀ L sqrtP sqrtP_next, 0 < L → 0 < sqrtP_next → sqrtP_next < sqrtP →
    0 < deltaX L sqrtP sqrtP_next
  h_x_zero_upper : ∀ (r : PriceRangePosition), amountX r.L r.pb r.pb = 0
  h_y_zero_lower : ∀ (r : PriceRangePosition), amountY r.L r.pa r.pa = 0
  h_delta_x_pos : ∀ r, 0 < maxDeltaX r
  h_delta_y_pos : ∀ r, 0 < maxDeltaY r
  h_cpmm_prod : ∀ (r : PriceRangePosition) (p : ℝ), 0 < p →
    shiftedVirtualX (amountX r.L p r.pb) r.L r.pb *
      shiftedVirtualY (amountY r.L p r.pa) r.L r.pa = r.L ^ 2

theorem defi_concentrated_liquidity_master_verification_suite :
    DeFiConcentratedLiquidityFormalSuite := {
  h_virt_x_eq := virt_x_eq
  h_virt_y_eq := virt_y_eq
  h_invariant := uniswap_v3_invariant_identity
  h_bound_sa_y := boundary_at_sa_y_zero
  h_bound_sa_x := boundary_at_sa_x_pos
  h_bound_sb_x := boundary_at_sb_x_zero
  h_bound_sb_y := boundary_at_sb_y_pos
  h_mono_x := reserve_x_strictly_decreases
  h_mono_y := reserve_y_strictly_increases
  h_cap_x := capital_savings_x
  h_cap_y := capital_savings_y
  h_virt_prod := virtual_reserves_product_eq_L_sq
  h_realX_pos := realX_pos
  h_realY_pos := realY_pos
  h_shifted_eq := real_reserves_shifted_product_eq_L_sq
  h_deltaY_pos := deltaY_pos_of_price_increase
  h_deltaX_pos := deltaX_pos_of_price_decrease
  h_x_zero_upper := amount_x_zero_at_upper
  h_y_zero_lower := amount_y_zero_at_lower
  h_delta_x_pos := max_delta_x_pos
  h_delta_y_pos := max_delta_y_pos
  h_cpmm_prod := virtual_reserves_product
}

/-- Compatibility name for the extended collection of algebraic guarantees. -/
theorem defi_concentrated_liquidity_master_suite : DeFiConcentratedLiquidityFormalSuite :=
  defi_concentrated_liquidity_master_verification_suite

#print axioms defi_concentrated_liquidity_master_verification_suite

end DeFiConcentratedLiquidity
