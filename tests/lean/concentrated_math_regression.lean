import Verification.DeFiConcentratedLiquidityMath

open DeFiConcentratedLiquidityMath

example : DeFiConcentratedLiquidityMathSuite := verification_suite
example (a b c : ℕ) : mulDivFloor a b c = a * b / c := floor_div_formula a b c
example (a b c : ℕ) (h : 0 < c) : mulDivCeil a b c = (a * b + c - 1) / c :=
  ceil_div_formula a b c h
example : mulDivFloor 7 3 2 = 10 := by rw [floor_div_formula]
example : mulDivCeil 7 3 2 = 11 := by rw [ceil_div_formula _ _ _ (by decide)]
example : mulDivFloor 6 4 3 = mulDivCeil 6 4 3 := by
  norm_num [mulDivFloor, mulDivCeil]
example (a b : ℕ) (r : Bool) : getAmount0Delta a b 0 r = 0 := amount0_zero a b r
example (a b : ℕ) (r : Bool) : getAmount1Delta a b 0 r = 0 := amount1_zero a b r
example (a L : ℕ) (r : Bool) : getAmount0Delta a a L r = 0 := amount0_same a L r
example (i : ℤ) : 0 < idealPrice i := idealPrice_pos i
example (i : ℤ) : (sqrtPriceReference i : ℚ)^2 ≤ idealPrice i * (scale : ℚ)^2 :=
  (sqrt_reference_bracket i).1
example (p : SwapParams) (h : p.mode = .exactInput) :
    (computeSwapStep p).amountIn + (computeSwapStep p).fee ≤ p.remaining :=
  exact_input_budget p h
example (p : SwapParams) (h : p.mode = .exactOutput) :
    (computeSwapStep p).amountOut ≤ p.remaining := exact_output_budget p h
example (p : SwapParams) : 0 < (computeSwapStep p).nextPrice := swap_price_positive p
example (p : SwapParams) (h : p.remaining = 0) :
    computeSwapStep p = ⟨p.current, 0, 0, 0⟩ := swap_zero_remaining p h
example (p : SwapParams) (hL : p.liquidity = 0) (h : p.remaining ≠ 0) :
    computeSwapStep p = ⟨p.target, 0, 0, 0⟩ := zero_liquidity_transit p hL h
example (p : SwapParams) (h : p.remaining ≠ 0) (ha : admissible p (distance p)) :
    (computeSwapStep p).nextPrice = p.target := swap_reaches_affordable_target p h ha
example (ps : List Position) (i : ℤ) : 0 ≤ activeLiquidity ps i := active_nonneg ps i
example (ps : List Position) (s : TickState) (h : ValidTickState ps s) (ds : List Bool) :
    ValidTickState ps (crossTrace ps s ds) := cross_trace_preserves ps ds s h
example (ps : List Position) (s : TickState) (h : ValidTickState ps s) :
    crossTrace ps s [false, true] = s := crossing_round_trip ps s h
example (ps : List Position) (s : TickState) (b : ℤ) (d : Bool) :
    crossAt ps (crossAt ps s b d true) b d true = crossAt ps s b d true :=
  cross_at_idempotent ps s b d
example (ps : List SwapParams) (b : ℕ) : spendTrace ps b ≤ b := spend_trace_budget ps b
example : crossTick 0 (-1) false = -1 := by decide

private def up (mode : SwapMode) (remaining fee : ℕ) (hf : fee < 1000000) : SwapParams :=
  ⟨scale, scale + 2, scale, remaining, fee, mode, scale_pos, by have := scale_pos; omega, hf⟩
private def down (mode : SwapMode) (remaining : ℕ) : SwapParams :=
  ⟨scale + 2, scale, scale, remaining, 0, mode, by have := scale_pos; omega, scale_pos, by decide⟩
private def gap : SwapParams :=
  ⟨scale, scale + 2, 0, 1, 0, .exactInput, scale_pos, by have := scale_pos; omega, by decide⟩
private def ps : List Position := [⟨0, 2, 5, by decide⟩, ⟨3, 5, 7, by decide⟩]
private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

#eval do
  check "root at zero" (sqrtPriceReference 0 == scale)
  check "root negative tick" (sqrtPriceReference (-1) < scale)
  check "floor / ceiling" (mulDivFloor 7 3 2 == 10 && mulDivCeil 7 3 2 == 11)
  check "exact division" (mulDivFloor 6 4 3 == 8 && mulDivCeil 6 4 3 == 8)
  check "zero amount" (computeSwapStep (up .exactInput 0 0 (by decide)) == (⟨scale, 0, 0, 0⟩ : SwapResult))
  check "one wei input" ((computeSwapStep (up .exactInput 1 0 (by decide))).nextPrice == scale + 1)
  check "up target" ((computeSwapStep (up .exactInput 2 0 (by decide))).nextPrice == scale + 2)
  check "down input" ((computeSwapStep (down .exactInput 2)).nextPrice == scale)
  check "up output" ((computeSwapStep (up .exactOutput 1 0 (by decide))).amountOut ≤ 1)
  check "down output" ((computeSwapStep (down .exactOutput 1)).amountOut == 1)
  check "fee budget" ((computeSwapStep (up .exactInput 2 3000 (by decide))).amountIn +
    (computeSwapStep (up .exactInput 2 3000 (by decide))).fee ≤ 2)
  check "empty liquidity gap" (computeSwapStep gap == (⟨scale + 2, 0, 0, 0⟩ : SwapResult))
  check "multiple ticks through gap" (crossTrace ps ⟨0, 5⟩ [false, false, false] == (⟨3, 7⟩ : TickState))
  check "return across boundary" (crossTrace ps ⟨1, 5⟩ [false, true] == (⟨1, 5⟩ : TickState))
  check "no duplicate crossing" (crossAt ps (crossAt ps ⟨1, 5⟩ 2 false true) 2 false true == (⟨2, 0⟩ : TickState))
  check "unreached boundary" (crossAt ps ⟨1, 5⟩ 2 false false == (⟨1, 5⟩ : TickState))
  IO.println "CLMATH_EXEC_OK: 16 cases"
