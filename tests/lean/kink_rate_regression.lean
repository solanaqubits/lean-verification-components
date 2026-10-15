import Verification.DeFiKinkedInterestRateUtilization

open DeFiKinkedInterestRateUtilization
namespace KinkRateRegression

def params : FixedParams where
  scale := 1000
  base := 20
  slope₁ := 100
  slope₂ := 500
  kink := 800
  reserveFactor := 100
  scale_pos := by norm_num
  kink_pos := by norm_num
  kink_lt_scale := by norm_num
  reserve_le_scale := by norm_num

def noReserve : FixedParams := { params with reserveFactor := 0, reserve_le_scale := by decide }
def allReserve : FixedParams := { params with reserveFactor := 1000, reserve_le_scale := by decide }
def fallingSlope : FixedParams := { params with slope₁ := 500, slope₂ := 100 }
def zeroCurve : FixedParams := { params with base := 0, slope₁ := 0, slope₂ := 0 }

example : DeFiKinkedInterestRateUtilizationSuite := verification_suite
example : utilization 10 100 20 = 10/9 := by norm_num [utilization, denominator]
example : 1 < utilization 10 100 20 := utilization_gt_one_counterexample.2.2.2
example : utilization 0 0 100 = 0 := utilization_zero _ _
example : checked_utilization 10 100 20 = some (10/9) := by
  norm_num [checked_utilization, ValidPoolState, utilization, denominator]
example : checked_utilization 0 1 1 = none := by
  norm_num [checked_utilization, ValidPoolState, denominator]
example : checked_utilization (-1) 0 0 = none := by
  norm_num [checked_utilization, ValidPoolState]
example : checked_utilization 0 0 100 = some 0 := by
  norm_num [checked_utilization, ValidPoolState, utilization]
example : utilization 100 100 0 = 1/2 := by norm_num [utilization, denominator]
example : utilization 10 100 10 = 1 := by norm_num [utilization, denominator]
example (c b r : ℚ) (hb : 0 < b) (hd : 0 < denominator c b r) :
    utilization c b r ≤ 1 ↔ r ≤ c := utilization_le_one_iff hb hd
example : borrow_rate params.lift 0 = 1/50 := by norm_num [borrow_rate, FixedParams.lift, params]
example : supply_rate params.lift 0 = 0 := (rates_at_zero _).2
example : borrow_rate params.lift (1/2) = 7/100 := by
  norm_num [borrow_rate, FixedParams.lift, params]
example : borrow_rate params.lift (4/5) = 1/10 := by
  norm_num [borrow_rate, FixedParams.lift, params]
example : borrow_rate params.lift (9/10) = 3/20 := by
  norm_num [borrow_rate, FixedParams.lift, params]
example : Continuous (borrow_rate fallingSlope.lift) := borrow_rate_continuous _
example : Monotone (borrow_rate fallingSlope.lift) := borrow_rate_monotone _
example : ConvexOn ℚ Set.univ (borrow_rate params.lift) :=
  borrow_rate_convex_slope _ (by norm_num [FixedParams.lift, params])
example : borrow_rate fallingSlope.lift (9/10) = 43/100 := by
  norm_num [borrow_rate, FixedParams.lift, fallingSlope, params]
-- Falling slopes retain monotonicity but fail Jensen convexity at a crossing interval.
example : ¬ ConvexOn ℚ Set.univ (borrow_rate fallingSlope.lift) := by
  intro h
  have hh := h.2 (show (3/5:ℚ) ∈ Set.univ from Set.mem_univ _)
    (show (1:ℚ) ∈ Set.univ from Set.mem_univ _) (by norm_num : (0:ℚ) ≤ 1/2)
    (by norm_num : (0:ℚ) ≤ 1/2) (by norm_num : (1/2:ℚ)+1/2=1)
  norm_num [smul_eq_mul, borrow_rate, FixedParams.lift, fallingSlope, params] at hh
example : supply_rate noReserve.lift 1 = borrow_rate noReserve.lift 1 :=
  spread_zero_at_full_util_zero_reserve _ (by norm_num [FixedParams.lift, noReserve])
example : supply_rate allReserve.lift (9/10) = 0 :=
  full_reserve_supply_zero _ (by norm_num [FixedParams.lift, allReserve, params]) _
example : supply_rate params.lift 1 < borrow_rate params.lift 1 := by
  norm_num [supply_rate, borrow_rate, FixedParams.lift, params]
example : ¬ supply_rate zeroCurve.lift (1/2) < borrow_rate zeroCurve.lift (1/2) := by
  norm_num [supply_rate, borrow_rate, FixedParams.lift, zeroCurve, params]
example : borrow_rate_int params 1 = 21 := by decide
example : supply_rate_int params 1 = 0 := by decide
example : quote_rates params 100 100 0 = some (500,70,31) := by decide
example : quote_rates params 200 800 0 = some (800,100,72) := by decide
example : quote_rates params 100 900 0 = some (900,150,121) := by decide
example : quote_rates params 0 1000 0 = some (1000,200,180) := by decide
example : quote_rates noReserve 0 1000 0 = some (1000,200,200) := by decide
example : quote_rates allReserve 0 1000 0 = some (1000,200,0) := by decide
example : quote_rates params 0 0 100 = some (0,20,0) := by decide
example : utilization_int 0 100 100 0 = none := by decide
example : utilization_int 1000 0 1 1 = none := by decide
example : utilization_int 1000 0 1 2 = none := by decide
example : utilization_int 1000 10 100 20 = some 1111 := by decide
example : quote_rates params 10 100 20 = none := by decide
-- Rounding can hide U>1; admission checks the exact reserves/cash predicate.
example : utilization_int 1000 0 10001 1 = some 1000 ∧ quote_rates params 0 10001 1 = none := by decide
example : quote_rates params 999 1 0 = some (1,21,0) := by decide
example (P : FixedParams) (u : ℕ) (hu : u ≤ P.scale) :
    supply_rate_int P u ≤ borrow_rate_int P u := supply_rate_int_le_borrow P hu
example : 0 ≤ (borrow_rate_int params 1 : ℚ) / params.scale -
    borrow_rate params.lift (1 / params.scale) ∧
    (borrow_rate_int params 1 : ℚ) / params.scale - borrow_rate params.lift (1 / params.scale) <
      1 / params.scale := borrow_rate_int_error params 1
example : -(1 / (params.scale : ℚ)) < (supply_rate_int params 500 : ℚ) / params.scale -
    supply_rate params.lift (500 / params.scale) ∧
    (supply_rate_int params 500 : ℚ) / params.scale - supply_rate params.lift (500 / params.scale) <
      1 / params.scale := supply_rate_int_error params (by decide)
example (P : FixedParams) (c b r u rb rs : ℕ)
    (h : quote_rates P c b r = some (u,rb,rs)) : u ≤ P.scale ∧ rs ≤ rb := quote_rates_preserves P h
example : ceil_div 100 10 = 10 ∧ ceil_div 101 10 = 11 ∧ ceil_div 0 10 = 0 := by decide

/-- Runtime scenarios exercise the same natural arithmetic as the kernel regressions. -/
def scenarios : List Bool := [
  utilization_int 1000 100 100 0 == some 500,
  utilization_int 1000 0 0 100 == some 0,
  utilization_int 0 0 0 0 == none,
  utilization_int 1000 0 1 1 == none,
  utilization_int 1000 0 1 2 == none,
  utilization_int 1000 10 100 20 == some 1111,
  quote_rates params 100 100 0 == some (500,70,31),
  quote_rates params 200 800 0 == some (800,100,72),
  quote_rates params 100 900 0 == some (900,150,121),
  quote_rates params 0 1000 0 == some (1000,200,180),
  quote_rates noReserve 0 1000 0 == some (1000,200,200),
  quote_rates allReserve 0 1000 0 == some (1000,200,0),
  quote_rates params 0 0 100 == some (0,20,0),
  quote_rates params 10 100 20 == none,
  utilization_int 1000 0 10001 1 == some 1000,
  quote_rates params 0 10001 1 == none,
  quote_rates params 999 1 0 == some (1,21,0),
  borrow_rate_int params 0 == 20,
  borrow_rate_int params 1 == 21,
  borrow_rate_int params 800 == 100,
  borrow_rate_int params 801 == 101,
  supply_rate_int params 1 == 0,
  ceil_div 100 10 == 10,
  ceil_div 101 10 == 11,
  ceil_div 0 10 == 0]

end KinkRateRegression

def main : IO Unit := do
  if KinkRateRegression.scenarios.all id then
    IO.println s!"KINK_RATE_OK {KinkRateRegression.scenarios.length}"
  else throw (IO.userError "kink rate regression failure")
