import Verification.DeFiLendingLiquidationHealthFactor
import Mathlib.Data.Fin.VecNotation

open DeFiLendingLiquidationHealthFactor
namespace LendingHealthRegression

def p : Position 1 := oneAsset 100 95 (4/5) (3/4)
def full : Position 1 := oneAsset 105 100 (4/5) (3/4)
def mixed : Position 2 := ⟨![50, 100], ![2, 1], ![4/5, 1/2], ![7/10, 2/5], 150⟩
def ints : DiscretePosition 1 := ⟨fun _ => 100, fun _ => 3, fun _ => 4/5, fun _ => 3/4, 280⟩
def fullInts : DiscretePosition 1 := ⟨fun _ => 105, fun _ => 1, fun _ => 4/5, fun _ => 3/4, 100⟩
def step : LiquidationStep 1 := ⟨0, 10, 1/10, 1⟩

example : DeFiLendingLiquidationHealthFactorSuite := verification_suite
example : p.Valid := by decide +kernel
example : collateralValue p = 100 ∧ weightedValue p = 80 ∧ borrowLimit p = 75 := by decide +kernel
example : healthFactor p = some (16/19) ∧ liquidatable p := by decide +kernel
example : healthFactor (oneAsset 0 0 0 0) = none := by decide +kernel
example : ¬ liquidatable (oneAsset 0 0 0 0) := by decide +kernel
example : execute (oneAsset 0 0 0 0) 0 1 0 1 = none := by decide +kernel
example : execute p 0 0 0 1 = none := by decide +kernel
example : execute p 0 (-1) 0 1 = none := by decide +kernel
example : execute p 0 96 0 1 = none := by decide +kernel
example : execute p 0 50 (1/10) (1/2) = none := by decide +kernel
example : execute p 0 1 (-1/10) 1 = none := by decide +kernel
example : execute p 0 1 0 0 = none := by decide +kernel
example : execute p 0 1 0 2 = none := by decide +kernel
example : execute (oneAsset 200 100 (4/5) (3/4)) 0 1 0 1 = none := by decide +kernel
example : execute (oneAsset 100 100 (6/5) (3/4)) 0 1 0 1 = none := by decide +kernel
example : execute (oneAsset 10 100 (4/5) (3/4)) 0 20 0 1 = none := by decide +kernel
example : executeCovered p 0 50 (1/10) 1 = some (settle p 0 50 55) := by decide +kernel
example : covered (settle p 0 50 55) ∧ healthFactor (settle p 0 50 55) = some (4/5) := by decide +kernel
example : execute p 0 50 (1/5) 1 = some (settle p 0 50 60) := by decide +kernel
example : ¬ covered (settle p 0 50 60) ∧ executeCovered p 0 50 (1/5) 1 = none := by decide +kernel
example : execute full 0 100 (1/20) 1 = some (settle full 0 100 105) := by decide +kernel
example : healthFactor (settle full 0 100 105) = none := by decide +kernel
example : execute full 0 100 (1/20) (1/2) = none := by decide +kernel
example : mixed.Valid ∧ collateralValue mixed = 200 ∧ weightedValue mixed = 130 := by decide +kernel
example : execute mixed 0 20 (1/10) 1 = some (settle mixed 0 20 11) := by decide +kernel
example : execute mixed 1 20 (1/10) 1 = some (settle mixed 1 20 22) := by decide +kernel
example : weightedValue (settle mixed 0 20 11) = 562/5 := by decide +kernel
example : weightedValue (settle mixed 1 20 22) = 119 := by decide +kernel
example : healthFactor (settle mixed 0 20 11) = some (281/325) := by decide +kernel
example : healthFactor (settle mixed 1 20 22) = some (119/130) := by decide +kernel
example : (281/325 : ℚ) < 13/15 ∧ (13/15 : ℚ) < 119/130 := by norm_num
example : executeChain p [step, step] = some (settle (settle p 0 10 11) 0 10 11) := by decide +kernel
example : collateralValue (settle (settle p 0 10 11) 0 10 11) - 75 = 3 := by decide +kernel
example : floorSeizure ints 0 1 (1/10) = 0 := by decide +kernel
example : ceilRepayment ints 0 1 (1/10) = 3 := by decide +kernel
example : floorSeizure ints 0 30 (1/10) = 11 := by decide +kernel
example : ceilRepayment ints 0 11 (1/10) = 30 := by decide +kernel
example : executeFloor ints 0 1 (1/10) 1 = some (ints.settle 0 1 0) := by decide +kernel
example : executeCeil ints 0 1 (1/10) 1 = some (ints.settle 0 3 1) := by decide +kernel
example : executeCeil ints 0 100 (1/10) (1/2) = none := by decide +kernel
example : executeFloor fullInts 0 100 (1/20) 1 = some (fullInts.settle 0 100 105) := by decide +kernel
example : healthFactor (fullInts.settle 0 100 105).lift = none := by decide +kernel
example : (executeDiscreteCovered ints 0 1 0 (1/10) 1).isSome = true := by decide +kernel
example : (executeCeil ints 0 0 (1/10) 1).isSome = false := by decide +kernel
example (W B t r β : ℚ) (hr : 0 < r) (hb : r < B) :
    W / B ≤ (W-t*((1+β)*r))/(B-r) ↔ t*(1+β) ≤ W/B :=
  health_nondecreases_iff W B t r β hr hb
example (p : Position n) (h : p.Valid) (hb : 0 < p.debt) (prices : Fin n → ℚ)
    (hp : ∀ i, p.price i ≤ prices i) :
    weightedValue p / p.debt ≤ weightedValue (reprice p prices) / p.debt :=
  reprice_health_mono p h hb prices hp
example (p : DiscretePosition n) (hp : p.lift.Valid) k s β (hb : 0 ≤ β) :
    0 ≤ (ceilRepayment p k s β : ℚ) - p.price k * s / (1+β) ∧
      (ceilRepayment p k s β : ℚ) - p.price k * s / (1+β) < 1 :=
  ceil_repayment_error p hp k s β hb

def checks : List (String × Bool) := [
  ("zero debt", decide (healthFactor (oneAsset 0 0 0 0) = none)),
  ("liquidatable covered", decide (liquidatable p ∧ covered p)),
  ("zero input rejected", decide (execute p 0 0 0 1 = none)),
  ("negative input rejected", decide (execute p 0 (-1) 0 1 = none)),
  ("over debt rejected", decide (execute p 0 96 0 1 = none)),
  ("close factor rejected", decide (execute p 0 50 (1/10) (1/2) = none)),
  ("negative bonus rejected", decide (execute p 0 1 (-1/10) 1 = none)),
  ("invalid close rejected", decide (execute p 0 1 0 2 = none)),
  ("healthy rejected", decide (execute (oneAsset 200 100 (4/5) (3/4)) 0 1 0 1 = none)),
  ("collateral cap", decide (execute (oneAsset 10 100 (4/5) (3/4)) 0 20 0 1 = none)),
  ("invalid price", decide (execute {p with price := fun _ => 0} 0 1 0 1 = none)),
  ("invalid LTV", decide (execute (oneAsset 100 95 (4/5) (9/10)) 0 1 0 1 = none)),
  ("HF worsens", decide (healthFactor (settle p 0 50 55) = some (4/5))),
  ("deficit allowed by base", decide ((execute p 0 50 (1/5) 1).isSome = true)),
  ("deficit blocked by guard", decide (executeCovered p 0 50 (1/5) 1 = none)),
  ("full repayment", decide (execute full 0 100 (1/20) 1 = some (settle full 0 100 105))),
  ("full debt-free", decide (healthFactor (settle full 0 100 105) = none)),
  ("mixed asset zero", decide (execute mixed 0 20 (1/10) 1 = some (settle mixed 0 20 11))),
  ("mixed asset one", decide (execute mixed 1 20 (1/10) 1 = some (settle mixed 1 20 22))),
  ("two-step chain", decide (executeChain p [step,step] =
    some (settle (settle p 0 10 11) 0 10 11))),
  ("floor one unit", decide (floorSeizure ints 0 1 (1/10) = 0)),
  ("ceil one unit", decide (ceilRepayment ints 0 1 (1/10) = 3)),
  ("floor exact", decide (floorSeizure ints 0 30 (1/10) = 11)),
  ("ceil exact", decide (ceilRepayment ints 0 11 (1/10) = 30)),
  ("floor execution", decide (executeFloor ints 0 1 (1/10) 1 = some (ints.settle 0 1 0))),
  ("ceil execution", decide (executeCeil ints 0 1 (1/10) 1 = some (ints.settle 0 3 1))),
  ("integer close", decide (executeCeil ints 0 100 (1/10) (1/2) = none)),
  ("integer full", decide (executeFloor fullInts 0 100 (1/20) 1 =
    some (fullInts.settle 0 100 105))),
  ("integer guarded", decide ((executeDiscreteCovered ints 0 1 0 (1/10) 1).isSome = true)),
  ("zero target rejected", decide (executeCeil ints 0 0 (1/10) 1 = none))]

def main : IO Unit := do
  for (name, ok) in checks do
    unless ok do throw (IO.userError s!"Lending health regression failed: {name}")
  IO.println s!"LENDING_HEALTH_EXEC_OK: {checks.length} cases"
#eval main
end LendingHealthRegression
