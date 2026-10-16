import Verification.DeFiLendingLiquidationAccounting

namespace LiquidationAccountingRegression
open DeFiLendingLiquidationAccounting DeFiLendingCompoundInterestIndex
open scoped BigOperators

def params : Parameters := ⟨1, 1, 3/4, 1/2, 1/10, 1/5⟩
def rational : LiquidationState 2 :=
  ⟨⟨10, 5, 145, 2, ![50,20]⟩, ![120,100], 7, 3⟩
def p : DiscreteParameters := ⟨1000,1,1,750,500,100,200⟩
def s : IntegerState 2 := ⟨10,140,5,145,1000,![100,40],![120,100],7,3⟩
def one : IntegerState 1 := ⟨0,1,0,1,10,fun _ => 1,fun _ => 1,0,0⟩
def tiny : DiscreteParameters := ⟨10,1,1,5,10,0,0⟩
def quote (t : IntegerState 2) :=
  [t.cash,t.debt,t.reserves,t.liabilities,t.index,t.scaled 0,t.scaled 1,t.collateral 0,t.collateral 1,
    t.liquidatorCollateral,t.treasuryCollateral]

example : DeFiLendingLiquidationAccountingSuite := verification_suite
example (B a : ℚ) (hB : 0 < B) (ha : a ≤ 1) : B ≤ a*B ↔ a=1 := full_repay_iff_close_factor_one B a hB ha
example : ¬ (100:ℚ) ≤ (1/2)*100 := by norm_num
example : (100:ℚ) ≤ 1*100 := by norm_num
example : c_base 20 2 4 = 10 := by norm_num [c_base]
example : c_seize 20 2 4 (1/10) = 11 := by norm_num [c_seize,c_bonus,c_base]
example : c_fee 20 1 1 (1/10) (1/5) = 2/5 := by norm_num [c_fee,c_bonus,c_base]
example : c_liq 20 1 1 (1/10) (1/5) = 108/5 := by norm_num [c_liq,c_bonus,c_base]
example : c_fee 20 1 1 (1/10) 0 = 0 ∧ c_liq 20 1 1 (1/10) 0 = c_seize 20 1 1 (1/10) := fee_zero _ _ _ _
example : c_fee 20 1 1 (1/10) 1 = c_bonus 20 1 1 (1/10) ∧ c_liq 20 1 1 (1/10) 1 = c_base 20 1 1 := fee_one _ _ _ _
example : c_bonus 20 1 1 0 = 0 ∧ c_fee 20 1 1 0 (1/5) = 0 ∧ c_liq 20 1 1 0 (1/5) = c_base 20 1 1 := bonus_zero _ _ _ _
example : params.Valid := by norm_num [Parameters.Valid,params]
example : rational.Valid := by
  norm_num [LiquidationState.Valid,PoolState.Valid,rational,Fin.forall_fin_succ]
example : rational.pool.Balanced := by
  norm_num [PoolState.Balanced,PoolState.debt,total_debt_from_scaled,rational,Fin.sum_univ_two]
example : admissible rational params 0 20 := by
  norm_num [admissible,LiquidationState.Valid,Parameters.Valid,PoolState.Valid,rational,params,
    borrower_debt,DeFiLendingLiquidationHealthFactor.liquidatable,
    DeFiLendingLiquidationHealthFactor.weightedValue,valued_position,c_seize,c_bonus,c_base,Fin.forall_fin_succ]
example : (liquidate rational params 0 20).pool.scaled 0 = 40 := by norm_num [liquidate,transfer_debt,rational]
example : (liquidate rational params 0 20).pool.scaled 1 = 20 := by norm_num [liquidate,transfer_debt,rational]
example : (liquidate rational params 0 20).pool.debt = 120 := by
  norm_num [liquidate,transfer_debt,PoolState.debt,total_debt_from_scaled,rational,Fin.sum_univ_two]
example : (liquidate rational params 0 20).treasuryCollateral = 17/5 := by
  norm_num [liquidate,rational,params,c_fee,c_bonus,c_base]
example : (liquidate rational params 0 20).pool.reserves = 5 := rfl
example : health 120 100 1 1 (3/4) < health 98 80 1 1 (3/4) := by norm_num [health]
example : health 78 80 1 1 (3/4) < health 100 100 1 1 (3/4) := by norm_num [health]
example : execute_int s p 0 50 = some (liquidate_int s p 0 50) := by decide
example : (execute_int s p 0 50).map quote = some [60,90,5,145,1000,50,40,65,100,61,4] := by decide
example : (execute_int s {p with closeFactor := 1000} 0 100).map quote = some [110,40,5,145,1000,0,40,10,100,115,5] := by decide
example : execute_int s p 0 51 = none := by decide
example : execute_int s p 0 0 = none := by decide
example : execute_int {s with collateral := ![10,100]} p 0 50 = none := by decide
example : execute_int {s with collateral := ![200,100]} p 0 50 = none := by decide
example : execute_int s {p with scale := 0} 0 1 = none := by decide
example : execute_int {s with index := 0} p 0 1 = none := by decide
example : execute_int s {p with debtPrice := 0} 0 1 = none := by decide
example : execute_int s {p with collateralPrice := 0} 0 1 = none := by decide
example : execute_int s {p with feeFraction := 1001} 0 1 = none := by decide
example : execute_int s {p with closeFactor := 0} 0 1 = none := by decide
example : execute_int s {p with closeFactor := 1001} 0 1 = none := by decide
example : execute_int {s with debt := 0} p 0 1 = none := by decide
example : (execute_int one tiny 0 1).isSome = true := by decide
example : shares_burn 10 100 1 1 = 0 := by decide
example : (1:ℕ)-shares_burn 10 15 1 1 = 0 := by decide
example : (1:ℚ)-(1:ℚ)*10/15 = 1/3 := by norm_num
example : ledger_index_gap 9 10 100 (fun _ : Fin 1 => 1) = -1 := by decide
example : recon_dust 10 100 (fun _ : Fin 1 => 1) = 0 := by decide
example : recon_dust 10 15 (fun _ : Fin 2 => 1) = 1 := by decide
example (W I b r : ℕ) (hW : 0<W) (hI : 0<I) (hr : r ≤ b*I/W) (hne : r ≠ b*I/W) :
    0 ≤ ((b-shares_burn W I b r:ℕ):ℚ)-((b:ℚ)-(r:ℚ)*W/I) ∧
    ((b-shares_burn W I b r:ℕ):ℚ)-((b:ℚ)-(r:ℚ)*W/I) < 1 := partial_shares_rounding W I b r hW hI hr hne
example (W I b : ℕ) (hW : 0<W) (hI : 0<I) :
    0 ≤ (b:ℚ)-((b*I/W:ℕ):ℚ)*W/I ∧ (b:ℚ)-((b*I/W:ℕ):ℚ)*W/I < (W:ℚ)/I := full_shares_rounding W I b hW hI

end LiquidationAccountingRegression
open LiquidationAccountingRegression DeFiLendingLiquidationAccounting

def main : IO Unit := do
  let checks : List Bool := [
    (execute_int s p 0 50).map quote == some [60,90,5,145,1000,50,40,65,100,61,4],
    (execute_int s {p with closeFactor := 1000} 0 100).map quote == some [110,40,5,145,1000,0,40,10,100,115,5],
    (execute_int s p 0 51).isNone,
    (execute_int s p 0 0).isNone,
    (execute_int {s with collateral := ![10,100]} p 0 50).isNone,
    (execute_int {s with collateral := ![200,100]} p 0 50).isNone,
    (execute_int s {p with scale := 0} 0 1).isNone,
    (execute_int {s with index := 0} p 0 1).isNone,
    (execute_int s {p with debtPrice := 0} 0 1).isNone,
    (execute_int s {p with collateralPrice := 0} 0 1).isNone,
    (execute_int s {p with feeFraction := 1001} 0 1).isNone,
    (execute_int s {p with closeFactor := 0} 0 1).isNone,
    (execute_int s {p with closeFactor := 1001} 0 1).isNone,
    (execute_int {s with debt := 0} p 0 1).isNone,
    (execute_int s {p with threshold := 0} 0 1).isNone,
    (execute_int s {p with threshold := 1001} 0 1).isNone,
    (execute_int one tiny 0 1).isSome,
    (execute_int {one with scaled := fun _ => 0} tiny 0 1).isNone,
    (execute_int s {p with feeFraction := 0} 0 50).map (fun t => t.treasuryCollateral) == some 3,
    (execute_int s {p with feeFraction := 1000} 0 50).map (fun t => t.liquidatorCollateral) == some 57,
    (execute_int s {p with bonus := 0} 0 50).map (fun t => t.collateral 0) == some 70,
    shares_burn 10 100 1 1 == 0,
    shares_burn 10 15 1 1 == 1,
    base_int {p with debtPrice := 2, collateralPrice := 4} 20 == 10,
    seize_int {p with debtPrice := 2, collateralPrice := 4} 20 == 11,
    fee_int p 50 == 1,
    liq_int p 50 == 54,
    fee_int p 1 == 0,
    (execute_int s p 0 101).isNone,
    decide (health 120 100 1 1 (3/4) < health 98 80 1 1 (3/4)),
    decide (health 78 80 1 1 (3/4) < health 100 100 1 1 (3/4))]
  for (ok,i) in checks.zipIdx do
    unless ok do throw (IO.userError s!"liquidation scenario {i} failed")
  IO.println s!"LIQUIDATION_ACCOUNTING_OK {checks.length}"
