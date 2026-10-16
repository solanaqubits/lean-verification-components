import Verification.DeFiLendingBadDebtSocialization

namespace BadDebtRegression
open DeFiLendingBadDebtSocialization DeFiLendingCompoundInterestIndex
open scoped BigOperators

def s : IntegerState 2 := ⟨⟨10,140,20,130,10,![100,40],![0,12],7,3⟩,100⟩
def rational : State 2 := ⟨⟨10,20,130,2,![50,20]⟩,100⟩
def exhausted : IntegerState 2 := ⟨⟨0,100,20,80,10,![100,0],![0,0],0,0⟩,100⟩
def rounding : IntegerState 1 := ⟨⟨0,10,0,10,100,fun _ => 1,fun _ => 0,0,0⟩,10⟩
def tiny : IntegerState 1 := ⟨⟨0,1,0,1,15,fun _ => 1,fun _ => 0,0,0⟩,1⟩
def dustOnly : IntegerState 1 := ⟨⟨0,0,0,0,1,fun _ => 1,fun _ => 0,0,0⟩,0⟩
def quote (t : IntegerState 2) :=
  [t.pool.cash,t.pool.debt,t.pool.reserves,t.pool.liabilities,t.pool.index,
   t.pool.scaled 0,t.pool.scaled 1,t.pool.collateral 0,t.pool.collateral 1,
   t.pool.liquidatorCollateral,t.pool.treasuryCollateral,t.supplierShares]

example : DeFiLendingBadDebtSocializationSuite := verification_suite
example : rational.Valid := by norm_num [State.Valid,PoolState.Valid,rational,Fin.forall_fin_succ]
example : rational.pool.Balanced := by
  norm_num [PoolState.Balanced,PoolState.debt,total_debt_from_scaled,rational,Fin.sum_univ_two]
example : admissible true rational 0 30 := by
  norm_num [admissible,WriteOffAuthorized,State.Valid,PoolState.Valid,rational,
    borrower_debt,PoolState.debt,total_debt_from_scaled,socialized_haircut,Fin.forall_fin_succ]
example : (writeoff rational 0 30).pool.debt = 110 := by
  norm_num [writeoff,rational,transfer_debt,PoolState.debt,total_debt_from_scaled,Fin.sum_univ_two]
example : (writeoff rational 0 30).pool.scaled 0 = 35 := by norm_num [writeoff,rational,transfer_debt]
example : (writeoff rational 0 30).pool.scaled 1 = 20 := by norm_num [writeoff,rational,transfer_debt]
example : (writeoff rational 0 30).pool.cash = 10 := rfl
example : (writeoff rational 0 30).pool.liabilities = 120 := by norm_num [writeoff,rational,socialized_haircut]
example : (writeoff rational 0 30).pool.reserves = 0 := by norm_num [writeoff,rational,reserve_absorbed]
example : lp_exchange_rate 130 100 - lp_exchange_rate 120 100 = 1/10 := by norm_num [lp_exchange_rate]
example : socialized_haircut 20 10 = 0 := by norm_num [socialized_haircut]
example : socialized_haircut 20 20 = 0 := by norm_num [socialized_haircut]
example : socialized_haircut 20 30 = 10 := by norm_num [socialized_haircut]
example : socialized_haircut 0 30 = 30 := by norm_num [socialized_haircut]
example : (1:ℚ) - (1:ℚ)*10/15 = 1/3 := by norm_num
example : (1:ℚ) - (1 - (1:ℚ)*10/100) = 1/10 := by norm_num
example (R L S x : ℚ) (hS : 0 < S) :
    lp_exchange_rate (L-socialized_haircut R x) S = lp_exchange_rate L S ↔ x ≤ R :=
  lp_exchange_rate_preserved_iff R L S x hS
example (cash B R L x : ℚ) (hb : cash+B=R+L) (hc : 0≤cash) (hL : 0≤L) (hx : x≤B) :
    socialized_haircut R x ≤ L ∧ 0≤L-socialized_haircut R x :=
  haircut_le_liabilities_of_balance cash B R L x hb hc hL hx

example : ((execute_int true 10 s 0 0).map quote == some [10,140,20,130,10,100,40,0,12,7,3,100]) = true := by decide
example : ((execute_int true 10 s 0 10).map quote == some [10,130,10,130,10,90,40,0,12,7,3,100]) = true := by decide
example : ((execute_int true 10 s 0 20).map quote == some [10,120,0,130,10,80,40,0,12,7,3,100]) = true := by decide
example : ((execute_int true 10 s 0 30).map quote == some [10,110,0,120,10,70,40,0,12,7,3,100]) = true := by decide
example : ((execute_int true 10 s 0 100).map quote == some [10,40,0,50,10,0,40,0,12,7,3,100]) = true := by decide
example : ((execute_int true 10 {s with pool := {s.pool with reserves := 0, liabilities := 150}} 0 30).map quote == some [10,110,0,120,10,70,40,0,12,7,3,100]) = true := by decide
example : ((execute_int true 10 exhausted 0 100).map quote == some [0,0,0,0,10,0,0,0,0,0,0,100]) = true := by decide
example : ((execute_int true 10 s 0 1).map quote == some [10,139,19,130,10,99,40,0,12,7,3,100]) = true := by decide
example : ((execute_int false 10 s 0 30).isNone) = true := by decide
example : ((execute_int true 10 s 0 101).isNone) = true := by decide
example : ((execute_int true 10 {s with pool := {s.pool with debt := 99}} 0 1).isNone) = true := by decide
example : ((execute_int true 10 {s with pool := {s.pool with liabilities := 9}} 0 30).isNone) = true := by decide
example : ((execute_int true 10 {s with supplierShares := 0} 0 30).isNone) = true := by decide
example : ((execute_int true 10 {s with supplierShares := 0} 0 20).isSome) = true := by decide
example : ((execute_int true 0 s 0 1).isNone) = true := by decide
example : ((execute_int true 10 {s with pool := {s.pool with index := 0}} 0 1).isNone) = true := by decide
example : ((execute_int true 10 tiny 0 1).map (fun t => t.pool.scaled 0) == some 0) = true := by decide
example : ((execute_int true 10 rounding 0 1).map (fun t => t.pool.scaled 0) == some 1) = true := by decide
example : ((execute_int true 10 rounding 0 1).map (fun t => ledger_index_gap t.pool.debt 10 t.pool.index t.pool.scaled) == some (-1)) = true := by decide
example : (recon_dust 10 100 (fun _ : Fin 1 => 1) == 0) = true := by decide
example : (recon_dust 10 15 (fun _ : Fin 2 => 1) == 1) = true := by decide
example : ((execute_int true 10 dustOnly 0 0).map (fun t => t.pool.scaled 0) == some 1) = true := by decide
example : ((execute_int true 10 dustOnly 0 1).isNone) = true := by decide
example : (lp_exchange_rate_int 10 130 100 == some 13) = true := by decide
example : (lp_exchange_rate_int 10 120 100 == some 12) = true := by decide
example : (lp_exchange_rate_int 10 1 3 == some 3) = true := by decide
example : (lp_exchange_rate_int 10 0 100 == some 0) = true := by decide
example : ((lp_exchange_rate_int 10 10 0).isNone) = true := by decide
example : ((execute_int false 10 s 0 0).isNone) = true := by decide
example : ((execute true rational 0 30).isSome) = true := by
  norm_num [execute,admissible,WriteOffAuthorized,State.Valid,PoolState.Valid,rational,
    borrower_debt,PoolState.debt,total_debt_from_scaled,socialized_haircut,Fin.forall_fin_succ]
example : ((execute false rational 0 30).isNone) = true := by
  norm_num [execute,admissible,WriteOffAuthorized,State.Valid,PoolState.Valid,rational,
    borrower_debt,PoolState.debt,total_debt_from_scaled,socialized_haircut,Fin.forall_fin_succ]
example : ((execute true rational 0 (-1)).isNone) = true := by
  norm_num [execute,admissible,WriteOffAuthorized,State.Valid,PoolState.Valid,rational,
    borrower_debt,PoolState.debt,total_debt_from_scaled,socialized_haircut,Fin.forall_fin_succ]
example : ((execute true rational 0 101).isNone) = true := by
  norm_num [execute,admissible,WriteOffAuthorized,State.Valid,PoolState.Valid,rational,
    borrower_debt,PoolState.debt,total_debt_from_scaled,socialized_haircut,Fin.forall_fin_succ]
example : ((execute true {rational with supplierShares := 0} 0 30).isNone) = true := by
  norm_num [execute,admissible,WriteOffAuthorized,State.Valid,PoolState.Valid,rational,
    borrower_debt,PoolState.debt,total_debt_from_scaled,socialized_haircut,Fin.forall_fin_succ]
example : ((execute true {rational with supplierShares := 0} 0 20).isSome) = true := by
  norm_num [execute,admissible,WriteOffAuthorized,State.Valid,PoolState.Valid,rational,
    borrower_debt,PoolState.debt,total_debt_from_scaled,socialized_haircut,Fin.forall_fin_succ]
example : ((execute true {rational with pool := {rational.pool with liabilities := 9}} 0 30).isNone) = true := by
  norm_num [execute,admissible,WriteOffAuthorized,State.Valid,PoolState.Valid,rational,
    borrower_debt,PoolState.debt,total_debt_from_scaled,socialized_haircut,Fin.forall_fin_succ]
example : ((execute true {rational with pool := {rational.pool with index := 0}} 0 0).isNone) = true := by
  norm_num [execute,admissible,WriteOffAuthorized,State.Valid,PoolState.Valid,rational,
    borrower_debt,PoolState.debt,total_debt_from_scaled,socialized_haircut,Fin.forall_fin_succ]

end BadDebtRegression
open BadDebtRegression DeFiLendingBadDebtSocialization DeFiLendingCompoundInterestIndex

def main : IO Unit := do
  let checks : List Bool := [
    (execute_int true 10 s 0 0).map quote == some [10,140,20,130,10,100,40,0,12,7,3,100],
    (execute_int true 10 s 0 10).map quote == some [10,130,10,130,10,90,40,0,12,7,3,100],
    (execute_int true 10 s 0 20).map quote == some [10,120,0,130,10,80,40,0,12,7,3,100],
    (execute_int true 10 s 0 30).map quote == some [10,110,0,120,10,70,40,0,12,7,3,100],
    (execute_int true 10 s 0 100).map quote == some [10,40,0,50,10,0,40,0,12,7,3,100],
    (execute_int true 10 {s with pool := {s.pool with reserves := 0, liabilities := 150}} 0 30).map quote == some [10,110,0,120,10,70,40,0,12,7,3,100],
    (execute_int true 10 exhausted 0 100).map quote == some [0,0,0,0,10,0,0,0,0,0,0,100],
    (execute_int true 10 s 0 1).map quote == some [10,139,19,130,10,99,40,0,12,7,3,100],
    (execute_int false 10 s 0 30).isNone,
    (execute_int true 10 s 0 101).isNone,
    (execute_int true 10 {s with pool := {s.pool with debt := 99}} 0 1).isNone,
    (execute_int true 10 {s with pool := {s.pool with liabilities := 9}} 0 30).isNone,
    (execute_int true 10 {s with supplierShares := 0} 0 30).isNone,
    (execute_int true 10 {s with supplierShares := 0} 0 20).isSome,
    (execute_int true 0 s 0 1).isNone,
    (execute_int true 10 {s with pool := {s.pool with index := 0}} 0 1).isNone,
    (execute_int true 10 tiny 0 1).map (fun t => t.pool.scaled 0) == some 0,
    (execute_int true 10 rounding 0 1).map (fun t => t.pool.scaled 0) == some 1,
    (execute_int true 10 rounding 0 1).map (fun t => ledger_index_gap t.pool.debt 10 t.pool.index t.pool.scaled) == some (-1),
    recon_dust 10 100 (fun _ : Fin 1 => 1) == 0,
    recon_dust 10 15 (fun _ : Fin 2 => 1) == 1,
    (execute_int true 10 dustOnly 0 0).map (fun t => t.pool.scaled 0) == some 1,
    (execute_int true 10 dustOnly 0 1).isNone,
    lp_exchange_rate_int 10 130 100 == some 13,
    lp_exchange_rate_int 10 120 100 == some 12,
    lp_exchange_rate_int 10 1 3 == some 3,
    lp_exchange_rate_int 10 0 100 == some 0,
    (lp_exchange_rate_int 10 10 0).isNone,
    (execute_int false 10 s 0 0).isNone,
    (execute true rational 0 30).isSome,
    (execute false rational 0 30).isNone,
    (execute true rational 0 (-1)).isNone,
    (execute true rational 0 101).isNone,
    (execute true {rational with supplierShares := 0} 0 30).isNone,
    (execute true {rational with supplierShares := 0} 0 20).isSome,
    (execute true {rational with pool := {rational.pool with liabilities := 9}} 0 30).isNone,
    (execute true {rational with pool := {rational.pool with index := 0}} 0 0).isNone]
  for (ok,i) in checks.zipIdx do
    unless ok do throw (IO.userError s!"bad debt scenario {i} failed")
  IO.println s!"BAD_DEBT_OK {checks.length}"
