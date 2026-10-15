import Verification.DeFiLendingCompoundInterestIndex

namespace CompoundIndexRegression
open DeFiLendingCompoundInterestIndex
open scoped BigOperators

def pool : PoolState 1 := ⟨10, 5, 105, 1, fun _ => 100⟩
def state : DiscreteState := ⟨10, 100, 5, 105, 1000⟩
def quote (s : PoolState 1) : ℚ × ℚ × ℚ × ℚ × ℚ :=
  (s.cash, s.debt, s.reserves, s.liabilities, s.index)
def afterAccrue := execute_accrue pool (1 / 5) 1 (1 / 2)
def afterBorrow := execute_borrow pool 0 5
def afterRepay := execute_repay pool 0 100

def params : DeFiKinkedInterestRateUtilization.KinkRateParams where
  base := 1 / 100
  slope₁ := 1 / 10
  slope₂ := 1 / 2
  kink := 4 / 5
  reserveFactor := 1 / 10
  base_nonneg := by norm_num
  slope₁_nonneg := by norm_num
  slope₂_nonneg := by norm_num
  kink_pos := by norm_num
  kink_lt_one := by norm_num
  reserve_nonneg := by norm_num
  reserve_le_one := by norm_num

example : DeFiLendingCompoundInterestIndexSuite := verification_suite
example : accrue_index 100 2 0 = 100 := by norm_num [accrue_index]
example : accrue_index 100 0 50 = 100 := by norm_num [accrue_index]
example : accrue_index 100 (1 / 10) 1 = 110 := by norm_num [accrue_index]
example : accrue_index (accrue_index 100 (1 / 10) 1) (1 / 10) 1 = 121 := by norm_num [accrue_index]
example : accrue_index 100 (1 / 10) 2 = 120 := by norm_num [accrue_index]
example : accrue_chain 100 [(1 / 10, 1), (1 / 10, 1)] = 121 := by
  norm_num [accrue_chain, accrue_index]
example (I r t : ℚ) (hI : 0 < I) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    0 < accrue_index I r t := accrue_index_pos I r t hI hr ht
example (I r t u : ℚ) : accrue_index (accrue_index I r t) r u = 
    accrue_index I r (t + u) + I * r ^ 2 * t * u := subdivision_identity I r t u
example : total_debt_from_scaled (fun _ : Fin 2 => 5) 2 = 20 := by
  norm_num [total_debt_from_scaled, Fin.sum_univ_two]
example : (accrue pool (1 / 5) 1 (1 / 2)).debt = 120 := by norm_num [accrue, accrue_index, PoolState.debt,
    total_debt_from_scaled, pool]
example : net_accounting_assets 10 120 15 = 115 := by norm_num [net_accounting_assets]
example : net_accounting_assets 10 100 5 = 105 := by norm_num [net_accounting_assets]
example : pool.Valid := by norm_num [PoolState.Valid, pool]
example : pool.Balanced := by norm_num [PoolState.Balanced, PoolState.debt, total_debt_from_scaled,
    pool]
example : (accrue pool (1 / 5) 1 (1 / 2)).Balanced := by
  apply accrue_preserves_balance
  norm_num [PoolState.Balanced, PoolState.debt, total_debt_from_scaled, pool]
example : (transfer_debt pool 0 5).debt = 105 := by
  norm_num [afterAccrue, afterBorrow, afterRepay, execute_accrue, execute_borrow,
    execute_repay, PoolState.Valid, pool, quote, transfer_debt, accrue, accrue_index,
    PoolState.debt, total_debt_from_scaled, borrower_debt]
example : (transfer_debt pool 0 (-100)).debt = 0 := by
  norm_num [afterAccrue, afterBorrow, afterRepay, execute_accrue, execute_borrow,
    execute_repay, PoolState.Valid, pool, quote, transfer_debt, accrue, accrue_index,
    PoolState.debt, total_debt_from_scaled, borrower_debt]
example : afterAccrue.map quote = some (10, 120, 15, 115, 6 / 5) := by
  norm_num [afterAccrue, afterBorrow, afterRepay, execute_accrue, execute_borrow,
    execute_repay, PoolState.Valid, pool, quote, transfer_debt, accrue, accrue_index,
    PoolState.debt, total_debt_from_scaled, borrower_debt]
example : afterBorrow.map quote = some (5, 105, 5, 105, 1) := by
  norm_num [afterAccrue, afterBorrow, afterRepay, execute_accrue, execute_borrow,
    execute_repay, PoolState.Valid, pool, quote, transfer_debt, accrue, accrue_index,
    PoolState.debt, total_debt_from_scaled, borrower_debt]
example : afterRepay.map quote = some (110, 0, 5, 105, 1) := by
  norm_num [afterAccrue, afterBorrow, afterRepay, execute_accrue, execute_borrow,
    execute_repay, PoolState.Valid, pool, quote, transfer_debt, accrue, accrue_index,
    PoolState.debt, total_debt_from_scaled, borrower_debt]
example : (execute_borrow pool 0 11).isNone = true := by
  norm_num [afterAccrue, afterBorrow, afterRepay, execute_accrue, execute_borrow,
    execute_repay, PoolState.Valid, pool, quote, transfer_debt, accrue, accrue_index,
    PoolState.debt, total_debt_from_scaled, borrower_debt]
example : (execute_repay pool 0 101).isNone = true := by
  norm_num [afterAccrue, afterBorrow, afterRepay, execute_accrue, execute_borrow,
    execute_repay, PoolState.Valid, pool, quote, transfer_debt, accrue, accrue_index,
    PoolState.debt, total_debt_from_scaled, borrower_debt]
example : (execute_accrue pool (-1) 1 0).isNone = true := by
  norm_num [afterAccrue, afterBorrow, afterRepay, execute_accrue, execute_borrow,
    execute_repay, PoolState.Valid, pool, quote, transfer_debt, accrue, accrue_index,
    PoolState.debt, total_debt_from_scaled, borrower_debt]
example : (execute_accrue pool 1 1 2).isNone = true := by
  norm_num [afterAccrue, afterBorrow, afterRepay, execute_accrue, execute_borrow,
    execute_repay, PoolState.Valid, pool, quote, transfer_debt, accrue, accrue_index,
    PoolState.debt, total_debt_from_scaled, borrower_debt]
example : (accrue pool (1 / 5) 1 0).reserves = 5 := by
  norm_num [afterAccrue, afterBorrow, afterRepay, execute_accrue, execute_borrow,
    execute_repay, PoolState.Valid, pool, quote, transfer_debt, accrue, accrue_index,
    PoolState.debt, total_debt_from_scaled, borrower_debt]
example : (accrue pool (1 / 5) 1 1).liabilities = 105 := by
  norm_num [afterAccrue, afterBorrow, afterRepay, execute_accrue, execute_borrow,
    execute_repay, PoolState.Valid, pool, quote, transfer_debt, accrue, accrue_index,
    PoolState.debt, total_debt_from_scaled, borrower_debt]
example : DeFiKinkedInterestRateUtilization.utilization 10 120 15 = 24 / 23 := by
  norm_num [DeFiKinkedInterestRateUtilization.utilization,
      DeFiKinkedInterestRateUtilization.denominator]
example : accrue_index 100 (DeFiKinkedInterestRateUtilization.borrow_rate params (1 / 2)) 1 = 106
    := by
  norm_num [accrue_index, DeFiKinkedInterestRateUtilization.borrow_rate, params]
example : accrue_discrete state 1000 200 1 500 = some ⟨10, 120, 15, 115, 1200⟩ := by decide
example : accrue_discrete state 1000 200 0 500 = some state := by decide
example : accrue_discrete state 1000 0 10 500 = some state := by decide
example : accrue_discrete state 0 200 1 500 = none := by decide
example : accrue_discrete state 1000 200 1 1001 = none := by decide
example : accrue_discrete ⟨0, 0, 0, 0, 0⟩ 1000 200 1 500 = none := by decide
example : interest_floor 1000 1 1 1 = 0 := by decide
example : index_floor 1000 1000 1 1 = 1001 := by decide
example : aggregate_int 10 15 (fun _ : Fin 2 => 1) = 3 := by decide
example : recon_dust 10 15 (fun _ : Fin 2 => 1) = 1 := by decide
example : recon_dust 10 19 (fun _ : Fin 4 => 1) = 3 := by decide
example : recon_dust 10 20 (fun _ : Fin 4 => 1) = 0 := by decide
example : recon_dust 10 19 (fun _ : Fin 1 => 1) = 0 := by decide
example : recon_dust 10 19 (fun _ : Fin 0 => 1) = 0 := by decide
example : ledger_index_gap 11 10 1 (fun _ : Fin 1 => 100) = 1 := by decide
example (W I r t : ℕ) (hW : 0 < W) :
    0 ≤ accrue_index ((I:ℚ) / W) ((r:ℚ) / W) t - (index_floor W I r t:ℚ) / W ∧
    accrue_index ((I:ℚ) / W) ((r:ℚ) / W) t - (index_floor W I r t:ℚ) / W < 1 / (W:ℚ) :=
  index_floor_error W I r t hW
example (n W I : ℕ) (b : Fin n → ℕ) (hW : 0 < W) (hn : 0 < n) :
    (∑ i, individual_int W I (b i)) ≤ aggregate_int W I b ∧ recon_dust W I b ≤ n - 1 :=
  recon_dust_bounds W I b hW hn
example (W rho d : ℕ) (hW : 0 < W) (hρ : rho ≤ W) : rho * d / W ≤ d :=
  reserve_split_le W rho d hW hρ
example (n : ℕ) (s s' : PoolState n) (k : Fin n) (a : ℚ) (h : RepayStep s s' k a)
    (hb : s.Balanced) : s'.Valid ∧ s'.Balanced ∧ s'.index = s.index ∧ s'.debt = s.debt - a :=
  repay_step_invariants h hb

def scenarios : List Bool := [
  decide (accrue_index 100 2 0 = 100),
  decide (accrue_index 100 0 50 = 100),
  decide (accrue_chain 100 [(1 / 10, 1), (1 / 10, 1)] = 121),
  decide (accrue_index 100 (1 / 10) 2 = 120),
  decide (afterAccrue.map quote = some (10, 120, 15, 115, 6 / 5)),
  decide (afterBorrow.map quote = some (5, 105, 5, 105, 1)),
  decide (afterRepay.map quote = some (110, 0, 5, 105, 1)),
  (execute_borrow pool 0 11).isNone,
  (execute_repay pool 0 101).isNone,
  (execute_accrue pool (-1) 1 0).isNone,
  (execute_accrue pool 1 1 2).isNone,
  (execute_accrue pool 1 (-1) 0).isNone,
  decide ((accrue pool (1 / 5) 1 0).reserves = 5),
  decide ((accrue pool (1 / 5) 1 1).liabilities = 105),
  decide (accrue_discrete state 1000 200 1 500 = some ⟨10, 120, 15, 115, 1200⟩),
  decide (accrue_discrete state 1000 200 0 500 = some state),
  decide (accrue_discrete state 1000 0 10 500 = some state),
  (accrue_discrete state 0 200 1 500).isNone,
  (accrue_discrete state 1000 200 1 1001).isNone,
  (accrue_discrete ⟨0, 0, 0, 0, 0⟩ 1000 200 1 500).isNone,
  decide (interest_floor 1000 1 1 1 = 0),
  decide (index_floor 1000 1000 1 1 = 1001),
  decide (recon_dust 10 15 (fun _ : Fin 2 => 1) = 1),
  decide (recon_dust 10 19 (fun _ : Fin 4 => 1) = 3),
  decide (recon_dust 10 20 (fun _ : Fin 4 => 1) = 0),
  decide (recon_dust 10 19 (fun _ : Fin 1 => 1) = 0),
  decide (recon_dust 10 19 (fun _ : Fin 0 => 1) = 0),
  decide (ledger_index_gap 11 10 1 (fun _ : Fin 1 => 100) = 1),
  decide (accrue_discrete state 1000 200 1 0 = some ⟨10, 120, 5, 125, 1200⟩),
  decide (accrue_discrete state 1000 200 1 1000 = some ⟨10, 120, 25, 105, 1200⟩)
]
end CompoundIndexRegression

def main : IO Unit := do
  if CompoundIndexRegression.scenarios.all id then
    IO.println s!"COMPOUND_INDEX_OK {CompoundIndexRegression.scenarios.length}"
  else throw (IO.userError "compound - index regression failed")
