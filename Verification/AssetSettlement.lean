import Mathlib.Data.Nat.Basic

set_option linter.style.header false

namespace AssetSettlement

structure Account where
  balanceA : ℕ
  balanceB : ℕ
  deriving DecidableEq, Repr

/-- Two distinct account slots in a sequential ledger model. -/
structure LedgerState where
  party1 : Account
  party2 : Account
  deriving DecidableEq, Repr

structure DvPOrder where
  amountA : ℕ
  amountB : ℕ
  deriving DecidableEq, Repr

inductive SettlementStatus where
  | pending
  | executed
  | rejected
  deriving DecidableEq, Repr

/-- The caller must retain the updated status; there is no global identifier registry. -/
structure SettlementContract where
  order : DvPOrder
  status : SettlementStatus
  deriving DecidableEq, Repr

def totalAssetA (st : LedgerState) : ℕ := st.party1.balanceA + st.party2.balanceA
def totalAssetB (st : LedgerState) : ℕ := st.party1.balanceB + st.party2.balanceB

def CanSettle (st : LedgerState) (order : DvPOrder) : Prop :=
  order.amountA ≤ st.party1.balanceA ∧ order.amountB ≤ st.party2.balanceB

instance (st : LedgerState) (order : DvPOrder) : Decidable (CanSettle st order) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- One model transition updates both legs, or leaves the entire ledger unchanged. -/
def executeDvP (st : LedgerState) (order : DvPOrder) : LedgerState :=
  if CanSettle st order then
    ⟨⟨st.party1.balanceA - order.amountA, st.party1.balanceB + order.amountB⟩,
     ⟨st.party2.balanceA + order.amountA, st.party2.balanceB - order.amountB⟩⟩
  else st

theorem dvp_conservation_assetA (st : LedgerState) (order : DvPOrder) :
    totalAssetA (executeDvP st order) = totalAssetA st := by
  unfold executeDvP
  split
  · rename_i h
    dsimp [totalAssetA]
    rcases h with ⟨ha, hb⟩
    omega
  · rfl

theorem dvp_conservation_assetB (st : LedgerState) (order : DvPOrder) :
    totalAssetB (executeDvP st order) = totalAssetB st := by
  unfold executeDvP
  split
  · rename_i h
    dsimp [totalAssetB]
    rcases h with ⟨ha, hb⟩
    omega
  · rfl

theorem dvp_exact_exchange (st : LedgerState) (order : DvPOrder) (h : CanSettle st order) :
    (executeDvP st order).party1.balanceB = st.party1.balanceB + order.amountB ∧
    (executeDvP st order).party2.balanceA = st.party2.balanceA + order.amountA := by
  simp [executeDvP, h]

/-- Exact debits together with credits describe both legs of a successful exchange. -/
theorem dvp_exact_debits (st : LedgerState) (order : DvPOrder) (h : CanSettle st order) :
    (executeDvP st order).party1.balanceA + order.amountA = st.party1.balanceA ∧
    (executeDvP st order).party2.balanceB + order.amountB = st.party2.balanceB := by
  simp only [executeDvP, if_pos h]
  rcases h with ⟨ha, hb⟩
  exact ⟨Nat.sub_add_cancel ha, Nat.sub_add_cancel hb⟩

theorem dvp_insufficient_funds_noop (st : LedgerState) (order : DvPOrder)
    (h : ¬ CanSettle st order) : executeDvP st order = st := by
  simp [executeDvP, h]

def processContract (st : LedgerState) (c : SettlementContract) :
    LedgerState × SettlementContract :=
  match c.status with
  | .pending =>
      if CanSettle st c.order then
        (executeDvP st c.order, ⟨c.order, .executed⟩)
      else (st, ⟨c.order, .rejected⟩)
  | .executed => (st, c)
  | .rejected => (st, c)

/-- Reprocessing a contract whose supplied status is executed is a no-op. -/
theorem process_contract_no_double_spend (st : LedgerState) (c : SettlementContract)
    (h_exec : c.status = .executed) : processContract st c = (st, c) := by
  simp [processContract, h_exec]

theorem process_contract_rejected_noop (st : LedgerState) (c : SettlementContract)
    (h : c.status = .rejected) : processContract st c = (st, c) := by
  simp [processContract, h]

theorem process_contract_conserves_supplies (st : LedgerState) (c : SettlementContract) :
    totalAssetA (processContract st c).1 = totalAssetA st ∧
    totalAssetB (processContract st c).1 = totalAssetB st := by
  cases hc : c.status <;> by_cases hs : CanSettle st c.order <;>
    simp [processContract, hc, hs, dvp_conservation_assetA, dvp_conservation_assetB]

/-- Reprocessing the returned ledger and contract never changes either component. -/
theorem process_contract_idempotent (st : LedgerState) (c : SettlementContract) :
    processContract (processContract st c).1 (processContract st c).2 = processContract st c := by
  cases hc : c.status <;> by_cases hs : CanSettle st c.order <;>
    simp [processContract, hc, hs]

structure AssetSettlementFormalSuite : Prop where
  h_conserve_A : ∀ st order, totalAssetA (executeDvP st order) = totalAssetA st
  h_conserve_B : ∀ st order, totalAssetB (executeDvP st order) = totalAssetB st
  h_exact_trade : ∀ st order, CanSettle st order →
    (executeDvP st order).party1.balanceB = st.party1.balanceB + order.amountB ∧
    (executeDvP st order).party2.balanceA = st.party2.balanceA + order.amountA
  h_no_replay : ∀ st c, c.status = .executed → processContract st c = (st, c)
  h_proc_conserve : ∀ st c,
    totalAssetA (processContract st c).1 = totalAssetA st ∧
    totalAssetB (processContract st c).1 = totalAssetB st
  h_idempotent : ∀ st c,
    processContract (processContract st c).1 (processContract st c).2 = processContract st c

theorem asset_settlement_master_verification_suite : AssetSettlementFormalSuite := {
  h_conserve_A := dvp_conservation_assetA
  h_conserve_B := dvp_conservation_assetB
  h_exact_trade := dvp_exact_exchange
  h_no_replay := process_contract_no_double_spend
  h_proc_conserve := process_contract_conserves_supplies
  h_idempotent := process_contract_idempotent
}

#print axioms asset_settlement_master_verification_suite

end AssetSettlement
