import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option linter.style.header false

namespace LightningHTLCNetwork

/-- Aggregate balances; individual HTLC identifiers and authorization are not modeled. -/
structure ChannelState where
  balanceA : ℕ
  balanceB : ℕ
  lockedHTLC : ℕ
  deriving DecidableEq, Repr

def channelCapacity (ch : ChannelState) : ℕ := ch.balanceA + ch.balanceB + ch.lockedHTLC

def lockHTLC (ch : ChannelState) (amount : ℕ) : ChannelState :=
  if amount ≤ ch.balanceA then
    ⟨ch.balanceA - amount, ch.balanceB, ch.lockedHTLC + amount⟩
  else ch

/-- Balance transfer only: no hash preimage is checked. -/
def claimHTLC (ch : ChannelState) (amount : ℕ) : ChannelState :=
  if amount ≤ ch.lockedHTLC then
    ⟨ch.balanceA, ch.balanceB + amount, ch.lockedHTLC - amount⟩
  else ch

/-- Balance refund only: no clock or expiry condition is checked. -/
def timeoutHTLC (ch : ChannelState) (amount : ℕ) : ChannelState :=
  if amount ≤ ch.lockedHTLC then
    ⟨ch.balanceA + amount, ch.balanceB, ch.lockedHTLC - amount⟩
  else ch

theorem capacity_lock_invariant (ch : ChannelState) (amount : ℕ) :
    channelCapacity (lockHTLC ch amount) = channelCapacity ch := by
  dsimp [channelCapacity, lockHTLC]
  split
  · dsimp
    omega
  · rfl

theorem capacity_claim_invariant (ch : ChannelState) (amount : ℕ) :
    channelCapacity (claimHTLC ch amount) = channelCapacity ch := by
  dsimp [channelCapacity, claimHTLC]
  split
  · dsimp
    omega
  · rfl

theorem capacity_timeout_invariant (ch : ChannelState) (amount : ℕ) :
    channelCapacity (timeoutHTLC ch amount) = channelCapacity ch := by
  dsimp [channelCapacity, timeoutHTLC]
  split
  · dsimp
    omega
  · rfl

structure Hop where
  amount : ℕ
  timelock : ℕ
  deriving DecidableEq, Repr

abbrev Route := List Hop

def ValidRouteTimelocks (minDelta : ℕ) : Route → Prop
  | [] => True
  | [_] => True
  | h1 :: h2 :: rest =>
      h2.timelock + minDelta ≤ h1.timelock ∧ ValidRouteTimelocks minDelta (h2 :: rest)

theorem timelock_strict_decrease_step (minDelta : ℕ) (h_delta : 1 ≤ minDelta)
    (h1 h2 : Hop) (rest : Route)
    (h_val : ValidRouteTimelocks minDelta (h1 :: h2 :: rest)) :
    h2.timelock < h1.timelock := by
  have h_step := h_val.1
  omega

/-- Tail index k denotes full-route position k+1, hence k+1 time gaps. -/
theorem route_timelock_cumulative (minDelta : ℕ) (h1 : Hop) (rest : Route)
    (h_val : ValidRouteTimelocks minDelta (h1 :: rest)) :
    ∀ (k : ℕ) (hk : Hop), rest[k]? = some hk →
      hk.timelock + (k + 1) * minDelta ≤ h1.timelock := by
  induction rest generalizing h1 with
  | nil =>
      intro k hk h_get
      simp only [List.getElem?_nil] at h_get
      cases h_get
  | cons h2 tail ih =>
      intro k hk h_get
      rcases h_val with ⟨h_step, h_tail⟩
      cases k with
      | zero =>
          have he : h2 = hk := Option.some.inj h_get
          subst hk
          simpa using h_step
      | succ k =>
          have hi := ih h2 h_tail k hk h_get
          have hm : (k + 1 + 1) * minDelta = (k + 1) * minDelta + minDelta :=
            Nat.succ_mul (k + 1) minDelta
          omega

structure IntermediaryState where
  incomingBalance : ℕ
  outgoingBalance : ℕ
  deriving DecidableEq, Repr

/-- Equal incoming and funded outgoing transfers preserve the sum of balances. -/
theorem intermediary_balance_neutral (st : IntermediaryState) (amount : ℕ)
    (h_out : amount ≤ st.outgoingBalance) :
    (st.incomingBalance + amount) + (st.outgoingBalance - amount) =
      st.incomingBalance + st.outgoingBalance := by omega

theorem intermediary_routing_fee_profit (inAmt outAmt : ℕ) (h_fee : outAmt < inAmt) :
    0 < inAmt - outAmt := by omega

structure LightningHTLCFormalSuite : Prop where
  h_cap_lock : ∀ ch amount, channelCapacity (lockHTLC ch amount) = channelCapacity ch
  h_cap_claim : ∀ ch amount, channelCapacity (claimHTLC ch amount) = channelCapacity ch
  h_cap_timeout : ∀ ch amount, channelCapacity (timeoutHTLC ch amount) = channelCapacity ch
  h_step_decrease : ∀ minDelta, 1 ≤ minDelta → ∀ h1 h2 rest,
    ValidRouteTimelocks minDelta (h1 :: h2 :: rest) → h2.timelock < h1.timelock
  h_cumul_timelock : ∀ minDelta h1 rest, ValidRouteTimelocks minDelta (h1 :: rest) →
    ∀ (k : ℕ) (hk : Hop), rest[k]? = some hk →
      hk.timelock + (k + 1) * minDelta ≤ h1.timelock
  h_neutral_bal : ∀ (st : IntermediaryState) (amount : ℕ), amount ≤ st.outgoingBalance →
    (st.incomingBalance + amount) + (st.outgoingBalance - amount) =
      st.incomingBalance + st.outgoingBalance
  h_fee_profit : ∀ (inAmt outAmt : ℕ), outAmt < inAmt → 0 < inAmt - outAmt

theorem lightning_htlc_master_verification_suite : LightningHTLCFormalSuite := {
  h_cap_lock := capacity_lock_invariant
  h_cap_claim := capacity_claim_invariant
  h_cap_timeout := capacity_timeout_invariant
  h_step_decrease := timelock_strict_decrease_step
  h_cumul_timelock := route_timelock_cumulative
  h_neutral_bal := intermediary_balance_neutral
  h_fee_profit := intermediary_routing_fee_profit
}

#print axioms lightning_htlc_master_verification_suite

end LightningHTLCNetwork
