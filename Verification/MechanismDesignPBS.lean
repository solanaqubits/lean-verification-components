import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring

set_option linter.style.header false
noncomputable section

namespace MechanismDesignPBS

/-- Prescribed block values, with the bid bounded by MEV as an assumption. -/
structure PBSBlock where
  mevValue : ℝ
  bid : ℝ
  gasBurnt : ℝ
  hmev_pos : 0 ≤ mevValue
  hbid_pos : 0 ≤ bid
  hbid_le : bid ≤ mevValue
  hgas_pos : 0 ≤ gasBurnt

def builderProfit (b : PBSBlock) : ℝ := b.mevValue - b.bid

/-- Bookkeeping total defined as MEV plus the supplied burn amount. -/
def totalExtractedValue (b : PBSBlock) : ℝ := b.mevValue + b.gasBurnt

theorem builder_profit_nonneg (b : PBSBlock) : 0 ≤ builderProfit b :=
  sub_nonneg.mpr b.hbid_le

theorem pbs_value_conservation (b : PBSBlock) :
    totalExtractedValue b = builderProfit b + b.bid + b.gasBurnt := by
  dsimp [totalExtractedValue, builderProfit]
  ring

structure PBSActorBalances where
  proposer : ℝ
  builder : ℝ
  escrow : ℝ

def totalBalance (s : PBSActorBalances) : ℝ := s.proposer + s.builder + s.escrow

/-- Credit the prescribed bid and profit; leave escrow unchanged. -/
def executePBSBlock (s : PBSActorBalances) (b : PBSBlock) : PBSActorBalances :=
  ⟨s.proposer + b.bid, s.builder + builderProfit b, s.escrow⟩

theorem pbs_balance_transition_invariant (s : PBSActorBalances) (b : PBSBlock) :
    totalBalance (executePBSBlock s b) = totalBalance s + b.mevValue := by
  dsimp [totalBalance, executePBSBlock, builderProfit]
  ring

structure BuilderBid where
  builderId : ℕ
  bidAmount : ℝ

/-- Membership and maximality, without an auction selection algorithm. -/
def WinningBid (bids : List BuilderBid) (winner : BuilderBid) : Prop :=
  winner ∈ bids ∧ ∀ b ∈ bids, b.bidAmount ≤ winner.bidAmount

theorem winning_bid_maximizes_proposer_revenue
    (bids : List BuilderBid) (winner : BuilderBid) (hw : WinningBid bids winner)
    (other : BuilderBid) (h_other : other ∈ bids) : other.bidAmount ≤ winner.bidAmount :=
  hw.2 other h_other

structure MechanismDesignPBSFormalSuite : Prop where
  h_profit_nonneg : ∀ b, 0 ≤ builderProfit b
  h_value_conserv : ∀ b, totalExtractedValue b = builderProfit b + b.bid + b.gasBurnt
  h_bal_transition : ∀ s b, totalBalance (executePBSBlock s b) = totalBalance s + b.mevValue
  h_auction_max : ∀ bids winner other,
    WinningBid bids winner → other ∈ bids → other.bidAmount ≤ winner.bidAmount

theorem mechanism_design_pbs_master_verification_suite : MechanismDesignPBSFormalSuite := {
  h_profit_nonneg := builder_profit_nonneg
  h_value_conserv := pbs_value_conservation
  h_bal_transition := pbs_balance_transition_invariant
  h_auction_max := fun bids winner other hw ho =>
    winning_bid_maximizes_proposer_revenue bids winner hw other ho
}

#print axioms mechanism_design_pbs_master_verification_suite

end MechanismDesignPBS
