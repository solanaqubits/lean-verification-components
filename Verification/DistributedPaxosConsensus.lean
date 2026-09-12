import Mathlib.Data.Nat.Basic

set_option linter.style.header false

namespace DistributedPaxosConsensus

/-- Arithmetic cluster parameter; no failures or node set are modeled. -/
structure PaxosCluster where
  f : ℕ

def totalNodes (c : PaxosCluster) : ℕ := 2 * c.f + 1
def quorumSize (c : PaxosCluster) : ℕ := c.f + 1

/-- Cardinality arithmetic only, without actual quorum sets. -/
theorem quorum_intersection_overlap (c : PaxosCluster) (q1 q2 : ℕ)
    (hq1 : quorumSize c ≤ q1) (hq2 : quorumSize c ≤ q2) :
    1 ≤ q1 + q2 - totalNodes c := by
  dsimp [quorumSize, totalNodes] at hq1 hq2 ⊢
  omega

structure AcceptorState where
  promisedBallot : ℕ
  acceptedBallot : ℕ
  acceptedValue : Option ℕ
  h_order : acceptedBallot ≤ promisedBallot

/-- Ballot eligibility, not a complete acceptance transition. -/
def canAccept (acc : AcceptorState) (b : ℕ) : Prop := acc.promisedBallot ≤ b

theorem reject_stale_ballot (acc : AcceptorState) (b : ℕ)
    (h_stale : b < acc.promisedBallot) : ¬ canAccept acc b := by
  dsimp [canAccept]
  omega

/-- Raise the promise while retaining the accepted fields. -/
def prepareResponse (acc : AcceptorState) (b : ℕ)
    (hb : acc.promisedBallot < b) : AcceptorState :=
  ⟨b, acc.acceptedBallot, acc.acceptedValue, Nat.le_trans acc.h_order (Nat.le_of_lt hb)⟩

theorem prepare_monotone (acc : AcceptorState) (b : ℕ) (hb : acc.promisedBallot < b) :
    acc.promisedBallot < (prepareResponse acc b hb).promisedBallot := hb

structure Proposal where
  ballot : ℕ
  value : ℕ
  deriving DecidableEq, Repr

/-- Proposal equality conditional on an assumed same-ballot value equality. -/
theorem ballot_value_uniqueness (p1 p2 : Proposal)
    (h_same_ballot : p1.ballot = p2.ballot)
    (h_leader_deterministic : p1.ballot = p2.ballot → p1.value = p2.value) :
    p1 = p2 := by
  have h_val := h_leader_deterministic h_same_ballot
  cases p1 with
  | mk b1 v1 =>
    cases p2 with
    | mk b2 v2 =>
      dsimp at h_same_ballot h_val
      cases h_same_ballot
      cases h_val
      rfl

structure DistributedPaxosFormalSuite : Prop where
  h_quorum_overlap : ∀ (c : PaxosCluster) (q1 q2 : ℕ),
    quorumSize c ≤ q1 → quorumSize c ≤ q2 → 1 ≤ q1 + q2 - totalNodes c
  h_reject_stale : ∀ (acc : AcceptorState) (b : ℕ),
    b < acc.promisedBallot → ¬ canAccept acc b
  h_prep_monotone : ∀ (acc : AcceptorState) (b : ℕ) (hb : acc.promisedBallot < b),
    acc.promisedBallot < (prepareResponse acc b hb).promisedBallot
  h_ballot_unique : ∀ p1 p2 : Proposal,
    p1.ballot = p2.ballot →
    (p1.ballot = p2.ballot → p1.value = p2.value) → p1 = p2

/-- Registry of local arithmetic and conditional proposal properties. -/
theorem distributed_paxos_master_verification_suite : DistributedPaxosFormalSuite := {
  h_quorum_overlap := quorum_intersection_overlap
  h_reject_stale := reject_stale_ballot
  h_prep_monotone := prepare_monotone
  h_ballot_unique := ballot_value_uniqueness
}

end DistributedPaxosConsensus
