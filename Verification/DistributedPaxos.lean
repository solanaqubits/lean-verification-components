/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-!
# DistributedPaxos

Algebraic and conditional invariants; see the theorem hypotheses and knowledge card for scope.
-/

namespace DistributedPaxos

/-! Same-ballot agreement from actual majority quorums and an explicit single-vote hypothesis.
No protocol transitions or cross-ballot safety invariant are modeled. -/

/-- A ballot key; allocation and uniqueness of keys in an execution are not modeled. -/
structure Ballot where
  round : ℕ
  proposerId : ℕ
  deriving DecidableEq, Repr

/-- Lexicographic comparison of the complete ballot key. -/
def ballotLt (b1 b2 : Ballot) : Prop :=
  b1.round < b2.round ∨ (b1.round = b2.round ∧ b1.proposerId < b2.proposerId)

theorem ballot_lt_irreflexive (b : Ballot) : ¬ ballotLt b b := by
  simp [ballotLt]

theorem ballot_lt_transitive {b1 b2 b3 : Ballot}
    (h12 : ballotLt b1 b2) (h23 : ballotLt b2 b3) : ballotLt b1 b3 := by
  dsimp [ballotLt] at *
  omega

theorem ballot_lt_trichotomy (b1 b2 : Ballot) :
    ballotLt b1 b2 ∨ b1 = b2 ∨ ballotLt b2 b1 := by
  cases b1
  cases b2
  simp only [ballotLt, Ballot.mk.injEq]
  omega

/-- Arithmetic consequence of increasing rounds, not a Promise transition invariant. -/
theorem paxos_ballot_monotonicity (b1 b2 : Ballot)
    (h_gt : b1.round < b2.round) : b1.round ≠ b2.round := by
  omega

structure Proposal where
  ballot : Ballot
  val : ℕ
  deriving DecidableEq, Repr

/-- Candidate record. Actual choice requires a proof of IsChosen. -/
structure ChosenValue where
  ballot : Ballot
  val : ℕ
  deriving DecidableEq, Repr

/-- A finite, nonempty acceptor universe. -/
structure PaxosCluster where
  N : ℕ
  h_pos : 0 < N

abbrev Node (cluster : PaxosCluster) := Fin cluster.N

/-- Strict majority of the entire acceptor universe. -/
def IsMajority (cluster : PaxosCluster) (Q : Finset (Node cluster)) : Prop :=
  cluster.N < 2 * Q.card

/-- Two strict majorities contain an actual common acceptor. -/
theorem majority_quorums_intersect (cluster : PaxosCluster)
    (Q1 Q2 : Finset (Node cluster))
    (h1 : IsMajority cluster Q1) (h2 : IsMajority cluster Q2) :
    (Q1 ∩ Q2).Nonempty := by
  apply Finset.inter_nonempty_of_card_lt_card_add_card
    (Finset.subset_univ Q1) (Finset.subset_univ Q2)
  simp only [Finset.card_univ, Fintype.card_fin]
  dsimp [IsMajority] at h1 h2
  omega

/-- Supplied acceptance history, without an execution or delivery model. -/
abbrev Accepted (cluster : PaxosCluster) := Node cluster → Ballot → ℕ → Prop

/-- Per-acceptor uniqueness at one ballot, assumed rather than derived from protocol steps. -/
def SingleVote {cluster : PaxosCluster} (accepted : Accepted cluster) : Prop :=
  ∀ node ballot v1 v2, accepted node ballot v1 → accepted node ballot v2 → v1 = v2

/-- A value is chosen when a strict majority has accepted it at the stated ballot. -/
def IsChosen {cluster : PaxosCluster} (accepted : Accepted cluster) (c : ChosenValue) : Prop :=
  ∃ Q : Finset (Node cluster), IsMajority cluster Q ∧
    ∀ node ∈ Q, accepted node c.ballot c.val

/-- Same-ballot safety follows from quorum overlap and single voting.
This does not establish agreement across different ballots. -/
theorem paxos_consensus_safety {cluster : PaxosCluster} (accepted : Accepted cluster)
    (h_single : SingleVote accepted) (c1 c2 : ChosenValue)
    (h_chosen1 : IsChosen accepted c1) (h_chosen2 : IsChosen accepted c2)
    (h_same_ballot : c1.ballot = c2.ballot) : c1.val = c2.val := by
  obtain ⟨Q1, hq1, ha1⟩ := h_chosen1
  obtain ⟨Q2, hq2, ha2⟩ := h_chosen2
  obtain ⟨node, hn⟩ := majority_quorums_intersect cluster Q1 Q2 hq1 hq2
  obtain ⟨hn1, hn2⟩ := Finset.mem_inter.mp hn
  have h2 : accepted node c1.ballot c2.val := by
    rw [h_same_ballot]
    exact ha2 node hn2
  exact h_single node c1.ballot c1.val c2.val (ha1 node hn1) h2

/-- Equal ballot fields alone do not imply equal candidate values. -/
theorem same_ballot_counterexample :
    ∃ c1 c2 : ChosenValue, c1.ballot = c2.ballot ∧ c1.val ≠ c2.val := by
  exact ⟨⟨⟨0, 0⟩, 0⟩, ⟨⟨0, 0⟩, 1⟩, rfl, by decide⟩

/-- The majority definition includes the one-acceptor boundary case. -/
theorem singleton_cluster_majority :
    IsMajority ⟨1, by decide⟩ (Finset.univ : Finset (Fin 1)) := by
  simp [IsMajority]

structure DistributedPaxosFormalSuite : Prop where
  h_irrefl : ∀ b, ¬ ballotLt b b
  h_trans : ∀ {b1 b2 b3}, ballotLt b1 b2 → ballotLt b2 b3 → ballotLt b1 b3
  h_trichotomy : ∀ b1 b2, ballotLt b1 b2 ∨ b1 = b2 ∨ ballotLt b2 b1
  h_mono : ∀ b1 b2 : Ballot, b1.round < b2.round → b1.round ≠ b2.round
  h_intersection : ∀ cluster (Q1 Q2 : Finset (Node cluster)),
    IsMajority cluster Q1 → IsMajority cluster Q2 → (Q1 ∩ Q2).Nonempty
  h_safety : ∀ {cluster} (accepted : Accepted cluster), SingleVote accepted →
    ∀ c1 c2, IsChosen accepted c1 → IsChosen accepted c2 →
    c1.ballot = c2.ballot → c1.val = c2.val

/-- Registry of ballot ordering and conditional same-ballot quorum agreement. -/
theorem distributed_paxos_master_suite : DistributedPaxosFormalSuite := {
  h_irrefl := ballot_lt_irreflexive
  h_trans := ballot_lt_transitive
  h_trichotomy := ballot_lt_trichotomy
  h_mono := paxos_ballot_monotonicity
  h_intersection := majority_quorums_intersect
  h_safety := paxos_consensus_safety
}

end DistributedPaxos
