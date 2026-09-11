import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

set_option linter.style.header false

namespace DistributedRaftConsensus

open Finset

def IsMajorityQuorum {α : Type*} [DecidableEq α] (U Q : Finset α) : Prop :=
  Q ⊆ U ∧ 2 * Q.card > U.card

theorem majority_intersection_nonempty {α : Type*} [DecidableEq α] (U A B : Finset α)
    (hA : A ⊆ U) (hB : B ⊆ U)
    (hA_maj : 2 * A.card > U.card) (hB_maj : 2 * B.card > U.card) :
    (A ∩ B).card > 0 := by
  have hu := card_le_card (union_subset hA hB)
  have hi := card_inter_add_card_union A B
  omega

/-- One shared vote function models the single-choice assumption for a fixed election. -/
theorem election_safety_unique_leader {α : Type*}
    (U A B : Finset α) (c1 c2 : ℕ) (votedFor : α → ℕ)
    (hA : A ⊆ U) (hB : B ⊆ U)
    (hA_maj : 2 * A.card > U.card) (hB_maj : 2 * B.card > U.card)
    (hA_votes : ∀ x ∈ A, votedFor x = c1) (hB_votes : ∀ x ∈ B, votedFor x = c2) :
    c1 = c2 := by
  classical
  obtain ⟨node, hn⟩ := card_pos.mp (majority_intersection_nonempty U A B hA hB hA_maj hB_maj)
  exact (hA_votes node (mem_inter.mp hn).1).symm.trans (hB_votes node (mem_inter.mp hn).2)

/-- Set overlap only, without a log-freshness rule or a fault model. -/
theorem leader_commit_quorum_overlap {α : Type*} [DecidableEq α]
    (U commitQuorum leaderQuorum : Finset α)
    (hc : commitQuorum ⊆ U) (hl : leaderQuorum ⊆ U)
    (hc_maj : 2 * commitQuorum.card > U.card) (hl_maj : 2 * leaderQuorum.card > U.card) :
    (commitQuorum ∩ leaderQuorum).Nonempty :=
  card_pos.mp (majority_intersection_nonempty U commitQuorum leaderQuorum hc hl hc_maj hl_maj)

structure LogEntry where
  index : ℕ
  term : ℕ
  deriving DecidableEq, Repr

/-- A prefix property, not a proved invariant of a protocol transition system. -/
def LogMatchingInvariant (log1 log2 : List LogEntry) : Prop :=
  ∀ (i : ℕ) e1 e2, log1[i]? = some e1 → log2[i]? = some e2 → e1.term = e2.term →
    ∀ (j : ℕ), j ≤ i → ∃ ej1 ej2, log1[j]? = some ej1 ∧ log2[j]? = some ej2 ∧ ej1 = ej2

structure NodeState where
  currentTerm : ℕ
  votedFor : Option ℕ
  log : List LogEntry

/-- Only the term inequality is constrained. -/
def ValidTermTransition (s s' : NodeState) : Prop := s.currentTerm ≤ s'.currentTerm

theorem term_transition_transitive (s1 s2 s3 : NodeState)
    (h1 : ValidTermTransition s1 s2) (h2 : ValidTermTransition s2 s3) :
    ValidTermTransition s1 s3 := le_trans h1 h2

structure DistributedRaftFormalSuite : Prop where
  h_quorum_overlap : ∀ {α : Type*} [DecidableEq α] (U A B : Finset α),
    A ⊆ U → B ⊆ U → 2 * A.card > U.card → 2 * B.card > U.card → (A ∩ B).card > 0
  h_election_safety : ∀ {α : Type*}
    (U A B : Finset α) (c1 c2 : ℕ) (votedFor : α → ℕ),
    A ⊆ U → B ⊆ U → 2 * A.card > U.card → 2 * B.card > U.card →
    (∀ x ∈ A, votedFor x = c1) → (∀ x ∈ B, votedFor x = c2) → c1 = c2
  h_commit_overlap : ∀ {α : Type*} [DecidableEq α] (U commitQuorum leaderQuorum : Finset α),
    commitQuorum ⊆ U → leaderQuorum ⊆ U →
    2 * commitQuorum.card > U.card → 2 * leaderQuorum.card > U.card →
    (commitQuorum ∩ leaderQuorum).Nonempty
  h_term_trans : ∀ s1 s2 s3,
    ValidTermTransition s1 s2 → ValidTermTransition s2 s3 → ValidTermTransition s1 s3

theorem distributed_raft_master_verification_suite : DistributedRaftFormalSuite := {
  h_quorum_overlap := majority_intersection_nonempty
  h_election_safety := election_safety_unique_leader
  h_commit_overlap := leader_commit_quorum_overlap
  h_term_trans := term_transition_transitive
}

#print axioms distributed_raft_master_verification_suite

end DistributedRaftConsensus
