import Mathlib.Data.Nat.Basic

set_option linter.style.header false

namespace DistributedBullyElection

structure Node where
  id : ℕ
  isAlive : Bool
  deriving DecidableEq, Repr

/-- A static two-node snapshot with strictly ordered identifiers. -/
structure System2 where
  n1 : Node
  n2 : Node
  h_diff_id : n1.id < n2.id

/-- Select the highest identifier whose supplied activity flag is true. -/
def leaderElectionWinner (sys : System2) : Option ℕ :=
  if sys.n2.isAlive then some sys.n2.id
  else if sys.n1.isAlive then some sys.n1.id
  else none

theorem bully_top_node_wins_if_alive (sys : System2) (h_alive : sys.n2.isAlive = true) :
    leaderElectionWinner sys = some sys.n2.id := by
  simp [leaderElectionWinner, h_alive]

/-- Conditional selection in a snapshot, not a temporal failover guarantee. -/
theorem bully_fallback_to_lower_if_top_dead (sys : System2)
    (h_dead2 : sys.n2.isAlive = false) (h_alive1 : sys.n1.isAlive = true) :
    leaderElectionWinner sys = some sys.n1.id := by
  simp [leaderElectionWinner, h_dead2, h_alive1]

theorem bully_leader_uniqueness (sys : System2) (l1 l2 : ℕ)
    (h1 : leaderElectionWinner sys = some l1)
    (h2 : leaderElectionWinner sys = some l2) : l1 = l2 := by
  exact Option.some.inj (h1.symm.trans h2)

theorem bully_leader_is_alive (sys : System2) (leaderId : ℕ)
    (h_lead : leaderElectionWinner sys = some leaderId) :
    (leaderId = sys.n2.id ∧ sys.n2.isAlive = true) ∨
      (leaderId = sys.n1.id ∧ sys.n1.isAlive = true) := by
  cases h2 : sys.n2.isAlive <;> cases h1 : sys.n1.isAlive <;>
    simp [leaderElectionWinner, h2, h1] at h_lead ⊢ <;> omega

/-- Maximality among the two nodes with true activity flags. -/
theorem bully_leader_is_maximum (sys : System2) (leaderId : ℕ)
    (h_lead : leaderElectionWinner sys = some leaderId) :
    ∀ (n : Node), (n = sys.n1 ∨ n = sys.n2) → n.isAlive = true → n.id ≤ leaderId := by
  intro n hn h_alive
  have h_order := sys.h_diff_id
  rcases hn with rfl | rfl
  · cases h2 : sys.n2.isAlive <;>
      simp [leaderElectionWinner, h2, h_alive] at h_lead <;> omega
  · simp [leaderElectionWinner, h_alive] at h_lead
    omega

structure DistributedBullyFormalSuite : Prop where
  h_top_wins : ∀ (sys : System2), sys.n2.isAlive = true →
    leaderElectionWinner sys = some sys.n2.id
  h_fallback : ∀ (sys : System2), sys.n2.isAlive = false → sys.n1.isAlive = true →
    leaderElectionWinner sys = some sys.n1.id
  h_unique : ∀ (sys : System2) (l1 l2 : ℕ), leaderElectionWinner sys = some l1 →
    leaderElectionWinner sys = some l2 → l1 = l2
  h_alive : ∀ (sys : System2) (l : ℕ), leaderElectionWinner sys = some l →
    (l = sys.n2.id ∧ sys.n2.isAlive = true) ∨ (l = sys.n1.id ∧ sys.n1.isAlive = true)
  h_maximal : ∀ (sys : System2) (l : ℕ), leaderElectionWinner sys = some l →
    ∀ (n : Node), (n = sys.n1 ∨ n = sys.n2) → n.isAlive = true → n.id ≤ l

theorem distributed_bully_master_verification_suite : DistributedBullyFormalSuite := {
  h_top_wins := bully_top_node_wins_if_alive
  h_fallback := bully_fallback_to_lower_if_top_dead
  h_unique := bully_leader_uniqueness
  h_alive := bully_leader_is_alive
  h_maximal := bully_leader_is_maximum
}

end DistributedBullyElection
