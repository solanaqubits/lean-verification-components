import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option linter.style.header false

namespace BFTConsensusQuorum

open Finset

/-- Lower parameter bounds alone do not guarantee quorum intersection or availability. -/
structure BFTConfig where
  f : ℕ
  N : ℕ
  Q : ℕ
  h_total : 3 * f + 1 ≤ N
  h_quorum : 2 * f + 1 ≤ Q
  h_q_le_N : Q ≤ N

def minIntersectionCard (cfg : BFTConfig) : ℕ := 2 * cfg.Q - cfg.N

theorem min_intersection_ge_f_add_one (cfg : BFTConfig)
    (hN : cfg.N = 3 * cfg.f + 1) (hQ : cfg.Q = 2 * cfg.f + 1) :
    cfg.f + 1 ≤ minIntersectionCard cfg := by
  dsimp [minIntersectionCard]
  omega

theorem honest_intersection_card_ge_one (cfg : BFTConfig)
    (hN : cfg.N = 3 * cfg.f + 1) (hQ : cfg.Q = 2 * cfg.f + 1) :
    1 ≤ minIntersectionCard cfg - cfg.f := by
  have := min_intersection_ge_f_add_one cfg hN hQ
  omega

variable {V : Type*} [DecidableEq V]

/-- Inclusion-exclusion gives a lower bound for any two sufficiently large subsets. -/
theorem quorum_intersection_card (nodes Q1 Q2 : Finset V) (N Q : ℕ)
    (h_nodes_card : nodes.card ≤ N) (h_Q1_sub : Q1 ⊆ nodes) (h_Q2_sub : Q2 ⊆ nodes)
    (h_Q1_card : Q ≤ Q1.card) (h_Q2_card : Q ≤ Q2.card) :
    2 * Q - N ≤ (Q1 ∩ Q2).card := by
  have hu := le_trans (card_le_card (union_subset h_Q1_sub h_Q2_sub)) h_nodes_card
  have hi := card_inter_add_card_union Q1 Q2
  omega

/-- General honest-intersection condition; no voting or decision rule is modeled. -/
theorem honest_intersection_of_threshold
    (nodes Q1 Q2 faulty : Finset V) (f N Q : ℕ)
    (h_nodes_card : nodes.card ≤ N) (h_faulty_card : faulty.card ≤ f)
    (h_Q1_sub : Q1 ⊆ nodes) (h_Q2_sub : Q2 ⊆ nodes)
    (h_Q1_card : Q ≤ Q1.card) (h_Q2_card : Q ≤ Q2.card)
    (h_threshold : N + f < 2 * Q) :
    1 ≤ ((Q1 ∩ Q2) \ faulty).card := by
  have hi := quorum_intersection_card nodes Q1 Q2 N Q h_nodes_card
    h_Q1_sub h_Q2_sub h_Q1_card h_Q2_card
  have hd : (Q1 ∩ Q2).card ≤ ((Q1 ∩ Q2) \ faulty).card + faulty.card :=
    card_le_card_sdiff_add_card
  omega

theorem quorum_honest_intersection_nonempty
    (nodes Q1 Q2 faulty : Finset V) (f N Q : ℕ)
    (h_nodes_card : nodes.card = N) (_h_faulty_sub : faulty ⊆ nodes)
    (h_faulty_card : faulty.card ≤ f) (h_Q1_sub : Q1 ⊆ nodes) (h_Q2_sub : Q2 ⊆ nodes)
    (h_Q1_card : Q ≤ Q1.card) (h_Q2_card : Q ≤ Q2.card)
    (h_N : N = 3 * f + 1) (h_Q : Q = 2 * f + 1) :
    1 ≤ ((Q1 ∩ Q2) \ faulty).card := by
  apply honest_intersection_of_threshold nodes Q1 Q2 faulty f N Q
    h_nodes_card.le h_faulty_card h_Q1_sub h_Q2_sub h_Q1_card h_Q2_card
  omega

/-- Cardinal availability does not assert message delivery or protocol termination. -/
theorem honest_nodes_of_threshold (nodes faulty : Finset V) (f N Q : ℕ)
    (h_nodes_card : nodes.card = N) (h_faulty_sub : faulty ⊆ nodes)
    (h_faulty_card : faulty.card ≤ f) (h_threshold : Q + f ≤ N) :
    Q ≤ (nodes \ faulty).card := by
  have := card_sdiff_add_card_eq_card h_faulty_sub
  omega

theorem honest_nodes_can_form_quorum (nodes faulty : Finset V) (f N Q : ℕ)
    (h_nodes_card : nodes.card = N) (h_faulty_sub : faulty ⊆ nodes)
    (h_faulty_card : faulty.card ≤ f)
    (h_N : N = 3 * f + 1) (h_Q : Q = 2 * f + 1) :
    Q ≤ (nodes \ faulty).card := by
  apply honest_nodes_of_threshold nodes faulty f N Q h_nodes_card h_faulty_sub h_faulty_card
  omega

structure BFTConsensusFormalSuite : Prop where
  h_arith_min_inter : ∀ cfg, cfg.N = 3 * cfg.f + 1 → cfg.Q = 2 * cfg.f + 1 →
    cfg.f + 1 ≤ minIntersectionCard cfg
  h_arith_honest_pos : ∀ cfg, cfg.N = 3 * cfg.f + 1 → cfg.Q = 2 * cfg.f + 1 →
    1 ≤ minIntersectionCard cfg - cfg.f
  h_quorum_safety : ∀ (nodes Q1 Q2 faulty : Finset ℕ) (f N Q : ℕ),
    nodes.card = N → faulty ⊆ nodes → faulty.card ≤ f →
    Q1 ⊆ nodes → Q2 ⊆ nodes → Q ≤ Q1.card → Q ≤ Q2.card →
    N = 3 * f + 1 → Q = 2 * f + 1 → 1 ≤ ((Q1 ∩ Q2) \ faulty).card
  h_quorum_liveness : ∀ (nodes faulty : Finset ℕ) (f N Q : ℕ),
    nodes.card = N → faulty ⊆ nodes → faulty.card ≤ f →
    N = 3 * f + 1 → Q = 2 * f + 1 → Q ≤ (nodes \ faulty).card

theorem bft_consensus_master_verification_suite : BFTConsensusFormalSuite := {
  h_arith_min_inter := min_intersection_ge_f_add_one
  h_arith_honest_pos := honest_intersection_card_ge_one
  h_quorum_safety := quorum_honest_intersection_nonempty
  h_quorum_liveness := honest_nodes_can_form_quorum
}

#print axioms bft_consensus_master_verification_suite

end BFTConsensusQuorum
