/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-!
# DistributedPBFTConsensus

Algebraic and conditional invariants; see the theorem hypotheses and knowledge card for scope.
-/

namespace DistributedPBFTConsensus

/-! Arithmetic quorum bounds. Fixed 2f+1 quorums require N=3f+1 for the overlap bound. -/
structure PBFTSetup where
  N : ℕ
  f : ℕ
  h_threshold : 3 * f + 1 ≤ N

def quorumSize (setup : PBFTSetup) : ℕ := 2 * setup.f + 1

theorem quorum_size_le_total (setup : PBFTSetup) : quorumSize setup ≤ setup.N := by
  have := setup.h_threshold
  dsimp [quorumSize]
  omega

/-- Corrected fixed-quorum bound: the cluster has exactly 3f+1 nodes. -/
theorem pbft_quorum_intersection_size (setup : PBFTSetup)
    (h_exact : setup.N = 3 * setup.f + 1) :
    2 * quorumSize setup - setup.N ≥ setup.f + 1 := by
  dsimp [quorumSize]
  omega

/-- A cardinality subtraction identity, not a theorem about node sets. -/
theorem pbft_honest_node_in_quorum_intersection (setup : PBFTSetup) :
    (setup.f + 1) - setup.f ≥ 1 := by omega

theorem pbft_conflicting_quorums_impossible (setup : PBFTSetup)
    (h_exact : setup.N = 3 * setup.f + 1) :
    setup.N < 2 * quorumSize setup := by
  dsimp [quorumSize]
  omega

/-- Counterexample to extending the fixed-quorum intersection claim to all N≥3f+1. -/
theorem larger_cluster_counterexample :
    let setup : PBFTSetup := ⟨5, 1, by omega⟩
    ¬ (2 * quorumSize setup - setup.N ≥ setup.f + 1) := by decide

structure PrepareVote where
  view : ℕ
  seq : ℕ
  val : ℕ
  deriving DecidableEq, Repr

/-- Conditional value equality; honest-node uniqueness is assumed. -/
theorem pbft_single_value_prepared_in_view (v1 v2 : PrepareVote)
    (h_same_view : v1.view = v2.view) (h_same_seq : v1.seq = v2.seq)
    (h_honest_unique : v1.view = v2.view ∧ v1.seq = v2.seq → v1.val = v2.val) :
    v1.val = v2.val := h_honest_unique ⟨h_same_view, h_same_seq⟩

structure DistributedPBFTFormalSuite : Prop where
  h_quorum_le_n : ∀ (setup : PBFTSetup), quorumSize setup ≤ setup.N
  h_intersect_ge : ∀ (setup : PBFTSetup), setup.N = 3 * setup.f + 1 →
    2 * quorumSize setup - setup.N ≥ setup.f + 1
  h_honest_exists : ∀ (setup : PBFTSetup), (setup.f + 1) - setup.f ≥ 1
  h_no_disjoint : ∀ (setup : PBFTSetup), setup.N = 3 * setup.f + 1 →
    setup.N < 2 * quorumSize setup
  h_view_safety : ∀ (v1 v2 : PrepareVote), v1.view = v2.view → v1.seq = v2.seq →
    (v1.view = v2.view ∧ v1.seq = v2.seq → v1.val = v2.val) → v1.val = v2.val

theorem distributed_pbft_master_verification_suite : DistributedPBFTFormalSuite := {
  h_quorum_le_n := quorum_size_le_total
  h_intersect_ge := pbft_quorum_intersection_size
  h_honest_exists := pbft_honest_node_in_quorum_intersection
  h_no_disjoint := pbft_conflicting_quorums_impossible
  h_view_safety := pbft_single_value_prepared_in_view
}

end DistributedPBFTConsensus
