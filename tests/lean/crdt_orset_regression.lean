import Verification.DistributedCRDTORSet
open DistributedCRDTORSet

example : DistributedCRDTORSetSuite := distributed_crdt_orset_master_suite
example (α : Type) [DecidableEq α] (n : ℕ) : SemilatticeSup (ORSetState α n) := inferInstance
example (α : Type) [DecidableEq α] (n : ℕ) : OrderBot (ORSetState α n) := inferInstance

-- Fair dissemination is a liveness premise, not an assumed final equality.
example [DecidableEq α] (E : Execution α n) (hs : FairSend E) (hf : WeakFairness E)
    (T : ℕ) (hq : NoUpdatesAfter E T) :
    ∃ B ≥ T, ∀ u ≥ B, ∀ p, ((E.state u).node p).payload =
      Finset.univ.sup (fun q => ((E.state T).node q).payload) := by
  simpa only [global_join_exact (E.reachable T)] using eventual_stabilization E hs hf T hq

-- Actual post-operation snapshots inherit causality; the full-state add-wins theorem
-- includes metadata from the histories, not merely the two singleton effects.
example : contains 7 (Regression.addPacket.payload ⊔ Regression.removePacket.payload) := by
  apply concurrent_add_wins_snapshots Regression.concurrent_reachable
    (a := Regression.a) (b := Regression.r)
  · simp [Regression.a, Regression.concurrent, add, commit]
  · simp [Regression.r, Regression.concurrent, Regression.removed, add, erase, commit]
  · rfl
  · exact Regression.reg_independent_causality
  · exact (reachable_invariant Regression.concurrent_reachable).sound 1
  · exact (reachable_invariant Regression.concurrent_reachable).sound 0
  · exact (reachable_invariant Regression.concurrent_reachable).histories 1
  · exact (reachable_invariant Regression.concurrent_reachable).histories 0
  · exact commit_operation_snapshot Regression.removed 1 (.add 7)
  · simpa [Regression.removePacket, Regression.concurrent, Regression.removed, Regression.r,
      add, erase, commit] using
      commit_operation_snapshot Regression.shared 0
        (.remove 7 (observed 7 (Regression.shared.node 0).payload))

-- A later observed removal is allowed to remove the formerly concurrent add.
def laterRemoval : Config ℕ 3 := erase Regression.removeFirst 2 7
example : Reachable laterRemoval := reachable_remove Regression.both_orders_reachable.1 2 7
example : ¬ contains 7 (laterRemoval.node 2).payload := by
  rw [laterRemoval, remove_payload]
  exact fun h => ((observed_remove_exact 7 7 (1, (0 : Fin 3))
    (Regression.removeFirst.node 2).payload).2.mp h).2 rfl
example : ((receive laterRemoval 2 Regression.addPacket).node 2).payload =
    (laterRemoval.node 2).payload := by
  apply ORSetState.ext <;> decide +kernel
example : contains 7 ((add laterRemoval 2 7).node 2).payload :=
  operational_readd (reachable_remove Regression.both_orders_reachable.1 2 7) 2 7

-- No ordering on values is required, and deleting one value preserves another.
def boolState : ORSetState Bool 1 := addTag false (1, 0) (addTag true (2, 0) ⊥)
example : contains true (remove false boolState) := by
  apply (observed_remove_exact false true (2, (0 : Fin 1)) boolState).2.mpr
  exact ⟨⟨(2, 0), by decide +kernel, by decide +kernel⟩, by decide +kernel⟩
example : ¬ contains 7 (addTag 7 (1, 0) Regression.deletedState) := Regression.counterexample_tag_reuse
example : contains 7 (Regression.unsafeGC Regression.deletedState ⊔ Regression.oldState) :=
  Regression.counterexample_tombstone_gc.2.2.1

example [DecidableEq α] (C : Config α n) (hc : Reachable C) (E : BroadcastBridge.CBExecution n)
    (hr : DistributedCausalBroadcast.ReliableArrival E)
    (hf : DistributedCausalBroadcast.WeakFairness E) (T : ℕ)
    (ha : BroadcastBridge.CheckpointAnnounced E T) :
    ∃ B, ∀ u ≥ B, ∀ p,
      BroadcastBridge.adapter E (BroadcastBridge.checkpointPacket C) u p = summarize C.issued :=
  BroadcastBridge.causal_broadcast_bridge hc E hr hf T ha
