import Verification.DistributedCRDTStateLWW
open DistributedCRDTStateLWW

example : DistributedCRDTStateLWWSuite := distributed_crdt_state_lww_master_suite
example (E : Execution α n) (sending : FairSend E) (fair : WeakFairness E)
    (T : ℕ) (stop : NoWritesAfter E T) :
    ∃ B ≥ T, ∀ u ≥ B, ∀ p, ((E.state u).node p).reg = summarize (E.state T).issued :=
  eventual_consistency_stabilization E sending fair T stop
example (C D : Config α n) (hc : Reachable C) (hd : Reachable D) (p q : ReplicaId n)
    (he : ∀ a, a ∈ (C.node p).history ↔ a ∈ (D.node q).history) :
    (C.node p).reg = (D.node q).reg := sec_across_traces hc hd p q he
example (C : Config α n) (hc : Reachable C) (E : BroadcastBridge.CBExecution n)
    (hr : DistributedCausalBroadcast.ReliableArrival E)
    (hf : DistributedCausalBroadcast.WeakFairness E) (T : ℕ)
    (ha : BroadcastBridge.CheckpointAnnounced E T) :
    ∃ B, ∀ u ≥ B, ∀ p,
      BroadcastBridge.adapter E (BroadcastBridge.checkpointPacket C) u p = summarize C.issued :=
  BroadcastBridge.causal_broadcast_bridge hc E hr hf T ha
example : Reachable Regression.leftFirst := Regression.both_orders_reachable.1
example : Reachable Regression.rightFirst := Regression.both_orders_reachable.2
example : ¬ RegLE (Regression.observed.node 1).reg
    ((Regression.staleOverwrite Regression.observed 1 30).node 1).reg :=
  counterexample_stale_stamp.2

-- A fresh relay observes a remote maximum, writes above it, then ignores a stale packet.
def relayWrite : Config ℕ 3 := write Regression.leftFirst 2 99
def relayReceiveOld : Config ℕ 3 := receive relayWrite 2 Regression.leftPacket
example : Reachable relayWrite := reachable_write Regression.both_orders_reachable.1 2 99
example : (relayWrite.node 2).reg = some (⟨2, 2⟩, 99) := by decide +kernel
example : (relayReceiveOld.node 2).reg = (relayWrite.node 2).reg := by decide +kernel

-- The payload type needs no order: only the stamp determines the winning value.
example : merge (some ((⟨3, 0⟩ : Stamp 2), false)) (some (⟨2, 1⟩, true)) =
    some (⟨3, 0⟩, false) := by decide +kernel

example (H : List (Entry α n)) [Fact (Unique H)] : SemilatticeSup (ValidState H) := inferInstance
example (H : List (Entry α n)) [Fact (Unique H)] : OrderBot (ValidState H) := inferInstance
