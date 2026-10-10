import Verification.DistributedCausalBroadcast
open DistributedCausalBroadcast

example : DistributedCausalBroadcastSuite := distributed_causal_broadcast_master_suite
example (E : Execution n) (reliable : ReliableArrival E) (fair : WeakFairness E) :
    EventualDelivery E := liveness_under_fairness E reliable fair
example (E : Execution n) (p : NodeId n) (a b : MessageId n) (t v : ℕ)
    (ht : t + 1 ≤ v) (hb : DeliveredAt E p b t)
    (hab : MsgHappensBefore (E.state v) a b) : ∃ u < t, DeliveredAt E p a u :=
  causal_delivery_safety_extended E p a b t v ht hab hb
example (C : Config n) (h : Reachable C) (r : Record n) (hr : r ∈ C.archive) (k : NodeId n) :
    ((insert r.message.id r.parents).filter fun a => a.sender = k).card = r.message.timestamp k :=
  (timestamp_causal_past_exact h hr k).1
example : ¬ IsReady (Regression.causalBlocked.node 2) Regression.relay :=
  Regression.three_process_chain.1
example : (Regression.parallel.node 0).log ≠ (Regression.parallel.node 1).log := by decide +kernel
example : ¬ MsgHappensBefore Regression.parallel Regression.first.id Regression.independent.id :=
  Regression.parallel_causally_unrelated.1
example : Reachable Regression.reordered := counterexample_skip_sequence.1
example : Regression.first.id ∉ ((deliver Regression.causalBlocked 2 Regression.relay).node 2).log :=
  counterexample_missing_cross_check.2.2.2.2.2.2
example : LegalSchedule (initial 3) Regression.duplicateSchedule :=
  Regression.duplicate_arrival_no_redelivery.1

-- A fresh two-node witness: an undelivered network arrival conveys no application knowledge.
def twoFirst : Message 2 := ⟨⟨0,1⟩,![1,0]⟩
def twoSchedule : List (Action 2) := [.broadcast 0,.arrive 1 twoFirst,.broadcast 1]
example : LegalSchedule (initial 2) twoSchedule := by decide +kernel
example : ((runSchedule (initial 2) twoSchedule).node 1).delivered = ![0,1] := by decide +kernel
example : twoFirst ∈ ((runSchedule (initial 2) twoSchedule).node 1).buffer := by decide +kernel
example : ((runSchedule (initial 2) twoSchedule).archive.map fun r => r.message.timestamp) =
    [![1,0],![0,1]] := by
  decide +kernel
