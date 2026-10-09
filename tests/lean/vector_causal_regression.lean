import Verification.DistributedVectorClocksCausalOrder

open DistributedVectorClocksCausalOrder

-- The causal relation is extracted from events, before any timestamp is supplied.
example {n l : ℕ} {H : History n l} (h : H.Legal) {a b : Fin l}
    (hs : (H.event a).proc = (H.event b).proc)
    (hn : (H.event a).seq < (H.event b).seq) : HappensBefore H a b :=
  Relation.TransGen.single ⟨(local_order_iff h hs).mp hn, Or.inl hs⟩

example {n l : ℕ} {H : History n l} (E : Execution H) {a b : Fin l}
    (h : H.messageEdge a b) : VectorLT (E.stamp a) (E.stamp b) :=
  (happens_before_iff_vector_lt E a b).mp
    (Relation.TransGen.single ⟨matching_send_precedes E.legal h, Or.inr h⟩)

-- Reflection and injectivity must hold for every legal execution, not just compute.
example {n l : ℕ} {H : History n l} (E : Execution H) {a b : Fin l}
    (h : VectorLE (E.stamp a) (E.stamp b)) : a = b ∨ HappensBefore H a b :=
  (causal_past_iff_vector_le E a b).mpr h

example {n l : ℕ} {H : History n l} (E : Execution H) {a b : Fin l}
    (h : E.stamp a = E.stamp b) : a = b := event_timestamp_injective E h

example {n l : ℕ} {H : History n l} (E : Execution H) :
    E.stamp = (execute H E.legal).stamp := execution_unique E _

-- Equal coordinates are allowed in strict vector order.
example : VectorLT (![1, 0] : VectorClock 2) ![1, 1] := by
  constructor
  · intro i; fin_cases i <;> decide
  · intro h; have := congrFun h 1; change (0 : ℕ) = 1 at this; omega

example : Concurrent independentHistory 0 1 := reg_independent_concurrent
example : ¬ Concurrent independentHistory 0 0 := reg_no_self_concurrency _ _
example : relayExecution.stamp 3 = ![1, 2, 1] := reg_relay_stamps.2.2.2
example : HappensBefore relayHistory 0 3 := reg_three_process_causality

-- A later global trace index does not imply causality (an outstanding send).
example : Concurrent reorderedHistory 3 4 := by
  apply (concurrent_iff_vector_incomparable reorderedExecution 3 4).mpr
  rw [reg_out_of_order_stamps.2.1, reg_out_of_order_stamps.2.2]
  constructor
  · intro h; have := h 1; change 2 ≤ 0 at this; omega
  · intro h; have := h 0; change 3 ≤ 2 at this; omega

example : (reorderedHistory.event 4).payload = .send 2 1 ∧
    ∀ e, (reorderedHistory.event e).payload ≠ .recv 2 := reg_undelivered_message

-- Independent fresh computation covers the n = 1 boundary.
example : compute sequentialHistory 0 = ![1] ∧ compute sequentialHistory 1 = ![2] := by
  decide +kernel

example : ¬ VectorLT (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0) :=
  counterexample_no_increment.2.2
example : ¬ VectorLE (tick (0 : Fin 3) (fun _ => 0)) (tick (1 : Fin 3) (fun _ => 0)) :=
  counterexample_no_merge.2.2

example (v w : VectorClock 2) :
    toPair (tick 1 (merge v w)) = DistributedVectorClocks.receive2 (toPair v) (toPair w) :=
  n2_receive2_bridge v w

example : DistributedVectorClocksCausalOrderSuite := distributed_vector_clocks_causal_order_master_suite
