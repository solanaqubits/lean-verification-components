---
id: DistributedLamportClocks
language: en
section: distributed
source: Verification/DistributedLamportClocks.lean
source_sha256: 2ea1af72a0e3dba8b708808b0692fb8513ddc4992a3a1208bb0849103374219f
novelty: not-assessed
status: reviewed
---

# DistributedLamportClocks

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedLamportClocks.lean)

## Verified result

The original localTick, receiveMsg and numeric HappensBeforeStep model are preserved. The aliases tick and recvUpdate compute c+1 and max(c_local,c_msg)+1. Strict increase over both inputs and send_recv_causality for the send timestamp tick(c_send) are proved.

Event contains id, pid and clock. HappensBefore is the transitive closure of two supplied relations R_proc and R_msg. Assuming that every elementary edge strictly increases clock, happens_before_clock_condition extends that property to every causal chain. Irreflexivity and asymmetry follow. These are conditional theorems: a protocol implementation must separately connect its local and network transitions to the clock rules.

lamportTotalOrder compares (clock,pid) keys lexicographically. Irreflexivity, transitivity and extension of HappensBefore under the same monotonicity assumptions are proved. lamport_total_order_trichotomy establishes comparability provided equality of clock and pid implies equality of events. lamport_key_collision_example demonstrates the need for this restriction: events (id=0,pid=0,clock=0) and (id=1,pid=0,clock=0) are distinct and incomparable. A linear order on an event domain requires unique (clock,pid) keys in that domain; the Event record alone does not enforce this.

## Assumptions and limitations

The old HappensBeforeStep contains only numeric timestamps and is equivalent to strict numeric inequality. The new HappensBefore retains supplied event edges and is a different relation. empty_edges_no_happens_before proves absence of causal chains for empty relations, including between events with increasing clocks. The converse from scalar clock order to causality is false in general. Vector clocks and their causality criterion are not formalized here.

R_proc does not enforce equal PIDs by definition; R_msg does not model send/receive matching. There is no executable network model, derivation of timestamp uniqueness from process histories, bounded-counter overflow, physical clock synchronization through NTP/PTP/TrueTime, dynamic membership or Byzantine timestamp forgery. Counters are unbounded natural numbers. Scientific novelty has not been assessed.

Existing definitions, theorem signatures and the type of MasterSuite.lamport_clocks are preserved. DistributedLamportClocksFormalSuite gains h_extended : DistributedLamportFormalSuite, which manual constructors must supply. The event-level suite is available as distributed_lamport_events_master_suite and through h_extended of the original master theorem.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `DistributedLamportClocks.distributed_lamport_clocks_master_suite`.
