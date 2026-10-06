---
id: DistributedChandyMisraHaasDeadlock
language: en
section: distributed
source: Verification/DistributedChandyMisraHaasDeadlock.lean
source_sha256: b321a71b941abf249fa356819482d5f351a5ab03f3a5f9df7a33c0a5bf8985df
novelty: not-assessed
status: reviewed
---

# DistributedChandyMisraHaasDeadlock

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedChandyMisraHaasDeadlock.lean)

## Model and contract

This module is a static-epoch, AND wait-graph edge-chasing specialization inspired by Chandy–Misra–Haas. Processes are `Fin n`; proofs also cover the vacuous n=0 case and self-loops for n=1. A process is blocked exactly when it has an outgoing wait edge. The resource-manager semantics behind those edges are assumed, not implemented.

A probe carries initiator, sender and receiver. Initiation and forwarding append all outgoing probes to an explicit queue. Delivery consumes a real queue occurrence; active receivers absorb probes. Local fanout is atomic, network delivery is not. Delivery order is arbitrary. A sent-message history is proof bookkeeping, not an additional wire payload. There is no duplicate suppression, no message-complexity bound and no claim to implement all details of the original dynamic CMH algorithm.

The wait graph is fixed throughout an execution. `EpochReachable.reset` describes an external fresh-epoch contract: replacing the graph clears queued probes and reports. It is not an implementation of distributed reset or stale-packet fencing. Arbitrary graph changes preserving in-flight probes are excluded from the soundness result.

## Proved statements

- `probe_transmission_validity`: every sent probe in a reachable state follows an edge of the fixed graph.
- `probe_path_reconstruction`: every queued or sent probe has a wait path from its initiator to its sender and a final edge to its receiver.
- `cycle_detection_soundness`: every reachable report for i has a nonempty closed wait walk through i. `WaitCycle` means a nonempty closed walk; a separate simple-cycle extraction theorem is not claimed.
- `phantom_deadlock_absence`: in an acyclic fixed graph every reachable report set is empty. These are inductive transition invariants, not guards that assume safety.
- `cycle_detection_path_exists`: a cycle through i permits a finite valid continuation that initiates detection and reports i.
- `cycle_eventually_detected`: after an actual initiation on a cycle, every valid run satisfying `DeliveryFair` eventually reports its initiator. `DeliveryFair` requires each queued probe payload eventually to have a matching delivery event at a later or equal index. It is payload-level service, not FIFO or distinct-instance fairness. It does not assume the desired report. No numerical time bound is proved.
- `reset_epoch_soundness`: the same safety holds within each externally reset isolated epoch.

Only initiators on cycles are covered by the detection theorem. A process that merely reaches a cycle need not receive its own probe. No theorem equates every blocked process with cycle membership.

## Counterexamples and limits

`dynamic_send_checks_insufficient` exhibits a valid trace of the deliberately weakened dynamic protocol: every instantaneous graph is acyclic, every send uses a current edge, yet retained probes return to the initiator and produce a false report. This refutes the proposed send-time-only criterion, not the original CMH algorithm with its additional request/reply and controller conditions. `unfair_execution_counterexample` retains an initiated probe forever in an idle run, showing why message storage alone gives no guaranteed detection.

OR waiting, changing process membership, deadlock resolution, packet loss, crashes, resource grants and physical timers are not modeled. Python, JSON/SHA-256, SimLab input-to-byte binding and runtime implementations remain external obligations. Scientific novelty is not assessed.

Reference: K. M. Chandy, J. Misra and L. M. Haas, [Distributed Deadlock Detection (1983), Section 3](https://www.cs.utexas.edu/~misra/scannedPdf.dir/DistrDeadlockDetection.pdf).
