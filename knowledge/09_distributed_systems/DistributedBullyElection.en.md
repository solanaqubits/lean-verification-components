---
id: DistributedBullyElection
language: en
section: distributed
source: Verification/DistributedBullyElection.lean
source_sha256: 99b879843fd9dce0ee268e08e5fa90718b62f66c3940c7dae6ef62a631607d56
novelty: not-assessed
status: reviewed
---

# DistributedBullyElection

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedBullyElection.lean)

## Verified result

For a two-node snapshot with n1.id < n2.id, the selection function returns n2 when its activity flag is true, otherwise n1 when its flag is true, and otherwise none. Any returned identifier belongs to a node with a true flag and is at least the identifier of every active node among these two. Two successful outputs of the same function on the same snapshot have equal identifiers.

## Assumptions and limitations

The strict identifier ordering is a field of System2. Activity flags are supplied inputs, not observations produced by a failure detector. The fallback theorem evaluates a snapshot where the higher-ranked node is already marked inactive; it does not prove a transition, eventual failover, recovery or termination. Uniqueness is determinism for one shared snapshot, not agreement between processes with different local views. Maximality is the stated non-strict inequality and is restricted to n1 and n2.

No initiator, ELECTION/ANSWER/COORDINATOR messages, asynchronous delivery, heartbeat timeouts, partitions, stale observations, execution traces or dynamic clusters with more than two nodes are modeled. This module verifies a static priority selector, not full Bully protocol safety or liveness.

## Value and novelty

A checked specification of two-node priority selection and its explicit preconditions. Scientific novelty and first-formalization claims have not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `DistributedBullyElection.distributed_bully_master_verification_suite`.
