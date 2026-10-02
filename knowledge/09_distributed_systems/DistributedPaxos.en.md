---
id: DistributedPaxos
language: en
section: distributed
source: Verification/DistributedPaxos.lean
source_sha256: fae29cb982da1331b2e2a40987bd2ff7d555209d20e45185bd7ff201967d8f8a
novelty: not-assessed
status: reviewed
---

# DistributedPaxos

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedPaxos.lean)

## Verified result

The module proves conditional same-ballot agreement of chosen values. Ballot contains round and proposerId; ballotLt compares the full key lexicographically. Irreflexivity, transitivity and trichotomy are proved. paxos_ballot_monotonicity establishes only the arithmetic fact that strictly increasing rounds cannot be equal. It is not a Promise transition invariant.

PaxosCluster specifies N > 0, nodes have type Fin N, and quorums are finite node sets. IsMajority requires N < 2 * Q.card. majority_quorums_intersect supplies an actual common node of two majorities for any positive N, including even cluster sizes. The one-node boundary case is also checked.

Accepted is a supplied acceptance-history predicate. SingleVote requires that a node never accepts different values at the same ballot. IsChosen accepted c means that a majority of nodes have each accepted c.val at c.ballot. Given SingleVote and two chosen records with equal ballots, paxos_consensus_safety proves their values equal: the shared quorum member accepted both values, so single voting identifies them.

ChosenValue is a candidate record, not evidence of choice on its own. same_ballot_counterexample proves that equal ballot fields in records with values 0 and 1 do not imply equal values.

## Assumptions and limitations

SingleVote is an explicit premise, not an axiom or a proved protocol transition invariant. Preservation of this condition by an implementation is not established. The acceptance history has no time, network or reachability semantics. Unique allocation of ballot keys is not modeled either.

The theorem concerns one ballot only. Full Single-Decree Paxos safety requires agreement across different ballots and is not proved here. Prepare/Promise/Accept/Accepted transitions, phase-one selection of a previously accepted value, message delivery, node/leader crashes and recovery, liveness, dynamic membership, Byzantine behavior and Multi-Paxos are not formalized. Actual majority-quorum intersection is formalized, but not connected to protocol execution.

The existing DistributedPaxosConsensus component and paxos registry field are preserved. The new component is registered separately as paxos_consensus. Scientific novelty has not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `DistributedPaxos.distributed_paxos_master_suite`.
