---
id: DistributedPaxosConsensus
language: en
section: distributed
source: Verification/DistributedPaxosConsensus.lean
source_sha256: 6add20b06145d0ed3456a7716b356c6d52787b7fa2698901d44bb2d080238ea2
novelty: not-assessed
status: reviewed
---

# DistributedPaxosConsensus

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedPaxosConsensus.lean)

## Verified result

For N = 2*f+1 and q1,q2 ≥ f+1, natural-number arithmetic gives 1 ≤ q1+q2-N. An acceptor whose promise exceeds b does not satisfy the eligibility predicate promisedBallot ≤ b. A successful prepare with a strictly larger ballot raises the promise and preserves the type-level inequality acceptedBallot ≤ promisedBallot. Proposal records are equal if their ballots are equal and an explicit premise supplies equality of their values at that ballot.

## Assumptions and limitations

The quorum lemma concerns sizes only: no node universe, quorum sets, subset bounds or intersection witness is present. The size parameters are not even bounded above by N. Translating the inequality to actual quorum intersection requires those missing set assumptions. The parameter f does not encode an execution with failures.

canAccept is only ballot eligibility, not an acceptance action. prepareResponse has a strict precondition and retains the accepted fields; repeated/lower prepare requests, replies and network transitions are not modeled. The same-ballot value-equality implication is assumed, not proved from a leader algorithm or quorum overlap. No connection between the quorum lemma and proposal uniqueness, cross-ballot agreement, chosen-value invariant, or complete Single-Decree Paxos safety/liveness proof is supplied. Separate ballot-order theorems are not introduced beyond the stated prepare growth.

Multi-Paxos, replicated logs, leader/epoch changes, phase-two proposal selection, asynchronous message delivery, crash recovery and Byzantine behavior are outside the model.

## Value and novelty

Small arithmetic and local state components with explicit prerequisites for future execution-level proofs. Scientific priority and first formalization have not been assessed.

## Verification

[Validation record](../VERIFICATION.en.md). Entry point: `DistributedPaxosConsensus.distributed_paxos_master_verification_suite`.
