---
id: DistributedPBFTConsensus
language: en
section: distributed
source: Verification/DistributedPBFTConsensus.lean
source_sha256: 900b7104b4a88397da6a312a3ed7eaae5aaa80d3bab0e82ca7d0cede22299693
novelty: not-assessed
status: reviewed
---

# DistributedPBFTConsensus

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedPBFTConsensus.lean)

## Verified result

PBFTSetup assumes N≥3f+1. The fixed quorum size 2f+1 is at most N. With the additional condition N=3f+1, the arithmetic overlap lower bound 2Q-N is at least f+1, and N<2Q. A checked counterexample at f=1,N=5 refutes the originally proposed overlap bound under the weaker assumption alone. The identity (f+1)-f≥1 is also proved. Equal view and sequence imply equal vote values conditionally on the supplied honest-uniqueness implication.

## Assumptions and limitations

The threshold is a setup assumption, not a proved protocol resilience or liveness bound. Quorums and faulty replicas are not represented as sets; the module proves arithmetic bounds, not an existential honest-node witness. The vote theorem assumes uniqueness and does not derive it from Prepare/Commit execution. No Committed predicate or connection between quorum arithmetic and vote equality is defined. For larger N, fixed 2f+1 quorums do not satisfy the claimed general bound; the two affected theorems and suite fields explicitly require N=3f+1.

View-change, checkpoints, state transfer, timers, message authentication, digital signatures, network transitions and full PBFT safety/liveness are not formalized. Scientific novelty and first-formalization claims have not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `DistributedPBFTConsensus.distributed_pbft_master_verification_suite`.
