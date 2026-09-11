---
id: BFTConsensusQuorum
language: en
section: distributed
source: Verification/BFTConsensusQuorum.lean
source_sha256: 4a4212d4662e7eb3a09025249e92ccb0397ad04d948174ea64a5272950e9def3
novelty: not-assessed
---

# BFTConsensusQuorum

[Section](README.md) · [Lean source](../../Verification/BFTConsensusQuorum.lean)

## Verified result

The intersection bound 2Q−N; honest intersection when N+f < 2Q; quorum availability when Q+f ≤ N, including classical exact thresholds.

## Assumptions and scope

Quorum intersection alone does not establish Leader Completeness. No full message-passing, failure, or distributed RPC model is proved correct.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`min_intersection_ge_f_add_one`](../../Verification/BFTConsensusQuorum.lean#L21)
- [`honest_intersection_card_ge_one`](../../Verification/BFTConsensusQuorum.lean#L27)
- [`quorum_intersection_card`](../../Verification/BFTConsensusQuorum.lean#L36)
- [`bft_consensus_master_verification_suite`](../../Verification/BFTConsensusQuorum.lean#L98)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
