---
id: DistributedTendermintHeaderChainEpochAuthContract
language: en
section: distributed
source: Verification/DistributedTendermintHeaderChainEpochAuthContract.lean
source_sha256: 524a8df0d07a39253f8695fbe2a4ccee536b2dfc502f017ae7eb5b85703a12d4
novelty: not-assessed
status: reviewed
---

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedTendermintHeaderChainEpochAuthContract.lean)

# Header-chain authentication of historical epoch configurations

Module ε202, distributed / distributed/tendermint-accountability, builds a historical
registry from a finite sequential header chain. Its formal companion contract is
[header-chain-epoch-auth-contract](../../docs/header-chain-epoch-auth-contract.en.md).
ε201 remains the separate HCTK scalar model.

## What the checker establishes

Headers bind chain ID, height, epoch ID, current and next configuration commitments
and parent-header commitment. Each non-root accepted header must pass the current
configuration's strict >2/3 weighted commit and exact-header signer checks. The
parent's nextValidatorsHash binds the child's current config. Adjacent heights,
chain identity, permitted epoch progression and parent links are checked.

The trusted root is an explicit input. The abstract signer interface represents
accepted signatures; it does not implement or prove public-key cryptography.
Weights and global IDs come from committed configs, not from an independently
chosen certificate-local map. The history uses the actual module196 API and contains
only heights represented by verified headers. Invalid chains yield no trusted history.

Within a checked chain a covered height resolves unambiguously. Across two checked
chains the conclusion concerns heights covered in both; a longer verified prefix
can contain a height absent from a shorter one. Common-root trust, commitment binding
and consistent committed headers are explicit premises. Quorum counts alone cannot
exclude a fork when signers equivocate.

## Relation to the existing master pipeline

The derived history is installed in the module200 context. A covered old configuration
supplies the resolution premise of AcceptedEvidence rather than asking a caller for
an arbitrary HistoryRegistry. The evidence itself still passes the actual checker;
positive collection retains admission, freshness, liability and held-funds premises.
Conservation and duplicate-certificate protection use the real historical application
and settlement operations. Existing safety still requires overlap, adopted locks and
honest vote rules. Header authentication does not establish ConflictCovered for
arbitrary cross-epoch conflicts or authenticate a complete offence reference.

## Boundaries

Commitments are abstract. Injectivity/binding is a hypothesis, not SHA-256 collision
resistance proved in Lean. The model may commit the entire EpochConfig, including
its height-range and byzantine annotations. Such a commitment is stronger than the
production encoding of a validator set and does not prove an annotation is true.

Trusted root acquisition, signature verification, key compromise over time,
trusting-period expiry, skipping verification, network delivery, time synchronization,
liveness and correspondence to a production implementation remain external.
The structural historical-registry premise is replaced by checked-chain conditions,
not by an unconditional cryptographic authenticity theorem. Novelty: not assessed.
Allowed axioms: propext, Classical.choice, Quot.sound.

Primary context: [CometBFT sequential verification](https://github.com/cometbft/cometbft/blob/main/spec/light-client/verification/README.md).
The adjacent-header binding and current-set quorum are modeled; the full light-client
protocol, notably its time-dependent trust, is not claimed.

Public release v0.7.9 exports private snapshot
831248e509744e9a7900fa0cc7f01a88ee957b2f. Lake remains 0.7.1. Public-tree verification
is recorded separately from private checks. The full public beta basis remains
2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1); private full control remains
090aed141b831aee5182197e9ea205176f361c0f. See [release notes](../../docs/release-v0.7.9.en.md).
