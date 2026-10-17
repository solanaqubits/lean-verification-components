---
id: AxiomAudit
language: en
section: verification
source: Verification/AxiomAudit.lean
source_sha256: 6e0e43ed103b51944b41e9299b6636a9cd8958cc3c14071ee81226171a82a3c6
novelty: not-assessed
status: reviewed
---

# AxiomAudit

[Section](README.md) · [Lean source](../../Verification/AxiomAudit.lean)

## Verified result

The #audit_axioms command rejects disallowed transitive axioms of a selected declaration, including sorryAx.

## Assumptions and scope

Axiom auditing checks dependencies of formal declarations, not whether the model faithfully represents its intended application. Allowed standard axioms are not custom assumptions.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

[Read the declarations](../../Verification/AxiomAudit.lean)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.

Module 191 adds `QuantumQutritDecoderCircuitRefinement.verification_suite` through
`QuantumPhysicsFullSuite.qutrit_circuit_refinement`; see the
[beta 0.7 release](../../docs/release-v0.7.0.en.md).

`DistributedSystemsFullSuite.tendermint_slashing` connects certified offender
attribution to exact rational slashing and conditional honest-share growth.
[Contract](../02_distributed_systems/DistributedTendermintSlashingPenaltyContract.md).

Module 193 adds `CryptoFullSuite.pedersen_opening`: two-branch opening extraction and conditional composition with module 178.

Module 194 adds `DistributedSystemsFullSuite.tendermint_replay`: sequential replay protection and conserved ledger accounting.

Module 195 adds `DistributedSystemsFullSuite.tendermint_unbonding`: finite queues, inclusive evidence windows, two-phase slots and conserved accounting.

Module 196 adds `DistributedSystemsFullSuite.tendermint_epoch_identity`: historical resolution, stable global identities and preserved cross-epoch liabilities.

Module 197 adds `DistributedSystemsFullSuite.epoch_quorum`: weighted honest quorum intersection across epochs, with strict and non-strict threshold conventions.

Module 198 adds `DistributedSystemsFullSuite.lock_handover`: checked adoption, conditional round-zero agreement and justified finite local lock replacements.
