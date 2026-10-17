---
id: AxiomAudit
language: en
section: verification
source: Verification/AxiomAudit.lean
source_sha256: c8d3c8fabef8a8a2164451f3fd361ee079b0e217df486a595db4626b15e644bb
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
