---
id: DistributedTendermintAccountableSafety
language: en
section: distributed
source: Verification/DistributedTendermintAccountableSafety.lean
source_sha256: ff25790bc249304f648308b5a7364ac6cb0060792dd90357f8ad7756e45eb526
novelty: not-assessed
status: reviewed
---

# Tendermint accountability with an explicit evidence contract

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedTendermintAccountableSafety.lean)

## Model and inputs

This module extends the fixed-height, static natural-weight model of module 165.
Config supplies the height and weights, including zero weights; total is their
sum. The attribution algorithm does not read Config.byzantine:
attribution_independent_of_fault_oracle proves this by definitional equality.
That field occurs only in the specification of honest participants.

SignedMessage is an alleged message envelope, not an implementation of a digital
signature. EvidenceView contains finite message and justification sets. An
optional reference transcript must be authenticated and complete externally.
ValidView checks the envelope height, membership in that reference and every
provided JustificationEvidence certificate: its signers must have the matching
prevotes in the observed set and strictly more than two thirds of total weight.
EvidenceSufficiency additionally requires every reference prevote to be observed.
This is a conservative sufficient coverage condition, not a minimal evidence
protocol. Reference precommits may be omitted. Providing a purported reference
does not establish its external authenticity or completeness.

## Verified statements

Equivocation is two messages from one sender at the same round and phase with
different values, including nil versus a block. InvalidPrecommit is a non-nil
precommit without a polka for its block in the SAME round, as required by module
165. LockViolation uses an earlier non-nil precommit and a later prevote for a
different block, with no polka for the new block at a round t satisfying
old_round <= t < new_round. Certificates and polkas are checked against actual
messages; the absence of an object from the certificate list alone is not blame.

culprits computes a Finset of validators from these predicates. accusations
constructs concrete message records for all three violation types;
mem_accusations_iff proves their validity, and culprits_eq_accusation_senders
identifies the deduplicated offender set exactly. Repeated messages or several
accusations of one validator cannot increase that validator's counted weight.

history_outside_culprits derives all History laws of module 165 for participants
outside the computed set. Combining this with history_safety proves
accountable_safety_attribution: two conflicting commits in the observed messages,
in equal or different rounds, imply total < 3 * mass(culprits). No pre-existing
fault list or one-third fault-budget assumption is used to compute the result.
A single local violation does NOT imply this weight bound.

honest_never_accused requires a sufficient view and the reference History laws.
reachable_honest_never_accused and attribution_honest derive those laws from an
actual Reachable execution of the core state machine. Thus they connect the
checker to protocol-following participants rather than defining honesty as
absence of an accusation.

attribute_evidence returns Except AttributionError (Finset (Fin n)). Missing
reference or missing reference prevotes yields insufficientEvidence. An invalid
height, reference membership or supplied certificate yields invalidEvidence.
attribute_success_iff characterizes acceptance exactly by EvidenceSufficiency
and the computed offender set. checked_accountable_safety connects that checked
result to the strict weight bound. All searches are finite and executable;
completeView and canonicalJustification construct convenient evidence inputs.

## Regressions

Kernel-checked examples and 24 executable scenarios cover actual run/Reachable
traces, same- and cross-round conflicts, legal lock switching with an intervening
polka, forged certificates, wrong heights, unknown messages, nil votes, stale
polkas, unequal and zero weights, strict quorum boundaries and deduplication.
A partial view containing only honest precommits would incorrectly accuse three
participants under the raw predicates; the checked wrapper rejects that view.
A single lock violator below one third provides the counterexample to treating
an isolated violation as accountable-safety threshold evidence.

## Clean Water

The result is conditional attribution in the state-machine model of module 165,
with externally authenticated complete reference data and checked relative
coverage. It does not implement obtaining that reference, authenticated absence
proofs, network evidence deadlines, slashing, concrete Ed25519/secp256k1 signature
verification, dynamic validator sets, or equivalence to deployed Tendermint or
CometBFT. It is not an unconditional accountability theorem for partial logs.
The remaining full Bulletproofs protocol extraction, rewinding and Fiat–Shamir/ROM
security obligations are unchanged, as are Python equivalence, JSON/SHA-256 and
SimLab obligations. Mathematical novelty is not assessed.

## Public gamma validation provenance

Public gamma release v0.5.77 exports private snapshot
13f4caf469645fd7f0dcdcb831f922d19d32c1c7. The previous public scoped release is
77c55bac6fe60df55393c84721e114f5459772d2 (v0.5.76). The last fully validated PUBLIC
baseline remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
Public-tree checks are recorded in [the release report](../../docs/release-v0.5.77.en.md).
Private evidence is not substituted for public validation; no new full-project
verify-all or full unittest result is claimed. The permitted axioms remain
propext, Classical.choice and Quot.sound.
