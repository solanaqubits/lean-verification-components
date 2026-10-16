# Release v0.5.77 — Tendermint accountability with explicit evidence

This gamma release exports private snapshot
`13f4caf469645fd7f0dcdcb831f922d19d32c1c7`. The previous public scoped release is
`77c55bac6fe60df55393c84721e114f5459772d2` (v0.5.76). The last fully validated
public baseline remains `b3410720b9af49c2fb70d15d65d3d012091cbf0b` (v0.5.73).
A scoped release does not advance that full-validation baseline.

## Mathematical scope

DistributedTendermintAccountableSafety extends module 165's fixed-height,
static-weight safety model. It enumerates explicit message witnesses for
same-phase same-round equivocation (including nil versus a block), non-nil
precommit without a SAME-round polka, and an unjustified switch to a different
block after an earlier precommit. A legitimate polka in the interval
old_round <= t < new_round justifies the switch. The offender Finset deduplicates
participants; repeated evidence does not multiply stake weight. Attribution does
not read Config.byzantine or require a pre-existing culprit list.

The proof first establishes the core History laws outside the computed offender
set. Core safety then implies total < 3 * mass(offenders) for two conflicting
commits, in equal or different rounds. A single local violation does not imply
this threshold. The no-framing theorems honest_never_accused,
reachable_honest_never_accused and attribution_honest connect sufficient observed
evidence to the actual History and Reachable state-machine contracts of module 165.

EvidenceSufficiency is conservative: observed messages must belong to an
externally authenticated complete reference transcript, with correct heights;
all reference prevotes must be present; all supplied justification certificates
must be backed by matching observed prevotes and a strict weighted quorum.
Reference precommits may be omitted. Completeness of the reference itself is an
external premise, not inferred from a caller-provided Boolean or partial log.
The wrapper returns insufficientEvidence without a reference or sufficient
prevote coverage, and invalidEvidence for wrong heights, foreign messages or
invalid supplied certificates. An absent certificate object alone is not blame:
polkas are checked against actual votes.

## Integration and provenance

All 222 root-inclusive Lean sources match the private snapshot byte-for-byte.
MasterSuite has 179 direct imports. DistributedSystemsFullSuite gains
`tendermint_accountability` in MasterSuiteComponents. Root and registry imports,
AxiomAudit, the integration recipe, targeted tests and English knowledge cards
are synchronized. Russian cards are not exported. Version 0.5.77 is set before
validation. Toolchain, dependency pins, verifier and CI implementation are unchanged.

## Clean Water

This is conditional evidence attribution in the core model, not unconditional
accountability from a partial network journal. Obtaining and authenticating a
complete reference, authenticated absence proofs, physical slashing, concrete
Ed25519/secp256k1 verification, evidence-delivery deadlines, dynamic validator
sets and equivalence to deployed Tendermint/CometBFT remain external obligations.
The remaining full Bulletproofs protocol extraction, rewinding and Fiat–Shamir/ROM
security obligations are unchanged. Python equivalence, JSON/SHA-256 and SimLab
also remain separate. No claim of mathematical novelty is made.

## Automatic CI scope

The existing push workflow runs full checks. After successful public-tree scoped
validation, this release uses the explicitly authorized `skip-checks: true`
commit trailer. A skipped workflow is not reported as a passing CI result.
Full gates remain for alpha/beta checkpoints; valid Lake caches are retained.
No duplicate standalone audit follows verify on unchanged inputs.

## Measured public validation

All required checks passed in this public tree with version 0.5.77 already set.

| Check | Measured result |
| --- | --- |
| `lake build --wfail` | 3860 incremental targets, no warnings; 11.967s |
| Module `verify` | 753 declarations in 3-source imported closure; 8.759s |
| MasterSuite `verify` | 25747 declarations in 216-source imported closure; 37.819s |
| Strict registry AxiomAudit | Passed; 2.544s |
| Module/registry unittest | 2 passed; 19.666s including startup |
| Existing registry unittest | 4 passed; 3.009s including startup |

All six selected tests ran with LEAN_VERIFIER_LIVE_TESTS=1, without errors or
skips. New regression files contain 39 examples and 6 named theorems (45 Lean
propositions), plus 24 executable scenarios checked for exact successful outcomes.
These cover reachable traces, same- and cross-round conflict, legal unlocks,
partial logs, false certificates, unequal and zero weights, strict quorum
boundaries, omission of precommits, concrete evidence records and deduplication.
Knowledge/catalog checks passed.

Both verifier reports have ok=true, source_unchanged=true, no policy findings
and no axiom violations. Only propext, Classical.choice and Quot.sound occur.
Declaration counts describe overlapping imported closures, not a new whole-project
measurement. Lake targets include cached work, not only freshly compiled proofs.
Full verify-all, the complete unittest suite and the independent full auditor
were not run for this gamma release.

[Machine-readable evidence](../tools/validation_v0.5.77.json) binds commands and
outcomes to source/configuration/test hashes. The last full public baseline
remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
