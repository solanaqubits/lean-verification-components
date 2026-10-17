# v0.7.2 — Pedersen commitment opening extraction

This public synchronization adds epsilon module 193,
`CryptoPedersenCommitmentOpeningExtractionContract`, its registry integration,
tests, declarative batch data and English documentation. All 237 root-inclusive
Lean sources are byte-identical to private snapshot
`f2d792cb7b4ebbe6f4e1cb973e8a7e4d4b51cbbe`; MasterSuite has 193 direct imports.

## Version and verification identity

- Hierarchy: alpha 0, historical beta generation 7, gamma `cryptography`,
  delta `cryptography/pedersen-opening-extraction`, epsilon 193.
- Git publication serial: v0.7.2. The patch number is not a coverage claim.
- Lake package version: 0.7.1, unchanged. VERSIONING.md permits serial tags and
  does not require a package-configuration edit for each scoped publication.
  Consumers requiring these changes must select tag v0.7.2 or its commit.
- Actual verification scope is assigned by the unchanged public planner.
  Only module/integration sources, tests, declarative data and documentation
  change. No trust mechanism or toolchain is modified to avoid escalation.
- Last full public control remains v0.7.1 at
  `2419489245019fb16e32ffac641b9f88eea94126`. This release is not a new beta basis.
- Private full control remains `090aed141b831aee5182197e9ea205176f361c0f`;
  the private module snapshot has its own scoped evidence.
- Historical v0.7.0 and v0.7.1 tags remain immutable. Epsilon 194 is unallocated.

## Mathematical scope

A linear representation protocol over a field admits explicit extraction from
two accepting transcripts for the same statement and announcement with distinct
challenges. Scalar and vector Pedersen instances recover a valid opening by
response differences divided by challenge difference. A checked interface rejects
mismatched statements/announcements, equal challenges and invalid responses.
Honest responses with a common mask recover the original witness. General
accepting forks need not identify a unique or historically original opening.

Distinct colliding scalar openings yield a discrete-log relation through the
existing algebraic theorem; computational binding and hiding are separate claims.
Three additional opening forks construct module 178's certificate for Ac, Sc, V.
Composition preserves its assumptions and its range-witness OR generator-relation
conclusion. The extra forks are explicit inputs, not extracted from the original
Bulletproofs TranscriptFamily. Original-protocol extraction, a probabilistic
Forking Lemma, PPT/expected-time bounds, random-oracle/Fiat-Shamir security and
implementation equivalence remain outside this result. Python, JSON/SHA-256 and
SimLab obligations remain open.

## Acceptance and publication

The unchanged scope planner selects the batch, affected consumers and registry.
The standard scoped runner retains Lake cache, performs strict builds, one
transitive verify of its maximal audit root, selected live tests, metadata and
knowledge validation, and diff checking. The verify command includes strict
AxiomAudit compilation; no duplicate audit of identical inputs is required.
Only propext, Classical.choice and Quot.sound are allowed.

New regression fixtures contain 53 Lean examples, three helper theorems and
13 executable scenarios. These include independent numeric scalar/vector forks,
zero and repeated challenges, mutations, nonunique openings, registry projections
and a concrete conditional range extraction returning witness 3.

Actual commands, measured counts and the accepted evidence digest are recorded
externally and in the annotated tag after successful checks. Private checks do
not substitute for this public-tree run. Hashes bind bytes, not authorship; the
publisher pins accepted evidence separately and compares committed bytes before
pushing main and then the tag. No private Git history, Russian cards, simulations,
chats-export or untracked working materials are exported.

See [versioning](../VERSIONING.md), [scope policy](verification-scope-policy.en.md)
and the [module contract](../knowledge/04_cryptography/CryptoPedersenCommitmentOpeningExtractionContract.md).
