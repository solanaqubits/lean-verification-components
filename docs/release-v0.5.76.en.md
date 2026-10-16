# Release v0.5.76 — conditional Bulletproofs range extraction

This gamma release (formerly level Z) exports private snapshot
`26ae7e5b13c3e646cb7bcfc42109fbc70f421903`. The previous public scoped release is
`39553b505bd256279c36c38900d8dd0d19b48d9b` (v0.5.75). The last fully validated
public baseline remains `b3410720b9af49c2fb70d15d65d3d012091cbf0b` (v0.5.73).
The previous scoped release is not relabeled as a full-validation baseline.

## Mathematical scope

CryptoBulletproofsRangeWitnessExtraction proves conditional composition given
certified openings of A,S,V. These inputs contain no bit, range or cross-branch
agreement assumption. The common commitments are fixed across the family; T1,T2
are fixed for each Y,Z pair before its three X responses. Accepting IPA trees are
checked against roots computed using range_target and the actual responses.

The implementation calls extractTree from module 170. Relations are lifted from
the scaled basis to the original G,H,B,Hblind,U with nontriviality preserved.
Otherwise, differences between extracted vectors and l_poly/r_poly provide a
zero group combination including the blinding and U coefficients. Nonzero
coefficients yield a concrete relation; zero coefficients prove agreement.
Three-point X interpolation eliminates T1,T2, leaving a relation on B,Hblind or
the residual grid equalities. Module 176 then gives bits, b=a-1, the represented
value and its exact natural reconstruction.

For n=2^k, the checked wrapper requires k>=1 and 2^n<q. The canonical value v.val
is less than 2^n on the successful witness branch, which includes the opening of
the ORIGINAL V. The alternative is an explicit nonzero coefficient tuple whose
group evaluation is zero. Invalid openings and substituted roots are rejected.
Y nodes are distinct and nonzero; Z and each X grid have three distinct nodes.
Internal IPA challenges separately require nonzero values with distinct squares.

## Integration and provenance

All 221 root-inclusive Lean sources match the private snapshot byte-for-byte.
MasterSuite has 178 direct imports; CryptoFullSuite gains range_extraction in
MasterSuiteComponents. Root/registry imports, AxiomAudit, integration recipe,
targeted tests and English knowledge documentation are synchronized.
Russian cards are not exported. Package version 0.5.76 is set before validation.
Toolchain, dependency pins, verifier implementation and CI workflow are unchanged.
The updated English policy names ranks alpha/beta/gamma, with delta iterations
in named parallel streams. Lower ranks do not weaken validation requirements;
counter allocation and merge automation are not implemented by this documentation.

## Clean Water

The theorem is conditional on supplied openings of A,S,V. Obtaining those
openings from the prover remains open even before byte parsing. No full protocol
knowledge extractor, rewinding/forking or expected-time bound, computational
binding reduction, HVZK, Fiat–Shamir/ROM security or deployed-byte correspondence
is established here. The remaining Bulletproofs protocol obligations remain open.
Tendermint accountable safety, Python equivalence, JSON/SHA-256 and SimLab remain
separate obligations. No global independence of cyclic-group generators is assumed.

## Automatic CI scope

The existing workflow runs full checks on push/pull_request. This release uses
the explicitly authorized `skip-checks: true` commit trailer after local scoped
public-tree validation. Workflow logic is unchanged. A skipped workflow is not a
passing GitHub Actions result. Full gates remain for alpha/beta checkpoints;
valid caches are retained, and no duplicate audit follows verify.

## Measured public validation

All required checks passed in this public tree with version 0.5.76 already set.

| Check | Measured result |
| --- | --- |
| `lake build --wfail` | 3859 incremental targets, no warnings; 13.223s |
| Module `verify` | 2587 declarations in 16-source imported closure; 23.144s |
| MasterSuite `verify` | 25500 declarations in 215-source imported closure; 38.042s |
| Strict registry AxiomAudit | Passed; 2.513s |
| Module/registry unittest | 2 passed; 5.842s including startup |
| Existing registry unittest | 4 passed; 2.955s including startup |

All six selected tests ran with LEAN_VERIFIER_LIVE_TESTS=1, without errors or
skips. New regression files contain 28 examples and 6 named theorems (34 Lean
propositions), plus 17 executable scenarios with exact output assertions.
They cover honest witnesses and masks, explicit polynomial and IPA witness
relations, malformed openings/roots/challenges and a relation from a depth-two tree.
Knowledge/catalog and skill-format checks passed.

Both verifier reports have ok=true, source_unchanged=true, no policy findings
and no axiom violations. Only propext, Classical.choice and Quot.sound occur.
The two declaration counts describe overlapping imported closures, not a new
whole-project declaration count. Lake targets include cached work; they are not
a count of freshly compiled proofs. Full verify-all, the complete unittest suite
and the pinned independent full auditor were not run for this gamma release.

[Machine-readable evidence](../tools/validation_v0.5.76.json) binds commands and
outcomes to source/configuration/test hashes. Earlier full and scoped evidence
remains historical. The last full public baseline remains v0.5.73.
