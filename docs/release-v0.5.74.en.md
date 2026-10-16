# Release v0.5.74 — fixed-witness range interpolation

This Z release exports private snapshot
`f5bac6750f7d5c9b741041ac86d213d9ca1474c0`. Its last fully validated public baseline
is `b3410720b9af49c2fb70d15d65d3d012091cbf0b` (v0.5.73).

## Change and mathematical scope

CryptoBulletproofsRangeInterpolation proves a deterministic implication for fixed
vectors a,b and field value v. For n≥1 and injective grids of n Y nodes and three
Z nodes, all range-reduction equalities imply formal_t0 a b = formal_rhs v n.
The residual has degree at most n-1 in Y and two in Z; cubic Z terms cancel.
Existing module 159 then yields bit constraints and the represented field value.
For a natural v<q with 2^n<q, the natural value is exactly reconstructed and v<2^n.
Zero nodes and symmetric but distinct Z nodes are allowed.

A checked wrapper rejects empty vectors, repeated Y/Z nodes and invalid grid
equalities. Regressions include honest n=1,2,4 examples, a two-Z-point residual
Z^2-Z, repeated Y=1 with residual Z*(1-Y), corrupted values/right vectors, reordered
grids and the noncanonical natural representative 106 of field value 5 mod 101.

## Integration and provenance

176 direct MasterSuite imports; 219 root-inclusive project Lean sources, all
byte-identical to the pinned private snapshot. Existing subject APIs are unchanged.
The registry extends CryptoFullSuite in MasterSuiteComponents with range_grid;
central/root imports, AxiomAudit, integration recipe, English knowledge catalog
and regressions are updated. Russian cards and private validation reports are not
exported. X/Y/Z instructions retain public English conventions.

The package version is 0.5.74 before checking. No verifier implementation,
toolchain, Mathlib dependency or GitHub workflow logic changes are included.
Public evidence is generated in this public tree, not copied from private tests.

## Clean Water

This is not full extraction from transcripts. Openings of A,S, interpolation in X,
cross-branch witness consistency and integration with the IPA tree remain separate
obligations. No global generator independence, computational binding reduction,
rewinding complexity, HVZK or Fiat–Shamir/ROM result is asserted. Tendermint
accountable safety, Python correspondence, JSON/SHA-256 and SimLab obligations
remain open in their documented scopes.

## Validation

All required checks completed in this public tree with version 0.5.74 already set.

| Check | Public measured result |
| --- | --- |
| `lake build --wfail` | 3857 incremental targets; no warnings; 11.988s |
| Module `verify` | 1869 declarations in its imported axiom closure; 22.072s |
| MasterSuite `verify` | 25233 declarations in its imported axiom closure; 37.265s |
| AxiomAudit strict compilation | Passed; 2.48s |
| New module/projection unittest | 2; 4.56s including Python startup |
| Existing registry unittest | 4; 2.956s including Python startup |
| Knowledge catalog unittest | 2; 0.056s including Python startup |

All eight selected unittest tests passed without errors or skips, under
LEAN_VERIFIER_LIVE_TESTS=1. The new regression files contain 39 exact Lean
examples and 12 executable scenarios. The catalog checker and skill validator
also pass. The allowed axiom set is strictly propext, Classical.choice, Quot.sound;
no violations were found. No duplicate `audit` followed `verify`.

The two declaration counts are overlapping imported contexts, not additive and
not a freshly measured complete-project declaration total. Cached build targets
are not counts of freshly recompiled proofs. Full verify-all, the entire unittest
suite and the independent full auditor were not run for this Z release.
[Machine-readable scoped evidence](../tools/validation_v0.5.74.json) records commands,
source/configuration/test hashes and the last full baseline. The existing
validation_snapshot.json remains historical evidence of that earlier baseline.

## Automatic CI scope

The existing workflow still runs full verification on push/pull_request. This
release commit uses GitHub's `skip-checks: true` trailer to avoid that redundant
full run under the approved Z policy. The workflow itself remains unchanged;
required scoped checks run locally in the public tree. A skipped workflow is not
a passing GitHub Actions result. Full checks remain available for X/Y checkpoints.
See [GitHub's documented skip mechanism](https://docs.github.com/en/actions/how-tos/manage-workflow-runs/skip-workflow-runs).
