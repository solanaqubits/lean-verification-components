# Release v0.5.84: Knill-Laflamme recovery necessity and equivalence

Gamma release: 186 direct MasterSuite imports and 229 root-inclusive Lean sources,
byte-identical to private snapshot 23becc8e3952239aa0142d72c97c530d3442c4b2.
Previous public main: 0b41b074d540b0d23a18823235e713d00bac7b04 (v0.5.83).
Last full public validation: b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).

## Mathematical scope

[Module contract](../knowledge/03_quantum_information/QuantumKnillLaflammeRecoveryNecessity.md).
For a Kraus channel E, a nonzero-dimensional isometric encoding J and any exact
CPTP recovery R, the module proves R_mu E_a J=c_mu,a I using matrix units and
nonnegative sums of squared complex norms. Completeness of R then yields
J† E_a† E_b J=(sum_mu conjugate(c_mu,a) c_mu,b) I, with the stated conjugation order.

Combined with modules 182 and 185, this establishes equivalence between existence
of exact CPTP recovery, general Knill-Laflamme conditions and a constant environment
on the code. Recovery existence quantifies independently over its finite Kraus
count. Environment constancy means Phi^c(J X J†)=trace(X) sigma for every complex
logical matrix X, with sigma a density matrix. Different physical input/output
dimensions, zero and repeated eigenvalues are covered.

Regressions include complex non-diagonal coefficients, arbitrary alternative
recovery families, complex coherences, degenerate spectra and rectangular channels.
Full-qubit dephasing admits no exact recovery for any finite Kraus count; this does
not assert that every smaller code is uncorrectable.

## Clean Water

The result is exact finite-dimensional correction for the given Kraus channels and
encoding. Approximate or asymptotic correction, executable numerical decoders,
fault tolerance and physical implementation are outside scope. General dilation
minimality and uniqueness, quantum capacity, remaining Bulletproofs protocol
extraction/security, Tendermint reference acquisition/slashing, Python,
JSON/SHA-256 and SimLab remain separate obligations. Novelty is not assessed.

## Measured public validation

All required checks passed in this public tree with version 0.5.84 already set.

| Check | Measured result |
| --- | --- |
| `lake build --wfail` | 3867 incremental targets, 6 freshly compiled modules, no warnings; 12.901s |
| Module `verify` | 3098 declarations in 29-source imported closure; 27.323s |
| MasterSuite `verify` | 26346 declarations in 223-source imported closure; 36.902s |
| Strict registry AxiomAudit | Passed; 2.464s |
| Module/registry unittest | 2 passed; 4.433s including startup |
| Existing registry unittest | 4 passed; 3.029s including startup |

All six selected tests ran with LEAN_VERIFIER_LIVE_TESTS=1, without errors or
skips. The selected unittest wrappers compile 34 new Lean examples (30 model
checks and 4 registry checks); these are counted separately, not as independent
runs. There are no new helper regression theorems. They cover scalar composite
operators, Gram coefficient reconstruction and uniqueness, general recovery
and environment equivalence, complex coherences, degenerate spectra,
rectangular channels, dephasing impossibility and registry integration.
These are exact symbolic Lean proofs; no executable complex arithmetic or
floating-point simulation count is asserted. Knowledge/catalog checks passed.

Both verifier reports have ok=true, source_unchanged=true, no policy findings
and no axiom violations. Only propext, Classical.choice and Quot.sound occur.
Declaration counts describe overlapping imported closures, not a new whole-project
measurement. Lake targets include cached work, not only freshly compiled proofs.
Full verify-all, the complete unittest suite and the independent full auditor
were not run for this gamma release.

[Machine-readable evidence](../tools/validation_v0.5.84.json) binds commands and
outcomes to source/configuration/test hashes. The last full public baseline
remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
