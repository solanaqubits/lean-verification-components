# Release v0.5.80: Knill-Laflamme environment independence criterion

Gamma release: 182 direct MasterSuite imports and 225 root-inclusive Lean sources,
byte-identical to private snapshot 56f231609ee635fe929b760c9e60e56f6be6f2eb.
Previous public main: f8af88298fbd07306590e23bdd1d5246020c01ab (v0.5.79).
Last full public validation: b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).

## Mathematical scope

[Module contract](../knowledge/03_quantum_information/QuantumKnillLaflammeEnvironmentCriterion.md).
For a supplied Kraus channel and encoding matrix J, the scalar identities
J† K_j† K_i J = sigma_ij I are equivalent to
Phi_c(J X J†) = Tr(X) sigma for EVERY complex logical matrix X.
The reverse direction explicitly tests off-diagonal matrix units as well as
diagonal ones. The algebraic equivalence requires neither isometry nor positive
logical dimension; these hypotheses are imposed for the physical conclusion.
When J†J=I and k>0, sigma is positive semidefinite, Hermitian and has trace one.

The standard coefficient convention J† K_i† K_j J = lambda_ij I gives
sigma_ij=lambda_ji, an ordinary transpose. Examples include any unitary channel,
a two-dimensional code with two nonzero orthogonal error spaces and unequal
weights, and full-space qubit dephasing that violates the criterion for every
sigma. Complex off-diagonal coefficients distinguish transpose from adjoint.

## Clean Water

The conclusion concerns the selected complementary output of the supplied
finite channel. It does not assert unrestricted protocol secrecy or absence
of all physical side channels. Recovery CPTP construction, the full recovery
equivalence, approximate correction, fault-tolerance thresholds, physical noise
models and deployment correspondence remain outside scope. General dilation
minimality/uniqueness, quantum capacity, remaining Bulletproofs protocol
extraction/security, Tendermint reference acquisition/slashing, Python,
JSON/SHA-256 and SimLab remain separate obligations. Novelty is not assessed.

## Measured public validation

All required checks passed in this public tree with version 0.5.80 already set.

| Check | Measured result |
| --- | --- |
| `lake build --wfail` | 3863 incremental targets, no warnings; 17.133s |
| Module `verify` | 2742 declarations in 25-source imported closure; 31.321s |
| MasterSuite `verify` | 25986 declarations in 219-source imported closure; 36.794s |
| Strict registry AxiomAudit | Passed; 2.517s |
| Module/registry unittest | 2 passed; 4.584s including startup |
| Existing registry unittest | 4 passed; 2.984s including startup |

All six selected tests ran with LEAN_VERIFIER_LIVE_TESTS=1, without errors or
skips. New regression files contain 34 kernel-checked examples (30 model checks
and 4 registry checks), plus four helper theorems for the complex coefficient
regressions. They cover trace pairing on non-Hermitian matrix units, the ordinary
transpose convention, environment positivity/normalization, orthogonal nonzero
errors, unitary channels, dephasing counterexamples, zero logical dimension
and failure of state validity without isometric encoding.
These are exact symbolic Lean proofs; no executable complex arithmetic or
floating-point simulation count is asserted. Knowledge/catalog checks passed.

Both verifier reports have ok=true, source_unchanged=true, no policy findings
and no axiom violations. Only propext, Classical.choice and Quot.sound occur.
Declaration counts describe overlapping imported closures, not a new whole-project
measurement. Lake targets include cached work, not only freshly compiled proofs.
Full verify-all, the complete unittest suite and the independent full auditor
were not run for this gamma release.

[Machine-readable evidence](../tools/validation_v0.5.80.json) binds commands and
outcomes to source/configuration/test hashes. The last full public baseline
remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
