# Release v0.5.79: complementary quantum channel and environment state

Gamma release: 181 direct MasterSuite imports and 224 root-inclusive Lean sources,
byte-identical to private snapshot 6efc674f70eb0181cd1c5667f919bcf0826cdd21.
Previous public main: 9d95f47fb7970af648f3c6b31977e627283dcca7 (v0.5.78).
Last full public validation: b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).

## Mathematical scope

[Module contract](../knowledge/03_quantum_information/QuantumComplementaryChannelContract.md).
The supplied finite Kraus family gives the Stinespring dilation V, ordered as
output system × environment. The complement is Tr_system(V X V†); its entry
(i,j) is Tr(K_i X K_j†) for ALL complex X. Swapping the output and Kraus indices
constructs its Kraus family, proves completeness and imports CPTP guarantees
from module 175. Both marginals come from the same joint matrix; this matrix
need not be a state for arbitrary X and need not be pure for a density input.

For a supplied rectangular W with W†W=I, V'=(I tensor W)V gives an unchanged main
channel and Phi_c'(X)=W Phi_c(X) W†. The covariance formula alone also holds for
arbitrary W. Unitary, reset, dephasing and redundant-environment cases are proved.
The |+>, |-> dephasing example has identical BOTH marginals but distinct joint
matrices, locating their distinction in correlations.

## Clean Water

The complement is attached to the selected Kraus representation. No theorem
asserts that the environment marginal alone receives every distinction absent
from the system. General uniqueness/minimality of dilations, unitary extension,
infinite dimensions, quantum capacity, general recovery maps, numerical
certification and physical realization remain outside scope. Remaining
Bulletproofs protocol extraction/security beyond supplied openings, Tendermint
reference acquisition/slashing, Python correspondence, JSON/SHA-256 and SimLab
obligations remain separate. Mathematical novelty is not assessed.

## Measured public validation

All required checks passed in this public tree with version 0.5.79 already set.

| Check | Measured result |
| --- | --- |
| `lake build --wfail` | 3862 incremental targets, no warnings; 13.162s |
| Module `verify` | 2676 declarations in 24-source imported closure; 26.911s |
| MasterSuite `verify` | 25919 declarations in 218-source imported closure; 37.988s |
| Strict registry AxiomAudit | Passed; 2.511s |
| Module/registry unittest | 2 passed; 5.333s including startup |
| Existing registry unittest | 4 passed; 2.997s including startup |

All six selected tests ran with LEAN_VERIFIER_LIVE_TESTS=1, without errors or
skips. New regression files contain 31 kernel-checked examples (27 model checks
and 4 registry checks), plus a helper theorem for a complex 3-by-2 isometry.
They cover complex conjugation order on non-Hermitian inputs, isometric covariance,
density preservation, unitary/reset/dephasing outputs, distinct joint states with
equal marginals, zero padding and failure of invariance without isometry.
These are exact symbolic Lean proofs; no executable complex arithmetic or
floating-point simulation count is asserted. Knowledge/catalog checks passed.

Both verifier reports have ok=true, source_unchanged=true, no policy findings
and no axiom violations. Only propext, Classical.choice and Quot.sound occur.
Declaration counts describe overlapping imported closures, not a new whole-project
measurement. Lake targets include cached work, not only freshly compiled proofs.
Full verify-all, the complete unittest suite and the independent full auditor
were not run for this gamma release.

[Machine-readable evidence](../tools/validation_v0.5.79.json) binds commands and
outcomes to source/configuration/test hashes. The last full public baseline
remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
