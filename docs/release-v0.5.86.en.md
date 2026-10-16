# Release v0.5.86: subsystem erasure correctability

Gamma release: 188 direct MasterSuite imports and 231 root-inclusive Lean sources,
byte-identical to private snapshot edc9fadd245c6da61c333448cb5211daac76a9ae.
Previous public main: 6a73333e0d1a4af1a14f02461e9370808fd13043 (v0.5.85).
Last full public validation: b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).

## Mathematical scope

[Module contract](../knowledge/03_quantum_information/QuantumErasureCorrectabilityContract.md).
The physical split is A tensor B, with A first in finProdFinEquiv. The module
constructs Kraus operators I_A tensor <j|_B and proves their completeness.
For every complex physical matrix Y, the channel is Tr_B(Y), retaining A,
and its complementary channel is exactly Tr_A(Y), retaining lost B.
No transpose or conjugation of the complementary output is inserted.

For k>0 and an isometry J into A tensor B, existence of an exact CPTP recovery
R(Tr_B(J X J†))=X for all complex logical matrices is equivalent to existence
of a density sigma_B with Tr_A(J X J†)=Tr(X) sigma_B. The finite number of
recovery Kraus operators is independently quantified. Both directions reuse
module 186 through proved channel/partial-trace bridges.

Module 187 supplies recovery with the same R for every finite reference and
reference/B factorization after encoding. The reference/environment map includes
J; no independence is claimed for arbitrary uncoded physical inputs.

Examples prove correction for |psi> tensor |v>, and for a logical qubit with
fixed auxiliary pair (3/5)|00>+(4/5)|11>. In the latter, A contains the logical
and retained auxiliary qubits, B the other auxiliary qubit. Recovery explicitly
traces out the auxiliary part of A. Lost B has density diag(9/25,16/25), proved
non-idempotent. The repetition code |0> -> |00>, |1> -> |11> becomes logical
dephasing after erasure; no exact finite-Kraus recovery exists on the full code.
Complex complementary entries test the index convention, and regressions cover
CPTP properties, Bell/reference recovery and environment factorization.

## Clean Water

This concerns exact finite-dimensional correction of a fixed, known erased factor.
Unknown error locations, probabilistic erasure with a flag, approximate correction,
general threshold secret-sharing schemes, numerical decoders and physical
implementation remain outside scope. The secret-sharing connection is motivation,
not a proved threshold construction. General dilation minimality/uniqueness,
quantum capacity, remaining Bulletproofs protocol extraction/security,
Tendermint reference acquisition/slashing, Python, JSON/SHA-256 and SimLab
remain separate obligations. Novelty is not assessed.

## Measured public validation

All required checks passed in this public tree with version 0.5.86 already set.

| Check | Measured result |
| --- | --- |
| `lake build --wfail` | 3869 incremental targets, 6 freshly compiled modules, no warnings; 14.225s |
| Module `verify` | 3220 declarations in 31-source imported closure; 28.699s |
| MasterSuite `verify` | 26469 declarations in 225-source imported closure; 37.728s |
| Strict registry AxiomAudit | Passed; 2.501s |
| Module/registry unittest | 2 passed; 4.448s including startup |
| Existing registry unittest | 4 passed; 3.03s including startup |

All six selected tests ran with LEAN_VERIFIER_LIVE_TESTS=1, without errors or
skips. The selected unittest wrappers compile 38 new Lean examples (34 model
checks and 4 registry checks); these are counted separately, not as independent
runs. There are no new helper regression theorems. They cover partial-trace
channel/complement bridges, complex complementary entries, CPTP properties,
fixed-factor and entangled-auxiliary recovery, mixed lost states, reference
preservation, environment factorization and repetition-code impossibility.
These are exact symbolic Lean proofs; no executable complex arithmetic or
floating-point simulation count is asserted. Knowledge/catalog checks passed.

Both verifier reports have ok=true, source_unchanged=true, no policy findings
and no axiom violations. Only propext, Classical.choice and Quot.sound occur.
Declaration counts describe overlapping imported closures, not a new whole-project
measurement. Lake targets include cached work, not only freshly compiled proofs.
Full verify-all, the complete unittest suite and the independent full auditor
were not run for this gamma release.

[Machine-readable evidence](../tools/validation_v0.5.86.json) binds commands and
outcomes to source/configuration/test hashes. The last full public baseline
remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
