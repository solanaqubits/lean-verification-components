# Release v0.5.82: recovery with certified unitary Kraus diagonalization

Gamma release: 184 direct MasterSuite imports and 227 root-inclusive Lean sources,
byte-identical to private snapshot d319bed6b9f14a54d67d650fa2a246c025cce9d2.
Previous public main: 7cdf431a79a99c19792f10bf293fdc9f1895335e (v0.5.81).
Last full public validation: b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).

## Mathematical scope

[Module contract](../knowledge/03_quantum_information/QuantumUnitaryKrausDiagonalizationRecoveryContract.md).
Inputs are a Kraus channel E, isometric encoding J with k>0, general complex
Knill-Laflamme coefficients Lambda, and a unitary diagonalization certificate
U† Lambda U = diag(p). Nonnegativity of p and sum(p)=1 are proved from the code
and channel conditions, not assumed.

The mixed errors K_i=sum_a U_ai E_a use the environment matrix W=U^T, with no
complex conjugation in this transpose. Its isometry and the physical-channel
identity Phi_K(X)=Phi_E(X) follow through module 181. The transformed code
satisfies the diagonal conditions, supplying module 183's explicit complete
CPTP recovery R, including zero weights and unused-space completion. The theorem
R(Phi_E(J X J†))=X holds for every complex logical matrix X, with density-matrix
recovery as a consequence.

Regressions include complex off-diagonal coefficients and a complex unitary,
an explicit failure of the wrong adjoint convention, complex logical coherences,
zero weights, and repeated eigenvalues. These are exact symbolic proofs.

## Clean Water

Recovery is conditional on the supplied unitary diagonalization certificate.
Existence of diagonalization without that certificate and an unconditional
recovery equivalence are not proved here. No executable numerical eigensolver,
floating-point decoder, approximate correction or fault-tolerance result is
claimed. General dilation minimality/uniqueness, quantum capacity, remaining
Bulletproofs protocol extraction/security, Tendermint reference acquisition and
slashing, Python, JSON/SHA-256 and SimLab remain separate obligations.
Novelty is not assessed.

## Measured public validation

All required checks passed in this public tree with version 0.5.82 already set.

| Check | Measured result |
| --- | --- |
| `lake build --wfail` | 3865 incremental targets, 6 freshly compiled modules, no warnings; 18.933s |
| Module `verify` | 2974 declarations in 27-source imported closure; 32.786s |
| MasterSuite `verify` | 26220 declarations in 221-source imported closure; 38.344s |
| Strict registry AxiomAudit | Passed; 2.477s |
| Module/registry unittest | 2 passed; 4.628s including startup |
| Existing registry unittest | 4 passed; 3.0s including startup |

All six selected tests ran with LEAN_VERIFIER_LIVE_TESTS=1, without errors or
skips. New regression files contain 39 kernel-checked examples (35 model checks
and 4 registry checks), plus one helper regression theorem. They cover complex
unitary mixing and coefficients, transpose versus adjoint, failure of the wrong
mixing convention, derived nonnegative normalized weights, exact recovery of
complex coherences, zero weights and repeated eigenvalues.
These are exact symbolic Lean proofs; no executable complex arithmetic or
floating-point simulation count is asserted. Knowledge/catalog checks passed.

Both verifier reports have ok=true, source_unchanged=true, no policy findings
and no axiom violations. Only propext, Classical.choice and Quot.sound occur.
Declaration counts describe overlapping imported closures, not a new whole-project
measurement. Lake targets include cached work, not only freshly compiled proofs.
Full verify-all, the complete unittest suite and the independent full auditor
were not run for this gamma release.

[Machine-readable evidence](../tools/validation_v0.5.82.json) binds commands and
outcomes to source/configuration/test hashes. The last full public baseline
remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
