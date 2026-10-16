# Release v0.5.81: explicit CPTP recovery for orthogonal error spaces

Gamma release: 183 direct MasterSuite imports and 226 root-inclusive Lean sources,
byte-identical to private snapshot d5d6dad4440eb91e6241fe485e025cd0c097adef.
Previous public main: 5ea996c66817194475a41f513009a604c9b7da41 (v0.5.80).
Last full public validation: b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).

## Mathematical scope

[Module contract](../knowledge/03_quantum_information/QuantumOrthogonalErrorRecoveryContract.md).
For a supplied Kraus channel, isometric encoding J with k>0, nonnegative weights
summing to one, and diagonal equations J† K_i† K_j J=delta_ij p_i I_k,
construct U_i=K_i J/sqrt(p_i) for positive weights and zero otherwise.
A zero-weight error is proved zero on the code, even when it is nonzero physically.
The positive-weight normalized errors have orthogonal isometric images. Their projection P
and its complement Q=I_e-P are proved Hermitian and idempotent.

The operators U_i† and |0><a|Q form a complete Kraus family on ALL e-dimensional
physical output matrices, mapping to the k-dimensional logical space. Completeness
is I_e even when the noise input dimension d differs from e. The resulting CPTP
map R satisfies R(Phi(J X J†))=X for every complex logical X. No decoder or recovery
equation is assumed as input. Examples use module 182's weights 9/25 and 16/25,
zero-weight physical errors, complex coherence, a nonzero unused output sector
and a rectangular C^2 -> C^4 channel. Reset completion is essential in the sector
example: syndrome operators alone fail completeness.

## Clean Water

Recovery is proved for DIAGONAL Knill-Laflamme data. General coefficient
diagonalization and the full recovery equivalence remain open. These symbolic
noncomputable real/complex matrices do not certify an executable floating-point
decoder. Approximate correction, fault-tolerance thresholds, physical noise
models and deployment correspondence are outside scope. General dilation
minimality/uniqueness, quantum capacity, remaining Bulletproofs protocol
extraction/security, Tendermint reference acquisition/slashing, Python,
JSON/SHA-256 and SimLab remain separate obligations. Novelty is not assessed.

## Measured public validation

All required checks passed in this public tree with version 0.5.81 already set.

| Check | Measured result |
| --- | --- |
| `lake build --wfail` | 3864 incremental targets, no warnings; 17.917s |
| Module `verify` | 2865 declarations in 26-source imported closure; 31.48s |
| MasterSuite `verify` | 26110 declarations in 220-source imported closure; 37.312s |
| Strict registry AxiomAudit | Passed; 2.487s |
| Module/registry unittest | 2 passed; 5.338s including startup |
| Existing registry unittest | 4 passed; 2.982s including startup |

All six selected tests ran with LEAN_VERIFIER_LIVE_TESTS=1, without errors or
skips. New regression files contain 33 kernel-checked examples (29 model checks
and 4 registry checks), plus two helper regression theorems. They cover unequal
weights, complex off-diagonal coherence, exact state recovery and zero recovery
trace distance, zero-weight errors that are nonzero physically, nonzero unused
space, full trace preservation, and rectangular physical channels. An explicit
sector formula checks reset behavior outside the code; the syndrome-only Kraus
family is proved incomplete there.
These are exact symbolic Lean proofs; no executable complex arithmetic or
floating-point simulation count is asserted. Knowledge/catalog checks passed.

Both verifier reports have ok=true, source_unchanged=true, no policy findings
and no axiom violations. Only propext, Classical.choice and Quot.sound occur.
Declaration counts describe overlapping imported closures, not a new whole-project
measurement. Lake targets include cached work, not only freshly compiled proofs.
Full verify-all, the complete unittest suite and the independent full auditor
were not run for this gamma release.

[Machine-readable evidence](../tools/validation_v0.5.81.json) binds commands and
outcomes to source/configuration/test hashes. The last full public baseline
remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
