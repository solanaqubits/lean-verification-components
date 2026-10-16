# Release v0.5.88: explicit unitary decoder for qutrit secret sharing

Gamma release: 190 direct MasterSuite imports and 233 root-inclusive Lean sources,
byte-identical to private snapshot 98c20f1755dc36138a2e7394e4473864328c5059.
Previous public main: 066c91704b4bad5e6b0bf440a6d204d930197b27 (v0.5.87).
Last full public validation: b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).

## Mathematical scope

[Module contract](../knowledge/03_quantum_information/QuantumQutritSecretSharingExplicitDecoder.md).
The pair decoder is the explicit permutation

    D|u,v> = |v-u,2v-u>,    inverse (s,t) -> (t-2s,t-s).

All labels use Fin 3 arithmetic. Both D†D=I_9 and DD†=I_9 are proved.
The cyclic regroupings of module 189 order retained and lost factors as BC×A,
CA×B and AB×C. In each ordering, (D tensor I_3)J_q has columns
|s> tensor |Omega_3>, and for every complex logical matrix X the decoded full
matrix is X tensor |Omega_3><Omega_3|, with explicit associative indexing.

The three operators R_t=(I_3 tensor <t|)D define explicitRecovery, a
KrausChannel 9 3 3. Their completeness sum_t R_t†R_t=I_9 gives a CPTP map on
the whole pair space. Each branch obeys R_t E_w J_q=delta_tw amplitude I_3.
Summing branches gives exact recovery for all complex X and every lost position.
The same decoder preserves every finite reference system, including the
maximally entangled logical/reference qutrit input. Its action agrees with
module 189's pairRecovery on encoded pair inputs; equality of the channels on
arbitrary pair inputs is not asserted.

## Clean Water

This is an explicit finite algebraic construction for the exact (2,3) qutrit
scheme. Recovery operators are not selected from an existence proof through
Classical.choose. Classical.choice may remain in proof dependencies; no smaller
axiom set is claimed. Executable numerical simulators, hardware realizations,
robustness to noise, protection against active share substitution and general
threshold families remain outside scope. Open Python, JSON/SHA-256 and SimLab
obligations remain. Novelty is not assessed.

## Measured public validation

All required checks passed in this public tree with version 0.5.88 already set.

| Check | Measured result |
| --- | --- |
| `lake build --wfail` | 3871 incremental targets, 6 freshly compiled modules, no warnings; 76.855s |
| Module `verify` | 3345 declarations in 33-source imported closure; 91.399s |
| MasterSuite `verify` | 26596 declarations in 227-source imported closure; 35.966s |
| Strict registry AxiomAudit | Passed; 2.509s |
| Module/registry unittest | 2 passed; 4.442s including startup |
| Existing registry unittest | 4 passed; 3.052s including startup |

All six selected tests ran with LEAN_VERIFIER_LIVE_TESTS=1, without errors or
skips. The selected unittest wrappers compile 39 new Lean examples (35 model
checks and 4 registry checks); these are counted separately, not as independent
runs. There are no new helper regression theorems. They cover the explicit basis permutation and both unitary identities,
full-state factorization, completeness and CPTP properties, recovery for every
lost position, complex coherences, arbitrary reference preservation, maximally
entangled qutrit inputs and agreement with the previous recovery on encoded
pair inputs.
These are exact symbolic Lean proofs; no executable complex arithmetic or
floating-point simulation count is asserted. Knowledge/catalog checks passed.

Both verifier reports have ok=true, source_unchanged=true, no policy findings
and no axiom violations. Only propext, Classical.choice and Quot.sound occur.
Declaration counts describe overlapping imported closures, not a new whole-project
measurement. Lake targets include cached work, not only freshly compiled proofs.
Full verify-all, the complete unittest suite and the independent full auditor
were not run for this gamma release.

[Machine-readable evidence](../tools/validation_v0.5.88.json) binds commands and
outcomes to source/configuration/test hashes. The last full public baseline
remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
