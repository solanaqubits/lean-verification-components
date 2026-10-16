# Release v0.5.87: qutrit two-of-three secret sharing

Gamma release: 189 direct MasterSuite imports and 232 root-inclusive Lean sources,
byte-identical to private snapshot 330ea2350bae059cac7b546fb9d8748ccf4ae0ef.
Previous public main: e24f559654d9edf3ded8949637cce8475512eb2c (v0.5.86).
Last full public validation: b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).

## Mathematical scope

[Module contract](../knowledge/03_quantum_information/QuantumQutritTwoOfThreeSecretSharingContract.md).
The explicit 27-by-3 code satisfies

    J|s> = (1/sqrt(3)) sum_{r in Fin 3} |r,r+s,r+2*s>,    J†J=I_3.

Labels use modulo-three arithmetic. The physical factors are ordered ABC.
For loss of A, B or C, proved bijective regroupings give BC×A, CA×B and AB×C.
They act on both matrix indices, with a proved bridge to grouped encoding.
For every complex logical X, every single-share marginal equals Tr(X) I_3/3.
The fixed marginal is a density matrix; arbitrary complex off-diagonal units
are erased, so the privacy claim is not limited to basis states.

Module 188 supplies exact CPTP recovery from each pair using the proved
isometry and privacy. Recovery is not an input assumption. Classical.choice
selects a finite Kraus family for each lost position, complete on the whole
nine-dimensional input space. The same recovery acts for every finite reference
dimension through module 187. The reference and any singleton share factorize,
and recovery preserves the maximally entangled logical/reference qutrit state.
The reference/environment map includes encoding; arbitrary uncoded physical
inputs are not claimed private. Recovery from a single share is impossible
for every finite Kraus family, because its channel kills E_01.

## Clean Water

This is the concrete exact finite-dimensional Cleve–Gottesman–Lo (2,3) qutrit
scheme with a known erased position. General threshold families, protection
against active share substitution, approximate correction, distribution protocols,
executable gate decompositions/numerical decoders and physical implementation
remain outside scope. Recovery selection is classical, not an executable
numerical algorithm. Open Python, JSON/SHA-256 and SimLab obligations remain.
Novelty is not assessed.

## Measured public validation

All required checks passed in this public tree with version 0.5.87 already set.

| Check | Measured result |
| --- | --- |
| `lake build --wfail` | 3870 incremental targets, 6 freshly compiled modules, no warnings; 28.705s |
| Module `verify` | 3283 declarations in 32-source imported closure; 42.719s |
| MasterSuite `verify` | 26533 declarations in 226-source imported closure; 37.254s |
| Strict registry AxiomAudit | Passed; 2.486s |
| Module/registry unittest | 2 passed; 4.297s including startup |
| Existing registry unittest | 4 passed; 3.029s including startup |

All six selected tests ran with LEAN_VERIFIER_LIVE_TESTS=1, without errors or
skips. The selected unittest wrappers compile 41 new Lean examples (37 model
checks and 4 registry checks); these are counted separately, not as independent
runs. There are no new helper regression theorems. They cover the modulo-three encoding and all cyclic regroupings,
singleton privacy including complex coherences, recovery from all three pairs,
CPTP properties, reference preservation, maximal entanglement and the
impossibility of recovery from any single share.
These are exact symbolic Lean proofs; no executable complex arithmetic or
floating-point simulation count is asserted. Knowledge/catalog checks passed.

Both verifier reports have ok=true, source_unchanged=true, no policy findings
and no axiom violations. Only propext, Classical.choice and Quot.sound occur.
Declaration counts describe overlapping imported closures, not a new whole-project
measurement. Lake targets include cached work, not only freshly compiled proofs.
Full verify-all, the complete unittest suite and the independent full auditor
were not run for this gamma release.

[Machine-readable evidence](../tools/validation_v0.5.87.json) binds commands and
outcomes to source/configuration/test hashes. The last full public baseline
remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
