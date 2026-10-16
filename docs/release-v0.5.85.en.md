# Release v0.5.85: reference-preserving entanglement recovery

Gamma release: 187 direct MasterSuite imports and 230 root-inclusive Lean sources,
byte-identical to private snapshot 42bc9680b7be87d4b81664b50b8a2b21f46903b2.
Previous public main: bbb8b76d88315e55e5b6e8c226d04d27efae2bae (v0.5.84).
Last full public validation: b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).

## Mathematical scope

[Module contract](../knowledge/03_quantum_information/QuantumReferencePreservingRecoveryContract.md).
From ExactRecovery E J R on all complex logical matrices, the module proves
(id_m tensor R)(id_m tensor Phi_E)(id_m tensor J)(X)=X for every finite reference
dimension m and every joint complex matrix X. The same fixed R is used for all m.
The existing amplify_kraus API relates the block maps to tensor Kraus operators.
Product indices are reference first; finProdFinEquiv gives an explicit flat-index
wrapper on Fin (m*k). The algebraic result also covers m=0.

For k>0 and isometric J, exact recovery yields a density sigma satisfying
(id_m tensor (Phi_E^c composed with J))(X)=Tr_logical(X) tensor sigma.
Encoding is included in this map; constancy is not asserted for arbitrary
uncoded physical inputs. For density inputs this is a product of the reference
marginal and the environment state, with no reference/environment correlations.

The normalized maximally entangled test matrix is proved positive semidefinite
and of trace one. Fixing it under amplified recovery is equivalent to fixing
all logical matrices. The reverse direction extracts matrix-unit blocks and
cancels the nonzero normalization factor 1/k, without assuming exact recovery.

Regressions cover Bell states, complex joint coherences, arbitrary alternative
recovery families, reference dimensions 0,1,2,3 and arbitrary m, zero/repeated
spectra and rectangular physical channels. Dephasing preserves basis projectors
but changes Bell coherence from 1/2 to zero. No finite recovery Kraus family
repairs full-qubit dephasing; smaller correctable subcodes are not excluded.

## Clean Water

These are exact finite-dimensional consequences of existing recovery criteria.
No new independent mathematical criterion or scientific priority is claimed.
Approximate/asymptotic bounds, diamond norm, numerical decoders and physical
implementation remain outside scope. General dilation minimality/uniqueness,
quantum capacity, remaining Bulletproofs protocol extraction/security,
Tendermint reference acquisition/slashing, Python, JSON/SHA-256 and SimLab
remain separate obligations. Novelty is not assessed.

## Measured public validation

All required checks passed in this public tree with version 0.5.85 already set.

| Check | Measured result |
| --- | --- |
| `lake build --wfail` | 3868 incremental targets, 6 freshly compiled modules, no warnings; 13.105s |
| Module `verify` | 3150 declarations in 30-source imported closure; 27.787s |
| MasterSuite `verify` | 26399 declarations in 224-source imported closure; 37.789s |
| Strict registry AxiomAudit | Passed; 2.491s |
| Module/registry unittest | 2 passed; 4.525s including startup |
| Existing registry unittest | 4 passed; 2.987s including startup |

All six selected tests ran with LEAN_VERIFIER_LIVE_TESTS=1, without errors or
skips. The selected unittest wrappers compile 35 new Lean examples (31 model
checks and 4 registry checks); these are counted separately, not as independent
runs. There are no new helper regression theorems. They cover arbitrary reference
sizes and recovery families, flat indices, tensor amplification, environment
factorization, the normalized entangled-state criterion, Bell coherences,
degenerate spectra, rectangular channels and dephasing impossibility.
These are exact symbolic Lean proofs; no executable complex arithmetic or
floating-point simulation count is asserted. Knowledge/catalog checks passed.

Both verifier reports have ok=true, source_unchanged=true, no policy findings
and no axiom violations. Only propext, Classical.choice and Quot.sound occur.
Declaration counts describe overlapping imported closures, not a new whole-project
measurement. Lake targets include cached work, not only freshly compiled proofs.
Full verify-all, the complete unittest suite and the independent full auditor
were not run for this gamma release.

[Machine-readable evidence](../tools/validation_v0.5.85.json) binds commands and
outcomes to source/configuration/test hashes. The last full public baseline
remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
