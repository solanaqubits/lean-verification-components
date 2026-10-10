# Release v0.5.32: Linear-optical Bell-state analyzer

Private proof snapshot: `59aa296435696dbe388d0e19a110f81c13e8b578`.
Previous public main: `d285f4b8fbfe3a7fe8c42b17d2e6145c4bdf9ace`.

## Proven scope and assumptions

The fixed four-mode passive network uses two imported balanced splitters B(1/2),
one for each polarization, and ideal PBS routing. Polynomial substitution derives
the normalized symmetric lift on all ten two-photon occupations. Both the
one-photon and two-photon scattering matrices are unitary.

The four Bell outputs are computed from this network. Psi-minus gives
opposite-polarization detections in different spatial ports; Psi-plus gives
opposite-polarization detections within one spatial port, separated by the PBS.
Each is unambiguously identified with probability one. Phi-plus and Phi-minus
have identical distributions over all ten Fock outcomes, with probability 1/4
on each of four double-occupation outcomes. Their pure output vectors remain distinct.

Detector POVM effects are derived by compressing the output projectors through
the optical transfer. Their exact Bell-projector forms, completeness,
Hermiticity, positivity and Born identity for arbitrary coherent inputs are proved.
Success equals p(Psi-minus)+p(Psi-plus); it is 1/2 for the uniform four-state
ensemble and 1 for a Psi-only ensemble. Equal Phi distributions remain equal
under classical postprocessing; binary guessing for equal Phi priors succeeds
exactly half the time. No postselection discards detector outcomes.

The assumptions are ideal lossless passive optics, matching temporal/spectral
wave packets, ideal PBS routing and Born detection with photon-number resolution.
This is a concrete finite normalized two-boson model, not an electromagnetic
or detector-hardware derivation. The universal Calsamiglia-Luetkenhaus bound
for arbitrary optical networks, ancilla-assisted or adaptive schemes,
chi(2)/chi(3) nonlinearities, spectral distinguishability, photon loss and dark
counts are outside scope. Python correctness, JSON/SHA-256 correctness and
SimLab correspondence remain open obligations.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 134 |
| Lean files under Verification/ | 174 top-level + 2 auxiliary = 176 |
| Root-inclusive sources identical to the private snapshot | 177 |
| Clean strict build | 3625 jobs; no warnings |
| Complete verifier audit | 16721 declarations; no violations |
| Pinned independent full audit | 16721 declarations; no violations |
| Public live tests | 79; no failures or skips; 277.483s |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

All 177 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.32. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/03_quantum_physics_and_optics/PhotonicsBellStateAnalyzer.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
