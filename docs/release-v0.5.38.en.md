# Release v0.5.38: Finite POVMs and Naimark dilation

Private proof snapshot: `5cfecd3773d40cc2ceca22686e0976416b3df834`.
Previous public main: `49f9d6d0e41e7647ee529d912be99014e7b6ac32`.

## Proven scope and assumptions

For any finite POVM of positive semidefinite complex matrices whose sum is I,
Mathlib CFC.sqrt supplies positive Hermitian roots F_m. The explicit block
isometry V and orthogonal projectors Pi_m satisfy V†V=I and V†Pi_m V=E_m.
Born traces agree for arbitrary complex input matrices. Density matrices lift
to density matrices, and outcome probabilities are real, nonnegative and normalized.

For a nonempty ancilla, a unitary extension U with UJ=V exists for the fixed
pure ancilla |0>. Partial trace of each projected branch gives the unnormalized
Lueders update F_m rho F_m. The singleton Kraus families {I} and {X} demonstrate
that identical POVM effects need not induce identical state updates. Bridges
instantiate the Bell analyzer's three effects and the depolarizing channel's
Kraus effects; the latter matches branch probabilities, not the full state update.

These are noncomputable mathematical constructions, not executable square-root
algorithms or quantum circuit synthesis. Born's rule supplies the physical model.
The theorem concerns finite-dimensional systems and finite outcome sets.
Infinite-dimensional spaces, spectral measures, minimality, gate synthesis and
hardware implementation are outside scope. Python, JSON/SHA-256 and SimLab
obligations remain open. Scientific novelty is not assessed.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 140 |
| Lean files under Verification/ | 180 top-level + 2 auxiliary = 182 |
| Root-inclusive sources identical to the private snapshot | 183 |
| Clean strict build | 3730 jobs; no warnings |
| Complete verifier audit | 18067 declarations; no violations |
| Pinned independent full audit | 18067 declarations; no violations |
| Public live tests | 85; no failures or skips; 279.862s |

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

All 183 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.38. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/03_quantum_physics_and_optics/QuantumPOVMNaimarkDilation.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
