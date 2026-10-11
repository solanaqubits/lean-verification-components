# Release v0.5.33: Linear-optical quantum teleportation

Private proof snapshot: `bc6ec6054e308654f2f2b010c66474b12719cc43`.
Previous public main: `27be20e1c3de0d6ac1f9046ae0ad425f3ffcc59b`.

## Proven scope and assumptions

The module derives an optical quantum instrument on the twenty-dimensional
invariant sector (ten Alice Fock outcomes times two Bob modes). Its ten Kraus
operators come from the existing Bell analyzer and resource embedding; their
completeness is proved. The successful branches are E_minus(rho) = XZ rho (XZ)†/4
and E_plus(rho) = X rho X†/4. Each has probability 1/4 for every density operator,
including mixed inputs; total success is 1/2. Unitary corrections ZX and X give
the successful channel rho/2, so normalization recovers rho with squared Uhlmann
fidelity one. Without Alice's classical record the uncorrected channel is I₂/2.
The physical partial trace and the abstract teleportation protocol are linked.

Regressions include |0>, |1>, |+>, |+i>, the maximally mixed input and trace
preservation. Incorrect correction Z leaves residual -X: |+> is preserved, but
|0> and |+i> have squared fidelity zero. Of the six inconclusive detector outcomes,
four have double occupation and two are dark on the embedded input sector.

The result concerns this conditional passive linear-optical scheme, with a supplied
ideal Phi-plus resource, matching photon wave packets, ideal detector projection
and classical feed-forward. Resource generation, deterministic teleportation,
universal optical discrimination bounds, spectral distinguishability, losses,
dark counts and detector noise are not modeled. Python, JSON/SHA-256 and SimLab
correctness obligations remain open.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 135 |
| Lean files under Verification/ | 175 top-level + 2 auxiliary = 177 |
| Root-inclusive sources identical to the private snapshot | 178 |
| Clean strict build | 3725 jobs; no warnings |
| Complete verifier audit | 16901 declarations; no violations |
| Pinned independent full audit | 16901 declarations; no violations |
| Public live tests | 80; no failures or skips; 276.334s |

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

All 178 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.33. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/03_quantum_physics_and_optics/PhotonicsQuantumTeleportation.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
