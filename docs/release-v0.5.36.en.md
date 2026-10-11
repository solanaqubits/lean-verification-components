# Release v0.5.36: Quantum E91 correlations and CHSH violation

Private proof snapshot: `1816caf49a2eee5ccc791a388fb28b1a83bb1da2`.
Previous public main: `cdb4a1124d95baa11c1e439117cce5a525730c59`.

## Proven scope and assumptions

The model defines the singlet density matrix and dichotomic XZ observables.
Born probabilities are computed from projector tensor products, with reality,
nonnegativity, normalization and uniform local marginals proved. All nine E91
correlators are derived. The specified settings attain S = -2 sqrt(2), with
|S| = 2 sqrt(2) > 2. Key pairs (2,1) and (3,2) are perfectly anticorrelated;
Bob's bit inversion yields agreement and ideal zero QBER. Independent uniform
settings give key/test/discard probabilities 2/9, 4/9 and 1/3.

The classical CHSH bound covers finite local hidden-variable laws using the same
law for all settings, and finite convex mixtures of products of physical qubit
density matrices. The explicit intercept/resend channel acts on the supplied
singlet: Eve measures Alice's half in any real unit XZ direction and prepares an
arbitrary valid outcome-dependent qubit. Partial-trace calculation gives a
separable result with trace one and |S| <= 2. Arbitrary inputs, general POVMs or
all attack models are not covered by this instrument theorem.

The Born rule is a physical modeling postulate; its algebraic consequences are
proved. Attaining 2 sqrt(2) is not a universal operator Tsirelson upper-bound proof.
Device-independent QKD security, final-key secrecy, finite-key statistics or
guaranteed finite-sample detection, error reconciliation, privacy amplification,
and detection loopholes are outside scope. The singlet source, measurements,
independent settings and authenticated classical channel are idealized.
Python, JSON/SHA-256 and SimLab obligations remain open.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 138 |
| Lean files under Verification/ | 178 top-level + 2 auxiliary = 180 |
| Root-inclusive sources identical to the private snapshot | 181 |
| Clean strict build | 3728 jobs; no warnings |
| Complete verifier audit | 17806 declarations; no violations |
| Pinned independent full audit | 17806 declarations; no violations |
| Public live tests | 83; no failures or skips; 279.434s |

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

All 181 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.36. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/03_quantum_physics_and_optics/QuantumE91ProtocolBellCHSH.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
