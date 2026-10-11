# Release v0.5.37: Quantum depolarizing channel and CHSH damping

Private proof snapshot: `09e41d2eca4d4b88ac8c779d8b7d60622b51aaa3`.
Previous public main: `bf2b908569ef068be37fb544f34bf9f533360de7`.

## Proven scope and assumptions

The Kraus-defined qubit depolarizing channel is trace preserving for p in [0,1]
and completely positive for every finite ancilla dimension. Its exact linear form
is D_p(M)=(1-4p/3) M+(2p/3) Tr(M) I for arbitrary complex matrices.
The Bloch vector scales by lambda=1-4p/3 and its length by |lambda|, including
negative lambda when p>3/4. Complete depolarization occurs at p=3/4.
Composition has parameter p+q-4pq/3, which remains in [0,1].

Acting on Bob's half of the E91 singlet yields lambda rho_minus+(1-lambda) I_4/4.
The actual Born probabilities give S(p)=-2 sqrt(2) lambda and key QBER=2p/3.
Regressions include endpoint channels, pure input states and a malformed affine
formula without the trace factor, which maps zero to a nonzero matrix.

The CHSH violation threshold is not a secret-key threshold. Quantum capacity,
optimal coding, error-correction protocols, DI-QKD and finite-key effects are not
modeled. The ideal E91 source, measurements and authenticated classical channel
retain their existing assumptions. Python, JSON/SHA-256 and SimLab obligations
remain open. Scientific novelty is not assessed.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 139 |
| Lean files under Verification/ | 179 top-level + 2 auxiliary = 181 |
| Root-inclusive sources identical to the private snapshot | 182 |
| Clean strict build | 3729 jobs; no warnings |
| Complete verifier audit | 17940 declarations; no violations |
| Pinned independent full audit | 17940 declarations; no violations |
| Public live tests | 84; no failures or skips; 281.541s |

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

All 182 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.37. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/03_quantum_physics_and_optics/QuantumDepolarizingChannel.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
