# Release v0.5.39: Exact unitary no-cloning

Private proof snapshot: `845ef3d56ad066f0b3896d917e3ebf90e9f7367c`.
Previous public main: `b55a2dd72141cb7c3aba5c1c393eb4c56424ed5f`.

## Proven scope and assumptions

Unitary evolution and tensor factorization imply c=c^2 for exact vector cloning
and t=t^2 for pure-density cloning, where t is the squared overlap. For normalized
inputs this proves a necessary condition: orthogonality or equality of the pure
density matrices. The general sufficiency theorem for an arbitrary orthogonal
pair is not asserted. Global phase invariance is proved for density matrices;
literal cloning of both psi and -psi is impossible.

An explicit unitary CNOT copies the computational basis, but sends |+>|0> to a
Bell state proved unequal to every product vector. A unitary cloner exists for
one prescribed normalized state and blank by isometry extension. This existence
proof is noncomputable and does not synthesize a circuit.

The squared overlap of |0> and |+> is 1/2 in every dimension at least two. No common
unitary and fixed normalized blank can clone both densities, hence no universal
cloner exists. Bridges derive the scalar module's quadratic premise and rule out
joint cloning of the actual four BB84 states.

The scope is exact deterministic square-unitary cloning of pure states on two
systems. General CPTP maps with discarded environments, mixed-state
no-broadcasting, probabilistic or approximate cloners and physical QKD security
are outside scope. Python, JSON/SHA-256 and SimLab obligations remain open.
Scientific novelty is not assessed.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 141 |
| Lean files under Verification/ | 181 top-level + 2 auxiliary = 183 |
| Root-inclusive sources identical to the private snapshot | 184 |
| Clean strict build | 3731 jobs; no warnings |
| Complete verifier audit | 18166 declarations; no violations |
| Pinned independent full audit | 18166 declarations; no violations |
| Public live tests | 86; no failures or skips; 289.434s |

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

All 184 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.39. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/03_quantum_physics_and_optics/QuantumNoCloningUnitary.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
