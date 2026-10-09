# Release v0.5.25: Two-photon Hong–Ou–Mandel interference

Private proof snapshot: `611ba17cda45a492ff45c83f698456408ea402e8`.
Previous public main: `76432d2a2e2deba4f95bb1167d7f80754f25b875`.

## Proven scope and assumptions

For 0<=T<=1 and R=1-T, the normalized occupation basis is
|2,0>, |1,1>, |0,2>. The symmetric-square construction is tied to the imported
complex splitter B(T) by a polynomial substitution theorem with factorial
normalizations. This is a finite two-photon sector, not a construction of the
full Fock space or canonical commutation relations.

The lifted matrix U_two_photon satisfies both U†U=I and UU†=I and preserves
the squared Hermitian norm of arbitrary complex input vectors. On |1,1>,
the actual output is (i sqrt(2TR), T-R, i sqrt(2TR)). Born probabilities are
defined as Complex.normSq of these components, yielding P20=P02=2TR and
P11=(2T-1)², nonnegative and summing to one. At T=1/2, P11=0 and the exact
state is (i/sqrt(2))(|2,0>+|0,2>).

The single-mode phase gauge diag(1,i) induces the occupation gauge
Q=diag(1,i,-1). The lifted complex matrix equals Q U_real Q†, and U_real
agrees with QuantumBeamSplitterTransform. For general inputs both input and
output coordinates are rephased. For |1,1> this changes the input by only
a global phase, so all three outcome probabilities agree directly.

The distinguishable reference retains particle labels and assigns independent
joint weights |B(j,0)|² |B(k,1)|². Their nonnegativity, normalization and
factorization into actual marginals are proved. Coincidence is the disjoint
event j!=k, giving P_dist=T²+R²>=1/2>0. The reference assumption is explicit.
HOM visibility uses (P_dist-P11)/P_dist, not a maximum-plus-minimum denominator.
It equals 2TR/(T²+R²), lies in [0,1], and equals one exactly when T=1/2.

Ideal indistinguishable modes, the stated preparation and lossless optics are
model assumptions. The temporal wave-packet profile P(tau), spectral overlap,
dip shape or width, partial distinguishability, photon loss, frequency jitter,
detector noise and hardware implementation are not modeled. Python, JSON/SHA-256
and SimLab-to-Lean correspondence remain open obligations. Novelty is not assessed.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 127 |
| Lean files under Verification/ | 167 top-level + 2 auxiliary = 169 |
| Root-inclusive sources identical to the private snapshot | 170 |
| Clean strict build | 3618 jobs; no warnings |
| Complete verifier audit | 14510 declarations; no violations |
| Pinned independent full audit | 14510 declarations; no violations |
| Public live tests | 72; no failures or skips; 260.670s |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1,
and the executable is pinned separately. No second independent proof kernel is asserted.

The project build directory started empty; pinned dependency caches were copied
into the isolated tree. Public checks were rerun against this release candidate.
Counts include generated declarations, not just independent mathematical theorems.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py" -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

Regressions cover arbitrary complex inputs and normalized substitution, exact
balanced bunching, real-convention probabilities, independent reference weights,
endpoint cases, and T=1/4 with probabilities (3/8,1/4,3/8), reference 5/8 and
visibility 3/5. At T=1/2 the reference remains 1/2 while HOM coincidence is zero.
Existing subject definitions and proofs remain unchanged.

All 170 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; no Russian cards are exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, verify its remote SHA, then
annotated v0.5.25. This is not atomic. Existing tags are not overwritten.
A separate receipt records the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/03_quantum_physics_and_optics/PhotonicsHongOuMandelInterference.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
