# Release v0.5.24: Complex beam splitter and MZI phase response

Private proof snapshot: `0556810415b74197251b6a7e8c2e712f5375b97f`.
Previous public main: `1e42907e3dbce79c24a09e584826c34c3c5590b1`.

## Proven scope and assumptions

For 0<=T<=1 the lossless symmetric splitter is
B=[[sqrt(T),i sqrt(1-T)],[i sqrt(1-T),sqrt(T)]]. The arm operator is
D(phi)=diag(exp(i phi),1), and U=B†DB explicitly uses the inverse second splitter.
Both inverse identities and Hermitian Euclidean norm preservation hold for B and U.
The reflection factor i=exp(i pi/2) belongs to this chosen convention, not every
reflecting device; a zero component does not have a defined relative phase.

For input (1,0), the actual matrix output gives c0=T exp(i phi)+1-T and
c1=i sqrt(T)sqrt(1-T)(1-exp(i phi)). Probabilities are defined by Complex.normSq,
then proved to equal P0=1-4T(1-T)sin²(phi/2) and P1=4T(1-T)sin²(phi/2).
They lie in [0,1], sum to one, have period 2pi and satisfy the endpoint cases.
At T=1/2 they are cos²(phi/2) and sin²(phi/2). For nonnegative input power,
the corresponding intensities exactly equal the SolarisMithraCore formulas.

For positive I0, port-0 extrema are I0 and I0(2T-1)², with both bounds proved
and attained at phases 0 and pi. They construct a valid InterferencePattern with
V=4T(1-T)/(1+(2T-1)²), equal to one at T=1/2. A constant phase offset shifts
the attainment points but leaves the extrema and visibility unchanged.
Geometric dependence is substitution under the external premise phi=kappa*DeltaL+phi0;
kappa=0 does not allow scanning the phase curve by changing path length.

These results follow from the specified complex matrix model, not from Maxwell's
equations. Material dispersion, polarization, loss, detectors, hardware synthesis
and full Fock-space dynamics are not modeled. Decoherence and stochastic phase
noise are not inferred from a deterministic phase offset. Python, JSON/SHA-256
and SimLab-to-Lean correspondence remain open obligations. Novelty is not assessed.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 126 |
| Lean files under Verification/ | 166 top-level + 2 auxiliary = 168 |
| Root-inclusive sources identical to the private snapshot | 169 |
| Clean strict build | 3617 jobs; no warnings |
| Complete verifier audit | 14415 declarations; no violations |
| Pinned independent full audit | 14415 declarations; no violations |
| Public live tests | 71; no failures or skips; 263.419s |

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

Regressions cover arbitrary complex inputs, endpoint splitters, a dark balanced
port, asymmetric probabilities (1/4,3/4) and visibility 3/5 at T=1/4, arbitrary
static phase shifts, zero input power, the Solaris bridge and zero geometric slope.
Existing subject definitions and proofs remain unchanged.

All 169 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; no Russian cards are exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, verify its remote SHA, then
annotated v0.5.24. This is not atomic. Existing tags are not overwritten.
A separate receipt records the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/03_quantum_physics_and_optics/PhotonicsBeamSplitterPhaseShift.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
