# Release v0.5.28: Postselected photonic controlled-Z

Private proof snapshot: `629e2ceb6441538c0abdf75331db6e1be6f2bcd7`.
Previous public main: `e7d02af088ed570a70801016179f1bd763260973`.

## Proven scope and assumptions

The module derives a coincidence-postselected controlled-Z operation from three
disjoint ideal lossless beam splitters. The six modes are a0,a1,b0,b1,va,vb;
the pairs (a0,va), (a1,b1), (b0,vb) use the imported complex B(T), for 0 <= T <= 1.
The normalized two-boson basis enumerates 21 unordered mode pairs. Equal-mode
creation monomials carry the factor 1/sqrt(2). A generic polynomial-substitution
theorem connects the symmetric lift to single-particle scattering. Both the
six-mode network and its 21-dimensional two-photon lift are proved unitary.

The dual-rail encoding J is an isometry. Its orthogonal projection JJ† accepts
exactly one photon in each logical rail pair and none in the auxiliary modes.
The success map is defined by compression K(T)=J†U(T)J; its diagonal
(T,T,T,2T-1) is derived. At T=1/3, K=CZ/3 and K†K=I/9. Every normalized input
has success probability 1/9; the normalized successful branch is CZ psi.
The matrix identity K rho K†=(1/9)CZ rho CZ† holds for every matrix rho,
and the success trace is 1/9 for every trace-one density matrix.

CZ is unitary, Hermitian and involutive. Four Pauli conjugation identities are
proved. The product input |++> becomes the graph state (1,1,1,-1)/2. A local
Hadamard maps this state to the Bell state Phi+. Its global density is pure;
both reduced densities are I2/2 and reduced purity is 1/2. The state is proved
not to factor into two local vectors. A product-state purity theorem supplies
an additional bridge to pure-state separability. A general theory of convex
mixed-state separability is not claimed.

Regressions cover all four basis inputs with success probability 1/9 and signs
(+,+,+,-), T=1/2 with K=diag(1/2,1/2,1/2,0), and T=1 with K=I. At T=1/2,
the |11> input bunches in the central computational modes and fails coincidence
selection; this particular input does not leak into the auxiliary vacuum modes.

This is a finite homogeneous-polynomial model of ideal indistinguishable bosons,
not an infinite Fock-space or canonical-commutation-relation construction.
Born-rule interpretation and ideal coincidence selection are model assumptions.
Full scattering is unitary; the accepted branch is conditional. Exact probability
1/9 does not mean deterministic success or a nondestructive herald.
Scalable KLM architectures, Kerr interactions, spectral wave-packet overlap,
partial distinguishability, photon loss and detector noise are not modeled.
Python correctness, JSON/SHA-256 correctness and SimLab-to-Lean correspondence
remain open. Novelty is not assessed. The network isolates the controlled-sign
core associated with Ralph, Langford, Bell and White (2002), using the project's
complex phase convention; exact identity with the paper's full CNOT diagram
is not asserted.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 130 |
| Lean files under Verification/ | 170 top-level + 2 auxiliary = 172 |
| Root-inclusive sources identical to the private snapshot | 173 |
| Clean strict build | 3621 jobs; no warnings |
| Complete verifier audit | 15177 declarations; no violations |
| Pinned independent full audit | 15177 declarations; no violations |
| Public live tests | 75; no failures or skips; 269.270s |

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

All 173 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.28. Existing tags are not overwritten. This is not an atomic push.
A separate receipt records the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/03_quantum_physics_and_optics/PhotonicsCPhaseGateUnitary.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
