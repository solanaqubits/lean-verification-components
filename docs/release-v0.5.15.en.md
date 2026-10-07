# Release v0.5.15: Shor order-finding core

Private proof snapshot: `110558af4e7411ac48d75c1a6fc9795db6c2fde1`.
Previous public main: `13960daf07ba4e047f5ce00bb37139a59ffb2912`.

## Proven scope and assumptions

The model supplies a modulus N≥2, a natural base a with Nat.Coprime a N and a
padded target register of dimension 2^m≥N. The control width n is independent.
The period is defined as orderOf (a : ZMod N), not as a supplied candidate answer.
It is positive; a^r mod N=1 and the powers for k<r are distinct.

The modular operator permutes every residue y<N, including zero and nonunits,
and fixes padding y≥N. Its inverse and Hermitian-product preservation are proved.
The constructed states

ψ_s = (1/√r) ∑k exp(−2πi sk/r) |a^k mod N⟩

are orthonormal eigenvectors with eigenvalue exp(2πi s/r). They describe the orbit
subspace, not an asserted basis of the entire padded register. Order one is allowed.
The accessible computational input |1⟩ and the operator do not depend on knowing r.
The exact identity |1⟩=(1/√r)∑s ψ_s is a coherent pure-state decomposition.

Linearity of the actual controlled-power/QFT circuit gives the joint output
(1/√r)∑s A_s/r(y) ψ_s. Orthonormality removes the cross terms from the marginal,
yielding P(y)=(1/r)∑s P_s/r(y). This mixture is proved from the circuit, not assumed
as its input. The marginal sums to one, including the zero-control-qubit case.

A component with exact dyadic phase s/r=x/2^n has probability one at x.
For each component and any modular nearest sample b, P_s/r(b)≥4/π².
Its guaranteed contribution to the actual |1⟩ marginal is weighted by 1/r:
P(b)≥4/(rπ²). Overlapping component peaks are not assumed disjoint.

Regressions cover orders four (N=15,a=2), three (N=7,a=2) and one; zero and nonunit
residues, padding, inverses, unitarity, orthonormality, decomposition, normalization
and n=0. For order four and n=2, the actual marginal is uniform with probability
1/4. A non-dyadic component checks the weighted bound. The reduced phase 2/4=1/2
is explicitly distinguished from the order four; non-coprime inputs are excluded.

Approximating s/r does not automatically recover r. Continued fractions, candidate
order validation, repeated independent runs, LCM recovery, integer factorization,
complexity and reversible gate synthesis are not proved. No physical preparation,
noise or decoherence model is claimed. Python, JSON/SHA-256 and binding external
SimLab inputs to bytes remain outside the Lean proof. No priority claim is made.

## Independently measured public validation

| Check | Result |
|---|---:|
| Direct MasterSuite imports | 117 |
| Lean files under Verification/ | 157 top-level + 2 support = 159 |
| Root-inclusive proof sources matching the private snapshot | 160 |
| Clean strict build | 3542 jobs; no warnings |
| Complete local audit | 12359 declarations; no violations |
| Independent pinned audit | 12359 declarations; no violations |
| Public live tests | 62; no failures or skips; 249.324s |

The project build directory started empty. Pinned dependency caches were copied
into the isolated clone; Mathlib was not rebuilt entirely from source. Declaration
counts include generated definitions and constructors, not just named theorems.
Both complete audits allow only propext, Classical.choice and Quot.sound.
The strict registry hook and knowledge catalog checks also passed.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
```

The independent auditor is leanprover-community/axiom-audit v0.1.2, commit
`46024e005996495c65ef609368e11ab39c4222e3`, built with the pinned Lean toolchain.
It runs through `lake env` with `--root Verification`,
`--allow propext,Classical.choice,Quot.sound` and `--json`.
The registry hook is additional; it is not a second proof kernel.

All 160 proof sources are transferred byte-for-byte from the private snapshot.
Previously published reports and Lean results are retained. The English card
separates historical private/export measurements from this public validation.
No Russian cards are exported. Reservoir metadata are retained; external indexing
is not asserted.

Publication uses an annotated v0.5.15 tag and two sequential pushes:
`git push origin main`, remote commit verification, then `git push origin v0.5.15`.
This procedure is not atomic. Existing tags are not rewritten.
The original workspace HEAD and all 406 tracked-file hashes outside simulations/
are preserved. This task does not write to simulations/; concurrent SimLab activity
is not interpreted as immutability of the entire directory.

[Theorems and assumptions](../knowledge/03_quantum_physics_and_optics/QuantumShorOrderFindingCore.md)
· [Source hashes and measured commands](../tools/validation_snapshot.json)
