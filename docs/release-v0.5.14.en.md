# Release v0.5.14: General Quantum Phase Estimation

Private proof snapshot: `9970e9170023db76f1a392a7235bb5a1af6778e2`.
Previous public main: `92962f30505be1cf63b3b6360fa084234e7e4f9e`.

## Proven scope

The control register has N=2^n basis states, including n=0; the target has arbitrary
finite dimension. An explicit binary Hadamard kernel prepares the uniform control
state from zero. A recursive controlled-power cascade applies U^j on basis branch j.
For a supplied complex-linear operator U and eigenstate ψ of eigenvalue exp(2πiθ),
phase kickback followed by inverse QFT yields the actual joint output Aθ(y) • ψ:

Aθ(y) = (1/N) ∑k exp(2πik(θ − y/N)).

Both Fourier inverse identities and Hermitian-product preservation are proved for
all N>0. The QPE circuit specializes to powers of two. Unitarity of U preserves
the target norm; probability claims use a normalized eigenstate.

Exact dyadic phases θ=x/N give Aθ(x)=1 and Aθ(y)=0 for y≠x.
For every real phase, the squared-modulus probabilities sum to one. The geometric
sum has a sine-ratio form when θ−y/N is not an integer; the singular branch is
proved separately. A constructive rounded sample b modulo N satisfies
|θ−b/N−z|≤1/(2N) for some integer z. Every such nearest sample, including both
tie choices, has probability at least 4/π². The result is also proved for the
marginal of the actual joint output on a normalized unitary eigen-input.

The n=2 bridge equates the full operational output with the existing two-qubit
module, with the same basis order. At n=0 the target is unchanged and the only
control outcome has probability one. Regressions cover exact N=8, non-dyadic and
negative phases, integer periodicity, wraparound ties, singular cases, generic n,
controlled powers, compatibility and a concrete normalized eigen-input witness.

These are exact finite-dimensional mathematical results. Eigenstate preparation,
physical implementation of controlled powers or QFT, gate-cost bounds, finite
precision, noise, decoherence and the full Shor algorithm are not proved.
Python, JSON/SHA-256 and binding external SimLab inputs to bytes remain obligations
outside the Lean model. No scientific-priority claim is made.

## Independently measured public validation

| Check | Result |
|---|---:|
| Direct MasterSuite imports | 116 |
| Lean files under Verification/ | 156 top-level + 2 support = 158 |
| Root-inclusive proof sources matching the private snapshot | 159 |
| Clean strict build | 3541 jobs; no warnings |
| Complete local audit | 12210 declarations; no violations |
| Independent pinned audit | 12210 declarations; no violations |
| Public live tests | 61; no failures or skips; 247.364s |

The project build directory started empty. Pinned dependency caches were copied
into the isolated clone; Mathlib was not rebuilt entirely from source. Declaration
counts include generated definitions and constructors, not just named theorems.
Both complete audits allow only propext, Classical.choice and Quot.sound.
The existing strict registry hook and catalog checks also pass.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
```

The independent auditor is leanprover-community/axiom-audit v0.1.2, commit
`46024e005996495c65ef609368e11ab39c4222e3`, built with the pinned Lean toolchain.
It is invoked through `lake env`, with `--root Verification`,
`--allow propext,Classical.choice,Quot.sound` and `--json`.
The registry hook is additional; it is not a second proof kernel.

All 159 proof sources are transferred byte-for-byte from the private snapshot.
Previously published reports and Lean results are retained. The English QPE card
separates historical implementation/export measurements from this public run.
No Russian cards are exported. Reservoir metadata are retained; actual external
indexing is not asserted by this release.

Publication uses an annotated v0.5.14 tag and
`git push --atomic origin main v0.5.14`; existing tags are not rewritten.
The original workspace HEAD and all 406 tracked-file hashes outside simulations/
are preserved. This task does not write to simulations/; concurrent SimLab activity
is not interpreted as immutability of the entire directory.

[Theorems and assumptions](../knowledge/03_quantum_physics_and_optics/QuantumPhaseEstimationGeneral.md)
· [Source hashes and measured commands](../tools/validation_snapshot.json)
