# Release v0.5.17: Shor continued fractions

Private proof snapshot: `189077d10183ebf11198f486c48fa156c4cbf11d`.
Previous public main: `fd4d7a4ec374a94e05f116caf9452aa4536a5bab`.

## Proven scope and assumptions

The algorithm computes finite partial quotients and convergents of the exact rational
y/Q by Euclidean descent, terminating at an integer. Its inputs y,Q,N do not contain
the unknown spectral numerator s or period r. The candidate list filters denominators
strictly below N. Membership in the unfiltered list is equivalent to being a Mathlib
Real.convergent, including its repeated terminal values.

For N≥2, a coprime to N, r=orderOf(a : ZMod N), 0≤s<r and 0≤y<Q, the existing Shor
model proves 0<r<N. With Q=2^n≥N², the modular QPE Nearest condition implies ordinary
|y/Q-s/r|≤1/(2Q). The proof handles s=0 and rules out wrap-around at this resolution.
Since q=r/gcd(s,r)≤r<N, the error is strictly below 1/(2q²). Pinned Mathlib's strict
Legendre theorem supplies the convergent, and the finite-list bridge proves its
presence among the executable candidates.

The correct reduced denominator q divides r. Other list entries are not asserted
to divide r. If gcd(s,r)=1, q=r and r belongs to the modularly checked list. The
modular check a^q mod N = 1 mod N proves r divides q; proper multiples can pass.
If q divides r is separately established, mutual divisibility gives equality.
For s=0 the reduced denominator is one, recovering the order only when r=1.

The number of Euclidean stages is at most 2*Nat.log 2 Q+1 for Q>0. This counts partial
quotients, not every list operation, bit operation, modular exponentiation or total
runtime. No O(log N) claim is made without additionally bounding Q in terms of N.

The existing actual-input QPE mixture gives a contribution bound 4/(r*pi²) for a
single component's nearest sample, combined here with candidate membership. This
is distinct from the conditional component bound 4/pi². Guaranteed single-run
success, independent repeated measurements, LCM recovery, classical factorization,
long-integer bit complexity, physical noise and gate synthesis are outside scope.
Python, JSON/SHA-256 and external SimLab input-to-byte binding remain open obligations.
No scientific-priority claim or full factoring algorithm is asserted.

## Independently measured public validation

| Check | Result |
|---|---:|
| Direct MasterSuite imports | 119 |
| Lean files under Verification/ | 159 top-level + 2 support = 161 |
| Root-inclusive sources identical to the private snapshot | 162 |
| Clean strict build | 3546 jobs; no warnings |
| Complete verifier audit | 12863 declarations; no violations |
| Pinned independent full audit | 12863 declarations; no violations |
| Public live tests | 64; no failures or skips; 252.627s |

The public version was set to 0.5.17 before validation. The project build directory
started empty; pinned dependency caches were copied into the isolated clone.
This is not a complete source rebuild of Mathlib. Counts include generated declarations.
Both full audits allow only propext, Classical.choice and Quot.sound. The registry
hook and knowledge catalog passed separately; the hook is not a second proof kernel.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
```

The independent auditor is leanprover-community/axiom-audit v0.1.2, source commit
`46024e005996495c65ef609368e11ab39c4222e3`, executable SHA-256
`8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254`.
It runs through `lake env` with `--root Verification`,
`--allow propext,Classical.choice,Quot.sound` and `--json`.
The project is pinned to Lean v4.33.1. The independent tool's source toolchain file
records v4.32.0-rc1; its executable is pinned separately and successful auditing is
measured. No second independent proof kernel is claimed.

Regressions cover executable rational examples, the strict Legendre boundary,
zero and integer inputs, negative rational Euclidean input, reduced denominators,
extraneous list entries, failed modular checks, passing nonminimal multiples and
the actual N=7,a=2,Q=256 bridge. Concrete computations use decide +kernel;
native_decide is not used. General tests preserve all recovery assumptions.

Integration is idempotent. Repeated exports agree in all 440 files; all 162
proof sources match the private commit byte-for-byte. Reproduction checks retain
the 7824-state 3PC certificate and the 256-node chip manifest. These are external
reproducibility checks, not formal verification of Python. Prior subject proofs
and historical release reports are preserved. English cards separate historical
private/export measurements from the fresh public results. No Russian cards are
exported. Reservoir metadata are retained; external indexing is not asserted.

## Publication and preservation

An annotated v0.5.17 tag is published by sequential pushes:
`git push origin main`, verify the remote commit, then `git push origin v0.5.17`.
This is not atomic. Existing tags are not overwritten. The final commit, annotated
tag object and peeled tag are checked against the remote and recorded in the
publication receipt after creation.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not a claim that the directory is globally immutable.

[Detailed contract](../knowledge/03_quantum_physics_and_optics/QuantumShorContinuedFractions.md)
· [Source hashes and validation commands](../tools/validation_snapshot.json)
