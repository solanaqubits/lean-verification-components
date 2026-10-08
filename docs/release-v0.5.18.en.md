# Release v0.5.18: Conditional Shor order recovery via LCM/GCD

Private proof snapshot: `5e714619c1455a47bc58d0f87d8cfe8a94db0c7b`.
Previous public main: `367dc9fcadea3ca709130e24c6ccf9ce293becba`.

## Proven scope and assumptions

listLCM is executable structural recursion over a finite list of natural-number
candidates. Neither the unknown order nor spectral numerators are inputs. The empty
LCM is one; append and membership invariance cover incremental use, reordering and
duplicates. No time or bit-complexity bound is asserted.

For r>0 and a nonempty list with every q dividing r, L=listLCM(qs) divides r and
L=r iff foldr (fun q acc => gcd(r/q,acc)) 0 qs = 1. Nonemptiness is necessary for
this unanchored GCD criterion. For spectral denominators q=r/gcd(s,r), the exact
identity is L=r/gcd(r,foldr gcd 0 ss); thus L=r iff the anchored GCD is one.
This version includes empty ss: empty input recovers only order one. At r=6,
ss=[3,2] gives denominators [2,3] and recovers six without any individual q=r.

The bridge reuses module 119's canonical reduced denominators and the existing
Shor Parameters (N>=2, coprime a,N, positive actual order and padded target register).
Given Q=2^n>=N² and each observed y<Q satisfying Nearest to its latent s/r with s<r,
the correct denominator occurs among the corresponding continued-fraction candidates.
This does not identify the latent label or select its denominator from the observable list.

The modular check proves r divides L. With separately established L divides r,
it gives equality. A certified divisor means mathematical provenance, not merely
a successful modular check. No automatic candidate-selection algorithm is supplied.

A kernel-checked counterexample has N=31,a=2,order=5,y=410,Q=1024. Candidate
denominators [1,2,5] have LCM 10, which passes the modular check but is not the order.
Regressions verify 31²<=1024 and |410/1024-2/5|<=1/(2*1024), so this failure persists
at adequate QPE resolution. Taking the LCM of all candidates is unjustified.

No i.i.d. measurement law, probability of a coprime sample family, number of runs,
factorization via gcd(a^(r/2)±1,N), physical implementation or gate synthesis is proved.
Python, JSON/SHA-256 and external SimLab input-to-byte binding remain open obligations.
The algebra reuses pinned Mathlib Nat.div_lcm_eq_div_gcd; scientific priority has
not been assessed. This is conditional multi-sample recovery, not a full Shor algorithm.

## Independently measured public validation

| Check | Result |
|---|---:|
| Direct MasterSuite imports | 120 |
| Lean files under Verification/ | 160 top-level + 2 support = 162 |
| Root-inclusive sources identical to the private snapshot | 163 |
| Clean strict build | 3547 jobs; no warnings |
| Complete verifier audit | 12922 declarations; no violations |
| Pinned independent full audit | 12922 declarations; no violations |
| Public live tests | 65; no failures or skips; 253.994s |

The public version was set to 0.5.18 before the recorded complete validation run.
An initial build with the old version was stopped, corrected and restarted from
an empty project build directory. Its incomplete log is separate evidence, not
part of the successful results. Pinned dependency caches were copied into the
isolated clone; this is not a complete source rebuild of Mathlib.
Counts include generated declarations. Both full audits allow only propext,
Classical.choice and Quot.sound. The strict registry hook and catalog passed
separately; the hook is not a second independent proof kernel.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
```

The independent full auditor is leanprover-community/axiom-audit v0.1.2, source commit
`46024e005996495c65ef609368e11ab39c4222e3`, executable SHA-256
`8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254`.
It runs through lake env with --root Verification,
--allow propext,Classical.choice,Quot.sound and --json.
The project is pinned to Lean v4.33.1. The auditor's source toolchain file records
v4.32.0-rc1; the executable is pinned separately and successful auditing is measured.

Regressions cover empty input, order one, inadmissible zero divisors, zero spectral
numerators, repeated and reordered candidates, insufficient divisors, modular
rejection, recovery of six from [2,3], and a proper multiple passing the modular
check. Concrete computations use decide and decide +kernel, not native_decide.

Integration is idempotent. Repeated exports agree in all 444 files, with all
163 proof sources matching the private snapshot byte-for-byte. Checks reproduce
the 7824-state 3PC certificate and the 256-node chip manifest; these are external
reproducibility checks, not proof of the Python environment. Earlier subject proofs
and historical release reports are preserved. English cards distinguish previous
private/export results from the new public measurements. No Russian cards are
exported. Reservoir metadata are retained; external indexing is not asserted.

## Publication and preservation

An annotated v0.5.18 tag is published by sequential pushes:
`git push origin main`, verify the remote commit, then `git push origin v0.5.18`.
This is not atomic. Existing tags are not overwritten. The final commit, tag object
and peeled SHA are checked against the remote and recorded in the publication receipt.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; no global immutability claim
is made about concurrent external activity.

[Detailed contract](../knowledge/03_quantum_physics_and_optics/QuantumShorOrderRecoveryGCD.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
