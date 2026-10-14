# Release v0.5.61: Bulletproofs multi-range aggregation

This release adds `CryptoBulletproofsAggregation`, the 163rd direct MasterSuite
import, with an executable aggregated prover and verifier connected to the
existing recursive inner-product argument (IPA).

## Proved contract

For n=2^a bits per value, m=2^b values and N=mn=2^(a+b), the block index is
j*n+i, the y power is y^(j*n+i), and the bit weight is z^(j+2)*2^i.
The quadratic inner product has constant term

    t0 = sum_j z^(j+2)*v_j + delta(m,n,y,z)
    delta = (z-z^2)*sum_(r<N) y^r - sum_j z^(j+3)*sum_(i<n) 2^i.

Formal polynomial coefficient identities recover all bit constraints and block
values. Reverse recovery over natural numbers requires v_j<q and 2^n<q.
The IPA target includes -mu*Hblind+t_x*U. Honest aggregated transcripts satisfy
the public commitment equation and are accepted by the composed verifier.
At m=1, the delta, curves, target and verifier reduce to module 159.

The exact inner IPA payload is 2(a+b) group elements and two scalars.
The proof body contains 4+2(a+b) group elements and five scalars; the envelope
also includes m public value commitments. Generators and verifier challenges
are separate. Logarithmic IPA payload size does not imply logarithmic envelope
size, verifier work or serialized byte size.

## Regressions

35 Lean examples and 38 compiled scenarios cover m,n in {1,2,4}, zero and maximum
values, mixed bits, m=1 compatibility, exact payload counts, wrong block weights,
zero y, and specific nondegenerate corrupted T1,T2,t_x,mu examples. A nonboolean
input can satisfy an evaluated equation while failing the formal identity.

## Clean Water scope

Proved: algebraic block reduction, the constant term and delta formulas, formal
coefficient characterization, the public IPA target, honest composition and
exact message counts. No witness extraction or special soundness, computational
binding, HVZK, Fiat-Shamir/ROM security, or post-hoc compression of completed
independent proofs without witnesses is claimed. Powers of z are dependent;
the independent-weight soundness bound of module 160 is not transferred here.
As in module 159, the algebraic verifier rejects y=0 and uses unit IPA challenges;
honest algebraic completeness allows x=0 and z=0 without a soundness claim.
Concrete curves, serialization, CSPRNG and MPC are outside scope. Python,
JSON/SHA-256 and SimLab correspondence obligations remain open.

[Detailed contract](../knowledge/04_cryptography/CryptoBulletproofsAggregation.md).
All 206 Lean proof sources are exported from reference snapshot
`e74d187fb7c0fe986ec7fd15af5bd6591f372736` without byte changes.

## Measured validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 163 |
| Lean files under Verification/ | 203 top-level + 2 auxiliary = 205 |
| Root-inclusive sources identical to the reference snapshot | 206 |
| Clean strict build | 3843 jobs; no warnings |
| Complete verifier audit | 22780 declarations; no violations |
| Pinned independent full audit | 22780 declarations; no violations |
| Public live tests | 108; no failures or skips; 320.972s |
| New kernel regression examples / compiled scenarios | 35 / 38 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 206 proof sources match reference snapshot
e74d187fb7c0fe986ec7fd15af5bd6591f372736 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

