# Release v0.5.57: Bulletproofs algebraic range reduction

This release adds `CryptoBulletproofsRangeReduction`, connecting natural bit
representations to the recursive inner product argument through formal polynomial
identities and an executable public verifier.

## Proved contract

- Exact quadratic expansion of <l(X),r(X)> and the constant term t0=z^2*v+delta(y,z).
- Equivalence between a genuine formal polynomial identity in independent X,Y,Z
  and the bit/value constraints; this is not inferred from a single evaluation.
- Recovery of the natural range with explicit v<q and 2^n<q hypotheses, for n=2^k.
- Polynomial commitment verification and the corrected public IPA target:
  P=A+x*S-z*sum(G)+sum((z*y^i+z^2*2^i)*Hprime_i)-mu*Hblind+t_x*U.
- Nonzero-y generator rescaling and perfect completeness of honest composition
  with the existing recursive IPA prover and verifier.
- Message independence from subsequent challenges, rejection of zero y, and
  explicit corruption regressions. The verifier receives public inputs only.

The target removes the vector-commitment blinding with -mu*Hblind and supplies the
actual inner product with t_x*U. A delta*U term alone would not give this relation.
Regressions cover n=1,2,4, lower/upper range endpoints, invalid bit representations,
selected damaged transcripts, and an evaluated equality that holds for nonbits
while its formal polynomial identity fails.

[Detailed mathematical contract](../knowledge/04_cryptography/CryptoBulletproofsRangeReduction.md)

## Measured validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 159 |
| Lean files under Verification/ | 199 top-level + 2 auxiliary = 201 |
| Root-inclusive sources identical to the reference snapshot | 202 |
| Clean strict build | 3766 jobs; no warnings |
| Complete verifier audit | 22043 declarations; no violations |
| Pinned independent full audit | 22043 declarations; no violations |
| Public live tests | 104; no failures or skips; 317.987s |
| New kernel examples / compiled execution cases | 19 / 13 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 202 proof sources match reference snapshot
76d180a7bac74db68d58218a3df9e4a780d528d1 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Clean Water

Knowledge extraction / special soundness, computational binding and DLOG security,
HVZK simulation, Fiat-Shamir and ROM are not modeled. Algebraic masking inputs
are not a proof of zero knowledge. Concrete curves, serialization and multiple
aggregated range claims are also outside this contract.
Python, JSON/SHA-256 and SimLab correspondence obligations remain open.
