# Release v0.5.67: Local Bulletproofs witness extraction

This release adds CryptoBulletproofsWitnessExtraction as the 169th direct
MasterSuite import. The proof sources match reference snapshot
c1171d85423c81d3d6dd6eaa8b040c9c817813ac.

[Detailed contract](../knowledge/04_cryptography/CryptoBulletproofsWitnessExtraction.md)

## Proved scope

For one IPA folding step, four accepting response equations share the expected
prefix and have nonzero challenges with pairwise distinct squares. The extractor
returns either original-length witness vectors for the target or explicit nonzero
coefficients giving a zero combination of the original generators G,H,U. It never
assumes generator independence. P,L,R are eliminated from the returned relation.
The relation branch does not assert that no witness exists.

At arbitrary depth, folded witness vectors are inputs to this local step; they
are not inferred from acceptance of four recursive proofs. At depth zero, a theorem
connects the input equations to module 158's actual one-round verifier.
The checked interface validates the independently supplied expected prefix,
nonzero challenges, distinct squares and all four response equations. Honest
folds recover the original vectors. Repeated or symmetric challenges u,-u,
changed prefixes and corrupted response equations are rejected.

The 3-by-3 Vandermonde determinant is nonzero at three distinct points. Executable
quadratic interpolation agrees with inverse-matrix multiplication and recovers
module 159's t0,t1,t2 from its actual inner-product curve. Interpolation alone
does not prove bitness or recover Pedersen openings from group elements.

## Clean Water

This establishes local algebraic extraction and checked-interface soundness.
Full recursive range-witness extraction, availability and probabilistic construction
of transcript trees, forking and running-time bounds, computational binding and
discrete-log reductions, HVZK and Fiat-Shamir/ROM remain open. No post-hoc
extraction from independent completed proofs is claimed. Concrete curves,
serialization, randomness and authentic storage of the expected context are
outside scope. Tendermint accountability still requires an observation/justification
contract. Python, JSON/SHA-256 and SimLab correspondence obligations remain open.

## Measured validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 169 |
| Lean files under Verification/ | 209 top-level + 2 auxiliary = 211 |
| Root-inclusive sources identical to the reference snapshot | 212 |
| Clean strict build | 3850 jobs; no warnings |
| Complete verifier audit | 24130 declarations; no violations |
| Pinned independent full audit | 24130 declarations; no violations |
| Public live tests | 114; no failures or skips; 334.96s |
| New kernel regression declarations | 30 |
| New executable scenarios | 28 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 212 proof sources match reference snapshot
c1171d85423c81d3d6dd6eaa8b040c9c817813ac byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

