# Release v0.5.58: Bulletproofs batch verification

This release adds CryptoBulletproofsBatchVerification as the 160th direct import
of MasterSuite. All 203 Lean sources, including Verification.lean, match reference
snapshot 3ae1fc1bffa43c957cdabaf661e375f4f99580b4 byte-for-byte.

## Proved contract

For a fixed batch with common dimension n=2^k and common public generators, the
module computes the polynomial and expanded IPA residuals from actual public
proof data. The strict individual wrapper checks y!=0 and x!=0; unit-typed IPA
challenges are already nonzero. It preserves module 159's API, which itself
permits x=0. The wrapper accepts exactly when its guards hold and both residuals
vanish, for arbitrary transcripts.

Independent uniform weights are sampled from the entire vector space over ZMod q,
including zero coordinates, after the batch and old protocol challenges are fixed.
The actual finite PMF assigns probability at most 1/q to acceptance of a batch
with an individually rejected proof. The proof uses at most q^(N-1) accepting
assignments for N residuals. Invalid guards reject deterministically.
This is a guarantee relative to individual verification, not knowledge soundness
of the underlying range proof.

The module proves perfect completeness for every choice of weights, equivalence
to one explicitly expanded MSM with shared-base coefficients combined across
proofs, and invariance under paired permutations of proofs and their weights.
Original IPA transcripts are retained; no new IPA or proof-message compression
is constructed. Equal dependent weights can cancel residuals D,-D.

Regression coverage includes empty and singleton batches, dimensions 1,2,4,
valid multi-proof batches, nontrivial scaling, invalid scalars, corrupted T1 and
t_x, zero weights, and paired permutations. Two damaged singleton proofs over
ZMod 17 each accept exactly 17 of 289 coefficient vectors in exhaustive execution.
The general PMF theorem is independent of those finite examples.

## Clean Water

Proved: public residual characterization, deterministic scalar checks, perfect
batch completeness, the finite-uniform error bound <=1/q, explicit combined MSM,
paired permutation invariance, and cancellation/corruption cases.
Witness extraction, computational binding, HVZK, Fiat-Shamir/ROM, CSPRNG
implementation, concrete curves, serialization and low-level MSM optimization
or side-channel guarantees are not modeled. Python, JSON/SHA-256 and SimLab
correspondence obligations remain open. Scientific novelty is not assessed.

[Detailed contract](../knowledge/04_cryptography/CryptoBulletproofsBatchVerification.md) ·
[Lean source](../Verification/CryptoBulletproofsBatchVerification.lean)

## Measured validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 160 |
| Lean files under Verification/ | 200 top-level + 2 auxiliary = 202 |
| Root-inclusive sources identical to the reference snapshot | 203 |
| Clean strict build | 3767 jobs; no warnings |
| Complete verifier audit | 22183 declarations; no violations |
| Pinned independent full audit | 22183 declarations; no violations |
| Public live tests | 105; no failures or skips; 330.075s |
| New kernel examples / compiled execution cases | 18 / 18 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 203 proof sources match reference snapshot
3ae1fc1bffa43c957cdabaf661e375f4f99580b4 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

