# Release v0.5.56: Bulletproofs inner product algebra

This release exports CryptoBulletproofsInnerProduct from reference snapshot
`620e2e03d62506f6a231a33c8dc044b31cebd800`, following public main
`d15308ac08229d8cac29589789aa9215f03736d8` (v0.5.55).

## Formal contract

Vectors have exactly 2^k coordinates over ZMod q for prime q. The algebraic
theorems hold in any additive commutative ZMod q module and specialize to cyclic
groups of prime order without assuming independent generators.

The round invariant proves that the canonical cross terms L and R and the
challenge-weighted halving transform preserve the target relation through
P' = x^2*L + P + x^-2*R. Challenges are units, which excludes zero. The executable
prover and public verifier have a recursive completeness proof down to dimension
one. A round's first message is independent of its subsequent challenge.

Expanded products of challenge powers give weights on the original generators.
The expanded multiscalar verifier equals the recursive verifier for every
transcript, including corrupt transcripts. The flattened prover payload contains
exactly k pairs (L,R), hence 2k group elements, and two final scalars. Public
parameters and verifier challenges are counted separately. Logarithmic message
size does not imply logarithmic verifier work; no runtime bound is claimed here.

The regression wrapper checks 22 kernel-proved examples and 12 compiled execution
cases: dimensions 1, 2 and 4, nontrivial unit challenges, zero vectors, explicit
expanded weights, exact payload sizes, first-message independence and concrete
rejections after altering L, R or a final scalar. These are explicit examples,
not an unconditional guarantee that every alteration is rejected.

## Clean Water

This is the algebraic core of the inner product argument, not a complete
Bulletproofs range proof or a proof of knowledge. Witness extraction via transcript
trees, reduction of arbitrary polynomial relations or ranges to IPA, blinding/HVZK,
Fiat-Shamir and the random-oracle model are outside scope. Concrete elliptic curves,
serialization and verified computational complexity are also outside scope.
Python, JSON/SHA-256 and SimLab correspondence obligations remain open.

[Detailed module contract](../knowledge/04_cryptography/CryptoBulletproofsInnerProduct.md)

## Measured validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 158 |
| Lean files under Verification/ | 198 top-level + 2 auxiliary = 200 |
| Root-inclusive sources identical to the reference snapshot | 201 |
| Clean strict build | 3765 jobs; no warnings |
| Complete verifier audit | 21912 declarations; no violations |
| Pinned independent full audit | 21912 declarations; no violations |
| Public live tests | 103; no failures or skips; 309.775s |
| New IPA kernel examples / compiled execution cases | 22 / 12 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 201 proof sources match reference snapshot
620e2e03d62506f6a231a33c8dc044b31cebd800 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

