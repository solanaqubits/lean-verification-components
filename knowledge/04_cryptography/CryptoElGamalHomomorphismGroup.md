---
id: CryptoElGamalHomomorphismGroup
language: en
section: cryptography
source: Verification/CryptoElGamalHomomorphismGroup.lean
source_sha256: 868b644d916b4669c18044846ccb18e5e212b46af2773f0f335224726a253d85
novelty: not-assessed
status: reviewed
---

# Group ElGamal: weighted homomorphism and malleability

The algebraic core works over a commutative ring R and an R-module H.
Ciphertexts are pairs in H × H. For generator G and a common public key Y,
enc G Y r M = (r • G, M + r • Y) and dec x c = c.2 − x • c.1.
If Y = x • G, decryption returns the arbitrary group plaintext M.

## Cyclic group and exponential encoding

The cryptographic specialization reuses CyclicSetup from the group MuSig module:
q is prime, H is a module over ZMod q, and m ↦ m • G is bijective.
enc_scalar replaces M by m • G. Decryption returns m • G. Every decrypted point
has exactly one scalar preimage in ZMod q, but no efficient discrete-logarithm
algorithm is supplied. The concrete model H = ZMod q, G = 1 witnesses the
hypotheses; it is not cryptographically secure or an absolute consistency proof.

## Proven identities

Encryption respects addition and scalar multiplication. For every finite family
with one common public key, weighted ciphertext sums encrypt the weighted sum of
randomness inputs and group plaintexts. For exponential encoding the result is
enc_scalar Y (∑ aᵢrᵢ) (∑ aᵢmᵢ). Decryption gives (∑ aᵢmᵢ) • G.
The weights and encoded messages are in ZMod q, so these sums are modulo q.
An interpretation as unbounded integer arithmetic is not asserted; unsigned
no-wrap interpretations require a nonnegative total below q, and signed
interpretations require an appropriate injective decoding interval.

Adding enc Y t 0 rerandomizes algebraically: it yields enc Y (r+t) M.
No PMF, independence or equality-of-distributions claim is made.

For an arbitrary ciphertext, replacing c.2 by c.2 + Δ • G adds exactly Δ • G
to decryption. For Δ ≠ 0, injectivity of the generator action proves that this
changes the decrypted point. The transformation uses no secret key. Applied to
an encryption, it gives an encryption of the shifted scalar m+Δ.

A commutative-ring identity is specialized independently to the existing real
ElGamal definitions and to ZMod q. No homomorphism from ℝ to ZMod q is claimed.

## Regressions and integration

Kernel regressions cover empty and singleton sums, two participants, permutations,
zero and negative weights, modulo-7 wraparound, rerandomization, scalar uniqueness
and a nontrivial malleability witness. The master suite exports group correctness,
weighted homomorphism, uniqueness, rerandomization, nontrivial shifts, the concrete
model and the ring identity through CryptoFullSuite.

## Clean Water boundaries

Proved: algebraic group and exponential correctness, unique scalar representation,
weighted homomorphism, algebraic rerandomization, malleability and the scalar bridge.
Not modeled: IND-CPA/IND-CCA, DDH reductions, randomness distributions, efficient
scalar decoding (including baby-step giant-step), concrete curves or serialization.
Python, JSON/SHA-256 and SimLab obligations remain open. Novelty is not assessed.

All project and export checks passed; measured results follow.

## Source theorem links

- [elgamal_group_decryption_correctness](../../Verification/CryptoElGamalHomomorphismGroup.lean#L31)
- [elgamal_add_homomorphism](../../Verification/CryptoElGamalHomomorphismGroup.lean#L36)
- [elgamal_smul_homomorphism](../../Verification/CryptoElGamalHomomorphismGroup.lean#L43)
- [module_weighted_sum](../../Verification/CryptoElGamalHomomorphismGroup.lean#L48)
- [elgamal_rerandomization_algebraic](../../Verification/CryptoElGamalHomomorphismGroup.lean#L60)
- [decryption_add](../../Verification/CryptoElGamalHomomorphismGroup.lean#L65)
- [decryption_smul](../../Verification/CryptoElGamalHomomorphismGroup.lean#L70)
- [elgamal_malleability_shift](../../Verification/CryptoElGamalHomomorphismGroup.lean#L75)
- [weighted_permutation](../../Verification/CryptoElGamalHomomorphismGroup.lean#L80)
- [elgamal_scalar_decryption_correctness](../../Verification/CryptoElGamalHomomorphismGroup.lean#L97)
- [elgamal_scalar_uniqueness](../../Verification/CryptoElGamalHomomorphismGroup.lean#L102)
- [elgamal_scalar_representation](../../Verification/CryptoElGamalHomomorphismGroup.lean#L106)
- [elgamal_weighted_sum_homomorphism](../../Verification/CryptoElGamalHomomorphismGroup.lean#L111)
- [weighted_decryption_correctness](../../Verification/CryptoElGamalHomomorphismGroup.lean#L119)
- [elgamal_malleability_nonzero](../../Verification/CryptoElGamalHomomorphismGroup.lean#L126)
- [shifted_encryption](../../Verification/CryptoElGamalHomomorphismGroup.lean#L137)
- [group_properties](../../Verification/CryptoElGamalHomomorphismGroup.lean#L160)
- [ring_elgamal_bridge](../../Verification/CryptoElGamalHomomorphismGroup.lean#L171)
- [bridge_to_existing_real_elgamal](../../Verification/CryptoElGamalHomomorphismGroup.lean#L180)
- [consistency_model_exists](../../Verification/CryptoElGamalHomomorphismGroup.lean#L192)
- [bridge_to_modular_elgamal](../../Verification/CryptoElGamalHomomorphismGroup.lean#L195)
- [crypto_elgamal_group_master_suite](../../Verification/CryptoElGamalHomomorphismGroup.lean#L209)

## Private snapshot validation: Group ElGamal weighted homomorphism

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 147 |
| Lean sources including root | 190 |
| Strict clean private build | 3737 jobs; no warnings |
| Both full axiom audits | 18916 declarations; no violations |
| Private live tests | 95; no failures or skips; 295.876s |
| Export live tests | 92; no failures or skips; 311.35s |
| Strict clean export build | 3737 jobs; no warnings |

Module verify and audit each covered 1100 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
Independent auditor source: 46024e005996495c65ef609368e11ab39c4222e3.
Binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: leanprover/lean4:v4.33.1; auditor source toolchain file: leanprover/lean4:v4.32.0-rc1.
The binary is pinned separately; a second independent proof kernel is not claimed.
Counts include generated declarations. Both project .lake/build directories were absent
before the final builds. Each tree uses its own copy of the pinned dependency cache.
All 190 exported Lean files match byte-for-byte; repeated exports agree.
Integration is idempotent. Original HEAD and 406 tracked files
are preserved. No writes to simulations/. That earlier private integration did not publish a public release.

Proved: group and exponential decryption correctness, unique scalar preimages,
finite weighted homomorphism, algebraic rerandomization and nontrivial malleability.
The generic ring identity specializes independently to real and modular scalars.
Decryption of exponential encoding returns a group point; no efficient scalar
decoder is supplied. Sums and weights are modulo q. The concrete scalar model
witnesses the assumptions and is not cryptographically secure. IND-CPA/IND-CCA,
DDH reductions, randomness distributions, concrete curves and serialization
are outside scope.
Python, JSON/SHA-256 and SimLab obligations remain open.

## Public release validation

The [v0.5.45 report](../../docs/release-v0.5.45.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 147 |
| Lean files under Verification/ | 187 top-level + 2 auxiliary = 189 |
| Root-inclusive sources identical to the private snapshot | 190 |
| Clean strict build | 3737 jobs; no warnings |
| Complete verifier audit | 18916 declarations; no violations |
| Pinned independent full audit | 18916 declarations; no violations |
| Public live tests | 92; no failures or skips; 287.423s |
