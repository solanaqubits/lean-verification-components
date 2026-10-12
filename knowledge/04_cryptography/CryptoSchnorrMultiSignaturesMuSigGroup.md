---
id: CryptoSchnorrMultiSignaturesMuSigGroup
language: en
section: cryptography
source: Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean
source_sha256: e58300315e0c35b9c2802f20b9fa01319834cd438ba814d901ac45df6fe07320
novelty: not-assessed
status: reviewed
---

# Finite-group Schnorr multisignature aggregation

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean)

## Model and proved results

Scalars are ZMod q for a prime q. The public group is an additive commutative
module over these scalars. CyclicSetup supplies a generator G and a bijection
x ↦ x • G; thus the group has exactly q elements and unique scalar representations.
The existence/uniqueness proof does not supply an efficient discrete-log algorithm.
The scalarSetup instance (the additive finite field, G = 1) establishes non-vacuity.

The static participant vector L : Fin n → G preserves order and duplicate keys.
HashContexts supplies separately typed deterministic aggregation and signature
functions. Their outputs define a_i = H_agg L (L i) and the common challenge
c = H_sig X_agg R_agg m. No hash implementation or security property is assumed.
The honest main theorem uses n ≥ 2 and the cyclic setup; auxiliary module identities
hold more generally, including empty and singleton sums.

For X_i = x_i • G and R_i = r_i • G, partial responses
s_i = r_i + c * a_i * x_i satisfy s_i • G = R_i + (c * a_i) • X_i.
Summing gives (sum s_i) • G = (sum R_i) + c • (sum a_i • X_i).
The separate composition theorem assembles any responses satisfying those partial
equations with the same challenge and coefficients. It does not establish knowledge
of secret keys. The requested name musig_group_aggregation_soundness denotes
honest algebraic completeness, not cryptographic soundness or unforgeability.

## Rogue-key witness and regressions

For naive two-key addition, bad = z • G - honest makes honest + bad = z • G.
Using R = r • G and c = H_sig (honest + bad) R m, the response r + c * z
passes aggregate verification. The construction takes the honest public key,
not its secret scalar. It witnesses cancellation in the naive verification rule;
it is not a formal adversary game or an attack on correctly instantiated MuSig.

Repeated keys receive equal coefficients in a fixed vector. A zero coefficient
removes that term from the fixed sum. Removing or changing a participant may change
other hash coefficients, so invariance under editing the list is not claimed.
Opposite keys cancel under naive addition; a zero aggregate key accepts s = r
with R = r • G for every challenge. Practical rejection of degenerate keys is not
implemented. Kernel regressions instantiate two signers over ZMod 7, duplicates,
zero weights, arbitrary participant counts, the attack witness and scalar bridges.

## Bridge to the existing real model

One general commutative-ring identity expresses two signers with effective nonces
r_i0 + b * r_i1. Its real specialization unfolds exactly partialSig, aggSig,
aggregateNonce and computeAggKey from CryptoMuSig2Aggregation. Its modular
specialization uses the scalar action on ZMod q. This is a shared polynomial
identity, not a reduction map from arbitrary real scalars into a finite field.
Two nonce variables in this bridge do not formalize two interactive rounds.

## Clean Water boundaries

The result is deterministic group algebra and perfect verification completeness.
There is no AGM/ROM reduction, discrete-log hardness assumption, unforgeability
game, rogue-key resistance proof for hashed coefficients, nonce sampling/reuse
protection, concurrent-session protection, interactive MuSig2/BIP327 protocol,
point validation, curve implementation or byte serialization. Two typed function
fields do not establish cryptographic domain separation. Python, JSON/SHA-256
and SimLab obligations remain open. Scientific novelty is not assessed.

Reference: [Maxwell et al., Simple Schnorr Multi-Signatures](https://eprint.iacr.org/2018/068).

## Validation

Base snapshot: 516c0748a91a7c5c222d76759b24ae3781886d1d.
All project and export checks passed; measured results follow.

## Source theorem links

- [two_nonce_ring_identity](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L31)
- [partial_module_identity](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L41)
- [assemble_module_identity](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L46)
- [scalar_action_injective](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L65)
- [unique_scalar_representation](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L69)
- [generator_ne_zero](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L74)
- [partial_verify_exact](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L108)
- [partial_to_aggregate_composition](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L113)
- [musig_group_aggregation_soundness](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L120)
- [rogue_key_naive_aggregation_vulnerability](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L134)
- [zero_coefficient_contribution](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L146)
- [duplicate_keys_equal_coefficients](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L151)
- [two_participant_key](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L156)
- [duplicate_key_aggregation](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L161)
- [naive_coefficients](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L167)
- [naive_key_cancellation](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L171)
- [zero_key_verification](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L175)
- [bridge_to_scalar_musig](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L190)
- [bridge_to_existing_real_musig](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L198)
- [crypto_schnorr_musig_group_master_suite](../../Verification/CryptoSchnorrMultiSignaturesMuSigGroup.lean#L242)

## Private snapshot validation: Finite-group Schnorr aggregation

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 143 |
| Lean sources | 185 under Verification/; 186 including root |
| Strict clean private build | 3733 jobs; no warnings |
| Both full axiom audits | 18362 declarations; no violations |
| Private live tests | 91; no failures or skips; 288.114s |
| Export live tests | 88; no failures or skips; 303.386s |
| Strict clean export build | 3733 jobs; no warnings |

Module verify and audit each covered 984 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
Independent auditor source: 46024e005996495c65ef609368e11ab39c4222e3.
Binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: leanprover/lean4:v4.33.1; auditor source toolchain file: leanprover/lean4:v4.32.0-rc1.
The binary is pinned separately; a second independent proof kernel is not claimed.
Counts include generated declarations. Both project .lake/build directories were empty
before the final builds. An existing pinned dependency package cache was shared because
copying it exhausted disk space; the incomplete task-created copy was removed.
All 186 exported Lean files match byte-for-byte; repeated exports agree.
Integration is idempotent. Original HEAD and 406 tracked files
are preserved. No writes to simulations/. That earlier private integration did not publish a public release.

The result is group algebraic completeness, composition of accepted partial responses,
a naive rogue-key witness and independent real/modular specializations of a common
ring identity. No map from arbitrary real scalars to ZMod q is asserted.
AGM/ROM security, hashed-coefficient rogue-key resistance, concurrent sessions,
nonce protection, interactive MuSig2/BIP327 and serialization are outside scope.
Python, JSON/SHA-256 and SimLab obligations remain open.

## Public release validation

The [v0.5.41 report](../../docs/release-v0.5.41.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 143 |
| Lean files under Verification/ | 183 top-level + 2 auxiliary = 185 |
| Root-inclusive sources identical to the private snapshot | 186 |
| Clean strict build | 3733 jobs; no warnings |
| Complete verifier audit | 18362 declarations; no violations |
| Pinned independent full audit | 18362 declarations; no violations |
| Public live tests | 88; no failures or skips; 290.769s |
