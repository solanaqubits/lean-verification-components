---
id: CryptoBLSSignatureAggregationGroup
language: en
section: cryptography
source: Verification/CryptoBLSSignatureAggregationGroup.lean
source_sha256: 1927eaccce9f68da65480a9edb22f8ebe02e029a9c0956a63fc0652f77f955cc
novelty: not-assessed
status: reviewed
---

# BLS aggregation in cyclic prime-order bilinear groups

This module proves algebraic completeness for BLS signatures on three abstract
cyclic groups of prime order q. It imports the scalar BLS module and the cyclic
setup from the group MuSig module. The target group uses additive notation.

## Model and results

`PairingSetup` supplies three modules over ZMod q, generators whose scalar maps
are bijective, a bilinear map G₁ →ₗ[ZMod q] G₂ →ₗ[ZMod q] GT, and a nonzero
pairing of the two source generators. Cyclicity and nondegeneracy imply that
P ↦ e(P,G₂) is injective. The generator bijections are mathematical hypotheses,
not efficient algorithms for recovering secret scalars.

A signature is σ = x • H and its public key is pk = x • G₂. Bilinearity proves
e(σ,G₂) = e(H,pk). For every finite indexed family, including empty families,
e(∑σᵢ,G₂) = ∑e(Hᵢ,pkᵢ). A common message gives e(∑σᵢ,G₂) = e(H,∑pkᵢ).
Arbitrary individually accepted signatures also compose. Distinct messages are
not required for these identities; security requirements are separate.

The rogue-key witness constructs bad = z • G₂ − honest from a public honest key.
The attacker can use z • H as the group's signature because honest + bad = z • G₂.
This is an algebraic vulnerability of naive common-message aggregation without PoP.

For any nonzero δ, two initially valid signatures modified to σ₁ + δ and σ₂ − δ
are each individually invalid, using pairing injectivity, while their sum still
passes aggregate verification. Aggregate validity does not certify its components.

`ConsistencyModel` instantiates all three groups with ZMod q, generator 1 and
multiplication as the pairing. This witnesses realizability of the hypotheses;
it is not a cryptographically secure pairing construction or an absolute
consistency proof of Lean. The shared commutative-ring identity is independently
specialized to the existing real scalar module and ZMod q. No homomorphism from
ℝ to ZMod q is asserted.

## Regressions and integration

Kernel regressions cover one and two participants, repeated keys and messages,
permutations, zero secrets, rogue keys, explicit arithmetic modulo 7, invalid
components with a valid aggregate, and real/modular bridges. The master suite
includes universal group properties, a concrete model for every prime q and
the ring identity. Registry integration uses CryptoFullSuite.

## Clean Water boundaries

Proved: bilinear individual and aggregate completeness, common-message
aggregation, composition of accepted partials, injectivity, rogue-key and error
cancellation witnesses, and the scalar bridge.

Not modeled: BLS12-381 or any concrete elliptic curve, Miller's algorithm,
hash-to-curve, point validation, serialization, PoP, or computational security
reductions in ROM/Co-CDH. Message points H are inputs to the algebraic model.
Python, JSON/SHA-256 and SimLab obligations remain open. Novelty is not assessed.

All project and export checks passed; measured results follow.

## Source theorem links

- [pairing_scalar_swap](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L52)
- [pairing_generator_injective](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L57)
- [individual_bls_verification](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L66)
- [individual_verification_iff](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L71)
- [aggregate_bls_distinct_messages](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L82)
- [aggregate_composition_from_valid_partials](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L90)
- [aggregate_bls_common_message](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L96)
- [common_signature_scalar_sum](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L101)
- [common_message_composition](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L106)
- [bls_rogue_key_vulnerability](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L113)
- [bls_error_cancellation_counterexample](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L123)
- [aggregate_permutation](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L143)
- [zero_secret_contribution](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L149)
- [one_participant](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L152)
- [two_participants](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L157)
- [group_properties](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L182)
- [ring_bilinear_bridge](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L194)
- [bridge_to_existing_real_bls](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L202)
- [consistency_model_exists](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L222)
- [bridge_to_modular_bls](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L225)
- [crypto_bls_group_master_suite](../../Verification/CryptoBLSSignatureAggregationGroup.lean#L242)

## Private snapshot validation: BLS aggregation in bilinear groups

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 146 |
| Lean sources including root | 189 |
| Strict clean private build | 3736 jobs; no warnings |
| Both full axiom audits | 18858 declarations; no violations |
| Private live tests | 94; no failures or skips; 296.555s |
| Export live tests | 91; no failures or skips; 309.287s |
| Strict clean export build | 3736 jobs; no warnings |

Module verify and audit each covered 1145 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
Independent auditor source: 46024e005996495c65ef609368e11ab39c4222e3.
Binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: leanprover/lean4:v4.33.1; auditor source toolchain file: leanprover/lean4:v4.32.0-rc1.
The binary is pinned separately; a second independent proof kernel is not claimed.
Counts include generated declarations. Both project .lake/build directories were absent
before the final builds. Each tree uses its own copy of the pinned dependency cache.
All 189 exported Lean files match byte-for-byte; repeated exports agree.
Integration is idempotent. Original HEAD and 406 tracked files
are preserved. No writes to simulations/. That earlier private integration did not publish a public release.

Proved: bilinear individual and aggregate BLS completeness, common-message
aggregation, composition of valid partials, pairing injectivity, rogue-key and
error-cancellation witnesses, and real/modular specializations of a ring identity.
The concrete ZMod q model witnesses the assumptions and is not cryptographically
secure. Concrete curves, pairing algorithms, hash-to-curve, serialization, PoP
and computational security in ROM/Co-CDH are outside scope.
Python, JSON/SHA-256 and SimLab obligations remain open.

## Public release validation

The [v0.5.44 report](../../docs/release-v0.5.44.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 146 |
| Lean files under Verification/ | 186 top-level + 2 auxiliary = 188 |
| Root-inclusive sources identical to the private snapshot | 189 |
| Clean strict build | 3736 jobs; no warnings |
| Complete verifier audit | 18858 declarations; no violations |
| Pinned independent full audit | 18858 declarations; no violations |
| Public live tests | 91; no failures or skips; 294.911s |
