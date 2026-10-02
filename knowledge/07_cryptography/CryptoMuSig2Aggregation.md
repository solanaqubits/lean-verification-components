---
id: CryptoMuSig2Aggregation
language: en
section: cryptography
source: Verification/CryptoMuSig2Aggregation.lean
source_sha256: 5236457dfbdf59b40499475fe5f0a70a5d00118bc14bffe572db0b9adafa5f44
novelty: not-assessed
status: reviewed
---

# CryptoMuSig2Aggregation

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoMuSig2Aggregation.lean)

## Model and results

This is a two-signer algebraic model over `ℝ`. `MuSig2Setup` supplies `g ≠ 0`,
and `publicKey` is the scalar `PK = x * g`. The coefficients `μ₁`, `μ₂`, nonce coefficient `b`, and challenge
`c` are supplied parameters. An honest partial response has the form
`sᵢ = rᵢ₁ + b * rᵢ₂ + c * μᵢ * xᵢ`; its effective public nonce is
`Rᵢ = (rᵢ₁ + b * rᵢ₂) * g`. Partial verification is the equation
`sᵢ * g = Rᵢ + c * μᵢ * PKᵢ`.

The weighted key is `computeAggKey μ₁ μ₂ PK₁ PK₂ = μ₁ * PK₁ + μ₂ * PK₂`.

- `musig2_partial_sig_relation`: honest partial responses satisfy verification.
- `musig2_aggregation_completeness`: two honest partials satisfy the aggregate equation.
- `musig2_linearity_homomorphism`: any two accepted responses, with common `b`
  and `c` and the agreed per-signer weights, assemble into
  `(s₁ + s₂) * g = (R₁ + R₂) + c * PKagg`. This assumes the partial verification
  equations; it does not infer honest behavior or knowledge of keys.
- `weighted_key_add`: fixed-weight key aggregation is additive in the pair of keys.
- `partial_sig_add`: a partial response is additive in its two secret nonces
  and secret key when `b`, `c`, and `μ` are fixed.

`verifyPartial` and `aggregateNonce` take public nonce scalars, whereas
`partialSig` takes secret nonce scalars. The honest completeness theorem
multiplies each secret nonce by `g` explicitly. The partial relation and assembly
identities hold even for `g = 0`; the setup's nonzero condition is needed for recovery.

The naive rogue key `PK₂ = target - PK₁` makes the unweighted sum equal
`target`. With weights, the same substitution gives
`μ₂ * target + (μ₁ - μ₂) * PK₁`, which differs from `μ₂ * target` when
`μ₁ ≠ μ₂` and `PK₁ ≠ 0`. This excludes only that cancellation expression.
This is `rogue_key_expansion` and `musig2_rogue_key_barrier`.
`equal_weights_cancel` records cancellation when the weights agree.
The barrier does not prove inequality with every target or prevent another key choice.
Indeed, `fixed_weights_allow_target_key` shows that, for fixed `μ₂ ≠ 0`,
choosing `PK₂ = (target - μ₁ * PK₁) / μ₂` reaches any prescribed target.
`public_key_reveals_scalar` records that `PK / g = x` when `g ≠ 0`.

`MuSig2AggregationFormalSuite` collects the partial, completeness, assembly,
linearity, restricted barrier, target-key, and recovery statements. Its instance
is `crypto_musig2_aggregation_master_suite`.

## Relation to BIP 327

[BIP 327](https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki#key-aggregation)
hashes an **ordered list**, not a multiset. Its MuSig2* coefficient is `1` for
the second distinct key and its duplicates; other coefficients use the list
hash and individual key. These rules are not implemented here.
The [signing equations](https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki#signing)
motivate the two-nonce expression; the present model omits parity corrections
and tweaks. Two nonce scalars do not formalize two communication rounds.

## Assumptions and limits

The algebra requires all contributions to use the same session parameters.
No hash function, message binding, random oracle, random sampling, adversary,
unforgeability game, or reduction to discrete-logarithm hardness is modeled.
Fixed scalar weights do not establish cryptographic rogue-key resistance;
the target-key construction and scalar recovery theorem expose this limitation.
They are not attacks on BIP 327, whose coefficients depend on the submitted keys.

There is no finite group, secp256k1 arithmetic, modular reduction, serialization,
point validation, infinity handling, parity normalization, or tweak processing.
Nonce generation, secure storage, deletion, non-reuse, concurrent sessions,
communication rounds, authenticated broadcast, abort behavior, and implementation
security are outside the model. The final equation is scalar Schnorr algebra,
not a checked BIP340 signature. The model has exactly two signers; arbitrary
participant counts are outside its scope. Novelty is not assessed.

## Verification

The module passed `verify`, `audit`, and integration as `CryptoFullSuite.musig2_aggregation`. Strict build, `verify-all`, independent axiom audit, the full test suite, and catalog checks passed. See the [validation record](../VERIFICATION.en.md).
