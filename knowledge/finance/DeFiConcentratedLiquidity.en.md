---
id: DeFiConcentratedLiquidity
language: en
section: finance
source: Verification/DeFiConcentratedLiquidity.lean
source_sha256: e07b57ca1770565ec3f10c3bdba6b5e0541b3409a1965fe9b2de15b00a0df888
novelty: not-assessed
---

# DeFiConcentratedLiquidity

[Section](README.md) · [Lean source](../../Verification/DeFiConcentratedLiquidity.lean)

## Verified result

Virtual reserves have product L²; real reserves are positive inside the active range; shifted-product and increment-sign identities hold for constant L.

## Assumptions and scope

The models retain their stated balance, price, and fee assumptions. They do not verify production smart-contract code, transaction ordering, or every protocol rule.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`virtual_reserves_product_eq_L_sq`](../../Verification/DeFiConcentratedLiquidity.lean#L26)
- [`realX_pos`](../../Verification/DeFiConcentratedLiquidity.lean#L34)
- [`realY_pos`](../../Verification/DeFiConcentratedLiquidity.lean#L38)
- [`defi_concentrated_liquidity_master_verification_suite`](../../Verification/DeFiConcentratedLiquidity.lean#L75)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
