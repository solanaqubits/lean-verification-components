---
id: AssetSettlement
language: en
section: finance
source: Verification/AssetSettlement.lean
source_sha256: f946cff61b9b4fd509c4a18b5420dd46132a137721f32d71f497a589e1b3f68f
novelty: not-assessed
---

# AssetSettlement

[Section](README.md) · [Lean source](../../Verification/AssetSettlement.lean)

## Verified result

Sequential exchange with sufficient funds preserves assets; a returned completed status makes repeated execution inactive.

## Assumptions and scope

The models retain their stated balance, price, and fee assumptions. They do not verify production smart-contract code, transaction ordering, or every protocol rule.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`dvp_conservation_assetA`](../../Verification/AssetSettlement.lean#L51)
- [`dvp_conservation_assetB`](../../Verification/AssetSettlement.lean#L61)
- [`dvp_exact_exchange`](../../Verification/AssetSettlement.lean#L71)
- [`asset_settlement_master_verification_suite`](../../Verification/AssetSettlement.lean#L132)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
