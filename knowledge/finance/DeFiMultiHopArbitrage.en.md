---
id: DeFiMultiHopArbitrage
language: en
section: finance
source: Verification/DeFiMultiHopArbitrage.lean
source_sha256: 9bba63e76d101a7912e614717e4e42f03da0671244e3960f369c163bd6b28719
novelty: not-assessed
---

# DeFiMultiHopArbitrage

[Section](README.md) · [Lean source](../../Verification/DeFiMultiHopArbitrage.lean)

## Verified result

The product of valid fee factors is at most one; a cycle with consistent fixed rates and a positive fee decreases the input amount.

## Assumptions and scope

The models retain their stated balance, price, and fee assumptions. They do not verify production smart-contract code, transaction ordering, or every protocol rule.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`effective_return_factoring`](../../Verification/DeFiMultiHopArbitrage.lean#L35)
- [`totalFeeFactor3_le_one`](../../Verification/DeFiMultiHopArbitrage.lean#L40)
- [`totalFeeFactor3_strict_lt_one`](../../Verification/DeFiMultiHopArbitrage.lean#L53)
- [`defi_multihop_arbitrage_master_verification_suite`](../../Verification/DeFiMultiHopArbitrage.lean#L121)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
