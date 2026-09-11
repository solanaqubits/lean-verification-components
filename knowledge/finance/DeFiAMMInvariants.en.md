---
id: DeFiAMMInvariants
language: en
section: finance
source: Verification/DeFiAMMInvariants.lean
source_sha256: 0d6344ffa8120be8d2e117aacbab03c1aa42693bbe7e4cf4a9ba556aa92e4794
novelty: not-assessed
---

# DeFiAMMInvariants

[Section](README.md) · [Lean source](../../Verification/DeFiAMMInvariants.lean)

## Verified result

Exact constant-product and swap formulas in an idealized reserve model.

## Assumptions and scope

The models retain their stated balance, price, and fee assumptions. They do not verify production smart-contract code, transaction ordering, or every protocol rule.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`output_pos`](../../Verification/DeFiAMMInvariants.lean#L22)
- [`output_lt_reserve`](../../Verification/DeFiAMMInvariants.lean#L28)
- [`newRy_pos`](../../Verification/DeFiAMMInvariants.lean#L36)
- [`defi_amm_master_verification_suite`](../../Verification/DeFiAMMInvariants.lean#L108)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
