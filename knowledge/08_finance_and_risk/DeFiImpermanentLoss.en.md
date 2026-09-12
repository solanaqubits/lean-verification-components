---
id: DeFiImpermanentLoss
language: en
section: finance
source: Verification/DeFiImpermanentLoss.lean
source_sha256: 4fafd51381bfb10fe0f73ffa134d33535237f992471f7d218bb2771eae78d72e
novelty: not-assessed
status: reviewed
---

# DeFiImpermanentLoss

[Section](../finance/README.md) · [Lean](../../Verification/DeFiImpermanentLoss.lean)

## Verified result

For the supplied values lpValue(k) = 2*sqrt(k) and hodlValue(k) = 1+k, their difference is -(sqrt(k)-1)^2 for k ≥ 0. An additional theorem establishes the full relative-loss factorization IL(k) = -(sqrt(k)-1)^2/(1+k). For k > 0, IL is nonpositive, vanishes exactly at k = 1, and is unchanged by replacing k with 1/k.

## Assumptions and limitations

Here k is the relative price Pt/P0, not the constant reserve product. The values have the same units and both equal 2 initially; they are not individually normalized to initial value 1. The dimensionless relative loss is their ratio minus one. The factorization includes k = 0, whereas reciprocal symmetry and the stated nonpositivity/zero criterion assume k > 0. No claim about negative prices is made.

The valuation formulas are definitions, not derived from reserves, arbitrage, swap transitions or a constant-product pool implementation. No time evolution or continuity theorem is supplied. Trading fees and LP fee APY, concentrated-liquidity tick ranges, unequal portfolio weights and multi-asset pools, price feeds, integer rounding and implementation correctness are not formalized. The inverse-price identity is algebraic; no logarithm is defined in the module.

## Value and novelty

Reusable exact loss identities and boundary conditions for a static equal-weight valuation model. Mathematical novelty and first-formalization status have not been assessed.

## Verification

[Validation record](../VERIFICATION.en.md). Entry point: `DeFiImpermanentLoss.defi_impermanent_loss_master_verification_suite`.
