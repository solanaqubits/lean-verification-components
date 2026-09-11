---
id: DeFiLendingCDP
language: en
section: finance
source: Verification/DeFiLendingCDP.lean
source_sha256: 17a09cebcd683ced46c255b15f723392f105bb4c513b33cd619e6cbccc15504a
novelty: not-assessed
status: reviewed
---

# DeFiLendingCDP

[Section](../finance/README.md) · [Lean](../../Verification/DeFiLendingCDP.lean)

## Verified result

Six scalar properties: nonnegative health factor; exact coverage and liquidation criteria; strict increase with price for positive collateral; strict decrease with debt for a positive numerator; and the seized-value identity.

## Assumptions and limitations

The position assumes C ≥ 0, P > 0, D > 0 and 0 < T ≤ 1. T is the liquidation threshold. The two monotonicity theorems state their positivity hypotheses explicitly; strictness does not hold at C = 0. Equality HF = 1 satisfies IsSolvent and is not IsLiquidatable in this model.

The seizure identity only requires a nonzero price. It does not assert nonnegative repayment or bonus, sufficient collateral, a repayment cap, close factors, or conservation across a liquidation state transition. These are static real-valued formulas for an isolated position, not verification of Aave, Compound or MakerDAO implementations. Multiple collateral assets, interest accrual, rounding, oracle delays and market-wide liquidation cascades are not modeled.

## Value and novelty

Reusable checked arithmetic for explicit specifications. Mathematical novelty and first-formalization status have not been assessed.

## Verification

[Validation record](../VERIFICATION.en.md). Entry point: `DeFiLendingCDP.defi_lending_cdp_master_verification_suite`.
