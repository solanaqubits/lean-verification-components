---
id: DeFiCDPLiquidation
language: en
section: finance
source: Verification/DeFiCDPLiquidation.lean
source_sha256: 945e833111c7a049fd112ac20b7250e96fdee8d3b84ff459ae3ea934bf6d33c7
novelty: not-assessed
status: reviewed
---

# DeFiCDPLiquidation

[Section](../finance/README.md) · [Lean](../../Verification/DeFiCDPLiquidation.lean)

## Verified result

For positive collateral, debt, price and threshold (at most one), the supplied health-factor ratio is at least one exactly when debt is at most adjusted collateral, and below one exactly when adjusted collateral is below debt. Partial repayment 0 < repay < debt strictly increases the ratio with collateral, price and threshold fixed. Multiplying the prescribed seized amount repay*(1+penalty)/price by a positive price returns repay*(1+penalty).

## Assumptions and limitations

These are scalar real-number identities and inequalities. The repayment theorem is pure repayment without collateral withdrawal; it does not prove health-factor improvement during liquidation with collateral seizure. No state update, transfer or execution trace is defined. The seized-value theorem assumes only positive price: repayment and penalty are arbitrary real inputs, with no nonnegativity, debt cap or available-collateral bound. Thus the formula alone does not establish a feasible liquidation or realized profit.

The criteria overlap the existing DeFiLendingCDP scalar model; this component presents the requested positive-collateral interface and explicit partial-repayment inequality. No derivation of a complete protocol is claimed. Cascades, DEX slippage, collateral auctions, bad debt, integer rounding, fees, oracle delays and deployed MakerDAO/Aave behavior are not formalized.

## Value and novelty

A specification of static coverage and partial-repayment algebra. Scientific novelty and first-formalization claims have not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `DeFiCDPLiquidation.defi_cdp_liquidation_master_verification_suite`.
