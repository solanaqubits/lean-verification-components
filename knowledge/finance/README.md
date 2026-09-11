# Finance, liquidity, and mechanisms

[All sections](../README.md)

## Modules

| Module | Verified result |
|---|---|
| [AssetSettlement](AssetSettlement.en.md) | Sequential exchange with sufficient funds preserves assets; a returned completed status makes repeated execution inactive. |
| [DeFiAMMInvariants](DeFiAMMInvariants.en.md) | Exact constant-product and swap formulas in an idealized reserve model. |
| [PortfolioRiskEngine](PortfolioRiskEngine.en.md) | Nonnegative two-asset variance, a diversification bound, and strict improvement for positive weights and risks with ρ < 1. |
| [LightningHTLCNetwork](LightningHTLCNetwork.en.md) | Conservation of free plus locked funds, decreasing timelocks, and a neutral intermediary balance. No preimage check is modeled. |
| [DeFiMultiHopArbitrage](DeFiMultiHopArbitrage.en.md) | The product of valid fee factors is at most one; a cycle with consistent fixed rates and a positive fee decreases the input amount. |
| [MechanismDesignEIP1559](MechanismDesignEIP1559.en.md) | For a real-valued model, the multiplier lies in [7/8,9/8], fees remain positive, and equilibrium occurs at target utilization. Integer rounding and the protocol's minimum increment are not modeled. |
| [MechanismDesignPBS](MechanismDesignPBS.en.md) | Under bid ≤ MEV, profit is nonnegative and prescribed credits satisfy a balance identity. Maximality of the winning bid is an assumption. |
| [DeFiConcentratedLiquidity](DeFiConcentratedLiquidity.en.md) | Virtual reserves have product L²; real reserves are positive inside the active range; shifted-product and increment-sign identities hold for constant L. |

## Scope

The models retain their stated balance, price, and fee assumptions. They do not verify production smart-contract code, transaction ordering, or every protocol rule.

[Contributing](../CONTRIBUTING.en.md) · [Validation](../VERIFICATION.en.md)

- [DeFiLendingCDP](../08_finance_and_risk/DeFiLendingCDP.en.md): health-factor and liquidation-quote scalar invariants.

- [DeFiCurveStableSwap](../08_finance_and_risk/DeFiCurveStableSwap.en.md): two-asset residual balance, zero-amplification equivalence and scaling.

- [DeFiTWAPOracle](../08_finance_and_risk/DeFiTWAPOracle.en.md)
