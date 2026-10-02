---
id: DeFiERC4626InflationDefense
language: en
section: finance
source: Verification/DeFiERC4626InflationDefense.lean
source_sha256: 427b7b4189ef97541edb31e95f8269de3bc19d567d59c64bb31e294d29239db8
novelty: not-assessed
status: reviewed
---

# DeFiERC4626InflationDefense

[Section](../finance/README.md) · [Lean](../../Verification/DeFiERC4626InflationDefense.lean)

## Verified result

Natural-number division reproduces zero minting for the naive parameters (deposit 999, assets 1000, supply 1). The supplied static redemption expression evaluates to 1999. With offset 3 the same conversion parameters yield 999 shares. Protected minting is nondecreasing in the deposit and strictly positive under the sufficient condition deposit ≥ totalAssets + 1.

## Assumptions and limitations

Virtual offsets do not universally prevent zero minting: the module also proves that deposit 1, assets 1000000, supply 1 and offset 3 produce zero shares. The positive-mint theorem is conditional, not a general inflation-attack defense.

These are static calculations over unbounded natural numbers with floor division. No sequence of deposits, donations and redemptions, economic attacker-profit bound, token ownership or transfers is proved. The protected example reuses supply 1; reachability from a protected empty-vault initialization is not established. The redemption value 1999 is not a net-profit calculation. The supplied conversion formula is not a verified OpenZeppelin implementation. Solidity overflow, fees, multiple users and caller slippage limits are not modeled.

## Value and novelty

Executable arithmetic examples and conditional rounding properties, with an explicit counterexample to unconditional protection. Scientific novelty has not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `DeFiERC4626InflationDefense.defi_erc4626_inflation_defense_master_suite`.
