---
id: DeFiConstantProductSwap
language: en
section: finance
source: Verification/DeFiConstantProductSwap.lean
source_sha256: c2480cb3537c7cad83b29469482b9d279dbafd03a2c480bb5ee13e9476bc365d
novelty: not-assessed
status: reviewed
---

# DeFiConstantProductSwap

[Section](../finance/README.md) · [Lean](../../Verification/DeFiConstantProductSwap.lean)

## Verified result

For positive reserves x,y, 0<gamma≤1 and positive dx, the defined output y*gamma*dx/(x+gamma*dx) preserves the effective product. The remainder equals x*y/(x+gamma*dx), is strictly positive, and output is below y. If gamma<1, the real post-swap product (x+dx)*remainingY strictly exceeds x*y. At fixed pool parameters, output is strictly increasing for positive inputs.

## Assumptions and limitations

These are exact real-arithmetic identities for a specified one-swap formula. The formula is a definition, not derived from contract execution; no state-transition system or sequence of swaps is modeled. Strict product growth requires a positive fee and positive input. It is a reserve-product statement, not a profit or return guarantee. Output below the reserve is not absence of arbitrage across markets.

Solidity floor division, feeTo protocol-share minting, fixed-width overflow, token-transfer behavior, mempool ordering and MEV sandwich attacks are not formalized. No correspondence with a deployed Uniswap implementation is proved. Scientific novelty and first-formalization claims have not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `DeFiConstantProductSwap.defi_constant_product_swap_master_verification_suite`.
