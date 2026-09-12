---
id: DeFiERC4626Vault
language: en
section: finance
source: Verification/DeFiERC4626Vault.lean
source_sha256: 3b4f2887fa040000751d03186c0ad66125795176f92d7eaf0b7a8fd4637a3423
novelty: not-assessed
status: reviewed
---

# DeFiERC4626Vault

[Section](../finance/README.md) · [Lean](../../Verification/DeFiERC4626Vault.lean)

## Verified result

With positive total assets A and supply S, the supplied conversions a*S/A and s*A/S are mutually inverse. Adding a positive deposit a and exactly a*S/A new shares preserves A/S. Conversion to shares is homogeneous under any real scaling factor and strictly increasing in the real asset argument.

## Assumptions and limitations

VaultState requires A > 0 and S > 0, excluding empty vaults. The raw conversion functions accept arbitrary real arguments; positivity of reserves is provided by the theorems using VaultState. Round trips permit arbitrary real amounts, including negative values. The deposit theorem assumes a > 0 and exact proportional minting. It proves equality of scalar ratios, not a complete state-transition or token-transfer protocol. There is no independent continuity theorem.

No Solidity integer rounding (floor/ceil), fees, empty-vault initialization, donation/inflation attack model, virtual shares/assets, preview operations, redemption limits, authorization, reentrancy or deployed contract is modeled. Exact round trips and strict monotonicity are properties of this real model, not a proof of ERC-4626 implementation compliance. The module does not establish attack resistance or all requirements of the standard.

## Value and novelty

Exact proportional accounting identities that can serve as a reference for later rounding-aware models and error bounds. Scientific priority and first formalization have not been assessed.

## Verification

[Validation record](../VERIFICATION.en.md). Entry point: `DeFiERC4626Vault.defi_erc4626_master_verification_suite`.
