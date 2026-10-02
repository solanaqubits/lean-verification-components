---
id: DeFiFlashLoan
language: en
section: finance
source: Verification/DeFiFlashLoan.lean
source_sha256: 451c7fca98adb2a6a066b614ba53da903d8f275feec738b4b4b2509b0fb6f120
novelty: not-assessed
status: reviewed
---

# DeFiFlashLoan

[Section](../finance/README.md) · [Lean](../../Verification/DeFiFlashLoan.lean)

## Verified result

For reserve R > 0, fee rate f ≥ 0 and amount a ≥ 0, repayment a+a*f yields exactly R+a*f, which is at least R. If a > 0 and f > 0, this reserve strictly exceeds R. Underpayment below a+a*f yields a reserve below the fee-inclusive target R+a*f. Fees are additive at a fixed rate. The defined maximum loan equals R and is therefore bounded by R.

Key theorems: `flash_loan_solvency_invariant`, `lp_yield_strict_growth`, `underpayment_depletes_pool`, `flash_fee_additive`, and `max_flash_loan_le_reserve`.

## Assumptions and limitations

These statements concern exact real arithmetic for specified formulas. The maximum-loan definition does not enforce a ≤ R; no admission or execution transition is defined. Solvency and growth are conditional on the specified full repayment. Reserve growth is not a proved LP return or share-value property. Underpayment may still leave the reserve at or above R: repaying principal alone misses a positive fee without reducing the initial reserve. The theorem provides a strict inequality, not an executable detector or rejection mechanism.

No EIP-3156 compliance or correspondence with a deployed lender is established. Callback validation, reentrancy, multi-token batch loans, fee-on-transfer tokens, integer rounding/overflow, EVM revert and gas limits are not modeled. Scientific novelty and first-formalization claims have not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `DeFiFlashLoan.defi_flash_loan_master_suite`.
