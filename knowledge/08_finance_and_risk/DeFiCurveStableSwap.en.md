---
id: DeFiCurveStableSwap
language: en
section: finance
source: Verification/DeFiCurveStableSwap.lean
source_sha256: 5dcb36a870fefc4c22a12043abfb4b8ce882ab17e3276e581390ee16361bef11
novelty: not-assessed
status: reviewed
---

# DeFiCurveStableSwap

[Section](../finance/README.md) · [Lean](../../Verification/DeFiCurveStableSwap.lean)

## Verified result

The specified two-asset real residual vanishes at x = y = D/2. At A = 0 and nonzero D, x and y, zero residual is equivalent to 4xy = D². Both the original sufficiency theorem and an explicit equivalence theorem are included. Simultaneous sum and product balance implies zero residual for any A. Scaling D, x and y by the same nonzero lambda scales the residual by lambda.

## Assumptions and limitations

StableSwap2Pool records A ≥ 0 and D, x, y > 0 but does not require a zero residual. The theorems take scalar arguments independently of that structure. The balance statements retain D ≠ 0; the equivalence needs it because D = 0 gives a zero residual at A = 0 without fixing xy. Homogeneity assumes x, y and lambda are nonzero, and is algebraic even for negative lambda; preservation of positive pool parameters requires positive scaling.

This is a static two-asset residual model with the displayed 4A convention. Simultaneous sum and product balance is not a proof of an A → infinity limit. Neither N > 2 assets, a Newton solver for D, existence or uniqueness of a positive solution, swap transitions, slippage monotonicity, integer rounding, dynamic fees nor deployed Curve contract correctness is formalized.

## Value and novelty

Reusable exact algebraic checks for balanced and rescaled configurations and the zero-amplification boundary. Mathematical novelty and first-formalization status have not been assessed.

## Verification

[Validation record](../VERIFICATION.en.md). Entry point: `DeFiCurveStableSwap.defi_curve_stableswap_master_verification_suite`.

- [`stableswap_zero_amplification_iff`](../../Verification/DeFiCurveStableSwap.lean#L42)
- [`stableswap_scale_homogeneity`](../../Verification/DeFiCurveStableSwap.lean#L66)
