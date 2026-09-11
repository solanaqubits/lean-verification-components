---
id: PortfolioRiskEngine
language: en
section: finance
source: Verification/PortfolioRiskEngine.lean
source_sha256: c57c9337b33adb6d2089f74509e3a996264bb1d3e76d7c41dc256bea968120b7
novelty: not-assessed
---

# PortfolioRiskEngine

[Section](README.md) · [Lean source](../../Verification/PortfolioRiskEngine.lean)

## Verified result

Nonnegative two-asset variance, a diversification bound, and strict improvement for positive weights and risks with ρ < 1.

## Assumptions and scope

The models retain their stated balance, price, and fee assumptions. They do not verify production smart-contract code, transaction ordering, or every protocol rule.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`variance_decomp`](../../Verification/PortfolioRiskEngine.lean#L37)
- [`portfolio_variance_nonneg`](../../Verification/PortfolioRiskEngine.lean#L43)
- [`diversification_effect_sq`](../../Verification/PortfolioRiskEngine.lean#L58)
- [`portfolio_risk_master_verification_suite`](../../Verification/PortfolioRiskEngine.lean#L97)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
