---
id: RiemannExplicitBound
language: en
section: riemann
source: Verification/RiemannExplicitBound.lean
source_sha256: 4a5992a2a527e2e056b7735e593bafc6cdc8c5e440c56e8bd702d7c1ae482553
novelty: not-assessed
---

# RiemannExplicitBound

[Section](README.md) · [Lean source](../../Verification/RiemannExplicitBound.lean)

## Verified result

The bounds kappaCrit > 63/128 > 0.49 and kappaCrit < 1, collected in a formal suite.

## Assumptions and scope

These are bounds for explicitly defined scalar functions. No connection to zeta zeros or proof of the Riemann hypothesis is established.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`log_sq_gt_sixteen`](../../Verification/RiemannExplicitBound.lean#L10)
- [`inv_log_sq_lt_one_sixteenth`](../../Verification/RiemannExplicitBound.lean#L16)
- [`neg_term_gt_neg_one_over_128`](../../Verification/RiemannExplicitBound.lean#L22)
- [`riemann_master_verification_suite`](../../Verification/RiemannExplicitBound.lean#L63)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
