---
id: RiemannBounds
language: en
section: riemann
source: Verification/RiemannBounds.lean
source_sha256: be29fac537aae9c3f24c9acbf684facd21c765745e84c364fe71175d3f06a011
novelty: not-assessed
---

# RiemannBounds

[Section](README.md) · [Lean source](../../Verification/RiemannBounds.lean)

## Verified result

Two-sided bounds for the explicitly defined kappaCrit with coefficient −1/8, for n ≥ 1000000.

## Assumptions and scope

These are bounds for explicitly defined scalar functions. No connection to zeta zeros or proof of the Riemann hypothesis is established.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`nat_cast_ge_million`](../../Verification/RiemannBounds.lean#L23)
- [`real_n_pos`](../../Verification/RiemannBounds.lean#L27)
- [`log_n_gt_one`](../../Verification/RiemannBounds.lean#L33)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
