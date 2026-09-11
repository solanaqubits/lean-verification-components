---
id: RiemannNumericBound
language: en
section: riemann
source: Verification/RiemannNumericBound.lean
source_sha256: 00149dc2ef04b7574a809590429f2caf2a270a86659e7a5855648e6c7bde61e2
novelty: not-assessed
---

# RiemannNumericBound

[Section](README.md) · [Lean source](../../Verification/RiemannNumericBound.lean)

## Verified result

A stronger bound placing the main term in (1/2,1).

## Assumptions and scope

These are bounds for explicitly defined scalar functions. No connection to zeta zeros or proof of the Riemann hypothesis is established.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`exp_one_gt_two`](../../Verification/RiemannNumericBound.lean#L10)
- [`exp_two_gt_four`](../../Verification/RiemannNumericBound.lean#L15)
- [`log_four_lt_two`](../../Verification/RiemannNumericBound.lean#L24)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
