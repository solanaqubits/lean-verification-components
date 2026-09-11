---
id: RiemannMainTerm
language: en
section: riemann
source: Verification/RiemannMainTerm.lean
source_sha256: 022b1c10547622ff8b8d94b345d08e893c13a0e814378765b6773dd7789c5547
novelty: not-assessed
---

# RiemannMainTerm

[Section](README.md) · [Lean source](../../Verification/RiemannMainTerm.lean)

## Verified result

The specified main logarithmic term lies between zero and one on the stated domain.

## Assumptions and scope

These are bounds for explicitly defined scalar functions. No connection to zeta zeros or proof of the Riemann hypothesis is established.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`log_log_lt_log`](../../Verification/RiemannMainTerm.lean#L10)
- [`log_ratio_lt_one`](../../Verification/RiemannMainTerm.lean#L17)
- [`log_ratio_pos`](../../Verification/RiemannMainTerm.lean#L23)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
