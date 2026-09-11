---
id: LamzouriMeasure
language: en
section: lamzouri
source: Verification/LamzouriMeasure.lean
source_sha256: da0afb4e03145ac77a89e5b18a52b964f9652a4962c935afefa5f18de668024b
novelty: not-assessed
---

# LamzouriMeasure

[Section](README.md) · [Lean source](../../Verification/LamzouriMeasure.lean)

## Verified result

An interval integral of a squared trial polynomial equals the functional; its minimum 1/8 is attained exactly at c=−5/2.

## Assumptions and scope

The conclusions concern the specified trial family and functional. They are not a proof of a general analytic number theory bound outside that model.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`trialPolySq_eq_decomp`](../../Verification/LamzouriMeasure.lean#L22)
- [`hasDerivAt_F0`](../../Verification/LamzouriMeasure.lean#L31)
- [`hasDerivAt_F1`](../../Verification/LamzouriMeasure.lean#L36)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
