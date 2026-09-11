---
id: LamzouriOptimization
language: en
section: lamzouri
source: Verification/LamzouriOptimization.lean
source_sha256: b5b52b63a70921cc59280bfcae6e3c254647027f4d7650dfdb63cc54903b7bf4
novelty: not-assessed
---

# LamzouriOptimization

[Section](README.md) · [Lean source](../../Verification/LamzouriOptimization.lean)

## Verified result

Rewriting quotient comparisons, endpoint values, and a bound above 0.6725 throughout [0,2].

## Assumptions and scope

The conclusions concern the specified trial family and functional. They are not a proof of a general analytic number theory bound outside that model.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`rayleigh_gt_iff`](../../Verification/LamzouriOptimization.lean#L10)
- [`norm_functional_at_zero`](../../Verification/LamzouriOptimization.lean#L14)
- [`spectral_functional_at_zero`](../../Verification/LamzouriOptimization.lean#L17)
- [`lamzouri_master_verification_suite`](../../Verification/LamzouriOptimization.lean#L65)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
