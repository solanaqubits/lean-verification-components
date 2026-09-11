---
id: Collatz2Adic
language: en
section: collatz
source: Verification/Collatz2Adic.lean
source_sha256: bfe5f012cf5053e7519ac653e61851eb425bcea0f9eb83a7e959f0488b63041b
novelty: not-assessed
---

# Collatz2Adic

[Section](README.md) · [Lean source](../../Verification/Collatz2Adic.lean)

## Verified result

Divisibility of differences by powers of two: one accelerated step loses at most one bit of precision, and n steps lose at most n bits.

## Assumptions and scope

Finite trajectories, congruences, and scalar estimates do not prove the Collatz conjecture. Weighted coefficient identities do not establish the behavior of every deterministic orbit.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`syracuseIter_zero`](../../Verification/Collatz2Adic.lean#L18)
- [`syracuseIter_succ`](../../Verification/Collatz2Adic.lean#L19)
- [`two_pow_pred`](../../Verification/Collatz2Adic.lean#L22)
- [`collatz_2adic_master_verification_suite`](../../Verification/Collatz2Adic.lean#L92)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
