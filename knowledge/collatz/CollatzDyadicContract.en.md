---
id: CollatzDyadicContract
language: en
section: collatz
source: Verification/CollatzDyadicContract.lean
source_sha256: 81469d240ccf2af7b2c67135c7519951f80f8028181eaefa869baf1a9c717fb3
novelty: not-assessed
---

# CollatzDyadicContract

[Section](README.md) · [Lean source](../../Verification/CollatzDyadicContract.lean)

## Verified result

Finite iteration formulas and a decrease on the specified residue branch modulo 8.

## Assumptions and scope

Finite trajectories, congruences, and scalar estimates do not prove the Collatz conjecture. Weighted coefficient identities do not establish the behavior of every deterministic orbit.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`collatzIter_three_strict_decrease`](../../Verification/CollatzDyadicContract.lean#L12)
- [`collatzIter_three_le_sub_one`](../../Verification/CollatzDyadicContract.lean#L18)
- [`collatz_mod8_three_intermediate`](../../Verification/CollatzDyadicContract.lean#L24)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
