---
id: CollatzParity
language: en
section: collatz
source: Verification/CollatzParity.lean
source_sha256: ba871a54d220b28b8b57bc3bb82e5f106e2ecdad51989d3230da37fa0dd96141
novelty: not-assessed
---

# CollatzParity

[Section](README.md) · [Lean source](../../Verification/CollatzParity.lean)

## Verified result

Exact branch formulas for parity and residues modulo 4 and 8.

## Assumptions and scope

Finite trajectories, congruences, and scalar estimates do not prove the Collatz conjecture. Weighted coefficient identities do not establish the behavior of every deterministic orbit.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`collatz_odd_step_even`](../../Verification/CollatzParity.lean#L10)
- [`collatzIter_two_odd`](../../Verification/CollatzParity.lean#L18)
- [`collatz_mod4_one_div4`](../../Verification/CollatzParity.lean#L34)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
