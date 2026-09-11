---
id: FinslerIndicatrix
language: en
section: finsler
source: Verification/FinslerIndicatrix.lean
source_sha256: 125d5fe872f2c6af17cbda8167eb1f908b14ae98a7b3668ff3be006e246e5b46
novelty: not-assessed
---

# FinslerIndicatrix

[Section](README.md) · [Lean source](../../Verification/FinslerIndicatrix.lean)

## Verified result

Positivity of a prescribed diagonal energy, a midpoint product bound, and preservation of the indicatrix by positive transformations.

## Assumptions and scope

The statements concern the defined coordinate forms and energy. They do not automatically identify this energy with a Finsler fundamental tensor or construct a general manifold theory.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`midpoint_in_positive_cone`](../../Verification/FinslerIndicatrix.lean#L19)
- [`metric_energy_nonneg`](../../Verification/FinslerIndicatrix.lean#L32)
- [`metric_energy_pos`](../../Verification/FinslerIndicatrix.lean#L36)
- [`finsler_indicatrix_master_verification_suite`](../../Verification/FinslerIndicatrix.lean#L124)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
