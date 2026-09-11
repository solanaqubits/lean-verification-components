---
id: MechanismDesignPBS
language: en
section: finance
source: Verification/MechanismDesignPBS.lean
source_sha256: f7a867205b4ad2266ff2cdd90b61ac4dfe9afb1dd78e19e5568b42041b16d138
novelty: not-assessed
---

# MechanismDesignPBS

[Section](README.md) · [Lean source](../../Verification/MechanismDesignPBS.lean)

## Verified result

Under bid ≤ MEV, profit is nonnegative and prescribed credits satisfy a balance identity. Maximality of the winning bid is an assumption.

## Assumptions and scope

The models retain their stated balance, price, and fee assumptions. They do not verify production smart-contract code, transaction ordering, or every protocol rule.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`builder_profit_nonneg`](../../Verification/MechanismDesignPBS.lean#L25)
- [`pbs_value_conservation`](../../Verification/MechanismDesignPBS.lean#L28)
- [`pbs_balance_transition_invariant`](../../Verification/MechanismDesignPBS.lean#L44)
- [`mechanism_design_pbs_master_verification_suite`](../../Verification/MechanismDesignPBS.lean#L69)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
