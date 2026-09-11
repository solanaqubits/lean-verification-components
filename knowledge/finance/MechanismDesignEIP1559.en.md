---
id: MechanismDesignEIP1559
language: en
section: finance
source: Verification/MechanismDesignEIP1559.lean
source_sha256: 36a679379583990f8012f760536fba058e570a988d980f0c9773d1bc1c69a653
novelty: not-assessed
---

# MechanismDesignEIP1559

[Section](README.md) · [Lean source](../../Verification/MechanismDesignEIP1559.lean)

## Verified result

For a real-valued model, the multiplier lies in [7/8,9/8], fees remain positive, and equilibrium occurs at target utilization. Integer rounding and the protocol's minimum increment are not modeled.

## Assumptions and scope

The models retain their stated balance, price, and fee assumptions. They do not verify production smart-contract code, transaction ordering, or every protocol rule.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`fee_multiplier_empty_block`](../../Verification/MechanismDesignEIP1559.lean#L25)
- [`fee_multiplier_target_block`](../../Verification/MechanismDesignEIP1559.lean#L31)
- [`fee_multiplier_full_block`](../../Verification/MechanismDesignEIP1559.lean#L34)
- [`mechanism_design_eip1559_master_verification_suite`](../../Verification/MechanismDesignEIP1559.lean#L105)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
