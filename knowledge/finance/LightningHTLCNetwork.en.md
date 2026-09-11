---
id: LightningHTLCNetwork
language: en
section: finance
source: Verification/LightningHTLCNetwork.lean
source_sha256: 83937644dc44591e00a2f26eeca72f72beada6dd6371d45ec05aad8dee3eeca0
novelty: not-assessed
---

# LightningHTLCNetwork

[Section](README.md) · [Lean source](../../Verification/LightningHTLCNetwork.lean)

## Verified result

Conservation of free plus locked funds, decreasing timelocks, and a neutral intermediary balance. No preimage check is modeled.

## Assumptions and scope

The models retain their stated balance, price, and fee assumptions. They do not verify production smart-contract code, transaction ordering, or every protocol rule.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`capacity_lock_invariant`](../../Verification/LightningHTLCNetwork.lean#L35)
- [`capacity_claim_invariant`](../../Verification/LightningHTLCNetwork.lean#L43)
- [`capacity_timeout_invariant`](../../Verification/LightningHTLCNetwork.lean#L51)
- [`lightning_htlc_master_verification_suite`](../../Verification/LightningHTLCNetwork.lean#L131)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
