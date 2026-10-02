---
id: DistributedRaftCommittedPrefixLemmas
language: en
section: distributed
source: Verification/DistributedRaftCommittedPrefixLemmas.lean
source_sha256: 641b24e5f6186d44e3aff84f671688ab64d90efc6d9bc2868fe473253176c203
novelty: not-assessed
status: reviewed
---

# DistributedRaftCommittedPrefixLemmas

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedRaftCommittedPrefixLemmas.lean)

## Prefix retention under partial batches

These pure list lemmas concern the existing `mergeSuffix` and `appendEntriesLog` functions. An exhausted incoming batch preserves the remaining local suffix; only the first conflicting entry replaces the remainder.

## Proved statements and assumptions

- `common_prefix_retained`: if a selected prefix belongs to both the old and source logs, any partial source batch preserves it.
- `incoming_prefix_merge`: the incoming list is a prefix of the merged result when `CompatibleEntries` equates aligned entries having equal terms.
- `transmitted_prefix_retained`: with `LogMatching`, a valid predecessor match, and `prev ≤ source.length`, the source prefix covered by the transmitted endpoint is retained.
- `covered_prefix_installed`: additionally, any selected source prefix ending by that endpoint is installed, even if absent locally.
- `source_prefix_unchanged`: replaying a source already prefixing the local log leaves the whole local log unchanged.
- `comparable_prefix_retained`: a local selected prefix survives when the source and selected prefix are comparable by prefix order.

## Boundaries

The module does not define protocol commitment. Its name describes the intended application; its assumptions must be established separately for actual network histories. These lemmas do not assume that arbitrary messages are safe, nor add prefix checks to `Step`. No election or global Leader Completeness theorem is proved here.

## Validation

Strict compilation, the full CLI audit, independent axiom auditing, and regression tests passed. See the [validation record](../VERIFICATION.en.md). Mathematical novelty is not assessed.
