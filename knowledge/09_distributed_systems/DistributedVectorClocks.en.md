---
id: DistributedVectorClocks
language: en
section: distributed
source: Verification/DistributedVectorClocks.lean
source_sha256: f8ca20c92f8de535fd77073f7fed664650f9f150d079e3763dbf0c8de3c683e0
novelty: not-assessed
status: reviewed
---

# DistributedVectorClocks

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedVectorClocks.lean)

## Verified result

Componentwise comparison of two natural-number counters is reflexive, transitive and antisymmetric. Its strict variant (comparison and inequality) is transitive. Either local tick strictly increases the vector. Componentwise maximum is commutative and is a least upper bound: both input bounds and minimality against every common upper bound are proved. Incomparability is symmetric and irreflexive, with witnesses (1,0) and (0,1).

## Assumptions and limitations

VClock2 contains exactly two unbounded natural counters. The predicates le and lt describe vector order. concurrent means incomparability, not an independently defined relation on network events. No event histories, send/receive actions, process-order relation, message graph or timestamp assignment are encoded. Thus no equivalence between vector order and an independently defined happens-before relation is proved.

merge is only componentwise maximum; a full receive transition that merges and then ticks is not specified. These lemmas do not prove delivery guarantees, causal consistency or independence of real events. N > 2 and dynamic membership, matrix clocks, asynchronous delivery, counter overflow and network failures are outside this model. The partial-order laws are explicit theorems; no Lean PartialOrder instance is installed.

## Value and novelty

Reusable counter-order and least-upper-bound lemmas for future distributed execution models. Mathematical novelty and first-formalization claims have not been assessed.

## Verification

[Validation record](../VERIFICATION.en.md). Entry point: `DistributedVectorClocks.distributed_vector_clocks_master_verification_suite`.

- [`lt_trans`](../../Verification/DistributedVectorClocks.lean#L26)
- [`merge_le`](../../Verification/DistributedVectorClocks.lean#L57)
- [`concurrent_witness_exists`](../../Verification/DistributedVectorClocks.lean#L70)
