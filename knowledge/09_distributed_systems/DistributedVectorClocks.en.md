---
id: DistributedVectorClocks
language: en
section: distributed
source: Verification/DistributedVectorClocks.lean
source_sha256: 767c56015644bb374cbe6af6a14d85c637a2ab9dc1dd9f964238e0560845d26b
novelty: not-assessed
status: reviewed
---

# DistributedVectorClocks

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedVectorClocks.lean)

## Verified result

The component preserves reflexivity, transitivity and antisymmetry of componentwise order, strict-order transitivity, both local-tick inequalities, merge as a least upper bound, and incomparability properties. VectorClock2 is an abbreviation for the existing VClock2. receive1/receive2 merge the supplied counters and increment the receiving coordinate. For both operations, the result strictly exceeds the local vector and dominates the message vector. The concrete vectors tick1(0,0) and tick2(0,0) are incomparable.

## Assumptions and limitations

These are algebraic properties of pairs of unbounded natural counters. No event identities, execution histories, message matching, network transition system or correspondence between vector order and event-level happens-before is formalized. The concurrency example proves incomparability of vectors, not independence of actual concurrent executions, and does not by itself close the event-model gap of the scalar Lamport component.

Existing definitions, theorem names and master entry point remain available. New vector_le_* names and distributed_vector_clocks_master_suite provide alternate entry points. The existing formal suite now has additional receive and concrete-incomparability fields; callers manually constructing it must provide them. No extra direct module import is introduced.

Dimensions above two, dynamic membership, interval tree clocks, vector compression, matrix clocks, overflow, failure detectors and implementation correctness are outside the model. Scientific novelty and first-formalization claims have not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `DistributedVectorClocks.distributed_vector_clocks_master_suite`.
