---
id: DistributedRaftNetworkLogLemmas
language: en
section: distributed
source: Verification/DistributedRaftNetworkLogLemmas.lean
source_sha256: 844424271abff08b9e796939546153b4c92bc30010558f9f273812e3535f649e
novelty: not-assessed
status: reviewed
---

# DistributedRaftNetworkLogLemmas

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedRaftNetworkLogLemmas.lean)

## Scope

This supporting module proves list-level facts needed by the global asynchronous Raft induction. It imports the existing operational state machine and leaves `Step`, `Reachable`, and the merge algorithm unchanged.

`LogMatching a b` means that equal terms at a shared list position imply equality of both prefixes through that position. These results concern lists of `LogEntry`; they do not independently prove that the `index` field equals the one-based list position.

## Proved statements

- `matching_refl`, `matching_symm`, and the take/prefix lemmas establish reflexivity, symmetry, and preservation when either or both input logs are restricted to prefixes.
- `matching_entry_eq` derives equality of complete entries, including their commands, from equal terms at an aligned position and Log Matching of the two logs.
- `matching_compatible_slice` derives `CompatibleEntries` between the old suffix and a finite contiguous incoming slice. Compatibility is a consequence of the input Log Matching relation, not an additional operational guard.
- `termAt_prefix` preserves the predecessor term under prefix extension, provided the requested predecessor index is at most the shorter log's length. Index zero retains the sentinel behavior of `termAt`.
- `matching_predecessor_prefix` proves equality of prefixes through `prev` from Log Matching, `prev ≤ source.length`, and the successful predecessor test `prevMatches old prev (termAt source prev)`.
- `matching_append_entries_choice` combines those facts: processing `(source.drop prev).take count` yields either the unchanged old log or `source.take (prev + count)`.

The last result uses the actual `mergeSuffix` behavior. An exhausted matching batch retains the old suffix; the first conflicting term replaces it. It does not model every message as unconditional truncation followed by concatenation. The count may exceed the available source suffix; `List.take` handles that case.

## Preconditions and boundaries

The local merge result assumes Log Matching of the old log and the historical source. This module does not assert that arbitrary logs or injected messages satisfy that premise. [DistributedRaftNetworkInduction](DistributedRaftNetworkInduction.md) supplies the reachable-state argument that discharges it for the modeled network.

These list lemmas do not establish Leader Completeness, preservation of committed entries, `VoterEvolution`, crash recovery, dynamic membership, or liveness. They are auxiliary proof infrastructure rather than a separate protocol or implementation certificate.

## Validation

Strict full-project build, per-module verification/audit of the importing network suite, `verify-all`, independent axiom audit, and the complete live test suite passed. Exact source hashes and project counts are in the [validation record](../VERIFICATION.en.md). No disallowed axioms were found; mathematical novelty is not assessed.
