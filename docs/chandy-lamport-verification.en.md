> Historical private validation record. Its 43 tests and original-workspace observations describe the private integration. Public release measurements are recorded in [v0.5.3](release-v0.5.3.en.md).

# Operational Chandy–Lamport snapshot validation

## Source and model

This change starts from private source `fb6176fdd9f0186c8c1406b7bf611d2b6b09af35` and adds `Verification/DistributedChandyLamportSnapshot.lean`.

Module SHA-256: `a60f818107358100b96662387c2c0763ba801549a0ba06715e7c4fae950730be`.

The model has two processes, one FIFO queue in each direction, one snapshot instance, atomic local capture plus outgoing marker insertion, and unbounded lossless queues. Application sends and receives advance local event counters; receives add the payload to a natural-number accumulator. Send ordinals and snapshot-phase stamps are ghost history metadata. They distinguish repeated payloads and are assigned by the operational rules. Receipt and transit recording do not branch on the sender's phase stamp.

The ordinary receive rule checks only the queue head. Safety is established by induction from the empty initial state, not imposed as an additional transition guard. The invariant explicitly separates pre-snapshot packets, the marker, and post-snapshot packets. A separate invariant connects phase-tagged histories to the lists actually saved in each node's local snapshot.

## Results and regressions

- `fifo_marker_ordering`: both channel queues have the proved marker separation shape.
- `no_future_messages_in_snapshot`: a post-snapshot send at the delivery head requires an already captured receiver.
- `chandy_lamport_cut_consistency`: each receive in an actual saved cut has its matching send in the peer's saved cut.
- `transit_channel_soundness`: after this channel's marker is consumed, transit is exactly the saved sender list filtered by absence from the saved receiver list, in order and with packet identity preserved.
- `transit_partial_soundness`: before closure, recording describes crossing receipts observed so far.
- `snapshots_preserved` and `closed_transit_preserved`: later traffic cannot overwrite saved local state or completed channel contents.
- `reachable_mirror`: results apply symmetrically to the other direction.

Kernel-checked regressions execute nonempty traffic with two equal payloads and distinct IDs, initiation at the receiver, both marker branches, partial and completed transit, a nonempty saved receive cut, and post-snapshot traffic. An invalid queue with a new packet before its marker has an ordinary head-receive transition but is proved unreachable. Thus the safety proof is not a consequence of a hidden safety check in `Step`.

## Reproduction

Use the repository's pinned Lean toolchain and dependencies:

```bash
python3 tools/verifier_skill.py verify Verification/DistributedChandyLamportSnapshot.lean
python3 tools/verifier_skill.py audit Verification/DistributedChandyLamportSnapshot.lean
python3 tools/verifier_skill.py integrate Verification.DistributedChandyLamportSnapshot ChandyLamportFormalSuite
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/check_knowledge.py
```

The independent project audit uses `leanprover-community/axiom-audit` v0.1.2, pinned and checked at commit `46024e005996495c65ef609368e11ab39c4222e3`, with the allowlist `propext,Classical.choice,Quot.sound`. The CI workflow records the tool invocation. There are no `audit-all` or `test-all` CLI subcommands.

## Measured verification

Strict `lake build --wfail` completed with **3523 jobs** and no warnings. `verify-all` freshly compiled all **141** Verification files and audited **9074 declarations**, with unchanged source hashes. The independent pinned audit counted the same **9074** declarations. Both permit only `propext`, `Classical.choice`, and `Quot.sound`; there are no violations. Module `verify` and `audit` each checked **363** declarations in the new module's project import closure.

The central registry has **105 direct imports**. A second integration plan is empty. The catalog checks all 141 module cards across 12 sections and local links in 328 Markdown files. Exact source hashes are in [validation_snapshot.json](../tools/validation_snapshot.json).

The full private test discovery ran **43 tests in 72.886 seconds**, with no failures, errors, or skips. Export regressions check byte equality of every Verification source, the English-only catalog, provenance inputs, and absence of private history. All integration recipes are idempotent. Public export is prepared; no public release was performed by this change.

## Scope

This proves two-process operational safety for the captured local prefixes, not liveness or a general arbitrary-event happens-before graph theorem. Completed channel equality has an explicit closure premise; it is not claimed for partial recording. No fairness, eventual marker delivery, distributed completion detector, arbitrary number of nodes, failures, recovery, lossy/non-FIFO channels, multiple concurrent snapshots, or production implementation is verified. No reordering theorem reconstructing an entire application execution is included.

The original algorithm is described by [Chandy and Lamport (1985)](https://lamport.azurewebsites.net/pubs/chandy.pdf). The model is the documented two-process specialization.

The suite extends `DistributedSystemsFullSuite` in `MasterSuiteComponents`, preserving prior fields and constructors. Existing aggregates using that structure inherit the new field. The historical hundred-import manifest remains unchanged; repository counts are measured separately. All prior numerical certificate limitations, including rationalization, cell search, Python/JSON/SHA-256 and external input binding, remain unchanged.

Implementation and validation run in an isolated clone. No simulation package is imported by the new module, and this task does not write to the original workspace or its `simulations/` directory. A public release is separate from this private integration.

## Original workspace preservation

The before/after control snapshots confirmed the same original workspace HEAD and all **406 tracked file hashes**. The original simulation directory was concurrently active: its metadata inventory increased from 31,345 to 35,441 entries and 14 previously listed entries changed (including directories). This task performed no writes there. Consequently, this report does not claim directory-wide immutability of the concurrently updated SimLab tree. Implementation and builds reside in the isolated clone; validation logs and control snapshots are in external temporary paths.
