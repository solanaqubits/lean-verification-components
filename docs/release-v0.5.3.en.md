# Release v0.5.3 verification record

This release adds DistributedChandyLamportSnapshot: an operational two-process FIFO snapshot model, consistency of saved local cuts, and exact completed-channel transit lists. Partial recording is characterized separately. Safety is proved from transitions and initial state; it is not inserted into receive guards.

## Source and export

Private source: `520eef27466667237fff4d6ef7d9821e17f9fcfe`.
Previous public main: `6d1314aa9b273f4ca836484ebc491ed82ebd2673`.

The existing allowlisted exporter provides the source, registry integration, recipe, compiler regression, Python test, English scope card and private validation record. `MasterSuiteComponents` is synchronized because it owns DistributedSystemsFullSuite. Older exporter page templates are not allowed to overwrite current public documentation. Existing public package settings, CI, dependency manifest, license, static evidence and release history are retained. Package version is 0.5.3.

The historical MasterHundredRegistry source and import manifest are unchanged. Its distributed package type inherits the new chandy_lamport field. Prior fields, universe parameters and theorem constructors remain available.

## Fresh-build correction

The first fresh public build rejected the broad `import Mathlib.Tactic` in the private module under the enabled header linter. That import was unused: `Mathlib.Data.List.Basic` and `Mathlib.Data.List.Nodup` suffice. The public module removes exactly that one import line; all definitions and proof bodies are byte-identical. No linter or warning policy was disabled. The selected private commit remains unchanged.

Consequently, 141 of the 142 Lean source files (including the root file) match the private snapshot byte-for-byte. The sole exception is this documented one-line import deletion in DistributedChandyLamportSnapshot. A fresh strict rebuild and both audits validate the public result.

## Measured checks

- **105 unique direct imports**, **141 Lean files** under Verification/.
- Final fresh strict build: **3523 jobs**, zero warnings.
- verify-all: all **141 modules** freshly compiled, **9074 declarations** audited, source hashes unchanged.
- Independent pinned audit: **9074 declarations**, only `propext`, `Classical.choice`, `Quot.sound`.
- **40 public tests** passed in **71.860 seconds**, with zero failures, errors or skips (historical private run: 43).
- Registry integration is idempotent; the second plan is empty.
- English catalog, local links and exact 256-node placement data checked.

## Reproduction

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/check_knowledge.py
python3 scripts/generate_chip_manifest.py --check
python3 tools/verifier_skill.py integrate Verification.DistributedChandyLamportSnapshot ChandyLamportFormalSuite
```

The independent project audit uses leanprover-community/axiom-audit v0.1.2, pinned and checked at `46024e005996495c65ef609368e11ab39c4222e3`, with the allowlist `propext,Classical.choice,Quot.sound`. There are no audit-all/test-all CLI subcommands.

## Scope

Two processes have one unbounded lossless FIFO queue in each direction and one snapshot instance. Capture of a local snapshot and insertion of the outgoing marker are atomic. Application sends append to the queue; receives remove the head. Ghost send ordinals distinguish repeated payloads, and phase observations are assigned by operational rules. Transit recording uses local snapshot/closure flags, not the sender's ghost phase.

Reachability establishes marker ordering, the send/receive ledger, and consistency of the actual saved local cuts: every saved receive has its matching saved send. Once a channel's marker has been received, its recorded list equals saved sender packets absent from the receiver's saved cut, preserving order and identity. An open channel's list describes only the crossing receipts observed so far. Recorded local snapshots and closed channel lists are preserved by later transitions.

No termination, fairness, eventual marker delivery, distributed completion detection, arbitrary n-node topology, crash/Byzantine failures, recovery, dynamic routing, non-FIFO delivery or concurrent snapshot instances are modeled or proved. Nor is a general application-execution reordering theorem or production implementation certified.

The earlier numerical limitations are unchanged: rationalization, exact cell-boundary comparison and SimLab search are not formalized. Python, JSON/RFC 8259, SHA-256, authenticated provenance and binding of external parameters to bytes remain separate obligations. Digest equality does not prove byte equality. Historical indeterminate intervals retain their results alongside separate exact-zero or exact-midpoint evidence. No simulation archive is copied or physical detector behavior certified.

[Validation snapshot](../tools/validation_snapshot.json) contains the source hashes.
[Scope card](../knowledge/09_distributed_systems/DistributedChandyLamportSnapshot.md) records the theorem interfaces.
[Historical private report](chandy-lamport-verification.en.md) retains its distinct private test count and isolation observations.

Implementation and validation occur in isolated source and public clones, with independent copies of dependency artifacts and a fresh project build directory. No command writes to the original workspace or simulations. The publication consists of public main and a new annotated tag, sent atomically without force.

The original workspace HEAD and all **406 tracked file hashes** remained unchanged in the control snapshots. SimLab was concurrently active and changed its own artifacts; these were neither modified nor reverted by this release task. Directory-wide simulation immutability is therefore not claimed.
