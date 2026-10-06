# Public verification record

[Knowledge base](README.md) · [Release v0.5.9](../docs/release-v0.5.9.en.md)

This release contains 111 direct imports, 151 Lean files under Verification/ and
11,063 project declarations. Exact proof-source hashes are recorded in
[validation_snapshot.json](../tools/validation_snapshot.json).

Public validation passed: 3533 strict build jobs, 46 tests with no skips, and two audits covering 11063 declarations.

Reproduce with:

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/check_knowledge.py
python3 scripts/generate_chip_manifest.py --check
```

Both audits permit only `propext`, `Classical.choice`, and `Quot.sound`.
The pinned independent axiom-audit complements the complete local verifier.
The CLI has no `audit-all` or `test-all` subcommands.

## Operational snapshot scope

DistributedChandyLamportSnapshot derives saved-cut consistency and exact completed-channel contents from two-process FIFO transitions. Open-channel recording has separate received-so-far semantics. There is one snapshot instance; no failures, arbitrary n-node topology, fairness, eventual completion or completion detector are verified.

All 152 Lean sources, including the root file, match private snapshot `a6fafc6f74f01dcd5de7b2d5a216f47834af0080` byte-for-byte.

## Exact QPE scope

QuantumPhaseEstimation has two control qubits and a one-qubit complex target. Controlled U/U² derive phase kickback from an exact eigenstate equation; the inverse Fourier transform returns the correct basis state. The four supported phases are 0, 1/4, 1/2 and 3/4. A normalized eigenstate and norm-preserving complex-linear operator are supplied. Physical measurement, preparation, gate noise and approximate QPE are not certified.

## Numerical scope

- NumericBinaryGrid supplies the exact binary64 magnitude decoder and parity lemmas.
- NumericRoundingCertificates checks rational interval and exact-midpoint witnesses,
  with signed zero, subnormals and overflow. The mathematical checker is not a
  verification of Python or CPU instructions.
- NumericRealRounding transports rational endpoint certificates to enclosed real values.
- NumericSQLIntervalBounds encloses `sqrt(hbar/(mass*frequency))` under explicit
  positive input intervals and containment hypotheses. Physical calibration is external;
  the separate gap expression is handled by NumericSQLGapBounds.
- NumericSQLGapBounds derives affine gap bounds, exact zero iff balance for positive
  parameters, canonical +0 and composition with real rounding. Rationalization,
  exact cell-boundary comparison and the new SimLab search are not formalized.
- NumericCertificateDigestBridge composes explicit pure digest/parser parameters
  with the mathematical checker. Expected digest, parser, grid and SQL inputs are
  external context. SHA-256, JSON/RFC 8259, Python equivalence, byte binding of those
  inputs and source authenticity are not proved. Digest equality is not byte equality.

Historical indeterminate intervals remain indeterminate. Later exact-midpoint or
exact-zero evidence is separate. No simulation runtime or full simulation archive
is distributed. The curated rounding provenance JSON is external metadata; its
source simulation paths are not included in this package.

The earlier placement certificate retains its exact 256 rational records, boundary
and pairwise-disjointness guarantees. The deterministic converter is checked
externally; its JSON parser and hashing are not Lean-verified.

Scalar MuSig2 does not establish cryptographic security; the forking module proves
an elementary finite-matrix bound, not a general ROM reduction. Visibility does
not prove quantum decoherence. The documented optomechanical approximation regime
is not derived in Lean. Historical hundred-module aggregation preserves these limits.

## Multiple-target Grover scope

QuantumGroverMultipleTargets proves all-subset N=4 real dynamics, all-natural-iteration
success weights, arbitrary-state norm preservation, singleton compatibility and
an invariant orthonormal plane for nonempty proper target sets. It also proves
both rank-one reflection counterexamples. No arbitrary-N search, query-complexity,
trigonometric-angle formula, separate topological-closedness theorem, physical
measurement, noise or hardware certification is claimed.

## Raft commit application scope

DistributedRaftCommitApplication and its two support modules derive actual
commit-event provenance for server and RPC prefixes, retained committed prefixes,
and ordered deterministic local application. A reachable 45-transition example
shows why an old-term majority alone is insufficient. Cross-node fold agreement
requires equality of full entries, including commands. This extension does not
prove a new global State Machine Safety theorem, liveness, client exactly-once
behavior, timeout handling, crash/recovery or fsync/WAL.

## Operational 2PC timeout scope

Two independent participants and a stopped coordinator distinguish safe pre-vote
abort from unsafe forced decisions on identical prepared local views. Under both
prepared and coordinator stopped, no queued decision is equivalent to no finite
continuation reaching a terminal participant. Other packets may remain in flight.
Decision delivery is possible, not guaranteed. Fairness, recovery, peer termination,
3PC and disk durability are not claimed.

## Two-participant 3PC scope

The fixed two-participant model uses bounded request/response queues and crash-stop
failures. Reachable agreement includes stopped terminal decisions. Completion paths
and eventual completion under weak fairness are separate theorems. Exact surviving
membership, unique coordinator appointment and atomic epoch fencing are external
contracts. No arbitrary-n protocol, dynamic joining, network partition tolerance,
crash recovery or runtime implementation is certified.
