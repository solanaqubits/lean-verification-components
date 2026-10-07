# Public verification record

[Knowledge base](README.md) · [Release v0.5.14](../docs/release-v0.5.14.en.md)

This release contains 116 direct imports, 158 Lean files under Verification/
and 12,210 project declarations. The two nested specification files belong to
meta-audit tooling, not additional subject suites. Exact hashes are recorded in
[validation_snapshot.json](../tools/validation_snapshot.json).

Public validation passed: 3541 strict build jobs, 61 live tests with no failures
or skips (247.364 seconds), and two full audits covering 12210 declarations.
Both permit only `propext`, `Classical.choice`, and `Quot.sound`.
The strict registry AxiomAudit hook also passed; it checks selected theorems and
is separate from the complete independent audit.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
```

## General QPE scope

[QuantumPhaseEstimationGeneral](03_quantum_physics_and_optics/QuantumPhaseEstimationGeneral.md)
derives the output for an arbitrary finite target and n-bit control register from
controlled powers and the inverse Fourier transform. Fourier unitarity, exact
dyadic recovery, probability normalization and the nearest-sample lower bound
4/π² hold in the exact complex model. The measured-output claims use a supplied
normalized eigenvector of a unitary operator. Both midpoint choices, modular
wraparound, negative phases, the singular geometric-sum branch and n=0 are covered.
The n=2 bridge identifies the complete old operational output.
Eigenstate preparation, gate synthesis and cost, physical noise, decoherence and
full Shor are not proved. Python, JSON/SHA-256 and SimLab byte binding remain external.

## Operational snapshot scope

DistributedChandyLamportSnapshot derives saved-cut consistency and exact completed-channel contents from two-process FIFO transitions. Open-channel recording has separate received-so-far semantics. There is one snapshot instance; no failures, arbitrary n-node topology, fairness, eventual completion or completion detector are verified.

All 159 Lean sources, including the root file, match private snapshot `9970e9170023db76f1a392a7235bb5a1af6778e2` byte-for-byte.

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

## Static-epoch CMH scope

The graph is fixed within each detector execution. Probe provenance and detection
soundness are inductive invariants; eventual detection after initiation requires
the explicit payload-delivery contract. Graph replacement requires an external
isolated reset. The dynamic counterexample refutes a naive send-time-only check,
not the original CMH protocol. See the [release scope](../docs/release-v0.5.10.en.md).

## Arbitrary-phase Grover scope

The one-target C^4 model proves complex linearity, explicit adjoints and inverse
identities, Hermitian norm preservation and a complex plane invariant under every
pair of real phases. Equal phases from uniform have
P(phi)=1-3*(1+cos(phi))^2/16 and P=1 iff cos(phi)=-1. At pi the raw step is the
negative of the canonical step; measurement weights agree. This is not a general
Hoyer phase-matching theorem or Long iteration schedule. Hardware, noise and
Python/JSON/SHA-256/SimLab byte binding remain outside the result.

## Simon scope

The complex H/XOR/H circuit yields exact uniform probability 2/(2^n) on s-perp under SimonPromise with nonzero s. Recovery requires orthogonal rows spanning rank n-1 over F2. No sample-count bound or implemented Gaussian solver is certified. See the [Simon card](03_quantum_physics_and_optics/QuantumSimonsAlgorithm.md).
