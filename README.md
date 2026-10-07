# Mathematical Verification Components in Lean 4

[![Lean verification](https://github.com/solanaqubits/lean-verification-components/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/solanaqubits/lean-verification-components/actions/workflows/lean_action_ci.yml)

Machine-checked mathematical components built with Lean 4 and Mathlib: algebraic
invariants, finite computations, conditional protocol properties, and explicit
scalar models. Browse the proofs by subject, inspect their assumptions, and reuse
the components in larger formal developments.

**[Knowledge base](knowledge/README.md)** · **[Results and value](knowledge/SUMMARY.en.md)** ·
[Technical reference](docs/verification-details.en.md)

## Proof sections

| Section | Focus |
|---|---|
| [Collatz and discrete dynamics](knowledge/collatz/README.md) | Finite orbits, congruences, and coefficient bounds |
| [Explicit logarithmic bounds](knowledge/riemann/README.md) | Prescribed analytic functions |
| [Almost-complex algebra](knowledge/hopf/README.md) | Algebraic identities and cross products |
| [Polynomial functionals](knowledge/lamzouri/README.md) | Integrals, quotients, and exact minima |
| [Coordinate geometry](knowledge/finsler/README.md) | Forms, polarization, and diagonal transformations |
| [Proof certificates and DAGs](knowledge/proof-graphs/README.md) | Conditional checker soundness |
| [Cryptographic algebra](knowledge/cryptography/README.md) | Diffusion, traces, folding, and commitment identities |
| [Quantum algebra, photonics, and mechanics](knowledge/quantum-physics/README.md) | Matrices, symmetries, and prescribed energy models |
| [Finance and mechanisms](knowledge/finance/README.md) | Balances, reserves, fees, and portfolio risk |
| [Distributed consensus](knowledge/distributed/README.md) | Quorums, reachable Log Matching, and operational Leader Completeness |
| [Registry and audit](knowledge/verification/README.md) | Selected suites and axiom dependencies |

## Verified snapshot

The [validation record](knowledge/VERIFICATION.en.md) covers **154 Lean files** under
`Verification/` and **114 direct MasterSuite imports**. There are **11,588 audited
declarations**, including generated declarations, with only `propext`,
`Classical.choice`, and `Quot.sound`. These are declarations, not independent theorems.

## Release v0.5.12

[Simon](knowledge/03_quantum_physics_and_optics/QuantumSimonsAlgorithm.md) derives
the complex two-register circuit and exact uniform weights on s-perp under the
nonzero-period promise. The unique nonzero solution is recovered when the
orthogonal observations span rank n-1 over F2. Sampling complexity and physical
implementation remain outside scope. See the [public release report](docs/release-v0.5.12.en.md)
and [Reservoir readiness](docs/reservoir-readiness.en.md).

**3537 strict build jobs**, **49 public live tests**, no warnings or skips.

## Earlier additions in v0.5.11

[Arbitrary-phase Grover](knowledge/03_quantum_physics_and_optics/QuantumGroverArbitraryPhase.md)
proves complex unitarity and invariant-plane preservation for every real phase pair
in dimension four with one marked item. For equal phases and the uniform input,
P(phi)=1-3*(1+cos(phi))^2/16; exact success is equivalent to cos(phi)=-1.
The canonical bridge at pi includes a global minus sign. This case does not
establish a noncanonical fractional correction of overshoot.
See the [public release report](docs/release-v0.5.11.en.md). **3535 strict build jobs**, **48 public tests**, no warnings or skips.

## Earlier additions in v0.5.10

[Static-epoch AND deadlock detection](knowledge/09_distributed_systems/DistributedChandyMisraHaasDeadlock.md)
proves probe provenance and detection soundness in a fixed wait graph, with
progress under explicit delivery assumptions and a dynamic phantom counterexample.
See the [public release report](docs/release-v0.5.10.en.md).

## Earlier additions in v0.5.9

[Two-participant 3PC](knowledge/09_distributed_systems/DistributedThreePhaseCommit.md)
adds operational safety, recovery and conditional completion. Accurate membership,
unique backup appointment and atomic epoch fencing are external contracts.
Eventual completion additionally requires a stable live view and weak action fairness.
See the [public release report](docs/release-v0.5.9.en.md).

## Earlier additions in v0.5.8

[Operational 2PC timeouts](knowledge/09_distributed_systems/DistributedTwoPhaseCommitTimeout.md)
derives safe pre-vote abort, reachable-history indistinguishability and the unsafety
of unilateral prepared decisions based only on a timeout. With both participants
prepared and the coordinator stopped, blocking is characterized by absence of
queued decision packets. A decision in flight permits a delivery step; fairness,
recovery and completion of both participants are not established.
See the [public release report](docs/release-v0.5.8.en.md).

## Earlier additions in v0.5.7

[Raft commit application](knowledge/09_distributed_systems/DistributedRaftCommitApplication.md)
derives commit-index provenance, prefix retention and ordered deterministic local
application from operational traces. The package includes a reachable 45-transition
old-term-majority counterexample. Cross-node fold agreement requires equality of
full entries, including commands; no new global State Machine Safety is claimed.
See the [public release report](docs/release-v0.5.7.en.md).

## Earlier additions in v0.5.6

[QuantumDeutschJozsaGeneral](knowledge/03_quantum_physics_and_optics/QuantumDeutschJozsaGeneral.md)
proves the n-qubit Hadamard transform, XOR-ancilla phase kickback, circuit-derived
amplitudes and zero-error classification under the constant-or-balanced promise.
It covers n=0, exact one-qubit compatibility and counterexamples outside the promise.
Physical implementation, gate synthesis and complexity bounds are not claimed.
See the [public release report](docs/release-v0.5.6.en.md).

## Earlier additions in v0.5.5

[QuantumGroverMultipleTargets](knowledge/03_quantum_physics_and_optics/QuantumGroverMultipleTargets.md)
proves exact N=4 real-amplitude dynamics for every target subset and every natural
iteration count, arbitrary-state norm preservation, the invariant symmetric plane
for nonempty proper target sets and exact compatibility with the original singleton
model. Two counterexamples delimit agreement with rank-one reflection.
Arbitrary N, oracle query complexity, fractional phase rotations, physical noise
and hardware remain outside scope. Born-rule interpretation is external.

See the [public release report](docs/release-v0.5.5.en.md).

## Earlier additions in v0.5.4

[QuantumPhaseEstimation](knowledge/03_quantum_physics_and_optics/QuantumPhaseEstimation.md)
proves controlled U/U² phase kickback, inverse Fourier cancellation and deterministic
recovery of the exact phases 0, 1/4, 1/2 and 3/4. The target operator preserves norm,
and its normalized exact eigenstate is supplied as an input hypothesis.
Approximate QPE, spectral leakage/error bounds, eigenstate preparation, noisy gates
and physical quantum hardware are outside scope.

See the [public release report](docs/release-v0.5.4.en.md).
That report records source correspondence and regression coverage. The fresh strict build passed **3524 jobs** and all **41 public tests** passed without skips.

## Earlier additions in v0.5.3

[DistributedChandyLamportSnapshot](knowledge/09_distributed_systems/DistributedChandyLamportSnapshot.md)
derives saved-cut consistency and exact completed-channel transit lists from
explicit two-process FIFO transitions. Partial recording has a separate theorem.
Termination, failures and arbitrary network topologies are not proved.

The public module removes one unused broad tactic import to pass the enabled
header linter on a fresh build; definitions and proof bodies are unchanged.
See the [public release report](docs/release-v0.5.3.en.md).
That report records source correspondence. The fresh strict build passed **3523 jobs** and all **40 public tests** passed without skips.

## Earlier additions in v0.5.2

[NumericSQLGapBounds](knowledge/12_numeric_certificates/NumericSQLGapBounds.md)
proves the affine enclosure of `G=A/I+B*I-2*sqrt(A*B)`, its exact-zero balance
criterion for positive parameters, canonical +0 and composition with real rounding.
Exact zero is distinct from a positive midpoint underflowing to +0.
Historical indeterminate records are retained alongside separate exact evidence.

Rationalization, exact cell-boundary comparison, the SimLab cell-search algorithm,
Python, JSON/SHA-256 and external input-byte binding remain outside these proofs.
The strict build passed 3,522 jobs and all 39 public tests passed without skips.
See the [public release report](docs/release-v0.5.2.en.md).

## Earlier additions in v0.5.1

This release adds exact binary rounding certificates, a real-input extension,
conditional enclosures of `sqrt(hbar/(mass*frequency))`, and a conditional bridge
through caller-supplied digest and parser functions. Three registry suites are
implemented by five Lean source files. The strict public build passed 3,521 tasks and all 38 public tests passed without skips. See the [release record](docs/release-v0.5.1.en.md).

SHA-256 implementation, JSON/Python conformance, authenticated provenance and the
separate SimLab gap `A/I+B*I-2*sqrt(A*B)` remain outside these results. Historical
indeterminate interval records are preserved; separate exact evidence does not
rewrite them.

## Earlier additions in v0.5.0

This release reaches **100 direct registry imports**, with three new domain
packages and an acyclic milestone registry. It adds five Lean files in total.

- [Time interval envelopes](knowledge/09_distributed_systems/DistributedMarzulloAlgorithm.md):
  truth inclusion under an explicit fault bound; maximum-overlap localization is
  refuted by a counterexample. No full NTP implementation is claimed.
- [Elementary transcript forking](knowledge/07_cryptography/CryptoTranscriptForkingLemma.md):
  finite matrix counting and scalar extraction, not the general multi-query
  Bellare–Neven lemma or a ROM security proof.
- [Beam splitter](knowledge/03_quantum_physics_and_optics/QuantumBeamSplitterTransform.md):
  real mode and finite two-boson norm preservation, with an ideal balanced HOM zero;
  complex phases, full Fock space, and physical detectors remain outside scope.
- [Milestone registry](knowledge/11_meta_registry/MasterHundredRegistry.md):
  selected existing guarantees assembled without changing hypotheses.
  `MasterSuiteComponents` prevents cyclic imports and preserves component names.
  The import count is not a count of independent domain results.

## Earlier additions in v0.4.5

This release adds finite-field batch counting and conditional scalar noise
optimization, bringing the registry to 96 direct imports.

- [Schnorr batch verification](knowledge/07_cryptography/CryptoSchnorrBatchVerification.md)
  proves completeness and exact accepting fractions `1/q` and `(1/q)^k` for
  a fixed nonzero discrepancy over a prime field. The coefficient space contains
  all vectors, including zeros. Uniform independent sampling is the interpretation
  of the finite counting ratios, not an implemented sampler. EUF-CMA security,
  CSPRNG correctness, and the BIP340 coefficient algorithm are outside scope.
- [Conditional standard quantum limit](knowledge/03_quantum_physics_and_optics/QuantumStandardQuantumLimit.md)
  proves the attained minimum `2*sqrt(A*B)`, balance, and unique positive optimizer
  `sqrt(A/B)` of `A/I + B*I`. SQL-shaped bounds require explicit calibration.
  The omitted noise correlation term is a modeling choice; no physical derivation
  of calibration or detector certification is claimed.

## Earlier additions in v0.4.4

Release v0.4.4 added two scalar algebraic models, bringing the registry to 94 direct imports.

- [MuSig2-style aggregation](knowledge/07_cryptography/CryptoMuSig2Aggregation.md)
  proves two-signer, two-nonce completeness and a restricted barrier to naive key
  subtraction. Weights and challenges are supplied real scalars. Hash-based
  rogue-key resistance, secp256k1, and the two-round network protocol are not proved.
  Fixed weights admit a chosen target key; scalar public keys reveal their secrets.
- [Interference visibility](knowledge/03_quantum_physics_and_optics/MithraicPhaseCollapse.md)
  proves bounds, exact zero/unit contrast criteria, fixed-maximum monotonicity,
  and threshold validity. Equality at the threshold is accepted. These results
  do not establish quantum decoherence or physical dump-port control.

## Earlier additions in v0.4.3

This release adds the Raft network induction and complete bridge, with eleven new
Lean files including supporting proofs. `reachable_global_log_matching` and
`reachable_leader_completeness` follow from the unchanged operational transitions.
Commitment is witnessed by an actual `Step.commit` in a finite execution, including
the majority replication evidence and current-term anchor.

A node already holding the entire committed prefix retains it through later steps
of that execution. Delayed acknowledgements, message loss, duplication, arbitrary
delivery order, and conflict-sensitive partial AppendEntries are covered.
The model has a fixed nonempty cluster and protocol-generated messages. Dynamic
membership, crash/recovery, Byzantine packet injection, and liveness are outside
scope; this is not a certification of a deployed Raft implementation.

See the [complete bridge card](knowledge/09_distributed_systems/DistributedRaftCompleteBridge.md)
and [validation record](knowledge/VERIFICATION.en.md).

## Earlier additions in v0.4.2

Release v0.4.2 added scalar Feldman share verification, translation and rectangular
placement geometry, an exact 256-node placement certificate, and scalar
optomechanical coupling. The concrete certificate is a separate registry module,
bringing that release to 90 direct imports.

- Feldman verification and reconstruction are algebraic statements over the reals.
  The public scalar commitment reveals the secret as `A0/G`; hiding is not claimed.
- The placement certificate checks 256 nodes in a 4000 by 4000 micrometre die,
  positive dimensions, unique identifiers, and pairwise disjoint closed rectangles.
  Bounds and nonintersection are separate statements. The packaged JSON and
  deterministic converter permit an external provenance check; Lean does not
  verify the JSON parser or SHA-256 implementation. No routes, optical losses, or
  propagation delays are certified.
- Optomechanics proves normalized scalar energy/force identities, affine frequency
  shifts, and properties of prescribed damping rates and an exponential envelope.
  The physical regime of `4*g^2/kappa` is documented, not derived in Lean. Neither
  quantum cooling nor full device stability is proved.

## What the proofs establish

Each result applies to its formal definitions and hypotheses. This repository
does not prove the Collatz or Riemann conjectures, resolve the Hopf problem, or
establish end-to-end security of the named protocols. Scalar commitment identities
do not prove cryptographic hiding or binding. Scientific priority of individual
formalizations has not been established.

Every module has an English knowledge card with its result, scope, and source links.

## Build and audit

Lean **4.33.1** and Mathlib **v4.33.1** are pinned. With elan installed:

```bash
lake build --wfail
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 tools/verifier_skill.py verify-all
python3 scripts/check_knowledge.py
```

`AxiomAudit.lean` checks the selected registry theorem's transitive axiom
dependencies. `verify-all` checks all project modules and audits all project
declarations in the imported environment. CI also runs an independent axiom audit.

## Verification tooling

The [verifier CLI and Python API](docs/verifier-skill.en.md) support strict module
verification, fresh axiom audits, integration using explicit recipes with source
rollback, and draft English knowledge cards. The tool operates on trusted local
projects; it is not a sandbox for untrusted Lean or Lake code.

[Contribution guide](knowledge/CONTRIBUTING.en.md) ·
[Machine-readable catalog](knowledge/catalog.json) ·
[Validation snapshot](tools/validation_snapshot.json)

## License and releases

Licensed under [Apache License 2.0](LICENSE). This repository is an independent
English-language source distribution with its own Git history and releases.
See [publication notes](docs/publication.en.md) for Reservoir requirements.

[Operational 2PC timeouts](knowledge/09_distributed_systems/DistributedTwoPhaseCommitTimeout.md) separates safe pre-vote abort from unsafe unilateral prepared decisions, and characterizes blocking only with both participants prepared and a stopped coordinator. Delivery of an in-flight decision remains possible; fairness and recovery are not claimed.

[Two-participant 3PC](knowledge/09_distributed_systems/DistributedThreePhaseCommit.md) proves operational safety and conditional completion using a kernel-checked finite invariant certificate. Accurate membership, unique backup appointment and atomic epoch fencing are explicit external contracts. Weak fairness is required for eventual completion; no partition tolerance or runtime implementation is claimed.
