---
id: MasterSuiteComponents
language: en
section: verification
source: Verification/MasterSuiteComponents.lean
source_sha256: 4d5ae1852549d62a305732f06c253a3443c0860d12afc43bdd06360e1c9d0da7
novelty: not-assessed
status: reviewed
---

# MasterSuiteComponents

[Section](README.md) · [Lean](../../Verification/MasterSuiteComponents.lean)

## Reusable package declarations

This module holds the existing package structures, proof constructors, and compatibility projections extracted from `MasterSuite.lean`. Their namespace remains `MasterSuite`; moving the source location does not rename the declarations. The extracted declaration block preserves the prior definitions and proof bodies, including inherited fields, Lamzouri's integral and unique-minimum results, and compatibility projections for existing components.

The top-level package types are `FinslerFullSuite`, `LamzouriFullSuite`, `CollatzFullSuite`, `CryptoFullSuite`, `QuantumPhysicsFullSuite`, `HopfFullSuite`, `ProofDAGFullSuite`, `FinanceRiskFullSuite`, `DistributedSystemsFullSuite`, `RiemannFullSuite`, and `PhotonicsInterposerFullSuite`. Supporting `FinslerFormalSuite` and `FinanceDeFiFullSuite` remain available. Each package has its existing constructor theorem, such as `crypto_full_master_suite`, `quantum_physics_full_master_suite`, and `distributed_systems_full_master_suite`.

Universe declarations are retained. In particular, the crypto package carries the AIR and FRI universe parameters, the distributed package carries the Raft universe parameters, and the Hopf package quantifies over its original ambient type universe. These abstractions have not been replaced with finite examples or fixed universe instances.

## Dependency purpose

The module imports the original 99 domain modules and the operational Chandy–Lamport and exact QPE modules. DistributedSystemsFullSuite now includes chandy_lamport; aggregates referring to this package inherit the added field. [`MasterHundredRegistry`](../11_meta_registry/MasterHundredRegistry.md) imports these components to assemble the milestone proposition, and the central [`MasterSuite`](MasterSuite.en.md) can import that milestone. Components do not import either registry, avoiding a cycle. The central registry declaration itself is not defined in this file.

The split is organizational. It introduces no new domain result and does not enlarge the meaning of any imported guarantee. A suite bundles selected propositions; it does not certify every declaration in its imports or complete coverage of every subject block. Counts of imports and source files are external repository checks, not theorems of the component packages.

The domain limitations remain in force. For example, `QuantumPhysicsFullSuite.beam_splitter` is a real orthogonal finite two-mode/two-boson model, not general complex unitarity. `CryptoFullSuite.forking_lemma` concerns finite matrix counting and scalar extraction. `DistributedSystemsFullSuite.marzullo_algorithm` concerns a threshold envelope with explicit interval assumptions. Aggregating these fields supplies no additional physical, cryptographic, or protocol guarantee.

## Verification

See the [current validation record](../VERIFICATION.en.md). The operational snapshot field is constructed by `DistributedChandyLamportSnapshot.chandy_lamport_master_suite`; it proves the two-process safety and completed-channel guarantees described in its [scope card](../09_distributed_systems/DistributedChandyLamportSnapshot.md). The historical registry's import manifest is unchanged, but its distributed package type includes this added field.

QuantumPhysicsFullSuite now includes phase_estimation, constructed by QuantumPhaseEstimation.quantum_phase_estimation_master_suite. It preserves the exact two-bit phase and eigenstate hypotheses; existing aggregates referencing the quantum package inherit the field.

`QuantumPhysicsFullSuite.grover_multiple_targets` adds exact N=4 subset dynamics, norm preservation, the proper-subset invariant plane and both rank-one reflection counterexamples.

`QuantumPhysicsFullSuite.deutsch_jozsa_general` adds the general Hadamard and XOR-ancilla circuit, promise separation, edge cases and one-qubit compatibility.

`DistributedSystemsFullSuite.raft_commit_application` adds operational commit-index provenance and deterministic local application. Global State Machine Safety is not claimed by this extension.

`DistributedSystemsFullSuite.two_phase_commit_timeout` adds reachable operational agreement, pre-vote abort safety, prepared-view indistinguishability and the conditional stopped-coordinator blocking equivalence. The legacy `two_pc` field is preserved.

`DistributedSystemsFullSuite.three_phase_commit` includes operational two-participant agreement, finite completion paths and conditional weak-fair completion. The accurate epoch-view service remains an explicit environment contract.

DistributedSystemsFullSuite.chandy_misra_haas adds inductive probe provenance and soundness for a fixed AND wait graph, finite detection paths and conditional progress under payload delivery fairness. Fresh-epoch reset is an external contract; arbitrary dynamic WFG soundness is explicitly refuted for the naive send-time-only extension. See the [CMH scope card](../09_distributed_systems/DistributedChandyMisraHaasDeadlock.md).

QuantumPhysicsFullSuite includes grover_arbitrary_phase, preserving the single-target C^4 scope: arbitrary phases preserve a complex plane, exact one-step success has cos(phi)=-1, and the canonical bridge includes a global minus sign.

`QuantumPhysicsFullSuite.simon` adds the complex two-register circuit, exact Simon distribution and rank-conditional binary period recovery. Existing fields are preserved.

`QuantumPhysicsFullSuite.phase_estimation_general` adds general controlled-power QPE, unitary Fourier transforms, exact dyadic recovery and the nearest-sample 4/π² probability bound. A normalized eigenstate is supplied. [Scope and assumptions](../03_quantum_physics_and_optics/QuantumPhaseEstimationGeneral.md).

`QuantumPhysicsFullSuite.shor_order_finding` derives the padded modular-multiplication spectrum and the QPE marginal on |1⟩. The component bound is 4/π²; its guaranteed contribution to the mixture is 4/(rπ²). Order recovery and factorization are not claimed. [Scope and assumptions](../03_quantum_physics_and_optics/QuantumShorOrderFindingCore.md).

`DistributedSystemsFullSuite.suzuki_kasami` proves reachable token conservation and mutual exclusion. Eventual service requires ReliableDelivery, WeakFairness and FiniteCS. A reachable counterexample refutes LN ≤ RN at the holder. [Scope and serialization](../09_distributed_systems/DistributedSuzukiKasamiMutex.md).

`QuantumPhysicsFullSuite.shor_continued_fractions` proves finite executable candidates and conditional recovery under the strict Legendre bound. Euclidean stages are bounded separately from bit complexity. [Scope and assumptions](../03_quantum_physics_and_optics/QuantumShorContinuedFractions.md).

`QuantumPhysicsFullSuite.shor_order_recovery` proves conditional recovery from certified divisors, the spectral GCD criterion and a counterexample to taking all candidate denominators. [Scope and assumptions](../03_quantum_physics_and_optics/QuantumShorOrderRecoveryGCD.md).

`DistributedSystemsFullSuite.raymond_tree` includes reachable token conservation, effective holder routing, conditional starvation freedom and exact isolated traffic. [Contract](../09_distributed_systems/DistributedRaymondTreeMutex.md).
