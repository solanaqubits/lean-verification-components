# Changelog

## v0.5.0

- Added threshold time envelopes, elementary transcript forking, and real beam-splitter models.
- Split reusable components from the milestone registry without cyclic imports or changed proofs.
- 100 direct imports, 134 Lean files, and 8,237 audited declarations.
- Strict build: 3,516 jobs; 35 public tests without skips; CLI and independent axiom audits.
- Preserved all model boundaries and exact placement provenance. No simulations are included.

## v0.4.3

- Added global reachable-state Raft Log Matching and operational Leader Completeness
  for actual commit events, plus retention of already-held committed prefixes.
- Added eleven Lean files across two registry packages and their supporting proofs:
  92 direct imports, 125 Lean files, and 7,812 audited declarations.
- Preserved the original operational transitions and conflict-sensitive partial
  AppendEntries. No abstract history validity or desired invariant is a new guard.
- Added two public execution regressions; synchronized English cards, catalog,
  source hashes, and model boundaries. Dynamic membership, crash/recovery,
  Byzantine injection, and liveness remain outside scope.
- Strict build: 3,507 jobs; 26 public tests; independent and CLI axiom audits.

## v0.4.2

- Added scalar Feldman VSS, chip layout geometry, an exact 256-node placement
  certificate, and scalar optomechanical coupling.
- 90 direct imports, 114 Lean files, 7,397 audited declarations; 24 public tests.
- Separated exact geometric guarantees from external JSON/hash provenance and
  physical assumptions. Scalar commitments do not establish cryptographic hiding.


## v0.4.1

- Added DistributedRaftLeaderCompleteness and DistributedRaftStateMachine;
  synchronized the registry and English knowledge catalog to 86 direct imports,
  110 Lean files, and 7,048 declarations, including generated declarations.
- Leader Completeness remains conditional on entry provenance, Log Matching,
  and admissible voter histories; it is not derived from a complete RPC execution.
- The operational model proves historical single voting and election safety for
  reachable states. It includes addressed RPCs, replication, and a three-server
  execution reaching a committed entry. Global reachable-state Log Matching and
  the HistoryValid/VoterEvolution bridge remain open. Local log-operation lemmas
  retain explicit compatibility and freshness premises.
- Updated English cards, source hashes, integration recipes and catalog validation
  for unsuffixed English Markdown cards. No Python simulations are included.
- Retained the pinned Lean/Mathlib v4.33.1 toolchain and Apache-2.0 license.

## v0.4.0

- Expanded the distribution from 83 to 108 Lean files and from 60 to 84 direct
  MasterSuite imports, with 6,442 audited declarations including generated ones.
- Added 25 source files across cryptographic algebra, quantum models, DeFi,
  distributed systems, and photonics; synchronized existing proofs and registries.
- Added the three-component PhotonicsInterposerFullSuite for scalar MZI intensity
  redistribution, exponential attenuation, and linear thermo-optic phase drift.
  SolarisPhysicalModels is exported and audited separately, including cosine
  orthogonality and conditional isometry, loss, and thermal-proxy results.
- Added same-ballot Paxos safety from majority intersection and the explicit
  SingleVote premise. This is not cross-ballot safety of a full Paxos execution.
- Updated all English knowledge cards and navigation with explicit model limits.
  MZI identities do not certify physical-device unitarity. The 9.812 MPa thermal
  value is a one-dimensional scalar proxy, not a von Mises stress certification.
- Added standard headers and module documentation to 17 exported files and
  replaced the broad tactic import in SolarisPhysicalModels with explicit imports
  so the public source builds with the configured header linter. Declaration and
  proof bodies are unchanged by these packaging corrections.
- Retained Lean 4.33.1, Mathlib v4.33.1, Apache-2.0 licensing, and independent
  public Git history. See the [verification record](knowledge/VERIFICATION.en.md)
  for the checks performed on this release.


## v0.3.0

- Added nine components: scalar Shamir reconstruction, superdense Bell vectors, two-vote commit rules, impermanent loss, scalar no-cloning obstruction, four-leaf Merkle paths, local Paxos properties, BB84 label/arithmetic checks, and proportional vault conversions.
- Expanded MasterSuite to 60 direct imports and the English catalog to 83 Lean module cards.
- Preserved Lean and Mathlib v4.33.1 and Apache-2.0 licensing.

The cards distinguish algebraic identities and local rules from cryptographic security, physical quantum protocols, execution-level consensus safety and integer smart-contract behavior.

## v0.2.0

- Added eight components: two-point R1CS/QAP, teleportation branch recovery, StableSwap, scalar Schnorr/Fiat-Shamir, one-bit Deutsch-Jozsa amplitudes, two-process vector clocks, N=4 Grover search, and arithmetic TWAP.
- Expanded MasterSuite to 51 direct imports and the English catalog to 74 Lean module cards.
- Preserved Lean and Mathlib v4.33.1 and the Apache-2.0 license.

These are bounded algebraic models. TWAP displacement does not prove flash-loan resistance; scalar cryptographic identities do not establish computational security. The quantum cards distinguish supplied amplitudes and branches from complete circuit and measurement models.

## v0.1.1

- Added the phase-flip syndrome model and static CDP lending invariants.
- Updated the registry to 43 direct component imports and the English knowledge catalog to 66 module cards.
- Preserved the existing Raft log-append and scalar Pedersen components.
- Corrected commit attribution to the author's current GitHub identity.

The phase-flip component verifies matrix identities and a prescribed syndrome decoder, not recovery of arbitrary quantum states. The CDP component verifies static real-valued formulas, not a lending protocol implementation or a liquidation state transition.

See [the verification record](knowledge/VERIFICATION.en.md) for reproducible checks and source hashes.
