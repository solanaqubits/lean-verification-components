# Changelog

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
