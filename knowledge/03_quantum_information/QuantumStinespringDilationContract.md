---
id: QuantumStinespringDilationContract
language: en
section: quantum-physics
source: Verification/QuantumStinespringDilationContract.lean
source_sha256: 56e786639375fed191c957bee33cf7df354ef8809819bdc73f7042ea292a8878
novelty: not-assessed
status: reviewed
---

# Stinespring isometric dilation from a supplied Kraus family

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumStinespringDilationContract.lean)

## Contract and API

The input is the existing `QuantumCPTPChannelContract.KrausChannel d e r`:
r rectangular complex matrices K_j with sum K_j† K_j = I_d. Dimensions d and e
may differ. `stinespring_matrix` stacks any family as V_(a,j),b = (K_j)_a,b.
Its row index is **output system × environment**, matching the existing
`QuantumPOVMNaimarkDilation.partialTrace`; no second partial-trace API is defined.
The actual POVM definitions reside in QuantumPOVMNaimarkDilation; there is no
QuantumInformationPOVM source module in this snapshot.

`stinespring_isometry_general` proves V† V = sum K_j† K_j for every family.
`stinespring_isometry` specializes this to V† V = I_d for a KrausChannel.
`dilation K X` is V X V†. For ALL complex matrices X,
`partial_trace_stinespring_eq_channel` identifies its partial trace with the
existing `apply_channel K X`. For ALL complex output matrices E,
`stinespring_dual_map_identity` proves V† (E tensor I_r) V = `dual_channel K E`.
Neither identity assumes Hermiticity, positivity or commutativity.

`dilation_positive`, `dilation_trace` and `dilation_density` prove that the joint
matrix of a density input is again a density matrix on the product index.
It is not necessarily pure. `dilation_mul` and `dilation_idempotent_iff` show that
idempotency (the pure-state projector criterion for density matrices) is preserved
in both directions. `dilation_recover` proves V† (V X V†) V = X, and
`dilation_injective` therefore proves that no information is lost by the embedding
itself. No trace-distance theorem on the product space is asserted here.

`append_zero` appends a zero Kraus operator using Fin.snoc. Its completeness,
unchanged channel and unchanged reduced output are proved; the last block of V
is exactly zero. The construction does not imply a minimal environment.
All identities allow zero dimensions algebraically; a zero-dimensional space has
no trace-one state. No physical state is inferred from such a vacuous case.

## Nonvacuous regressions

Identity and arbitrary unitary channels have a one-dimensional environment.
A 2-to-1 reset stores the input in the environment and outputs its trace;
a separate 2-to-3 example checks rectangular typing and density normalization.
Non-Hermitian input matrices with imaginary entries are explicitly checked.

For qubit dephasing, the joint entry ((0,0),(1,1)) of the |+><+| input equals 1/2,
whereas the corresponding reduced off-diagonal entry is zero. The |+> and |->
inputs have different joint matrices but equal reduced outputs. A mixed I/2
input is checked NOT to become a projector. Repeated zero-block padding preserves
outputs; a zero operator alone in positive input dimension fails completeness.
The new Python live wrapper compiles exact Lean examples and registry projections;
these are kernel-checked symbolic regressions, not floating-point simulations.

## Clean Water and existing results

This module constructs a finite dilation for an ALREADY SUPPLIED Kraus family.
`QuantumNoBroadcastingMixed.Channel.exists_kraus` already establishes a Kraus
representation in the library and is not reproved here. No new bridge from its
existential representation to this constructor is claimed. The existing Naimark
module also has a specialized unitary dilation; a general unitary extension of
this new rectangular construction is outside this module.

Minimality, uniqueness, general unitary continuation, infinite-dimensional
Stinespring theory, numerical certification and physical implementations remain
outside scope. Full Bulletproofs range extraction, Tendermint accountable safety,
Python, JSON/SHA-256 and SimLab correspondence remain open obligations.

## Scoped Z validation

Public Z release v0.5.75. The last fully validated PUBLIC baseline remains
b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73). Previous public release
2d3c739800c983569a7b81de601ed84fcb5de9f5 (v0.5.74) is a scoped Z snapshot.
The private export snapshot is 82173f51b471a3e2ceb3ef263909f8477dcb9bd8.
Public checks are recorded in [the release report](../../docs/release-v0.5.75.en.md).
Allowed axioms: propext, Classical.choice, Quot.sound. Private evidence is not
substituted for public validation; no new complete-library audit total is claimed.

Background: [Watrous, The Theory of Quantum Information, chapter 2](https://cs.uwaterloo.ca/~watrous/TQI/TQI.double.2.pdf).
Novelty is not assessed.
