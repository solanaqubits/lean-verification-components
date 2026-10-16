---
id: QuantumComplementaryChannelContract
language: en
section: quantum-physics
source: Verification/QuantumComplementaryChannelContract.lean
source_sha256: 2ca2ee2960200b0e3ec2393ff7f7fdf7b5cb385998a7385f34a5d9c8e985c39a
novelty: not-assessed
status: reviewed
---

# Complementary quantum channel and environment state

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumComplementaryChannelContract.lean)

## Input and construction

The input is a supplied `KrausChannel d e r` from module 175. The matrices K_j
have shape e by d and satisfy sum K_j† K_j = I_d. The module reuses the exact
Stinespring matrix and dilation of module 177, with product index **output system
× environment**. Dimensions d, e, r need not coincide.

`partialTrace_system M i j = sum_a M (a,i) (a,j)` traces out the first index.
The existing `partialTrace` traces out the second index. The new function is a
finite-index definition for this layout, not a change to the existing API.
`complementary_channel K X = partialTrace_system (dilation K X)`.
`complementary_entry` proves its (i,j) entry equals Tr(K_i X K_j†), with this
precise order of conjugation, for every complex matrix X.

`complementary_operators K a j b = K_j a b`. Their completeness follows by
exchanging the two finite sums in the original completeness equation.
`complementary_kraus K : KrausChannel d r e` therefore represents the environment
output with e Kraus operators. `complementary_eq_apply` identifies this channel
with the partial-trace construction. Complete positivity is obtained directly
from module 175's finite block-amplification definition, not assumed or replaced
by ordinary positivity. The module also proves linearity, trace preservation
and preservation of density matrices through the same API.

`simultaneous_reductions` obtains both channels from the same joint matrix.
For arbitrary X, this is just a complex matrix. Density inputs give density
joint matrices by module 177; mixed inputs need not become pure. All identities
are finite-dimensional, including algebraic zero-dimension cases. No trace-one
state is asserted to exist in a zero-dimensional space.

## Explicit changes of environment

For W of shape r' by r, `environment_lift W = I_e tensor W` and
`change_environment W M = (I_e tensor W) M (I_e tensor W)†`.
The block identity proves that each fixed-system block changes by M_ab -> W M_ab W†.
Summing diagonal blocks proves

    partialTrace_system(change_environment W M)
      = W * partialTrace_system(M) * W†.

This covariance identity holds for arbitrary W and arbitrary M. The separate
hypothesis W†W=I_r is necessary for the proved invariance of the other reduction:
`main_environment_invariant` uses cyclicity of the trace of each block.

`changed_stinespring_isometry` proves that V'=(I_e tensor W)V remains an isometry.
`changed_kraus` reconstructs an actual `KrausChannel d e r'` from its entries.
`changed_stinespring` and `changed_dilation` identify the constructions exactly.
`changed_main_channel` proves Phi'=Phi; `changed_complementary_channel` proves
Phi_c'(X)=W Phi_c(X) W†. W may be rectangular. This is a theorem about a GIVEN
isometric transformation, not existence of an isometry relating arbitrary
representations or a minimality/uniqueness theorem.

## Examples and regression evidence

For a unitary channel with a one-dimensional environment the complement is
Tr(X) I_1; for density inputs it is the fixed state I_1. The reset channel to a
fixed basis state has complement X itself, including unequal input/output
dimensions. Computational-basis dephasing has complement diag(X_ii).

For qubit |+> and |->, BOTH reduced channels give the same outputs, while the
joint dilations differ. `correlations_retain_distinction` proves all three
statements together. The environment alone therefore need not contain every
distinction absent from the system. The joint correlations can retain it.

Appending a zero Kraus operator leaves the main channel unchanged by module 177.
The new complementary matrix has the old environment as its leading block and
an exactly zero last row and column; three separate theorems establish this.
The new live regressions check a rectangular 3-by-2 environment isometry with
an imaginary phase, non-Hermitian input, density normalization, unequal reset
dimensions, mixed dephasing output, repeated padding, and a zero non-isometry
that fails invariance. These are exact Lean kernel checks over complex matrices,
not floating-point simulations or an executable complex-number engine.

## Clean Water and provenance

The complementary channel depends on the chosen Kraus representation. No claim
is made that all information missing from the main output is accessible in the
environment marginal alone. General isometric uniqueness, minimal environment,
unitary extension, infinite dimensions, quantum capacity, general recovery
maps, numerical certification and physical implementation remain outside scope.
Full Bulletproofs protocol extraction/security (beyond certified openings),
Tendermint reference acquisition/slashing, Python correspondence, JSON/SHA-256
and SimLab remain separate obligations. Mathematical novelty is not assessed.

Public gamma release v0.5.79 exports private snapshot
6efc674f70eb0181cd1c5667f919bcf0826cdd21. The previous public scoped release is
9d95f47fb7970af648f3c6b31977e627283dcca7 (v0.5.78). The last fully validated PUBLIC
baseline remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
Public-tree checks are recorded in [the release report](../../docs/release-v0.5.79.en.md).
Private evidence is not substituted for public validation; no new full-project
verify-all or full unittest result is claimed. The permitted axioms remain
propext, Classical.choice and Quot.sound.

Background: [Watrous, The Theory of Quantum Information](https://cs.uwaterloo.ca/~watrous/TQI/).
