---
id: QuantumReferencePreservingRecoveryContract
language: en
section: quantum-physics
source: Verification/QuantumReferencePreservingRecoveryContract.lean
source_sha256: 0c103e48dc3ed9dc7d21c00f0addc8fa6010b79076aa983ad7755c952ac270b5
novelty: not-assessed
status: reviewed
---

# Exact recovery preserving entanglement with a reference system

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumReferencePreservingRecoveryContract.lean)

## Inputs and scope

E : KrausChannel d e r, encoding J : Matrix (Fin d) (Fin k) C and
R : KrausChannel e k s satisfy ExactRecovery E J R: for EVERY complex logical
matrix X, R(Phi_E(J X J†))=X. The recovery family size s is independent of r.
The reference-preservation implication needs only this exact identity; the
usual code contract also assumes k>0 and J†J=I. These additional assumptions
are used to derive a physical density environment from module 186.

Joint indices are (reference, logical/physical/environment). Joint m k uses
Fin m × Fin k. The flat wrapper uses finProdFinEquiv in both directions to
cover Matrix (Fin (m*k)) (Fin (m*k)) C without an implicit factor swap.
The same fixed R works for every m, even m=0 as an algebraic boundary case.

## Amplification and environment

The module reuses QuantumNoBroadcastingMixed.amplify. encodingMap is the
singleton Kraus linear map for J. encoding_amplify and channel_amplify invoke
amplify_kraus, identifying block amplification with operators I_m tensor K_a.
liftedRecovery explicitly applies the three amplified maps in encoding,
noise, recovery order. reference_preserving_recovery proves the result equals
X for all joint complex matrices, including correlated and entangled inputs.
reference_preserving_recovery_flat gives the corresponding flat-index theorem.

traceLogical traces the SECOND factor and is proved equal to the existing
partialTrace API. environmentMap includes encoding: Phi_E^c composed with J.
independence_env_reference derives

    amplify(environmentMap E J, m, X) = traceLogical(X) tensor sigma

from EnvironmentConstant E J sigma (module 182). recovery_decouples_environment
uses module 186 to derive existence of a density sigma from k>0, J isometric
and ExactRecovery; it does not assume decoupling or a supplied sigma.
For joint density inputs the reference-environment output is a product, so no
correlations between these two reduced systems remain. This is not a claim
about where all information resides in the full system/environment dilation.

## One normalized maximally entangled test

maximallyEntangled k is the density operator of
Omega_k = (1/sqrt(k)) sum_i |i> tensor |i>. Its entry ((a,i),(b,j)) is 1/k
when a=i and b=j, and zero otherwise. The matrix definition avoids numerical
square roots. maximallyEntangled_density proves positive semidefiniteness
and trace one for k>0 using a scaled vector outer product.
maximallyEntangled_block identifies each block as (1/k) E_ab.

entangled_test_iff_identity proves, for any complex-linear T on logical
matrices, that amplify T k fixes this state iff T fixes EVERY matrix.
The reverse implication extracts the (a,b) blocks, cancels the nonzero 1/k,
and expands an arbitrary matrix into matrix units. It does not assume the
conclusion as a recovery hypothesis. maximally_entangled_recovery_equivalence
specializes this to the composite recovery map, for each fixed R.

## Regressions and obstruction

Tests cover the complex non-diagonal code from module 185, its Bell state,
non-Hermitian complex joint coherences, arbitrary alternative recovery families,
reference sizes 0, 1, 2, 3 and arbitrary m, and the explicit flat-index wrapper.
Zero/repeated spectra and a physical C^2 -> C^4 channel are included. Density
normalization is checked at dimensions 2 and 3, and the Bell reference marginal
is I/2. Tensor bridges and the environment product identity are exercised.

Dephasing preserves each computational-basis projector but removes Bell coherence:
the ((0,0),(1,1)) entry changes from 1/2 to 0. dephasing_bell_not_recoverable,
via module 186 and the entangled-state criterion, excludes every finite recovery
Kraus family for full-qubit dephasing. Smaller correctable subcodes are not excluded.

## Clean Water and validation

These are exact finite-dimensional consequences of the existing recovery and
environment criteria. No new independent mathematical criterion or scientific
priority is claimed. Approximate/asymptotic bounds, diamond norm, executable
numerical decoders and physical implementations remain outside scope.
General dilation minimality/uniqueness, quantum capacity, remaining Bulletproofs
protocol extraction/security, Tendermint reference acquisition/slashing, Python,
JSON/SHA-256 and SimLab remain separate obligations. Novelty is not assessed.

Public gamma release v0.5.85 exports private snapshot
42bc9680b7be87d4b81664b50b8a2b21f46903b2. The previous public scoped release is
bbb8b76d88315e55e5b6e8c226d04d27efae2bae (v0.5.84). The last fully validated PUBLIC
baseline remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
Public-tree checks are recorded in [the release report](../../docs/release-v0.5.85.en.md).
Private evidence is not substituted for public validation; no new full-project
verify-all or full unittest result is claimed. The permitted axioms remain
propext, Classical.choice and Quot.sound.

Background: [Knill and Laflamme, A Theory of Quantum Error-Correcting Codes](https://arxiv.org/abs/quant-ph/9604034).
