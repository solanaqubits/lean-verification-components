---
id: QuantumKnillLaflammeEnvironmentCriterion
language: en
section: quantum-physics
source: Verification/QuantumKnillLaflammeEnvironmentCriterion.lean
source_sha256: 4c586f2b3e889ea4122668d2a15d95a2aa08b14b993b7cab4cbac1caef0f83f3
novelty: not-assessed
status: reviewed
---

# Knill-Laflamme conditions and independence of the environment on a code

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumKnillLaflammeEnvironmentCriterion.lean)

## Definitions and exact equivalence

The supplied channel is `KrausChannel d e r` from module 175; its input and
output dimensions may differ. The encoding matrix J has shape d by k.
`codeSpace J` is the range of the vector map J.mulVec, and `encode J X = J X J†`.
Physical encoding assumes J†J=I_k and k>0. No implicit recovery map is supplied.

`KnillLaflamme K J sigma` means, for every pair of Kraus indices i,j,

    J† K_j† K_i J = sigma_ij I_k.

`EnvironmentConstant K J sigma` means, for EVERY complex logical matrix X,

    complementary_channel K (J X J†) = Tr(X) sigma.

`knill_laflamme_equiv_environment` proves these predicates equivalent.
`encoded_complementary_entry` rewrites the environment entry as
Tr((J† K_j† K_i J) X). The reverse implication uses `scalar_of_trace_pairing`,
which explicitly tests X=E_ba, including the off-diagonal matrix units. Testing
only diagonal matrices would be insufficient.

The algebraic equivalence actually needs neither isometry nor k>0: it is a
finite trace-pairing identity for any J, even when k=0. These hypotheses are
required separately for the physical density conclusion. The zero-dimensional
case is not presented as a nonvacuous code.

## Density, normalization and index convention

`encode_trace` uses J†J=I; `encode_density` preserves density matrices.
`environment_of_density` specializes the criterion to any logical density input,
giving exactly sigma. `environment_density` constructs a basis density input
using k>0, encodes it isometrically, and invokes module 181's complementary CPTP
result. It proves sigma is positive semidefinite and Tr(sigma)=1.
`environment_hermitian` then proves Hermiticity. Positivity, normalization and
Hermiticity of sigma are conclusions, not assumed in the criterion.

`StandardKnillLaflamme` instead uses J† K_i† K_j J = lam_ij I_k.
`standard_iff_transpose` proves that this is the environment convention with
sigma=lam.transpose. `coefficient_indices` derives sigma_ij=lam_ji when both
coefficient equations hold and k>0. The transpose is ordinary transpose, not
conjugate transpose. `environment_unique` proves uniqueness of sigma from
constant-environment equations for positive logical dimension.

The state-independence conclusion concerns the chosen complementary output of
the prescribed finite channel. No unrestricted protocol-level secrecy, absence
of all physical side channels or security of a deployed device is claimed.

## Nonvacuous examples and regressions

`unitary_criterion` proves the criterion for any unitary channel and any supplied
isometric encoding, with sigma=I_1.

`Regression.code` embeds C^2 into the first two coordinates of C^4.
`Regression.orthogonal_channel` has operators (3/5)I_4 and (4/5)S, where S swaps
the two coordinate blocks. Completeness is proved; both errors are nonzero on
the code and their images are orthogonal. The criterion is proved with
sigma=diag(9/25,16/25), and its state validity follows from the general theorem.
This is a two-dimensional logical code with two nonzero, unequal error weights,
not a one-dimensional vacuous example. No decoder is constructed.

Full qubit dephasing on the identity code sends |0><0| and |1><1| to distinct
environment states. `dephasing_not_constant` and `dephasing_not_criterion` rule
out every sigma for that full-space code, not merely one guessed coefficient.

Live regressions add a complex 2-by-1 environment isometry with entries 3/5 and
4i/5. Its sigma has off-diagonal entries -12i/25 and 12i/25 and differs from its
transpose, testing the convention beyond real diagonal examples. Further
regressions cover off-diagonal non-Hermitian logical inputs, two basis densities,
code membership, zero logical dimension, a zero non-isometric encoding, and
matrix-unit probes missed by diagonal tests. These are exact Lean kernel proofs,
not floating-point experiments or executable complex arithmetic.

## Clean Water and validation

This module proves an equivalence between an algebraic criterion and the
constant complementary channel on the code. It does not construct a recovery
CPTP map, prove the full recovery equivalence, or implement an error-correction
protocol. Approximate correction, fault-tolerance thresholds, physical noise
models and deployment correspondence remain outside scope. General dilation
minimality/uniqueness, quantum capacity, remaining Bulletproofs protocol
extraction/security, Tendermint reference acquisition/slashing, Python,
JSON/SHA-256 and SimLab remain separate obligations. Novelty is not assessed.

Public gamma release v0.5.80 exports private snapshot
56f231609ee635fe929b760c9e60e56f6be6f2eb. The previous public scoped release is
f8af88298fbd07306590e23bdd1d5246020c01ab (v0.5.79). The last fully validated PUBLIC
baseline remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
Public-tree checks are recorded in [the release report](../../docs/release-v0.5.80.en.md).
Private evidence is not substituted for public validation; no new full-project
verify-all or full unittest result is claimed. The permitted axioms remain
propext, Classical.choice and Quot.sound.

Background: [Knill and Laflamme, A Theory of Quantum Error-Correcting Codes](https://arxiv.org/abs/quant-ph/9604034).
