---
id: QuantumKnillLaflammeGeneralRecoveryTheorem
language: en
section: quantum-physics
source: Verification/QuantumKnillLaflammeGeneralRecoveryTheorem.lean
source_sha256: 12eb063b063944b9df60c4953794ada84031a5b3e3ce14cb51fb7affc485d77c
novelty: not-assessed
status: reviewed
---

# Exact recovery from general Knill-Laflamme conditions

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumKnillLaflammeGeneralRecoveryTheorem.lean)

## Input and result

`GeneralCode E J` is parameterized by a `KrausChannel d e r` and an encoding
matrix J of shape d by k. Its only fields are k>0, J†J=I_k, a complex coefficient
matrix Lambda and `StandardKnillLaflamme E J Lambda`:

    J† E_a† E_b J = Lambda_ab I_k.

Hermiticity, an eigenbasis, eigenvalues, their positivity/normalization and a
recovery map are NOT inputs. Physical dimensions d and e need not agree.
`generalRecovery C : KrausChannel e k (r+e)` is constructed and satisfies

    R(Phi_E(J X J†)) = X

for every complex logical matrix X, not just density matrices.
`exists_recovery` quantifies a KrausChannel with this property, so completeness
is part of its type. Separate theorems give complete positivity, trace preservation
on every physical output matrix, density preservation and exact logical density
recovery. The claim is sufficiency, not an equivalence.

## Proof chain and exact API

`coefficients_hermitian` invokes module 182's `environment_hermitian` for
sigma=Lambda^T using `standard_iff_transpose`, then uses
`Matrix.isHermitian_transpose_iff`. The index transpose is explicit.

The actual pinned import is `Mathlib.Analysis.Matrix.Spectrum`.
`spectralUnitary` and `spectralWeights` use `Matrix.IsHermitian.eigenvectorUnitary`
and `eigenvalues`. Both U†U=I and UU†=I follow from the unitary-group API.
`spectral_diagonalizes` uses `conjStarAlgAut_star_eigenvectorUnitary`, the
U† Lambda U=diag(p) form of Mathlib's spectral theorem, with ordinary matrix
adjoints. No additional spectral axiom or supplied certificate is introduced.

`spectralCertificate` assembles module 184's DiagonalizationCertificate.
`spectral_weights_nonnegative` and `spectral_weights_normalized` reuse its
proofs of p_i>=0 and sum(p)=1. `generalRecovery` invokes `certifiedRecovery`;
`general_recovery_theorem` invokes its theorem for the ORIGINAL channel E.
The transpose mixing W=U^T, physical-channel invariance and complete recovery
on unused output space are inherited from modules 181, 183 and 184.
Zero and repeated eigenvalues require no additional hypothesis.

## Nonvacuous regressions

`Examples.complexCode` has explicit coefficients
[[337/625,84i/625],[-84i/625,288/625]], reusing only the algebraic channel/code
facts from module 184's example. Its old manually supplied U and p are not passed
to the new recovery construction; Mathlib supplies a fresh spectral certificate.
`zeroCode` has coefficients diag(1,0). `repeatedCode` has diag(1/2,1/2,0).
Regressions check kernel and repeated-eigenvalue vectors of these coefficient
matrices, and recover arbitrary and complex off-diagonal logical matrices via
the new spectral construction. They do not constrain Mathlib's choice of basis
or ordering of eigenvalues.

`rectangularChannel` maps C^2 to C^4 using an isometric embedding. Its GeneralCode
uses identity logical encoding. Tests check recovery, completeness I_4, trace
preservation on arbitrary physical inputs, and a density input in the unused
output sector. Other tests cover the unitary identities, diagonalization,
derived weight properties, CP, density recovery, existence and registry fields.
Lean examples are compiled inside the targeted Python unittest wrappers; the
counts are reported separately, not as independent executions.

## Clean Water and validation

The module proves sufficiency of general finite-dimensional Knill-Laflamme
conditions for exact CPTP recovery without an external diagonalization certificate.
Necessity of those conditions given recovery remains a separate obligation.
The classical, noncomputable spectral construction over complex matrices is not
an executable numerical eigensolver or decoder. Approximate error correction,
fault-tolerance thresholds, physical noise correspondence, general dilation
minimality/uniqueness and quantum capacity are outside scope. Remaining
Bulletproofs protocol extraction/security, Tendermint reference acquisition and
slashing, Python, JSON/SHA-256 and SimLab obligations are unchanged.
Novelty is not assessed.

Public gamma release v0.5.83 exports private snapshot
5d3bca96616bdc3981ac060c6ca2ae4ff5c7b3ae. The previous public scoped release is
d7d37132a7f88c022f368d92f31c8e5ae9ae21fa (v0.5.82). The last fully validated PUBLIC
baseline remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
Public-tree checks are recorded in [the release report](../../docs/release-v0.5.83.en.md).
Private evidence is not substituted for public validation; no new full-project
verify-all or full unittest result is claimed. The permitted axioms remain
propext, Classical.choice and Quot.sound.

Background: [Knill and Laflamme, A Theory of Quantum Error-Correcting Codes](https://arxiv.org/abs/quant-ph/9604034).
