---
id: QuantumUnitaryKrausDiagonalizationRecoveryContract
language: en
section: quantum-physics
source: Verification/QuantumUnitaryKrausDiagonalizationRecoveryContract.lean
source_sha256: 0d0913a4faa092e9d350ad927d62d532841c294c7fa10546fce4e8cee359140e
novelty: not-assessed
status: reviewed
---

# Recovery from a supplied unitary diagonalization of Knill-Laflamme data

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumUnitaryKrausDiagonalizationRecoveryContract.lean)

## Exact input contract

`DiagonalizationCertificate E J` contains a `KrausChannel d e r`, encoding matrix
J of shape d by k, k>0, J†J=I_k, a complex coefficient matrix Lambda, and
`StandardKnillLaflamme E J Lambda` from module 182:

    J† E_a† E_b J = Lambda_ab I_k.

It supplies a square complex U with both U†U=I_r and UU†=I_r, real numbers p_i,
and the certificate U† Lambda U=diag(p_i). Neither p_i>=0 nor sum_i p_i=1 is a
field. No normalized error family, diagonal code, recovery map or recovery
equation is assumed. Both unitary equations are accepted explicitly; the
implementation does not claim to derive the right equation from the left.
Input/output physical dimensions d and e may differ.

## Transpose bridge and coefficient law

`transpose_isometry` obtains (U^T)† U^T=I_r by transposing UU†=I_r.
`mixedChannel E U` invokes module 181's `changed_kraus` with W=U^T.
`mixed_operators` proves the explicit column-mixing equation

    K_i = sum_a U_ai E_a.

There is NO complex conjugation on U_ai in this definition. The transpose is
ordinary transpose, not adjoint. `mixed_channel_invariant` reuses
`changed_main_channel`, proving Phi_K(X)=Phi_E(X) for every complex physical X.

`mixed_coefficients` proves the standard coefficient law

    J† K_i† K_j J = (U† Lambda U)_ij I_k.

Its proof uses complementary-channel covariance from module 181 and module 182's
trace-pairing equivalence with the explicit environment convention sigma=Lambda^T.
`coefficient_entry_sum` expands the coefficient as
sum_a sum_b conj(U_ai) Lambda_ab U_bj. Thus the environment and standard
Knill-Laflamme indices are not silently interchanged. `rotated_diagonal` applies
the supplied diagonalization to give the diagonal equations needed by module 183.

## Derived weights and recovery

`weights_nonnegative` uses positivity of (K_i J)†(K_i J) and its diagonal entry
at logical index 0, available because k>0, to derive p_i>=0.
`weights_normalized` sums the compressed diagonal equations, invokes completeness
of the rotated Kraus channel and J†J=I_k, then evaluates a logical diagonal entry
to obtain sum_i p_i=1. These are conclusions from the input certificate.

`diagonalCode` fills module 183's DiagonalCode with these derived facts.
`certifiedRecovery : KrausChannel e k (r+e)` uses its explicit recovery family,
including the zero-weight branch and reset completion on the unused output space.
`certified_recovery_theorem` proves

    R(Phi_E(J X J†)) = X

for every complex logical matrix X. This is a statement about the ORIGINAL
channel E, not only its rotated Kraus representation. Complete positivity,
completeness, trace preservation on all physical inputs and density preservation
are proved for R. `logical_density_recovered` also states exact recovery and
validity for every logical density input.

## Nonvacuous examples and regressions

`inverseCertificate` starts from an existing diagonal code, hides it by inverse
unitary Kraus mixing, and certifies the forward diagonalization. It supplies
examples, not a general existence theorem for arbitrary non-diagonal data.

The main example uses module 183's two-dimensional code with probabilities
9/25 and 16/25, and U=[[3/5,4i/5],[4i/5,3/5]]. The original channel's coefficients
are explicitly [[337/625,84i/625],[-84i/625,288/625]]. They are Hermitian and
genuinely complex and non-diagonal. `transpose_not_adjoint` proves U^T differs
from U†. `wrong_adjoint_diagonalization` proves U Lambda U† is NOT the prescribed
diagonal. A live regression strengthens this to failure of the claimed diagonal
Knill-Laflamme condition for the actual incorrectly mixed channel.

`zeroCertificate` uses a complex change of basis on module 183's sector example
with weights (1,0). `repeatedCertificate` has a two-dimensional logical code,
two orthogonal errors of equal positive weight and a third zero error, with
weights (1/2,1/2,0). No simple-spectrum or strictly-positive-spectrum assumption
is introduced. Live regressions check complex off-diagonal physical and logical
matrices, index-sign conventions, Hermiticity, exact coherent-state recovery,
CPTP properties, both degenerate cases and registry integration. These are
symbolic kernel proofs, not executable floating-point simulations.

## Clean Water and validation

Recovery is conditional on the SUPPLIED unitary diagonalization. The module
does not construct that certificate for an arbitrary Hermitian matrix or claim
the unconditional general recovery equivalence. Existing mathematical spectral
theory is not declared unknown; applying it to remove this input obligation is
outside this module. No numerical eigensolver, approximate correction,
fault-tolerance threshold or physical implementation is certified. General
dilation uniqueness/minimality, quantum capacity, remaining Bulletproofs
protocol extraction/security, Tendermint reference acquisition/slashing,
Python, JSON/SHA-256 and SimLab remain separate obligations. Novelty is not assessed.

Public gamma release v0.5.82 exports private snapshot
d319bed6b9f14a54d67d650fa2a246c025cce9d2. The previous public scoped release is
7cdf431a79a99c19792f10bf293fdc9f1895335e (v0.5.81). The last fully validated PUBLIC
baseline remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
Public-tree checks are recorded in [the release report](../../docs/release-v0.5.82.en.md).
Private evidence is not substituted for public validation; no new full-project
verify-all or full unittest result is claimed. The permitted axioms remain
propext, Classical.choice and Quot.sound.

Background: [Knill and Laflamme, A Theory of Quantum Error-Correcting Codes](https://arxiv.org/abs/quant-ph/9604034).
