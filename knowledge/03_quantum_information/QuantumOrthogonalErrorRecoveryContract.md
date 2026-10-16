---
id: QuantumOrthogonalErrorRecoveryContract
language: en
section: quantum-physics
source: Verification/QuantumOrthogonalErrorRecoveryContract.lean
source_sha256: 87b219fbc6117e69c3d0bc43c01ba412d9a8fd37ba19d9d722586b17a625b563
novelty: not-assessed
status: reviewed
---

# Explicit recovery for orthogonal error spaces

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumOrthogonalErrorRecoveryContract.lean)

## Input and mathematical scope

`DiagonalCode K J` contains a supplied `KrausChannel d e r`, an encoding J of
shape d by k with J†J=I_k and k>0, real probabilities p_i>=0 summing to one,
and the diagonal Knill-Laflamme equations

    J† K_i† K_j J = if i=j then p_i I_k else 0.

The channel output dimension e may differ from d. The recovery maps e-dimensional
physical outputs to k-dimensional logical outputs. No recovery map, successful
decoding equation, normalized error isometry or orthogonal complement is assumed
in the input. `diagonal_environment` connects these data to module 182's
Knill-Laflamme predicate with sigma=diag(p_i).

## Explicit Kraus construction

`errorOnCode K J i = K_i J` and `amplitude C i = sqrt(p_i)` (cast to C).
`zero_error` derives K_i J=0 from (K_i J)†(K_i J)=0 when p_i=0.
`normalizedError` uses an explicit zero branch; otherwise U_i=(sqrt(p_i))^(-1) K_i J.
`error_factorization` proves K_i J=sqrt(p_i) U_i in both cases.
`normalized_gram` proves U_i† U_j=I_k for equal active indices, zero otherwise.
Thus each positive-weight U_i is isometric and distinct images are orthogonal.
Zero on the code does not imply K_i is zero on the entire physical space.

The error projection P=sum_i U_i U_i† is Hermitian and idempotent; Q=I_e-P
is its Hermitian idempotent complement. `unused_on_code_error` proves Q K_i J=0.
For the fixed logical basis index b0=0 (available because k>0), define

    R_i = U_i†,
    T_a = |b0><a| Q,  a : Fin e.

There are r+e recovery operators, enumerated by Fin.addCases. The e reset
operators are rectangular matrices of shape k by e; a bare Q would have the
wrong output type and would not itself specify a reset. `residual_complete`
proves sum_a T_a† T_a=Q, and `recovery_complete` proves

    sum_m recoveryOperators_m† recoveryOperators_m = I_e.

`recoveryChannel C : KrausChannel e k (r+e)` is therefore a channel on ALL physical
output matrices, not merely a map defined on the space of errors. Complete
positivity, trace preservation and density preservation reuse module 175.
These are symbolic noncomputable real/complex matrix definitions in Lean;
no executable floating-point decoder or numerical square-root routine is certified.

## Exact recovery

`normalized_on_code_error` gives U_i† K_j J=delta_ij sqrt(p_j) I_k;
`residual_on_code_error` gives T_a K_j J=0. `recover_one_error` then proves
that the j-th noise contribution recovers to p_j X. Summing yields

    recovery_theorem C X : R(Phi(J X J†)) = X

for EVERY complex k-by-k matrix X, without a Hermiticity, positivity or trace
premise. Density-state recovery is a specialization. Output is the logical X;
re-encoding would give J X J†, a separate change of output space.

## Nonvacuous examples and regression boundaries

`Examples.twoErrorCode` uses the two-dimensional logical code from module 182
inside C^4, with probabilities 9/25 and 16/25 and two nonzero orthogonal errors.
`two_error_recovery` proves recovery for every logical matrix.

`Examples.sectorChannel` has physical operators diag(1,1,0,0) and diag(0,0,1,1).
On the same logical code the probabilities are 1 and 0. The second operator is
NONZERO physically but zero on the code; its normalized error is zero. The
unused projection is explicitly diag(0,0,1,1), hence nonzero.

Live regressions check complex off-diagonal coherence, a coherent density input,
zero trace-distance recovery error, the module-182 environment criterion, and
a rectangular C^2 -> C^4 channel. They also prove the sector recovery formula

    R(Y) = [[Y00 + Y22 + Y33, Y01], [Y10, Y11]]

for arbitrary complex Y. In particular an unused basis state is reset to |0><0|
with trace one, while coherence entirely inside the unused sector is discarded.
The syndrome operators alone fail completeness, proving that the added reset
operators are essential in this example. These are kernel-checked symbolic
regressions, not simulation counts or physical fault-rate measurements.

## Clean Water and validation

This is an explicit recovery theorem for the DIAGONAL Knill-Laflamme case.
No general coefficient diagonalization, treatment of arbitrary non-diagonal
Knill-Laflamme data, full recovery equivalence, approximate correction,
fault-tolerance threshold, implementation correspondence or deployed noise model
is claimed. General dilation uniqueness/minimality, quantum capacity, remaining
Bulletproofs protocol extraction/security, Tendermint reference acquisition/slashing,
Python, JSON/SHA-256 and SimLab remain separate obligations. Novelty is not assessed.

Public gamma release v0.5.81 exports private snapshot
d5d6dad4440eb91e6241fe485e025cd0c097adef. The previous public scoped release is
5ea996c66817194475a41f513009a604c9b7da41 (v0.5.80). The last fully validated PUBLIC
baseline remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
Public-tree checks are recorded in [the release report](../../docs/release-v0.5.81.en.md).
Private evidence is not substituted for public validation; no new full-project
verify-all or full unittest result is claimed. The permitted axioms remain
propext, Classical.choice and Quot.sound.

Background: [Knill and Laflamme, A Theory of Quantum Error-Correcting Codes](https://arxiv.org/abs/quant-ph/9604034).
