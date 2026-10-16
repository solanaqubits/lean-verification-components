---
id: QuantumCPTPChannelContract
language: en
section: quantum-physics
source: Verification/QuantumCPTPChannelContract.lean
source_sha256: d41a825fdaa774ec200854d96f29072d01f706a5eccf4c26e3666f5b7bde91b1
novelty: not-assessed
status: reviewed
---

# Quantum channels and trace-distance contraction

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumCPTPChannelContract.lean)

## Mathematical contract

KrausChannel d e r stores r rectangular complex matrices K_j of shape e by d
and the completeness equation sum K_j† K_j = I_d. apply_channel is the existing
complex linear krausMap: Phi(X) = sum K_j X K_j†. The module reuses
QuantumNoBroadcastingMixed.Channel and its proof of complete positivity under
EVERY finite block amplification, not just positivity on unextended states.
channel_add, channel_smul, channel_trace_preserving, channel_completely_positive,
channel_positive and channel_density expose the guarantees at the new interface.
Input and output dimensions may differ. A trace-one density matrix cannot exist
in dimension zero; no nonempty-state assumption is hidden in that case.

The dual is Phi*(E) = sum K_j† E K_j. dual_unital and dual_positive prove that
pullback_effect maps every Effect e to Effect d, including positivity of its
complement. trace_adjoint_identity holds for arbitrary complex matrices E and X;
there is no commutation assumption. The primal channel need not be unital.

trace_distance_contractive pulls the attained output spectral effect of module
172 back to the input and applies its variational bound. trace_norm_contractive
and optimal_success_contractive give the corresponding trace-norm and equal-prior
Helstrom statements. The norm is the existing spectral/Schatten trace norm, not
Lean's ambient matrix norm. cptp_trace_distance_contractive also covers EVERY
abstract Channel (Fin d) (Fin e) in the existing API. Its separate proof uses
the positive and negative parts of the input difference, positivity and trace
preservation; it does not assume a Kraus representation or an optimizer.

## Examples and regression coverage

identity_channel preserves every input. unitary_channel preserves trace distance
on density matrices, proved by contraction in both directions using the adjoint
unitary. reset_channel v replaces any density matrix by the fixed basis projector
|v><v|, allowing different input/output dimensions, and makes the distance zero.
This example is replacement by a pure basis state, not a parameterized constructor
for every mixed replacement state.

dephasing_channel removes off-diagonal entries in the computational basis.
The exact pure qubit states |+><+| and |-><-| have the same output I/2 and unequal
inputs; dephasing_strict_loss proves strict contraction. The live regression file
also checks arbitrary finite ancillas, rectangular channels, composed abstract
channels, dual effects, non-unital reset, and measurement TV after a quantum channel.
Regressions are exact Lean kernel checks, not floating-point executions.

## Clean Water

This module establishes finite-dimensional quantum-channel trace-distance
contraction, extending the measurement/classical result of module 172.
Stinespring dilation and equivalence of all channel representations are not proved
in this module. Existing Kraus and block-positivity results are reused; no claim is
made that such representation results are absent elsewhere in the library.
Relative-entropy DPI, infinite dimensions, numerical certification of approximate
Kraus operators, physical implementation and empirical state estimation are outside
scope. Full Bulletproofs range extraction via multipoint interpolation, Tendermint
accountable safety, Python, JSON/SHA-256 and SimLab correspondence remain open.

## Validation and references

The public export is checked by one final integrated project gate with the
incremental Lake cache retained. Private validation is not reused as evidence
for this public tree. Actual results are recorded
in [the validation record](../VERIFICATION.en.md). Only propext, Classical.choice
and Quot.sound are allowed. The containing commit identifies the checked source;
the SHA-256 above identifies this module. Novelty is not assessed.

Background: [Watrous, The Theory of Quantum Information, chapter 3](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf), Corollary 3.40.
