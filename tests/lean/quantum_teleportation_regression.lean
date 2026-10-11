import Verification.PhotonicsQuantumTeleportation
open PhotonicsQuantumTeleportation PhotonicsBellStateAnalyzer
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

example : PhotonicsQuantumTeleportationSuite := photonics_quantum_teleportation_master_suite
example : resourceEmbedding.conjTranspose * resourceEmbedding = 1 := resource_embedding_isometry
example : ∑ k : Fin 10, (kraus_op k).conjTranspose * kraus_op k = 1 := kraus_completeness
example (ρ : QMatrix) : branch .psiMinus ρ =
    (1/4 : ℂ) • ((X*Z) * ρ * (X*Z).conjTranspose) := branch_psi_minus_exact ρ
example (ρ : QMatrix) (hρ : IsDensity ρ) :
    (branch .psiMinus ρ + branch .psiPlus ρ).trace = 1/2 :=
  (branch_probabilities_invariant ρ hρ.2).2.2.2
example (ρ : QMatrix) (hρ : IsDensity ρ) :
    normalizedOutput ρ = ρ ∧ fidelity ρ (normalizedOutput ρ) = 1 :=
  teleportation_fidelity_one ρ hρ
example (ρ : QMatrix) :
    partialTrace (opticalTransfer * ρ * opticalTransfer.conjTranspose) =
    partialTrace (resourceEmbedding * ρ * resourceEmbedding.conjTranspose) :=
  no_signalling_partial_trace ρ
example (ρ : QMatrix) (hρ : ρ.trace = 1) : total ρ = (1/2 : ℂ) • (1 : QMatrix) :=
  no_signalling_theorem ρ hρ
example (b : BellState) (ψ : QuantumTeleportationProtocol.QubitState) :
    (bellContraction b).mulVec (stateVector ψ) =
    (1/2 : ℂ) • stateVector (QuantumTeleportationProtocol.bobReceivedState (oldOutcome b) ψ) :=
  bridge_to_quantum_teleportation_protocol b ψ
example : fidelity (pureDensity ketPlusI) (wrongCorrection (pureDensity ketPlusI)) = 0 :=
  counterexample_wrong_relative_phase
example : wrongCorrection (pureDensity ketPlus) = pureDensity ketPlus :=
  wrong_correction_plus_unchanged
example : let ρ : QMatrix := (1/2 : ℂ) • 1
    normalizedOutput ρ = ρ ∧ fidelity ρ (normalizedOutput ρ) = 1 ∧ (ρ*ρ).trace = 1/2 :=
  reg_maximally_mixed
example : kraus_op 2 = 0 ∧ kraus_op 6 = 0 := reg_dark_outcomes
