import Verification.QuantumQutritDecoderCircuitRefinement
import Verification.Specs.QuantumQutritDecoderSpec

noncomputable section
open scoped BigOperators ComplexOrder Kronecker
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract QuantumHelstromStateDiscrimination
open QuantumKnillLaflammeEnvironmentCriterion QuantumReferencePreservingRecoveryContract
open QuantumErasureCorrectabilityContract QuantumQutritTwoOfThreeSecretSharingContract
open QuantumQutritSecretSharingExplicitDecoder
open QuantumQutritDecoderCircuitRefinement
namespace QutritCircuitRegression
example : runCircuit decoderCircuit (0,0) = (0,0) := by decide
example : runCircuit decoderCircuit (0,1) = (1,2) := by decide
example : runCircuit decoderCircuit (0,2) = (2,1) := by decide
example : runCircuit decoderCircuit (1,0) = (2,2) := by decide
example : runCircuit decoderCircuit (1,1) = (0,1) := by decide
example : runCircuit decoderCircuit (1,2) = (1,0) := by decide
example : runCircuit decoderCircuit (2,0) = (1,1) := by decide
example : runCircuit decoderCircuit (2,1) = (2,0) := by decide
example : runCircuit decoderCircuit (2,2) = (0,2) := by decide
example (gs : List Gate) (x : Fin 3 × Fin 3) :
    runCircuit (inverseCircuit gs) (runCircuit gs x) = x := circuit_inverse_left gs x
example (gs : List Gate) (x : Fin 3 × Fin 3) :
    runCircuit gs (runCircuit (inverseCircuit gs) x) = x := circuit_inverse_right gs x
example (a b : List Gate) : circuitMatrix (a ++ b) = circuitMatrix b * circuitMatrix a :=
  matrix_append a b
example (gs : List Gate) : (circuitMatrix gs).conjTranspose * circuitMatrix gs = 1 :=
  circuit_unitary_left gs
example (gs : List Gate) : circuitMatrix gs * (circuitMatrix gs).conjTranspose = 1 :=
  circuit_unitary_right gs
example : circuitMatrix [.swap] * circuitMatrix [.addFirst 2] * circuitMatrix [.addSecond 2] =
    decoder := decoder_gate_product
example : ∀ x, runCircuit decoderCircuit x = QuantumQutritDecoderSpec.forward x :=
  decoder_coordinates
example : circuitMatrix decoderCircuit = QuantumQutritDecoderSpec.decoder := decoder_matrix
example (t : Fin 3) : circuitKraus t = QuantumQutritDecoderSpec.kraus t := kraus_refinement t
example (Y : Q 9) : apply_channel circuitRecovery Y =
    ∑ t, QuantumQutritDecoderSpec.kraus t * Y *
      (QuantumQutritDecoderSpec.kraus t).conjTranspose := by
  rw [channel_refinement]
  rfl
example (x : Fin 9) : runIndex decoderCircuit x = QuantumQutritDecoderSpec.expectedTable x := by
  rw [decoder_index]
  exact QuantumQutritDecoderSpec.table_witness x
example : ∑ t, (circuitKraus t).conjTranspose * circuitKraus t = 1 := circuit_complete
example (Y : Q 9) : apply_channel circuitRecovery Y = apply_channel explicitRecovery Y :=
  channel_refinement Y
example : QuantumNoBroadcastingMixed.IsCompletelyPositive (apply_channel circuitRecovery) :=
  channel_completely_positive _
example (Y : Q 9) : (apply_channel circuitRecovery Y).trace = Y.trace :=
  channel_trace_preserving _ _
example (Y : Q 9) (h : Density Y) : Density (apply_channel circuitRecovery Y) := channel_density _ h

example (X : Q 3) : apply_channel circuitRecovery (retainedPair 0 (encode code X)) = X :=
  circuit_recovery 0 X
example (X : Q 3) : apply_channel circuitRecovery (retainedPair 1 (encode code X)) = X :=
  circuit_recovery 1 X
example (X : Q 3) : apply_channel circuitRecovery (retainedPair 2 (encode code X)) = X :=
  circuit_recovery 2 X
example (q : Fin 3) : apply_channel circuitRecovery
    (retainedPair q (encode code (Matrix.single 2 0 (1+Complex.I)))) =
      Matrix.single 2 0 (1+Complex.I) := circuit_recovery q _
example (q : Fin 3) : apply_channel circuitRecovery
    (retainedPair q (encode code (Matrix.single 0 1 Complex.I))) =
      Matrix.single 0 1 Complex.I := circuit_recovery q _
example (q : Fin 3) (m : ℕ) (X : Joint m 3) :
    liftedRecovery (erasureChannel 9 3) (groupedCode q) circuitRecovery m X = X :=
  circuit_reference_recovery q m X
example (q : Fin 3) (X : Joint 2 3) :
    liftedRecovery (erasureChannel 9 3) (groupedCode q) circuitRecovery 2 X = X :=
  circuit_reference_recovery q 2 X
example : liftedRecovery (erasureChannel 9 3) (groupedCode 0) circuitRecovery 3
    (maximallyEntangled 3) = maximallyEntangled 3 := circuit_reference_recovery 0 3 _
example : liftedRecovery (erasureChannel 9 3) (groupedCode 1) circuitRecovery 3
    (maximallyEntangled 3) = maximallyEntangled 3 := circuit_reference_recovery 1 3 _
example : liftedRecovery (erasureChannel 9 3) (groupedCode 2) circuitRecovery 3
    (maximallyEntangled 3) = maximallyEntangled 3 := circuit_reference_recovery 2 3 _
example (q : Fin 3) (X : Q 3) :
    apply_channel circuitRecovery (retainedPair q (encode code X)) =
      apply_channel (pairRecovery q) (retainedPair q (encode code X)) := circuit_pair_agreement q X
example : runCircuit wrongSign (1,0) ≠ decodeCoordinates (1,0) := wrong_sign_witness
example : runCircuit missingSwap (0,1) ≠ decodeCoordinates (0,1) := missing_swap_witness
example : runCircuit wrongOrder (1,0) ≠ decodeCoordinates (1,0) := wrong_order_witness
example : runCircuit shiftedOutput (0,0) ≠ decodeCoordinates (0,0) := shifted_output_witness
example : circuitMatrix wrongSign ≠ decoder := wrong_sign_matrix
example : circuitMatrix missingSwap ≠ decoder := missing_swap_matrix
example : circuitMatrix wrongOrder ≠ decoder := wrong_order_matrix
example : circuitMatrix shiftedOutput ≠ decoder := shifted_output_matrix
end QutritCircuitRegression
