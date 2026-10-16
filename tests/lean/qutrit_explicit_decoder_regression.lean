import Verification.QuantumQutritSecretSharingExplicitDecoder

noncomputable section
open scoped BigOperators ComplexOrder Kronecker
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract QuantumHelstromStateDiscrimination
open QuantumKnillLaflammeEnvironmentCriterion QuantumReferencePreservingRecoveryContract
open QuantumErasureCorrectabilityContract QuantumQutritTwoOfThreeSecretSharingContract
open QuantumQutritSecretSharingExplicitDecoder
namespace QutritExplicitDecoderRegression

example : Function.LeftInverse encodeCoordinates decodeCoordinates := coordinates_left_inverse
example : Function.RightInverse encodeCoordinates decodeCoordinates := coordinates_right_inverse
example : decodeCoordinates (0,1) = (1,2) := rfl
example : decodeCoordinates (1,0) = (2,2) := rfl
example : encodeCoordinates (1,2) = (0,1) := rfl
example : decoder (pair (1 : Fin 3) (2 : Fin 3)) (pair (0 : Fin 3) (1 : Fin 3)) = 1 := rfl
example : decoder (pair (0 : Fin 3) (1 : Fin 3)) (pair (1 : Fin 3) (2 : Fin 3)) = 0 := rfl
example : decoder.conjTranspose * decoder = 1 := decoder_unitary_left
example : decoder * decoder.conjTranspose = 1 := decoder_unitary_right
example : liftedDecoder * groupedCode 0 = separatedCode := decoder_code 0
example : liftedDecoder * groupedCode 1 = separatedCode := decoder_code 1
example : liftedDecoder * groupedCode 2 = separatedCode := decoder_code 2
example : separatedCode (triple 1 2 2) 1 = amplitude := by rw [separated_entry]; rfl
example : separatedCode (triple 1 2 0) 1 = 0 := by rw [separated_entry]; rfl
example (q : Fin 3) (X : Q 3) :
    liftedDecoder * encode (groupedCode q) X * liftedDecoder.conjTranspose = factorized X :=
  decoding_factorization q X
example (q : Fin 3) : liftedDecoder * encode (groupedCode q) (Matrix.single 0 1 Complex.I) *
    liftedDecoder.conjTranspose = factorized (Matrix.single 0 1 Complex.I) :=
  decoding_factorization q _
example (t : Fin 3) : recoveryOperator t = erasureOperator 3 3 t * decoder := rfl
example : ∑ t, (recoveryOperator t).conjTranspose * recoveryOperator t = 1 := recovery_complete
example : QuantumNoBroadcastingMixed.IsCompletelyPositive (apply_channel explicitRecovery) :=
  channel_completely_positive _
example (Y : Q 9) : (apply_channel explicitRecovery Y).trace = Y.trace :=
  channel_trace_preserving _ _
example (Y : Q 9) (h : Density Y) : Density (apply_channel explicitRecovery Y) := channel_density _ h
example (q t w : Fin 3) : recoveryOperator t * erasureOperator 9 3 w * groupedCode q =
    (if t = w then amplitude else 0) • (1 : Q 3) := recovery_branch q t w
example (q : Fin 3) : recoveryOperator 0 * erasureOperator 9 3 1 * groupedCode q = 0 := by
  rw [recovery_branch]; norm_num
example (X : Q 3) : apply_channel explicitRecovery (retainedPair 0 (encode code X)) = X :=
  explicit_recovery 0 X
example (X : Q 3) : apply_channel explicitRecovery (retainedPair 1 (encode code X)) = X :=
  explicit_recovery 1 X
example (X : Q 3) : apply_channel explicitRecovery (retainedPair 2 (encode code X)) = X :=
  explicit_recovery 2 X
example (q : Fin 3) : apply_channel explicitRecovery
    (retainedPair q (encode code (Matrix.single 2 0 (1+Complex.I)))) =
      Matrix.single 2 0 (1+Complex.I) := explicit_recovery q _
example (q : Fin 3) (m : ℕ) (X : Joint m 3) :
    liftedRecovery (erasureChannel 9 3) (groupedCode q) explicitRecovery m X = X :=
  explicit_reference_recovery q m X
example (q : Fin 3) (X : Joint 2 3) :
    liftedRecovery (erasureChannel 9 3) (groupedCode q) explicitRecovery 2 X = X :=
  explicit_reference_recovery q 2 X
example : liftedRecovery (erasureChannel 9 3) (groupedCode 0) explicitRecovery 3
    (maximallyEntangled 3) = maximallyEntangled 3 := explicit_reference_recovery 0 3 _
example : liftedRecovery (erasureChannel 9 3) (groupedCode 1) explicitRecovery 3
    (maximallyEntangled 3) = maximallyEntangled 3 := explicit_reference_recovery 1 3 _
example : liftedRecovery (erasureChannel 9 3) (groupedCode 2) explicitRecovery 3
    (maximallyEntangled 3) = maximallyEntangled 3 := explicit_reference_recovery 2 3 _
example (q : Fin 3) (X : Q 3) :
    apply_channel explicitRecovery (retainedPair q (encode code X)) =
      apply_channel (pairRecovery q) (retainedPair q (encode code X)) := agrees_with_pairRecovery q X

example : factorized (Matrix.single 0 1 Complex.I) (triple 0 2 2) (triple 1 1 1) =
    Complex.I / 3 := by
  norm_num [factorized, triple, pair, finProdFinEquiv, Fin.divNat, Fin.modNat,
    maximallyEntangled, Matrix.single]
  ring
example : factorized (Matrix.single 0 1 Complex.I) (triple 0 2 1) (triple 1 1 1) = 0 := by
  norm_num [factorized, triple, pair, finProdFinEquiv, Fin.divNat, Fin.modNat,
    maximallyEntangled, Matrix.single]

end QutritExplicitDecoderRegression
