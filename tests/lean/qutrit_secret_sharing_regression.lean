import Verification.QuantumQutritTwoOfThreeSecretSharingContract

noncomputable section
open scoped BigOperators ComplexOrder Kronecker
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract QuantumHelstromStateDiscrimination
open QuantumKnillLaflammeEnvironmentCriterion QuantumReferencePreservingRecoveryContract
open QuantumErasureCorrectabilityContract QuantumQutritTwoOfThreeSecretSharingContract
namespace QutritSecretSharingRegression

example : code.conjTranspose * code = 1 := code_isometry
example (x : Fin 27) (s : Fin 3) : code x s = amplitude *
    ∑ r : Fin 3, (if x = triple r (r+s) (r+2*s) then (1 : ℂ) else 0) := code_column x s
example : code (triple 0 1 2) 1 = amplitude := by rw [code_entry]; rfl
example : code (triple 1 2 0) 1 = amplitude := by rw [code_entry]; rfl
example : code (triple 0 2 1) 2 = amplitude := by rw [code_entry]; rfl
example : code (triple 0 0 1) 0 = 0 := by rw [code_entry]; rfl
example : physicalIndex 0 (triple 0 1 2) = triple 2 0 1 := rfl
example : physicalIndex 1 (triple 0 1 2) = triple 1 2 0 := rfl
example : physicalIndex 2 (triple 0 1 2) = triple 0 1 2 := rfl
example (q : Fin 3) : Function.Bijective (physicalIndex q) := physicalIndex_bijective q
example (q : Fin 3) (X : Q 3) :
    regroup q (encode code X) = encode (groupedCode q) X := regroup_encode q X
example (X : Q 3) : share 0 (encode code X) = X.trace • mixedShare := share_privacy 0 X
example (X : Q 3) : share 1 (encode code X) = X.trace • mixedShare := share_privacy 1 X
example (X : Q 3) : share 2 (encode code X) = X.trace • mixedShare := share_privacy 2 X
example : mixedShare = (1/3 : ℂ) • (1 : Q 3) := rfl
example : Density mixedShare := mixedShare_density
example (q : Fin 3) : share q (encode code (Matrix.single 0 1 Complex.I)) = 0 :=
  share_coherence q 0 1 (by decide) _
example (q : Fin 3) : share q (encode code (Matrix.single 2 0 (1+Complex.I))) = 0 :=
  share_coherence q 2 0 (by decide) _
example (q : Fin 3) : share q (encode code (Matrix.single 1 1 1)) = mixedShare := by
  rw [share_privacy, Matrix.trace_single_eq_same, one_smul]
example (X : Q 3) : apply_channel (pairRecovery 0) (retainedPair 0 (encode code X)) = X :=
  pair_recovery 0 X
example (X : Q 3) : apply_channel (pairRecovery 1) (retainedPair 1 (encode code X)) = X :=
  pair_recovery 1 X
example (X : Q 3) : apply_channel (pairRecovery 2) (retainedPair 2 (encode code X)) = X :=
  pair_recovery 2 X
example (q : Fin 3) : apply_channel (pairRecovery q)
    (retainedPair q (encode code (Matrix.single 0 1 Complex.I))) = Matrix.single 0 1 Complex.I :=
  pair_recovery q _
example (q : Fin 3) : ∑ j, ((pairRecovery q).operators j).conjTranspose *
    (pairRecovery q).operators j = 1 := (pairRecovery q).complete
example (q : Fin 3) : QuantumNoBroadcastingMixed.IsCompletelyPositive (apply_channel (pairRecovery q)) :=
  channel_completely_positive _
example (q : Fin 3) (Y : Q 9) : (apply_channel (pairRecovery q) Y).trace = Y.trace :=
  channel_trace_preserving _ _
example (q : Fin 3) (Y : Q 9) (h : Density Y) : Density (apply_channel (pairRecovery q) Y) :=
  channel_density _ h
example (q : Fin 3) (m : ℕ) (X : Joint m 3) :
    liftedRecovery (erasureChannel 9 3) (groupedCode q) (pairRecovery q) m X = X :=
  reference_recovery q m X
example (q : Fin 3) (X : Joint 2 3) :
    liftedRecovery (erasureChannel 9 3) (groupedCode q) (pairRecovery q) 2 X = X :=
  reference_recovery q 2 X
example (q : Fin 3) (m : ℕ) (X : Joint m 3) :
    amplify (environmentMap (erasureChannel 9 3) (groupedCode q)) m X =
      traceLogical X ⊗ₖ mixedShare := reference_share_independence q m X
example : QuantumNoBroadcastingMixed.IsDensityMatrix (maximallyEntangled 3) :=
  maximallyEntangled_density (by decide)
example : liftedRecovery (erasureChannel 9 3) (groupedCode 0) (pairRecovery 0) 3
    (maximallyEntangled 3) = maximallyEntangled 3 := maximally_entangled_recovery 0
example : liftedRecovery (erasureChannel 9 3) (groupedCode 1) (pairRecovery 1) 3
    (maximallyEntangled 3) = maximallyEntangled 3 := maximally_entangled_recovery 1
example : liftedRecovery (erasureChannel 9 3) (groupedCode 2) (pairRecovery 2) 3
    (maximallyEntangled 3) = maximallyEntangled 3 := maximally_entangled_recovery 2
example : ¬ ∃ s, ∃ R : KrausChannel 3 3 s,
    ∀ X : Q 3, apply_channel R (share 0 (encode code X)) = X := single_share_not_recoverable 0
example : ¬ ∃ s, ∃ R : KrausChannel 3 3 s,
    ∀ X : Q 3, apply_channel R (share 1 (encode code X)) = X := single_share_not_recoverable 1
example : ¬ ∃ s, ∃ R : KrausChannel 3 3 s,
    ∀ X : Q 3, apply_channel R (share 2 (encode code X)) = X := single_share_not_recoverable 2

end QutritSecretSharingRegression
