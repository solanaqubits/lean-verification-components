import Verification.QuantumKnillLaflammeGeneralRecoveryTheorem

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract QuantumHelstromStateDiscrimination
open QuantumKnillLaflammeEnvironmentCriterion QuantumKnillLaflammeGeneralRecoveryTheorem
namespace GeneralRecoveryRegression
abbrev C := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.complexCode
abbrev E := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.complexChannel
abbrev J := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.logicalCode
abbrev Z := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.zeroCode
abbrev D := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.repeatedCode
abbrev T := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.rectangularCode
abbrev ET := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.rectangularChannel

example : C.coefficients.IsHermitian := coefficients_hermitian C
example : (C.coefficients 0 1).im = 84/625 := by norm_num [C, Examples.complexCode]
example : (C.coefficients 1 0).im = -84/625 := by norm_num [C, Examples.complexCode]
example : KnillLaflamme E J C.coefficients.transpose :=
  (standard_iff_transpose _ _ _).mp C.knill_laflamme
example : (spectralUnitary C).conjTranspose * spectralUnitary C = 1 := spectral_unitary_left C
example : spectralUnitary C * (spectralUnitary C).conjTranspose = 1 := spectral_unitary_right C
example : (spectralUnitary C).conjTranspose * C.coefficients * spectralUnitary C =
    Matrix.diagonal (fun i => (spectralWeights C i : ℂ)) := spectral_diagonalizes C
example : ∀ i, 0 ≤ spectralWeights C i := spectral_weights_nonnegative C
example : ∑ i, spectralWeights C i = 1 := spectral_weights_normalized C
example (X : Q 2) : apply_channel (generalRecovery C) (apply_channel E (encode J X)) = X :=
  general_recovery_theorem C X
example : apply_channel (generalRecovery C)
    (apply_channel E (encode J (Matrix.single 0 1 Complex.I))) = Matrix.single 0 1 Complex.I :=
  general_recovery_theorem C _
example : apply_channel (generalRecovery C)
    (apply_channel E (encode J (Matrix.single 1 0 (2+Complex.I)))) = Matrix.single 1 0 (2+Complex.I) :=
  general_recovery_theorem C _
example : apply_channel (generalRecovery C)
    (apply_channel E (encode J QuantumHelstromStateDiscrimination.Examples.rhoPlus)) =
      QuantumHelstromStateDiscrimination.Examples.rhoPlus := general_recovery_theorem C _
example : Density (apply_channel (generalRecovery C)
    (apply_channel E (encode J QuantumHelstromStateDiscrimination.Examples.rhoPlus))) :=
  (logical_density_recovered C QuantumHelstromStateDiscrimination.Examples.rhoPlus_density).2
example : ∃ R : KrausChannel 4 2 6, ∀ X : Q 2,
    apply_channel R (apply_channel E (encode J X)) = X := exists_recovery C
example : QuantumNoBroadcastingMixed.IsCompletelyPositive (apply_channel (generalRecovery C)) :=
  general_recovery_cp C
example (Y : Q 4) : (apply_channel (generalRecovery C) Y).trace = Y.trace := general_recovery_trace C Y
example : ∑ i, ((generalRecovery C).operators i).conjTranspose * (generalRecovery C).operators i = 1 :=
  general_recovery_complete C
example : Z.coefficients = Matrix.diagonal ![1, 0] := rfl
example : Z.coefficients *ᵥ ![0, 1] = 0 := by
  ext i; fin_cases i <;> norm_num [Z, Examples.zeroCode, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
example (X : Q 2) : apply_channel (generalRecovery Z)
    (apply_channel QuantumOrthogonalErrorRecoveryContract.Examples.sectorChannel (encode J X)) = X :=
  general_recovery_theorem Z X
example : apply_channel (generalRecovery Z)
    (apply_channel QuantumOrthogonalErrorRecoveryContract.Examples.sectorChannel
      (encode J (Matrix.single 1 0 Complex.I))) = Matrix.single 1 0 Complex.I :=
  general_recovery_theorem Z _
example : D.coefficients = Matrix.diagonal ![1/2, 1/2, 0] := rfl
example : D.coefficients *ᵥ ![0, 0, 1] = 0 := by
  ext i; fin_cases i <;> norm_num [D, Examples.repeatedCode, Matrix.diagonal, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
example : D.coefficients *ᵥ ![1, 0, 0] = (1/2 : ℂ) • ![1, 0, 0] := by
  ext i; fin_cases i <;> norm_num [D, Examples.repeatedCode, Matrix.diagonal, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
example : D.coefficients *ᵥ ![0, 1, 0] = (1/2 : ℂ) • ![0, 1, 0] := by
  ext i; fin_cases i <;> norm_num [D, Examples.repeatedCode, Matrix.diagonal, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
example (X : Q 2) : apply_channel (generalRecovery D)
    (apply_channel QuantumUnitaryKrausDiagonalizationRecoveryContract.Examples.repeatedChannel
      (encode J X)) = X := general_recovery_theorem D X
example : apply_channel (generalRecovery D)
    (apply_channel QuantumUnitaryKrausDiagonalizationRecoveryContract.Examples.repeatedChannel
      (encode J (Matrix.single 0 1 (1+Complex.I)))) = Matrix.single 0 1 (1+Complex.I) :=
  general_recovery_theorem D _
example : ∀ i, 0 ≤ spectralWeights D i := spectral_weights_nonnegative D
example : ∑ i, spectralWeights D i = 1 := spectral_weights_normalized D
example (X : Q 2) : apply_channel (generalRecovery T) (apply_channel ET X) = X :=
  Examples.rectangular_recovery X
example : apply_channel (generalRecovery T) (apply_channel ET (Matrix.single 0 1 Complex.I)) =
    Matrix.single 0 1 Complex.I := Examples.rectangular_recovery _
example : ∑ i, ((generalRecovery T).operators i).conjTranspose * (generalRecovery T).operators i =
    (1 : Q 4) := general_recovery_complete T
example (Y : Q 4) : (apply_channel (generalRecovery T) Y).trace = Y.trace := general_recovery_trace T Y
example : Density (apply_channel (generalRecovery T)
    (QuantumNoBroadcastingMixed.basisProjector (3 : Fin 4))) :=
  general_recovery_density T (basis_density _)
example : QuantumKnillLaflammeGeneralRecoveryTheoremSuite := verification_suite
end GeneralRecoveryRegression
