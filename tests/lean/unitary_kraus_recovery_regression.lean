import Verification.QuantumUnitaryKrausDiagonalizationRecoveryContract

noncomputable section
open scoped BigOperators ComplexOrder
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract QuantumHelstromStateDiscrimination
open QuantumComplementaryChannelContract QuantumKnillLaflammeEnvironmentCriterion
open QuantumOrthogonalErrorRecoveryContract QuantumUnitaryKrausDiagonalizationRecoveryContract
namespace UnitaryKrausRecoveryRegression
abbrev C := QuantumUnitaryKrausDiagonalizationRecoveryContract.Examples.complexCertificate
abbrev U := QuantumUnitaryKrausDiagonalizationRecoveryContract.Examples.complexUnitary
abbrev E := QuantumUnitaryKrausDiagonalizationRecoveryContract.Examples.complexChannel
abbrev J := QuantumUnitaryKrausDiagonalizationRecoveryContract.Examples.code
abbrev Z := QuantumUnitaryKrausDiagonalizationRecoveryContract.Examples.zeroCertificate
abbrev D := QuantumUnitaryKrausDiagonalizationRecoveryContract.Examples.repeatedCertificate

example : U.conjTranspose * U = 1 := Examples.complex_unitary_left
example : U * U.conjTranspose = 1 := Examples.complex_unitary_right
example : U.transpose.conjTranspose * U.transpose = 1 := transpose_isometry _ Examples.complex_unitary_right
example : U.transpose ≠ U.conjTranspose := Examples.transpose_not_adjoint
example : (C.coefficients 0 1).im ≠ 0 := Examples.imaginary_coefficient
example : (C.coefficients 0 1).im = 84/625 := by rw [Examples.complex_coefficients]; norm_num
example : (C.coefficients.transpose 0 1).im = -84/625 := by rw [Examples.complex_coefficients]; norm_num
example : C.coefficients.IsHermitian := by
  change C.coefficients.conjTranspose = C.coefficients
  rw [Examples.complex_coefficients]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [Matrix.conjTranspose_apply]
example : U.conjTranspose * C.coefficients * U = Matrix.diagonal (fun i => (C.weights i : ℂ)) :=
  C.diagonalizes
example : U * C.coefficients * U.conjTranspose ≠ Matrix.diagonal (fun i => (C.weights i : ℂ)) :=
  Examples.wrong_adjoint_diagonalization

/-- The actual incorrectly mixed channel does not satisfy the claimed diagonal
code, although its physical channel is still unchanged by that unitary mixing. -/
theorem wrong_mixing_fails :
    ¬ StandardKnillLaflamme
      (mixedChannel E U.conjTranspose (by simpa using Examples.complex_unitary_left)) J
      (Matrix.diagonal (fun i => (C.weights i : ℂ))) := by
  intro h
  have ht := mixed_coefficients E J C.coefficients U.conjTranspose
    (by simpa using Examples.complex_unitary_left) C.knill_laflamme
  simp only [Matrix.conjTranspose_conjTranspose] at ht
  have hi := coefficient_indices (by decide) _ J
    (U * C.coefficients * U.conjTranspose)
    (Matrix.diagonal (fun i => (C.weights i : ℂ))).transpose ht
    ((standard_iff_transpose _ _ _).mp h)
  apply Examples.wrong_adjoint_diagonalization
  ext i j
  simpa only [Matrix.transpose_apply] using (hi j i).symm

example : ∀ i, 0 ≤ C.weights i := weights_nonnegative C
example : ∑ i, C.weights i = 1 := weights_normalized C
example : (rotated C).operators 0 = ∑ a, U a 0 • E.operators a := mixed_operators _ _ _ _
example (X : Q 4) : apply_channel (rotated C) X = apply_channel E X := mixed_channel_invariant _ _ _ _
example : apply_channel (rotated C) (Matrix.single 0 3 Complex.I) =
    apply_channel E (Matrix.single 0 3 Complex.I) := mixed_channel_invariant _ _ _ _
example : (U.conjTranspose * C.coefficients * U) 0 1 =
    ∑ a, ∑ b, star (U a 0) * C.coefficients a b * U b 1 := coefficient_entry_sum _ _ _ _
example : J.conjTranspose * ((rotated C).operators 0).conjTranspose * (rotated C).operators 1 * J = 0 := by
  simpa using rotated_diagonal C 0 1
example : J.conjTranspose * ((rotated C).operators 0).conjTranspose * (rotated C).operators 0 * J =
    (9/25 : ℂ) • (1 : Q 2) := by
  have h := rotated_diagonal C 0 0
  rw [if_pos rfl] at h
  have hw : (C.weights 0 : ℂ) = 9/25 := by
    norm_num [C, Examples.complexCertificate, inverseCertificate, Examples.diagonalExample,
      QuantumOrthogonalErrorRecoveryContract.Examples.twoErrorCode]
  rw [hw] at h
  exact h
example (X : Q 2) : apply_channel (certifiedRecovery C) (apply_channel E (encode J X)) = X :=
  certified_recovery_theorem C X
example : apply_channel (certifiedRecovery C)
    (apply_channel E (encode J (Matrix.single 0 1 Complex.I))) = Matrix.single 0 1 Complex.I :=
  certified_recovery_theorem C _
example : apply_channel (certifiedRecovery C)
    (apply_channel E (encode J (Matrix.single 1 0 (2 + Complex.I)))) = Matrix.single 1 0 (2 + Complex.I) :=
  certified_recovery_theorem C _
example : apply_channel (certifiedRecovery C)
    (apply_channel E (encode J QuantumHelstromStateDiscrimination.Examples.rhoPlus)) =
      QuantumHelstromStateDiscrimination.Examples.rhoPlus := certified_recovery_theorem C _
example : Density (apply_channel (certifiedRecovery C)
    (apply_channel E (encode J QuantumHelstromStateDiscrimination.Examples.rhoPlus))) :=
  (logical_density_recovered C QuantumHelstromStateDiscrimination.Examples.rhoPlus_density).2
example : QuantumNoBroadcastingMixed.IsCompletelyPositive (apply_channel (certifiedRecovery C)) :=
  certified_recovery_cp C
example (Y : Q 4) : (apply_channel (certifiedRecovery C) Y).trace = Y.trace := certified_recovery_trace C Y
example : ∑ i, ((certifiedRecovery C).operators i).conjTranspose * (certifiedRecovery C).operators i = 1 :=
  certified_recovery_complete C
example : Z.weights 1 = 0 := rfl
example : normalizedError (diagonalCode Z) 1 = 0 := normalized_zero _ _ rfl
example : D.weights 0 = D.weights 1 ∧ D.weights 2 = 0 := ⟨rfl, rfl⟩
example : D.weights 0 > 0 ∧ D.weights 1 > 0 := by
  change (1/2 : ℝ) > 0 ∧ (1/2 : ℝ) > 0
  norm_num
example : ∑ i, D.weights i = 1 := weights_normalized D
example : normalizedError (diagonalCode D) 2 = 0 := normalized_zero _ _ rfl
example (X : Q 2) : apply_channel (certifiedRecovery Z)
    (apply_channel (inverseMixed (F := QuantumOrthogonalErrorRecoveryContract.Examples.sectorChannel)
      U Examples.complex_unitary_left) (encode J X)) = X := certified_recovery_theorem Z X
example : apply_channel (certifiedRecovery D)
    (apply_channel (inverseMixed (F := Examples.repeatedChannel) (1 : Q 3) (by simp))
      (encode J (Matrix.single 1 0 Complex.I))) = Matrix.single 1 0 Complex.I :=
  certified_recovery_theorem D _
example : QuantumUnitaryKrausDiagonalizationRecoveryContractSuite := verification_suite
end UnitaryKrausRecoveryRegression
