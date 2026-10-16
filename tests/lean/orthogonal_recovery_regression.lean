import Verification.QuantumOrthogonalErrorRecoveryContract

noncomputable section
open scoped BigOperators ComplexOrder
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract
open QuantumKnillLaflammeEnvironmentCriterion QuantumOrthogonalErrorRecoveryContract
open QuantumHelstromStateDiscrimination QuantumChannelTraceDistanceContract
namespace OrthogonalRecoveryRegression
abbrev C := QuantumOrthogonalErrorRecoveryContract.Examples.twoErrorCode
abbrev S := QuantumOrthogonalErrorRecoveryContract.Examples.sectorCode
abbrev J := QuantumOrthogonalErrorRecoveryContract.Examples.logicalCode
abbrev K := QuantumOrthogonalErrorRecoveryContract.Examples.twoErrorChannel
abbrev KS := QuantumOrthogonalErrorRecoveryContract.Examples.sectorChannel

example : C.probability 0 = 9/25 ∧ C.probability 1 = 16/25 := ⟨rfl, rfl⟩
example : (normalizedError C 0).conjTranspose * normalizedError C 0 = 1 :=
  normalized_isometry C 0 (by norm_num [C, Examples.twoErrorCode])
example : (normalizedError C 1).conjTranspose * normalizedError C 1 = 1 :=
  normalized_isometry C 1 (by norm_num [C, Examples.twoErrorCode])
example : (normalizedError C 0).conjTranspose * normalizedError C 1 = 0 := by
  simp [normalized_gram]
example : ∑ i, (recoveryOperators C i).conjTranspose * recoveryOperators C i = 1 :=
  recovery_complete C
example (X : Q 2) : apply_channel (recoveryChannel C) (apply_channel K (encode J X)) = X :=
  recovery_theorem C X
example : apply_channel (recoveryChannel C)
    (apply_channel K (encode J (Complex.I • Matrix.single 0 1 1))) =
      Complex.I • Matrix.single 0 1 1 := recovery_theorem C _
example : apply_channel (recoveryChannel C)
    (apply_channel K (encode J QuantumHelstromStateDiscrimination.Examples.rhoPlus)) =
      QuantumHelstromStateDiscrimination.Examples.rhoPlus := recovery_theorem C _
example : trace_distance (apply_channel (recoveryChannel C)
    (apply_channel K (encode J QuantumHelstromStateDiscrimination.Examples.rhoPlus)))
      QuantumHelstromStateDiscrimination.Examples.rhoPlus = 0 := by
  rw [recovery_theorem, trace_distance_self]
example : Density (apply_channel (recoveryChannel C)
    (apply_channel K (encode J QuantumHelstromStateDiscrimination.Examples.rhoPlus))) :=
  recovery_density C (channel_density K
    (encode_density J C.isometry QuantumHelstromStateDiscrimination.Examples.rhoPlus_density))
example : KnillLaflamme K J (Matrix.diagonal (fun i => (C.probability i : ℂ))) :=
  diagonal_environment C
example : EnvironmentConstant K J (Matrix.diagonal (fun i => (C.probability i : ℂ))) :=
  (knill_laflamme_equiv_environment _ _ _).mp (diagonal_environment C)
example : S.probability 1 = 0 := rfl
example : KS.operators 1 ≠ 0 := Examples.sector_error_nonzero
example : errorOnCode KS J 1 = 0 := Examples.sector_error_zero_on_code
example : normalizedError S 1 = 0 := normalized_zero S 1 rfl
example : unusedProjection S ≠ 0 := Examples.sector_unused_nonzero
example : (unusedProjection S).conjTranspose = unusedProjection S := unused_hermitian S
example : unusedProjection S * unusedProjection S = unusedProjection S := unused_idempotent S
example : apply_channel (recoveryChannel S)
    (apply_channel KS (encode J (Matrix.single 1 0 Complex.I))) = Matrix.single 1 0 Complex.I :=
  recovery_theorem S _

/-- Exact action on arbitrary physical input, including the unused subspace. -/
theorem sector_formula (Y : Q 4) : apply_channel (recoveryChannel S) Y =
    !![Y 0 0 + Y 2 2 + Y 3 3, Y 0 1; Y 1 0, Y 1 1] := by
  rw [apply_channel_eq, Fin.sum_univ_add]
  simp only [recoveryChannel, recoveryOperators, Fin.addCases_left, Fin.addCases_right]
  rw [Fin.sum_univ_two, Examples.sector_normalized.1, Examples.sector_normalized.2]
  simp only [residualOperator, Examples.sector_unused]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Examples.logicalCode, QuantumKnillLaflammeEnvironmentCriterion.Regression.code,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal,
      Matrix.single, Fin.sum_univ_succ]
  all_goals ring

example : apply_channel (recoveryChannel S) (QuantumNoBroadcastingMixed.basisProjector (2 : Fin 4)) =
    QuantumNoBroadcastingMixed.basisProjector (0 : Fin 2) := by
  rw [sector_formula]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [QuantumNoBroadcastingMixed.basisProjector,
    show (0 : Fin 4) ≠ 2 by decide, show (1 : Fin 4) ≠ 2 by decide,
    show (3 : Fin 4) ≠ 2 by decide]
example : (apply_channel (recoveryChannel S)
    (QuantumNoBroadcastingMixed.basisProjector (2 : Fin 4))).trace = 1 := by
  rw [recovery_trace, QuantumNoBroadcastingMixed.basisProjector_trace]
example : apply_channel (recoveryChannel S) (Matrix.single 2 3 Complex.I) = 0 := by
  rw [sector_formula]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [Matrix.single, Fin.ext_iff]

/-- Syndrome operators alone are NOT a trace-preserving map on all output states. -/
theorem incomplete_family :
    ∑ i : Fin 2, normalizedError S i * (normalizedError S i).conjTranspose ≠ (1 : Q 4) := by
  intro h
  have hu : unusedProjection S = 0 := by
    unfold unusedProjection errorProjection
    rw [h, sub_self]
  exact Examples.sector_unused_nonzero hu
example : ¬ (∑ i : Fin 2, normalizedError S i * (normalizedError S i).conjTranspose = (1 : Q 4)) :=
  incomplete_family
example (Y : Q 4) : (apply_channel (recoveryChannel S) Y).trace = Y.trace := recovery_trace S Y
example : QuantumNoBroadcastingMixed.IsCompletelyPositive (apply_channel (recoveryChannel S)) :=
  recovery_completely_positive S

/-- Rectangular physical channel C^2 -> C^4, with a genuine unused output space. -/
def rectangularChannel : KrausChannel 2 4 1 where
  operators := fun _ => J
  complete := by simpa using QuantumKnillLaflammeEnvironmentCriterion.Regression.code_isometry

def rectangularCode : DiagonalCode rectangularChannel (1 : Q 2) where
  nonempty := by decide
  isometry := by simp
  probability := fun _ => 1
  nonnegative := by intro _; norm_num
  normalized := by simp
  diagonal := by
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    simp [rectangularChannel, hij, QuantumKnillLaflammeEnvironmentCriterion.Regression.code_isometry]

example (X : Q 2) : apply_channel (recoveryChannel rectangularCode)
    (apply_channel rectangularChannel X) = X := by
  simpa [encode] using recovery_theorem rectangularCode X
example : (recoveryChannel rectangularCode).operators = recoveryOperators rectangularCode := rfl
example : QuantumOrthogonalErrorRecoveryContractSuite := verification_suite
end OrthogonalRecoveryRegression
