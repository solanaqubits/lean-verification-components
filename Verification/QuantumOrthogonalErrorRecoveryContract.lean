/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumKnillLaflammeEnvironmentCriterion
import Verification.QuantumComplementaryChannelContract
import Verification.QuantumCPTPChannelContract
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Explicit finite recovery for diagonal Knill-Laflamme data.
Zero-probability errors are zero on the code. Reset operators on the unused
output subspace complete the recovery to a trace-preserving channel.
No diagonalization of general Knill-Laflamme coefficients is claimed. -/
noncomputable section
open scoped BigOperators ComplexOrder
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract
open QuantumKnillLaflammeEnvironmentCriterion QuantumHelstromStateDiscrimination
namespace QuantumOrthogonalErrorRecoveryContract
variable {k d e r : ℕ}

/-- Input data, with no recovery map assumed. Output dimension e may differ from d. -/
structure DiagonalCode (K : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ) where
  nonempty : 0 < k
  isometry : J.conjTranspose * J = 1
  probability : Fin r → ℝ
  nonnegative : ∀ i, 0 ≤ probability i
  normalized : ∑ i, probability i = 1
  diagonal : ∀ i j, J.conjTranspose * (K.operators i).conjTranspose * K.operators j * J =
    if i = j then (probability i : ℂ) • (1 : Q k) else 0

variable {K : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}

def errorOnCode (K : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ)
    (i : Fin r) := K.operators i * J

def amplitude (C : DiagonalCode K J) (i : Fin r) : ℂ := (Real.sqrt (C.probability i) : ℂ)

/-- Explicit zero branch avoids normalizing an error of zero probability. -/
def normalizedError (C : DiagonalCode K J) (i : Fin r) : Matrix (Fin e) (Fin k) ℂ :=
  if C.probability i = 0 then 0 else (amplitude C i)⁻¹ • errorOnCode K J i

theorem error_gram (C : DiagonalCode K J) (i j : Fin r) :
    (errorOnCode K J i).conjTranspose * errorOnCode K J j =
      if i = j then (C.probability i : ℂ) • (1 : Q k) else 0 := by
  simpa only [errorOnCode, Matrix.conjTranspose_mul, Matrix.mul_assoc] using C.diagonal i j

theorem zero_error (C : DiagonalCode K J) (i : Fin r) (h : C.probability i = 0) :
    errorOnCode K J i = 0 := by
  apply Matrix.conjTranspose_mul_self_eq_zero.mp
  simpa [h] using error_gram C i i

@[simp] theorem amplitude_star (C : DiagonalCode K J) (i : Fin r) :
    star (amplitude C i) = amplitude C i := by simp [amplitude]

theorem amplitude_sq (C : DiagonalCode K J) (i : Fin r) :
    amplitude C i * amplitude C i = (C.probability i : ℂ) := by
  simp only [amplitude, ← Complex.ofReal_mul]
  exact congrArg Complex.ofReal (Real.mul_self_sqrt (C.nonnegative i))

theorem amplitude_ne_zero (C : DiagonalCode K J) (i : Fin r)
    (h : C.probability i ≠ 0) : amplitude C i ≠ 0 := by
  simp only [amplitude, ne_eq, Complex.ofReal_eq_zero]
  exact ne_of_gt (Real.sqrt_pos.2 (lt_of_le_of_ne (C.nonnegative i) (Ne.symm h)))

theorem normalized_zero (C : DiagonalCode K J) (i : Fin r) (h : C.probability i = 0) :
    normalizedError C i = 0 := by simp [normalizedError, h]

theorem error_factorization (C : DiagonalCode K J) (i : Fin r) :
    errorOnCode K J i = amplitude C i • normalizedError C i := by
  by_cases h : C.probability i = 0
  · simp [normalizedError, h, zero_error C i h]
  · simp [normalizedError, h, smul_smul, amplitude_ne_zero C i h]

theorem normalized_gram (C : DiagonalCode K J) (i j : Fin r) :
    (normalizedError C i).conjTranspose * normalizedError C j =
      if i = j ∧ C.probability i ≠ 0 then (1 : Q k) else 0 := by
  by_cases hi : C.probability i = 0
  · simp [normalized_zero C i hi, hi]
  by_cases hj : C.probability j = 0
  · by_cases hij : i = j
    · subst j; contradiction
    · simp [normalized_zero C j hj, hij]
  simp only [normalizedError, if_neg hi, if_neg hj, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, error_gram C]
  simp only [amplitude, Complex.star_def, map_inv₀, Complex.conj_ofReal]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, smul_smul, ne_eq, hi, not_false_eq_true, and_self]
    change ((amplitude C i)⁻¹ * (amplitude C i)⁻¹ * (C.probability i : ℂ)) • (1 : Q k) = 1
    rw [← amplitude_sq C i]
    rw [show (amplitude C i)⁻¹ * (amplitude C i)⁻¹ *
      (amplitude C i * amplitude C i) = 1 by field_simp [amplitude_ne_zero C i hi]]
    exact one_smul _ _
  · simp [hij]

theorem normalized_isometry (C : DiagonalCode K J) (i : Fin r)
    (h : 0 < C.probability i) :
    (normalizedError C i).conjTranspose * normalizedError C i = 1 := by
  simp [normalized_gram, ne_of_gt h]

def errorProjection (C : DiagonalCode K J) : Q e :=
  ∑ i, normalizedError C i * (normalizedError C i).conjTranspose

def unusedProjection (C : DiagonalCode K J) : Q e := 1 - errorProjection C

theorem projection_on_error (C : DiagonalCode K J) (j : Fin r) :
    errorProjection C * normalizedError C j = normalizedError C j := by
  classical
  rw [errorProjection, Matrix.sum_mul]
  by_cases hj : C.probability j = 0
  · simp [normalized_zero C j hj]
  · calc
      _ = ∑ i : Fin r, if i = j then normalizedError C j else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Matrix.mul_assoc, normalized_gram]
        by_cases h : i = j
        · subst i; simp [hj]
        · simp [h]
      _ = _ := by simp

theorem projection_hermitian (C : DiagonalCode K J) :
    (errorProjection C).conjTranspose = errorProjection C := by
  simp [errorProjection, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul]

theorem projection_idempotent (C : DiagonalCode K J) :
    errorProjection C * errorProjection C = errorProjection C := by
  conv_rhs => rw [errorProjection]
  conv_lhs => rhs; rw [errorProjection]
  rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Matrix.mul_assoc, projection_on_error]

theorem unused_hermitian (C : DiagonalCode K J) :
    (unusedProjection C).conjTranspose = unusedProjection C := by
  simp [unusedProjection, Matrix.conjTranspose_sub, projection_hermitian]

theorem unused_idempotent (C : DiagonalCode K J) :
    unusedProjection C * unusedProjection C = unusedProjection C := by
  simp only [unusedProjection, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    projection_idempotent]
  abel

theorem unused_on_error (C : DiagonalCode K J) (j : Fin r) :
    unusedProjection C * normalizedError C j = 0 := by
  simp [unusedProjection, Matrix.sub_mul, projection_on_error]

theorem unused_on_code_error (C : DiagonalCode K J) (j : Fin r) :
    unusedProjection C * errorOnCode K J j = 0 := by
  rw [error_factorization C j, Matrix.mul_smul, unused_on_error, smul_zero]

/-- Kraus operators for reset on the unused output subspace. There is one per
output basis vector, rather than an ill-typed rectangular projection. -/
def residualOperator (C : DiagonalCode K J) (a : Fin e) : Matrix (Fin k) (Fin e) ℂ :=
  Matrix.single (⟨0, C.nonempty⟩ : Fin k) a (1 : ℂ) * unusedProjection C

theorem residual_complete (C : DiagonalCode K J) :
    ∑ a, (residualOperator C a).conjTranspose * residualOperator C a =
      unusedProjection C := by
  have hr := (reset_channel (d := e) (⟨0, C.nonempty⟩ : Fin k)).complete
  change ∑ a : Fin e, (Matrix.single (⟨0, C.nonempty⟩ : Fin k) a (1 : ℂ)).conjTranspose *
    Matrix.single (⟨0, C.nonempty⟩ : Fin k) a (1 : ℂ) = 1 at hr
  calc
    _ = (unusedProjection C).conjTranspose *
        (∑ a : Fin e, (Matrix.single (⟨0, C.nonempty⟩ : Fin k) a (1 : ℂ)).conjTranspose *
          Matrix.single (⟨0, C.nonempty⟩ : Fin k) a (1 : ℂ)) * unusedProjection C := by
      simp only [residualOperator, Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul,
        Matrix.mul_assoc]
    _ = unusedProjection C := by rw [hr, Matrix.mul_one, unused_hermitian, unused_idempotent]

/-- The first r operators recover syndromes; the last e reset the unused space. -/
def recoveryOperators (C : DiagonalCode K J) : Fin (r + e) → Matrix (Fin k) (Fin e) ℂ :=
  Fin.addCases (fun i => (normalizedError C i).conjTranspose) (residualOperator C)

theorem recovery_complete (C : DiagonalCode K J) :
    ∑ a, (recoveryOperators C a).conjTranspose * recoveryOperators C a = 1 := by
  rw [Fin.sum_univ_add]
  simp only [recoveryOperators, Fin.addCases_left, Fin.addCases_right,
    Matrix.conjTranspose_conjTranspose]
  rw [residual_complete]
  change errorProjection C + (1 - errorProjection C) = 1
  abel

def recoveryChannel (C : DiagonalCode K J) : KrausChannel e k (r + e) where
  operators := recoveryOperators C
  complete := recovery_complete C

/-- Diagonal data is a specialization of module 182's environment convention. -/
theorem diagonal_environment (C : DiagonalCode K J) :
    KnillLaflamme K J (Matrix.diagonal (fun i => (C.probability i : ℂ))) := by
  intro i j
  rw [C.diagonal]
  by_cases h : i = j
  · subst j; simp
  · simp [Matrix.diagonal, h, Ne.symm h]

theorem normalized_on_code_error (C : DiagonalCode K J) (i j : Fin r) :
    (normalizedError C i).conjTranspose * errorOnCode K J j =
      if i = j then amplitude C j • (1 : Q k) else 0 := by
  rw [error_factorization C j, Matrix.mul_smul, normalized_gram]
  by_cases h : i = j
  · subst j
    by_cases hi : C.probability i = 0
    · simp [hi, amplitude]
    · simp [hi]
  · simp [h]

theorem residual_on_code_error (C : DiagonalCode K J) (a : Fin e) (j : Fin r) :
    residualOperator C a * errorOnCode K J j = 0 := by
  rw [residualOperator, Matrix.mul_assoc, unused_on_code_error, Matrix.mul_zero]

/-- Rearrange the rectangular sandwich without assuming Hermiticity of X. -/
theorem sandwich_compose (R : Matrix (Fin k) (Fin e) ℂ)
    (A : Matrix (Fin e) (Fin k) ℂ) (X : Q k) :
    R * (A * X * A.conjTranspose) * R.conjTranspose =
      (R * A) * X * (R * A).conjTranspose := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem recover_one_error (C : DiagonalCode K J) (j : Fin r) (X : Q k) :
    apply_channel (recoveryChannel C)
      (errorOnCode K J j * X * (errorOnCode K J j).conjTranspose) =
        (C.probability j : ℂ) • X := by
  classical
  rw [apply_channel_eq, Fin.sum_univ_add]
  simp only [recoveryChannel, recoveryOperators, Fin.addCases_left, Fin.addCases_right]
  have hres : ∀ a : Fin e, residualOperator C a *
      (errorOnCode K J j * X * (errorOnCode K J j).conjTranspose) *
      (residualOperator C a).conjTranspose = 0 := by
    intro a
    rw [sandwich_compose, residual_on_code_error]
    simp
  simp only [hres, Finset.sum_const_zero, add_zero]
  calc
    _ = ∑ i : Fin r, if i = j then (C.probability j : ℂ) • X else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [sandwich_compose, normalized_on_code_error]
      by_cases hij : i = j
      · simp only [if_pos hij, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
          Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
        simp only [amplitude, Complex.star_def, Complex.conj_ofReal]
        change (amplitude C j * amplitude C j) • X = (C.probability j : ℂ) • X
        rw [amplitude_sq]
      · simp [hij]
    _ = _ := by simp

theorem encoded_channel_sum (K : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (X : Q k) :
    apply_channel K (encode J X) =
      ∑ j, errorOnCode K J j * X * (errorOnCode K J j).conjTranspose := by
  simp only [apply_channel_eq, encode, errorOnCode, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Exact recovery of every complex logical matrix, including off-diagonal units. -/
theorem recovery_theorem (C : DiagonalCode K J) (X : Q k) :
    apply_channel (recoveryChannel C) (apply_channel K (encode J X)) = X := by
  rw [encoded_channel_sum, map_sum]
  simp only [recover_one_error]
  rw [← Finset.sum_smul, ← Complex.ofReal_sum, C.normalized, Complex.ofReal_one, one_smul]

theorem recovery_completely_positive (C : DiagonalCode K J) :
    QuantumNoBroadcastingMixed.IsCompletelyPositive (apply_channel (recoveryChannel C)) :=
  channel_completely_positive _

theorem recovery_trace (C : DiagonalCode K J) (Y : Q e) :
    (apply_channel (recoveryChannel C) Y).trace = Y.trace := channel_trace_preserving _ _

theorem recovery_density (C : DiagonalCode K J) {Y : Q e} (hY : Density Y) :
    Density (apply_channel (recoveryChannel C) Y) := channel_density _ hY

namespace Examples

abbrev logicalCode := QuantumKnillLaflammeEnvironmentCriterion.Regression.code
abbrev twoErrorChannel := QuantumKnillLaflammeEnvironmentCriterion.Regression.orthogonal_channel

def twoErrorCode : DiagonalCode twoErrorChannel logicalCode where
  nonempty := by decide
  isometry := QuantumKnillLaflammeEnvironmentCriterion.Regression.code_isometry
  probability := ![9/25, 16/25]
  nonnegative := by intro i; fin_cases i <;> norm_num
  normalized := by norm_num [Fin.sum_univ_succ]
  diagonal := by
    intro i j
    have h := QuantumKnillLaflammeEnvironmentCriterion.Regression.orthogonal_criterion j i
    fin_cases i <;> fin_cases j <;>
      simpa [QuantumKnillLaflammeEnvironmentCriterion.Regression.environment] using h

theorem two_error_recovery (X : Q 2) :
    apply_channel (recoveryChannel twoErrorCode)
      (apply_channel twoErrorChannel (encode logicalCode X)) = X := recovery_theorem _ _

/-- A nonzero physical error can have zero probability on the selected code. -/
def sectorErrors : Fin 2 → Q 4 :=
  ![Matrix.diagonal ![1, 1, 0, 0], Matrix.diagonal ![0, 0, 1, 1]]

def sectorChannel : KrausChannel 4 4 2 where
  operators := sectorErrors
  complete := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [sectorErrors, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal,
        Fin.sum_univ_succ, Matrix.one_apply]

def sectorCode : DiagonalCode sectorChannel logicalCode where
  nonempty := by decide
  isometry := QuantumKnillLaflammeEnvironmentCriterion.Regression.code_isometry
  probability := ![1, 0]
  nonnegative := by intro i; fin_cases i <;> norm_num
  normalized := by norm_num [Fin.sum_univ_succ]
  diagonal := by
    intro i j
    ext a b
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
      norm_num [sectorChannel, sectorErrors, logicalCode,
        QuantumKnillLaflammeEnvironmentCriterion.Regression.code,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal,
        Fin.sum_univ_succ, Matrix.one_apply]

theorem sector_normalized : normalizedError sectorCode 0 = logicalCode ∧
    normalizedError sectorCode 1 = 0 := by
  constructor
  · rw [normalizedError, if_neg (show sectorCode.probability 0 ≠ 0 by change (1 : ℝ) ≠ 0; norm_num)]
    have ha : amplitude sectorCode 0 = 1 := by norm_num [amplitude, sectorCode]
    rw [ha, inv_one, one_smul]
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [errorOnCode, sectorChannel, sectorErrors, logicalCode,
        QuantumKnillLaflammeEnvironmentCriterion.Regression.code,
        Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_succ]
  · exact normalized_zero sectorCode 1 rfl

theorem sector_unused : unusedProjection sectorCode = Matrix.diagonal ![0, 0, 1, 1] := by
  rw [unusedProjection, errorProjection, Fin.sum_univ_two, sector_normalized.1,
    sector_normalized.2]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [logicalCode, QuantumKnillLaflammeEnvironmentCriterion.Regression.code,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, Matrix.diagonal,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem sector_unused_nonzero : unusedProjection sectorCode ≠ 0 := by
  rw [sector_unused]
  intro h
  have h22 := congrArg (fun M : Q 4 => M 2 2) h
  change (1 : ℂ) = 0 at h22
  exact one_ne_zero h22

theorem sector_error_nonzero : sectorChannel.operators 1 ≠ 0 := by
  intro h
  have h22 := congrArg (fun M : Q 4 => M 2 2) h
  change (1 : ℂ) = 0 at h22
  exact one_ne_zero h22

theorem sector_error_zero_on_code : errorOnCode sectorChannel logicalCode 1 = 0 :=
  zero_error sectorCode 1 rfl

theorem sector_recovery (X : Q 2) :
    apply_channel (recoveryChannel sectorCode)
      (apply_channel sectorChannel (encode logicalCode X)) = X := recovery_theorem _ _

end Examples

structure QuantumOrthogonalErrorRecoveryContractSuite : Prop where
  complete : ∀ {k d e r} {K : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : DiagonalCode K J), ∑ a, (recoveryOperators C a).conjTranspose * recoveryOperators C a = 1
  exact_recovery : ∀ {k d e r} {K : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : DiagonalCode K J) (X : Q k),
    apply_channel (recoveryChannel C) (apply_channel K (encode J X)) = X
  completely_positive : ∀ {k d e r} {K : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : DiagonalCode K J),
    QuantumNoBroadcastingMixed.IsCompletelyPositive (apply_channel (recoveryChannel C))
  trace_preserving : ∀ {k d e r} {K : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : DiagonalCode K J) (Y : Q e), (apply_channel (recoveryChannel C) Y).trace = Y.trace
  preserves_density : ∀ {k d e r} {K : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : DiagonalCode K J) {Y : Q e}, Density Y → Density (apply_channel (recoveryChannel C) Y)
  zero_errors : ∀ {k d e r} {K : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : DiagonalCode K J) (i : Fin r), C.probability i = 0 → errorOnCode K J i = 0
  orthogonal_isometries : ∀ {k d e r} {K : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : DiagonalCode K J) (i j : Fin r),
    (normalizedError C i).conjTranspose * normalizedError C j =
      if i = j ∧ C.probability i ≠ 0 then (1 : Q k) else 0
  environment_criterion : ∀ {k d e r} {K : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : DiagonalCode K J),
    KnillLaflamme K J (Matrix.diagonal (fun i => (C.probability i : ℂ)))
  two_error_example : ∀ X : Q 2, apply_channel (recoveryChannel Examples.twoErrorCode)
    (apply_channel Examples.twoErrorChannel (encode Examples.logicalCode X)) = X
  zero_weight_example : errorOnCode Examples.sectorChannel Examples.logicalCode 1 = 0
  physical_error_nonzero : Examples.sectorChannel.operators 1 ≠ 0
  unused_space_nonzero : unusedProjection Examples.sectorCode ≠ 0

theorem verification_suite : QuantumOrthogonalErrorRecoveryContractSuite where
  complete := recovery_complete
  exact_recovery := recovery_theorem
  completely_positive := recovery_completely_positive
  trace_preserving := recovery_trace
  preserves_density := recovery_density
  zero_errors := zero_error
  orthogonal_isometries := normalized_gram
  environment_criterion := diagonal_environment
  two_error_example := Examples.two_error_recovery
  zero_weight_example := Examples.sector_error_zero_on_code
  physical_error_nonzero := Examples.sector_error_nonzero
  unused_space_nonzero := Examples.sector_unused_nonzero

end QuantumOrthogonalErrorRecoveryContract
