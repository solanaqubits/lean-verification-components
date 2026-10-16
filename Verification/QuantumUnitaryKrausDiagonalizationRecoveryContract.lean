/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumComplementaryChannelContract
import Verification.QuantumKnillLaflammeEnvironmentCriterion
import Verification.QuantumOrthogonalErrorRecoveryContract

/-! Recovery from general Knill-Laflamme coefficients and a SUPPLIED unitary
diagonalization certificate. Nonnegativity and normalization of its real spectrum
are derived, not assumed. No existence theorem for diagonalization is asserted. -/
noncomputable section
open scoped BigOperators ComplexOrder
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract
open QuantumComplementaryChannelContract QuantumKnillLaflammeEnvironmentCriterion
open QuantumOrthogonalErrorRecoveryContract QuantumHelstromStateDiscrimination
namespace QuantumUnitaryKrausDiagonalizationRecoveryContract
variable {k d e r : ℕ}

/-- Both unitary equations are explicit. The certificate contains no weight
positivity, normalization, diagonal code or recovery map. -/
structure DiagonalizationCertificate (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) where
  nonempty : 0 < k
  isometry : J.conjTranspose * J = 1
  coefficients : Q r
  knill_laflamme : StandardKnillLaflamme E J coefficients
  unitary : Q r
  unitary_left : unitary.conjTranspose * unitary = 1
  unitary_right : unitary * unitary.conjTranspose = 1
  weights : Fin r → ℝ
  diagonalizes : unitary.conjTranspose * coefficients * unitary =
    Matrix.diagonal (fun i => (weights i : ℂ))

/-- The environment API uses rows of W; column mixing of U requires W=U^T. -/
theorem transpose_isometry (U : Q r) (h : U * U.conjTranspose = 1) :
    U.transpose.conjTranspose * U.transpose = 1 := by
  have ht := congrArg Matrix.transpose h
  simpa only [Matrix.transpose_mul, Matrix.transpose_one,
    Matrix.conjTranspose_transpose_eq_transpose_conjTranspose] using ht

def mixedChannel (E : KrausChannel d e r) (U : Q r)
    (h : U * U.conjTranspose = 1) : KrausChannel d e r :=
  changed_kraus E U.transpose (transpose_isometry U h)

/-- Explicit column mixing, with NO complex conjugation of U_{ai}. -/
theorem mixed_operators (E : KrausChannel d e r) (U : Q r)
    (h : U * U.conjTranspose = 1) (i : Fin r) :
    (mixedChannel E U h).operators i = ∑ a, U a i • E.operators a := by
  ext a b
  simp [mixedChannel, changed_kraus, environment_lift,
    QuantumStinespringDilationContract.stinespring_matrix, Matrix.mul_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Matrix.sum_apply]

theorem mixed_channel_invariant (E : KrausChannel d e r) (U : Q r)
    (h : U * U.conjTranspose = 1) (X : Q d) :
    apply_channel (mixedChannel E U h) X = apply_channel E X := changed_main_channel _ _ _ _

/-- Coefficient covariance is obtained from the complementary-channel covariance
and module 182's trace-pairing equivalence, keeping the transpose convention explicit. -/
theorem mixed_coefficients (E : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ)
    (Λ U : Q r) (hU : U * U.conjTranspose = 1)
    (hKL : StandardKnillLaflamme E J Λ) :
    StandardKnillLaflamme (mixedChannel E U hU) J (U.conjTranspose * Λ * U) := by
  apply (standard_iff_transpose _ _ _).mpr
  apply (knill_laflamme_equiv_environment _ _ _).mpr
  intro X
  have henv := (knill_laflamme_equiv_environment E J Λ.transpose).mp
    ((standard_iff_transpose E J Λ).mp hKL) X
  rw [mixedChannel, changed_complementary_channel, henv]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_mul,
    Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, Matrix.mul_assoc]

variable {E : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}

def rotated (C : DiagonalizationCertificate E J) : KrausChannel d e r :=
  mixedChannel E C.unitary C.unitary_right

theorem rotated_diagonal (C : DiagonalizationCertificate E J) (i j : Fin r) :
    J.conjTranspose * ((rotated C).operators i).conjTranspose * (rotated C).operators j * J =
      if i = j then (C.weights i : ℂ) • (1 : Q k) else 0 := by
  have h := mixed_coefficients E J C.coefficients C.unitary C.unitary_right C.knill_laflamme i j
  rw [C.diagonalizes] at h
  by_cases hij : i = j
  · subst j; simpa [rotated] using h
  · simpa [rotated, Matrix.diagonal, hij] using h

theorem weights_nonnegative (C : DiagonalizationCertificate E J) (i : Fin r) :
    0 ≤ C.weights i := by
  have hg : (((rotated C).operators i * J).conjTranspose *
      ((rotated C).operators i * J)) = (C.weights i : ℂ) • (1 : Q k) := by
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using rotated_diagonal C i i
  have hp := Matrix.posSemidef_conjTranspose_mul_self ((rotated C).operators i * J)
  rw [hg] at hp
  have hd := hp.diag_nonneg (i := (⟨0, C.nonempty⟩ : Fin k))
  simpa using hd

theorem weights_normalized (C : DiagonalizationCertificate E J) : ∑ i, C.weights i = 1 := by
  have hsum : (∑ i, (C.weights i : ℂ)) • (1 : Q k) = 1 := by
    calc
      _ = ∑ i, J.conjTranspose * ((rotated C).operators i).conjTranspose *
          (rotated C).operators i * J := by
        simp only [rotated_diagonal, ite_true, Finset.sum_smul]
      _ = J.conjTranspose * (∑ i, ((rotated C).operators i).conjTranspose *
          (rotated C).operators i) * J := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = 1 := by rw [(rotated C).complete, Matrix.mul_one, C.isometry]
  have hd := congrArg (fun M : Q k => M ⟨0, C.nonempty⟩ ⟨0, C.nonempty⟩) hsum
  have hs : (∑ i, (C.weights i : ℂ)) = 1 := by simpa using hd
  exact_mod_cast hs

def diagonalCode (C : DiagonalizationCertificate E J) : DiagonalCode (rotated C) J where
  nonempty := C.nonempty
  isometry := C.isometry
  probability := C.weights
  nonnegative := weights_nonnegative C
  normalized := weights_normalized C
  diagonal := rotated_diagonal C

def certifiedRecovery (C : DiagonalizationCertificate E J) : KrausChannel e k (r + e) :=
  recoveryChannel (diagonalCode C)

theorem certified_recovery_theorem (C : DiagonalizationCertificate E J) (X : Q k) :
    apply_channel (certifiedRecovery C) (apply_channel E (encode J X)) = X := by
  have h := recovery_theorem (diagonalCode C) X
  rw [show apply_channel (rotated C) (encode J X) = apply_channel E (encode J X) from
    mixed_channel_invariant _ _ _ _] at h
  exact h

theorem certified_recovery_complete (C : DiagonalizationCertificate E J) :
    ∑ i, ((certifiedRecovery C).operators i).conjTranspose *
      (certifiedRecovery C).operators i = 1 :=
  (certifiedRecovery C).complete

theorem certified_recovery_cp (C : DiagonalizationCertificate E J) :
    QuantumNoBroadcastingMixed.IsCompletelyPositive (apply_channel (certifiedRecovery C)) :=
  channel_completely_positive _

theorem certified_recovery_trace (C : DiagonalizationCertificate E J) (Y : Q e) :
    (apply_channel (certifiedRecovery C) Y).trace = Y.trace := channel_trace_preserving _ _

theorem certified_recovery_density (C : DiagonalizationCertificate E J) {Y : Q e}
    (hY : Density Y) : Density (apply_channel (certifiedRecovery C) Y) := channel_density _ hY

/-- The same coefficient law in explicit summation form. -/
theorem coefficient_entry_sum (Λ U : Q r) (i j : Fin r) :
    (U.conjTranspose * Λ * U) i j =
      ∑ a, ∑ b, star (U a i) * Λ a b * U b j := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem diagonal_standard {F : KrausChannel d e r} (C : DiagonalCode F J) :
    StandardKnillLaflamme F J (Matrix.diagonal (fun i => (C.probability i : ℂ))) := by
  intro i j
  rw [C.diagonal]
  by_cases h : i = j
  · subst j; simp
  · simp [Matrix.diagonal, h]

/-- A general regression constructor: hide diagonal data by an inverse unitary
mixing, then certify the forward diagonalization. This does not assume recovery. -/
def inverseMixed {F : KrausChannel d e r} (U : Q r)
    (hleft : U.conjTranspose * U = 1) : KrausChannel d e r :=
  mixedChannel F U.conjTranspose (by simpa using hleft)

theorem inverse_mixed_coefficients {F : KrausChannel d e r} (C : DiagonalCode F J)
    (U : Q r) (hleft : U.conjTranspose * U = 1) :
    StandardKnillLaflamme (inverseMixed (F := F) U hleft) J
      (U * Matrix.diagonal (fun i => (C.probability i : ℂ)) * U.conjTranspose) := by
  simpa [inverseMixed] using mixed_coefficients F J
    (Matrix.diagonal (fun i => (C.probability i : ℂ))) U.conjTranspose
    (by simpa using hleft) (diagonal_standard C)

def inverseCertificate {F : KrausChannel d e r} (C : DiagonalCode F J)
    (U : Q r) (hleft : U.conjTranspose * U = 1) (hright : U * U.conjTranspose = 1) :
    DiagonalizationCertificate (inverseMixed (F := F) U hleft) J where
  nonempty := C.nonempty
  isometry := C.isometry
  coefficients := U * Matrix.diagonal (fun i => (C.probability i : ℂ)) * U.conjTranspose
  knill_laflamme := inverse_mixed_coefficients C U hleft
  unitary := U
  unitary_left := hleft
  unitary_right := hright
  weights := C.probability
  diagonalizes := by
    calc
      _ = (U.conjTranspose * U) * Matrix.diagonal (fun i => (C.probability i : ℂ)) *
          (U.conjTranspose * U) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hleft, Matrix.one_mul, Matrix.mul_one]

namespace Examples

def complexUnitary : Q 2 := !![3/5, 4/5 * Complex.I; 4/5 * Complex.I, 3/5]

theorem complex_unitary_left : complexUnitary.conjTranspose * complexUnitary = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [complexUnitary, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Matrix.one_apply]
  all_goals ring_nf
  all_goals norm_num [map_ofNat]
  all_goals ring

theorem complex_unitary_right : complexUnitary * complexUnitary.conjTranspose = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [complexUnitary, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Matrix.one_apply]
  all_goals ring_nf
  all_goals norm_num [map_ofNat]
  all_goals ring

abbrev code := QuantumOrthogonalErrorRecoveryContract.Examples.logicalCode
abbrev diagonalExample := QuantumOrthogonalErrorRecoveryContract.Examples.twoErrorCode

def complexChannel : KrausChannel 4 4 2 :=
  inverseMixed (F := QuantumOrthogonalErrorRecoveryContract.Examples.twoErrorChannel)
    complexUnitary complex_unitary_left

def complexCertificate : DiagonalizationCertificate complexChannel code :=
  inverseCertificate diagonalExample complexUnitary complex_unitary_left complex_unitary_right

theorem complex_coefficients : complexCertificate.coefficients =
    !![337/625, 84/625 * Complex.I; -84/625 * Complex.I, 288/625] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [complexCertificate, inverseCertificate, diagonalExample,
      QuantumOrthogonalErrorRecoveryContract.Examples.twoErrorCode, complexUnitary,
      Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, dotProduct,
      Matrix.conjTranspose_apply, Matrix.diagonal, Fin.sum_univ_two]
  all_goals ring_nf
  all_goals norm_num [map_ofNat]
  all_goals ring

theorem imaginary_coefficient : (complexCertificate.coefficients 0 1).im ≠ 0 := by
  rw [complex_coefficients]
  norm_num

theorem complex_recovery (X : Q 2) :
    apply_channel (certifiedRecovery complexCertificate)
      (apply_channel complexChannel (encode code X)) = X := certified_recovery_theorem _ _

/-- Transposition and adjoint demonstrably differ on the unitary used above. -/
theorem transpose_not_adjoint : complexUnitary.transpose ≠ complexUnitary.conjTranspose := by
  intro h
  have hi := congrArg (fun M : Q 2 => (M 0 1).im) h
  norm_num [complexUnitary, Matrix.transpose_apply, Matrix.conjTranspose_apply] at hi

/-- Replacing the required transpose mixing by an adjoint mixing fails to
produce diagonal coefficients for this complex example. -/
theorem wrong_adjoint_diagonalization :
    complexUnitary * complexCertificate.coefficients * complexUnitary.conjTranspose ≠
      Matrix.diagonal (fun i => (complexCertificate.weights i : ℂ)) := by
  intro h
  have hi := congrArg (fun M : Q 2 => (M 0 1).im) h
  rw [complex_coefficients] at hi
  norm_num [complexUnitary, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Matrix.conjTranspose_apply, Matrix.diagonal, Fin.sum_univ_two] at hi
  norm_num [map_ofNat] at hi

/-- A zero eigenvalue under a genuinely complex change of Kraus basis. -/
def zeroCertificate := inverseCertificate
  QuantumOrthogonalErrorRecoveryContract.Examples.sectorCode
  complexUnitary complex_unitary_left complex_unitary_right

/-- Two equal positive weights and a zero weight, on a two-dimensional code. -/
def repeatedErrors : Fin 3 → Q 4 :=
  ![((1 + Complex.I) / 2) • (1 : Q 4),
    ((1 + Complex.I) / 2) • QuantumKnillLaflammeEnvironmentCriterion.Regression.blockSwap, 0]

def repeatedChannel : KrausChannel 4 4 3 where
  operators := repeatedErrors
  complete := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [repeatedErrors, QuantumKnillLaflammeEnvironmentCriterion.Regression.blockSwap,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ, Matrix.one_apply]
    all_goals ring_nf
    all_goals norm_num [map_ofNat]

def repeatedCode : DiagonalCode repeatedChannel code where
  nonempty := by decide
  isometry := QuantumKnillLaflammeEnvironmentCriterion.Regression.code_isometry
  probability := ![1/2, 1/2, 0]
  nonnegative := by intro i; fin_cases i <;> norm_num
  normalized := by norm_num [Fin.sum_univ_succ]
  diagonal := by
    intro i j
    ext a b
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
      norm_num [repeatedChannel, repeatedErrors, code,
        QuantumOrthogonalErrorRecoveryContract.Examples.logicalCode,
        QuantumKnillLaflammeEnvironmentCriterion.Regression.code,
        QuantumKnillLaflammeEnvironmentCriterion.Regression.blockSwap,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ, Matrix.one_apply]
    all_goals ring_nf
    all_goals norm_num [map_ofNat]

def repeatedCertificate := inverseCertificate repeatedCode (1 : Q 3) (by simp) (by simp)

end Examples

theorem logical_density_recovered (C : DiagonalizationCertificate E J) {ρ : Q k}
    (hρ : Density ρ) :
    apply_channel (certifiedRecovery C) (apply_channel E (encode J ρ)) = ρ ∧
    Density (apply_channel (certifiedRecovery C) (apply_channel E (encode J ρ))) := by
  rw [certified_recovery_theorem]
  exact ⟨rfl, hρ⟩

structure QuantumUnitaryKrausDiagonalizationRecoveryContractSuite : Prop where
  transpose_bridge : ∀ {r} (U : Q r), U * U.conjTranspose = 1 →
    U.transpose.conjTranspose * U.transpose = 1
  column_mixing : ∀ {d e r} (E : KrausChannel d e r) (U : Q r)
    (h : U * U.conjTranspose = 1) (i : Fin r),
    (mixedChannel E U h).operators i = ∑ a, U a i • E.operators a
  channel_invariant : ∀ {d e r} (E : KrausChannel d e r) (U : Q r)
    (h : U * U.conjTranspose = 1) (X : Q d),
    apply_channel (mixedChannel E U h) X = apply_channel E X
  nonnegative_weights : ∀ {k d e r} {E : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : DiagonalizationCertificate E J) (i : Fin r), 0 ≤ C.weights i
  normalized_weights : ∀ {k d e r} {E : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : DiagonalizationCertificate E J), ∑ i, C.weights i = 1
  diagonalization : ∀ {k d e r} {E : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : DiagonalizationCertificate E J) (i j : Fin r),
    J.conjTranspose * ((rotated C).operators i).conjTranspose * (rotated C).operators j * J =
      if i = j then (C.weights i : ℂ) • (1 : Q k) else 0
  recovery : ∀ {k d e r} {E : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : DiagonalizationCertificate E J) (X : Q k),
    apply_channel (certifiedRecovery C) (apply_channel E (encode J X)) = X
  completely_positive : ∀ {k d e r} {E : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : DiagonalizationCertificate E J),
    QuantumNoBroadcastingMixed.IsCompletelyPositive (apply_channel (certifiedRecovery C))
  trace_preserving : ∀ {k d e r} {E : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : DiagonalizationCertificate E J) (Y : Q e),
    (apply_channel (certifiedRecovery C) Y).trace = Y.trace
  complex_nondiagonal : (Examples.complexCertificate.coefficients 0 1).im ≠ 0
  transpose_distinct : Examples.complexUnitary.transpose ≠ Examples.complexUnitary.conjTranspose
  wrong_adjoint : Examples.complexUnitary * Examples.complexCertificate.coefficients *
    Examples.complexUnitary.conjTranspose ≠
      Matrix.diagonal (fun i => (Examples.complexCertificate.weights i : ℂ))
  zero_weight : Examples.zeroCertificate.weights 1 = 0
  repeated_weights : Examples.repeatedCertificate.weights 0 = 1/2 ∧
    Examples.repeatedCertificate.weights 1 = 1/2 ∧ Examples.repeatedCertificate.weights 2 = 0

theorem verification_suite : QuantumUnitaryKrausDiagonalizationRecoveryContractSuite where
  transpose_bridge := transpose_isometry
  column_mixing := mixed_operators
  channel_invariant := mixed_channel_invariant
  nonnegative_weights := weights_nonnegative
  normalized_weights := weights_normalized
  diagonalization := rotated_diagonal
  recovery := certified_recovery_theorem
  completely_positive := certified_recovery_cp
  trace_preserving := certified_recovery_trace
  complex_nondiagonal := Examples.imaginary_coefficient
  transpose_distinct := Examples.transpose_not_adjoint
  wrong_adjoint := Examples.wrong_adjoint_diagonalization
  zero_weight := rfl
  repeated_weights := ⟨rfl, rfl, rfl⟩

end QuantumUnitaryKrausDiagonalizationRecoveryContract
