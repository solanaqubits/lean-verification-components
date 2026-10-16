/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Analysis.Matrix.Spectrum
import Verification.QuantumUnitaryKrausDiagonalizationRecoveryContract

/-! Sufficiency of general Knill-Laflamme conditions. The spectral certificate
is constructed using Mathlib, not supplied by the caller. Necessity and an
executable numerical decoder are outside this contract. -/
noncomputable section
open scoped BigOperators ComplexOrder
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract QuantumHelstromStateDiscrimination
open QuantumKnillLaflammeEnvironmentCriterion QuantumUnitaryKrausDiagonalizationRecoveryContract
namespace QuantumKnillLaflammeGeneralRecoveryTheorem
variable {k d e r : ℕ}

/-- Only the channel, encoding and algebraic code conditions are inputs. -/
structure GeneralCode (E : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ) where
  nonempty : 0 < k
  isometry : J.conjTranspose * J = 1
  coefficients : Q r
  knill_laflamme : StandardKnillLaflamme E J coefficients

variable {E : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}

/-- Module 182 uses environment coefficients sigma=Lambda^T. -/
theorem coefficients_hermitian (C : GeneralCode E J) : C.coefficients.IsHermitian := by
  have h := environment_hermitian C.nonempty E J C.isometry C.coefficients.transpose
    ((standard_iff_transpose E J C.coefficients).mp C.knill_laflamme)
  exact Matrix.isHermitian_transpose_iff.mp h

def spectralUnitary (C : GeneralCode E J) : Q r :=
  (coefficients_hermitian C).eigenvectorUnitary

def spectralWeights (C : GeneralCode E J) : Fin r → ℝ :=
  (coefficients_hermitian C).eigenvalues

theorem spectral_unitary_left (C : GeneralCode E J) :
    (spectralUnitary C).conjTranspose * spectralUnitary C = 1 :=
  Unitary.coe_star_mul_self _

theorem spectral_unitary_right (C : GeneralCode E J) :
    spectralUnitary C * (spectralUnitary C).conjTranspose = 1 :=
  Unitary.coe_mul_star_self _

/-- Mathlib's diagonalization conjugates by U†, matching module 184 exactly. -/
theorem spectral_diagonalizes (C : GeneralCode E J) :
    (spectralUnitary C).conjTranspose * C.coefficients * spectralUnitary C =
      Matrix.diagonal (fun i => (spectralWeights C i : ℂ)) := by
  simpa [Unitary.conjStarAlgAut_star_apply, spectralUnitary, spectralWeights,
    Function.comp_def, Matrix.mul_assoc, Matrix.star_eq_conjTranspose] using
    (coefficients_hermitian C).conjStarAlgAut_star_eigenvectorUnitary

/-- Derived certificate: no spectral data is an input to GeneralCode. -/
def spectralCertificate (C : GeneralCode E J) : DiagonalizationCertificate E J where
  nonempty := C.nonempty
  isometry := C.isometry
  coefficients := C.coefficients
  knill_laflamme := C.knill_laflamme
  unitary := spectralUnitary C
  unitary_left := spectral_unitary_left C
  unitary_right := spectral_unitary_right C
  weights := spectralWeights C
  diagonalizes := spectral_diagonalizes C

theorem spectral_weights_nonnegative (C : GeneralCode E J) (i : Fin r) :
    0 ≤ spectralWeights C i := weights_nonnegative (spectralCertificate C) i

theorem spectral_weights_normalized (C : GeneralCode E J) :
    ∑ i, spectralWeights C i = 1 := weights_normalized (spectralCertificate C)

/-- Classical spectral construction, with complete action on the physical output. -/
def generalRecovery (C : GeneralCode E J) : KrausChannel e k (r + e) :=
  certifiedRecovery (spectralCertificate C)

theorem general_recovery_theorem (C : GeneralCode E J) (X : Q k) :
    apply_channel (generalRecovery C) (apply_channel E (encode J X)) = X :=
  certified_recovery_theorem (spectralCertificate C) X

theorem exists_recovery (C : GeneralCode E J) :
    ∃ R : KrausChannel e k (r + e), ∀ X : Q k,
      apply_channel R (apply_channel E (encode J X)) = X :=
  ⟨generalRecovery C, general_recovery_theorem C⟩

theorem general_recovery_complete (C : GeneralCode E J) :
    ∑ i, ((generalRecovery C).operators i).conjTranspose *
      (generalRecovery C).operators i = 1 := (generalRecovery C).complete

theorem general_recovery_cp (C : GeneralCode E J) :
    QuantumNoBroadcastingMixed.IsCompletelyPositive (apply_channel (generalRecovery C)) :=
  channel_completely_positive _

theorem general_recovery_trace (C : GeneralCode E J) (Y : Q e) :
    (apply_channel (generalRecovery C) Y).trace = Y.trace := channel_trace_preserving _ _

theorem general_recovery_density (C : GeneralCode E J) {Y : Q e} (hY : Density Y) :
    Density (apply_channel (generalRecovery C) Y) := channel_density _ hY

theorem logical_density_recovered (C : GeneralCode E J) {ρ : Q k} (hρ : Density ρ) :
    apply_channel (generalRecovery C) (apply_channel E (encode J ρ)) = ρ ∧
      Density (apply_channel (generalRecovery C) (apply_channel E (encode J ρ))) := by
  rw [general_recovery_theorem C]; exact ⟨rfl, hρ⟩

namespace Examples
open QuantumUnitaryKrausDiagonalizationRecoveryContract.Examples
  (complexCertificate complex_coefficients)
abbrev logicalCode := QuantumOrthogonalErrorRecoveryContract.Examples.logicalCode
abbrev complexChannel := QuantumUnitaryKrausDiagonalizationRecoveryContract.Examples.complexChannel

/-- Reuse only the algebraic data of the complex example, discarding its U and p. -/
def complexCode : GeneralCode complexChannel logicalCode where
  nonempty := by decide
  isometry :=
    QuantumUnitaryKrausDiagonalizationRecoveryContract.Examples.complexCertificate.isometry
  coefficients := !![337/625, 84/625*Complex.I; -84/625*Complex.I, 288/625]
  knill_laflamme := by
    simpa only [complex_coefficients] using complexCertificate.knill_laflamme

theorem complex_offdiagonal : (complexCode.coefficients 0 1).im ≠ 0 := by
  norm_num [complexCode]

def zeroCode :
    GeneralCode QuantumOrthogonalErrorRecoveryContract.Examples.sectorChannel logicalCode where
  nonempty := by decide
  isometry := QuantumOrthogonalErrorRecoveryContract.Examples.sectorCode.isometry
  coefficients := Matrix.diagonal ![1, 0]
  knill_laflamme := by
    convert diagonal_standard QuantumOrthogonalErrorRecoveryContract.Examples.sectorCode using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [QuantumOrthogonalErrorRecoveryContract.Examples.sectorCode, Matrix.diagonal]

def repeatedCode :
    GeneralCode QuantumUnitaryKrausDiagonalizationRecoveryContract.Examples.repeatedChannel
    logicalCode where
  nonempty := by decide
  isometry := QuantumUnitaryKrausDiagonalizationRecoveryContract.Examples.repeatedCode.isometry
  coefficients := Matrix.diagonal ![1/2, 1/2, 0]
  knill_laflamme := by
    convert diagonal_standard
      QuantumUnitaryKrausDiagonalizationRecoveryContract.Examples.repeatedCode using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [QuantumUnitaryKrausDiagonalizationRecoveryContract.Examples.repeatedCode,
        Matrix.diagonal]

/-- A physical C^2 -> C^4 channel, with a nonzero unused output complement. -/
def rectangularChannel : KrausChannel 2 4 1 where
  operators := fun _ => logicalCode
  complete := by simpa using QuantumKnillLaflammeEnvironmentCriterion.Regression.code_isometry

def rectangularCode : GeneralCode rectangularChannel (1 : Q 2) where
  nonempty := by decide
  isometry := by simp
  coefficients := 1
  knill_laflamme := by
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    simp [rectangularChannel, logicalCode, hij, Matrix.one_apply,
      QuantumOrthogonalErrorRecoveryContract.Examples.logicalCode,
      QuantumKnillLaflammeEnvironmentCriterion.Regression.code_isometry]

theorem complex_recovery (X : Q 2) :
    apply_channel (generalRecovery complexCode)
      (apply_channel complexChannel (encode logicalCode X)) = X :=
  general_recovery_theorem complexCode X

theorem rectangular_recovery (X : Q 2) :
    apply_channel (generalRecovery rectangularCode) (apply_channel rectangularChannel X) = X := by
  simpa [encode] using general_recovery_theorem rectangularCode X
end Examples

structure QuantumKnillLaflammeGeneralRecoveryTheoremSuite : Prop where
  hermitian : ∀ {k d e r} {E : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : GeneralCode E J), C.coefficients.IsHermitian
  unitary_left : ∀ {k d e r} {E : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : GeneralCode E J), (spectralUnitary C).conjTranspose * spectralUnitary C = 1
  unitary_right : ∀ {k d e r} {E : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : GeneralCode E J), spectralUnitary C * (spectralUnitary C).conjTranspose = 1
  diagonalization : ∀ {k d e r} {E : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : GeneralCode E J), (spectralUnitary C).conjTranspose * C.coefficients * spectralUnitary C =
      Matrix.diagonal (fun i => (spectralWeights C i : ℂ))
  nonnegative_weights : ∀ {k d e r} {E : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : GeneralCode E J) (i : Fin r), 0 ≤ spectralWeights C i
  normalized_weights : ∀ {k d e r} {E : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : GeneralCode E J), ∑ i, spectralWeights C i = 1
  recovery : ∀ {k d e r} {E : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : GeneralCode E J) (X : Q k),
    apply_channel (generalRecovery C) (apply_channel E (encode J X)) = X
  existence : ∀ {k d e r} {E : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (_C : GeneralCode E J), ∃ R : KrausChannel e k (r + e), ∀ X : Q k,
      apply_channel R (apply_channel E (encode J X)) = X
  completely_positive : ∀ {k d e r} {E : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : GeneralCode E J),
    QuantumNoBroadcastingMixed.IsCompletelyPositive (apply_channel (generalRecovery C))
  trace_preserving : ∀ {k d e r} {E : KrausChannel d e r} {J : Matrix (Fin d) (Fin k) ℂ}
    (C : GeneralCode E J) (Y : Q e), (apply_channel (generalRecovery C) Y).trace = Y.trace
  complex_nondiagonal : (Examples.complexCode.coefficients 0 1).im ≠ 0
  rectangular_recovery : ∀ X : Q 2, apply_channel (generalRecovery Examples.rectangularCode)
    (apply_channel Examples.rectangularChannel X) = X

theorem verification_suite : QuantumKnillLaflammeGeneralRecoveryTheoremSuite where
  hermitian := coefficients_hermitian
  unitary_left := spectral_unitary_left
  unitary_right := spectral_unitary_right
  diagonalization := spectral_diagonalizes
  nonnegative_weights := spectral_weights_nonnegative
  normalized_weights := spectral_weights_normalized
  recovery := general_recovery_theorem
  existence := exists_recovery
  completely_positive := general_recovery_cp
  trace_preserving := general_recovery_trace
  complex_nondiagonal := Examples.complex_offdiagonal
  rectangular_recovery := Examples.rectangular_recovery

end QuantumKnillLaflammeGeneralRecoveryTheorem
