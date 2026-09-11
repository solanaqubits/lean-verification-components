import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum

set_option linter.style.header false
noncomputable section

namespace QuantumTeleportationProtocol

/-- An arbitrary complex amplitude pair; normalization is not assumed. -/
@[ext] structure QubitState where
  alpha : ℂ
  beta : ℂ

/-- An explicit complex matrix acting on amplitude pairs. -/
structure CMat2 where
  a11 : ℂ
  a12 : ℂ
  a21 : ℂ
  a22 : ℂ

def appMat (M : CMat2) (s : QubitState) : QubitState :=
  ⟨M.a11 * s.alpha + M.a12 * s.beta, M.a21 * s.alpha + M.a22 * s.beta⟩

def matI : CMat2 := ⟨1, 0, 0, 1⟩
def pauliX : CMat2 := ⟨0, 1, 1, 0⟩
def pauliZ : CMat2 := ⟨1, 0, 0, -1⟩
def pauliZX : CMat2 := ⟨0, 1, -1, 0⟩

/-- Labels for four idealized branches, not measurement projectors. -/
inductive BellMeasurement
  | phiPlus
  | phiMinus
  | psiPlus
  | psiMinus
  deriving DecidableEq, Repr

/-- Prescribed branch states, with a fixed sign convention. -/
def bobReceivedState (m : BellMeasurement) (psi : QubitState) : QubitState :=
  match m with
  | .phiPlus => ⟨psi.alpha, psi.beta⟩
  | .phiMinus => ⟨psi.alpha, -psi.beta⟩
  | .psiPlus => ⟨psi.beta, psi.alpha⟩
  | .psiMinus => ⟨-psi.beta, psi.alpha⟩

/-- Correction selected by a four-valued classical outcome (two bits). -/
def bobCorrectionOp (m : BellMeasurement) : CMat2 :=
  match m with
  | .phiPlus => matI
  | .phiMinus => pauliZ
  | .psiPlus => pauliX
  | .psiMinus => pauliZX

def reconstructState (m : BellMeasurement) (psi : QubitState) : QubitState :=
  appMat (bobCorrectionOp m) (bobReceivedState m psi)

theorem teleport_recovery_phi_plus (psi : QubitState) :
    reconstructState BellMeasurement.phiPlus psi = psi := by
  ext <;> simp [reconstructState, bobCorrectionOp, bobReceivedState, appMat, matI]

theorem teleport_recovery_phi_minus (psi : QubitState) :
    reconstructState BellMeasurement.phiMinus psi = psi := by
  ext <;> simp [reconstructState, bobCorrectionOp, bobReceivedState, appMat, pauliZ]

theorem teleport_recovery_psi_plus (psi : QubitState) :
    reconstructState BellMeasurement.psiPlus psi = psi := by
  ext <;> simp [reconstructState, bobCorrectionOp, bobReceivedState, appMat, pauliX]

theorem teleport_recovery_psi_minus (psi : QubitState) :
    reconstructState BellMeasurement.psiMinus psi = psi := by
  ext <;> simp [reconstructState, bobCorrectionOp, bobReceivedState, appMat, pauliZX]

/-- Exact equality after correction for each prescribed branch. -/
theorem teleportation_fidelity_exact (m : BellMeasurement) (psi : QubitState) :
    reconstructState m psi = psi := by
  cases m with
  | phiPlus => exact teleport_recovery_phi_plus psi
  | phiMinus => exact teleport_recovery_phi_minus psi
  | psiPlus => exact teleport_recovery_psi_plus psi
  | psiMinus => exact teleport_recovery_psi_minus psi

/-- Arithmetic normalization of four assigned weights; not a Born-rule derivation. -/
theorem branch_probabilities_sum :
    (1 / 4 : ℝ) + 1 / 4 + 1 / 4 + 1 / 4 = 1 := by
  norm_num

structure QuantumTeleportationFormalSuite : Prop where
  h_phi_plus : ∀ psi, reconstructState BellMeasurement.phiPlus psi = psi
  h_phi_minus : ∀ psi, reconstructState BellMeasurement.phiMinus psi = psi
  h_psi_plus : ∀ psi, reconstructState BellMeasurement.psiPlus psi = psi
  h_psi_minus : ∀ psi, reconstructState BellMeasurement.psiMinus psi = psi
  h_universal : ∀ m psi, reconstructState m psi = psi
  h_prob_sum : (1 / 4 : ℝ) + 1 / 4 + 1 / 4 + 1 / 4 = 1

theorem quantum_teleportation_master_verification_suite : QuantumTeleportationFormalSuite := {
  h_phi_plus := teleport_recovery_phi_plus
  h_phi_minus := teleport_recovery_phi_minus
  h_psi_plus := teleport_recovery_psi_plus
  h_psi_minus := teleport_recovery_psi_minus
  h_universal := teleportation_fidelity_exact
  h_prob_sum := branch_probabilities_sum
}

#print axioms quantum_teleportation_master_verification_suite

end QuantumTeleportationProtocol
