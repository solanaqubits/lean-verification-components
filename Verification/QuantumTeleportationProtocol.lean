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

/-- Real-amplitude interface; arbitrary amplitude pairs, not necessarily normalized. -/
@[ext] structure QState2 where
  x0 : ℝ
  x1 : ℝ

def dot (u v : QState2) : ℝ := u.x0 * v.x0 + u.x1 * v.x1
def applyI (q : QState2) : QState2 := q
def applyX (q : QState2) : QState2 := ⟨q.x1, q.x0⟩
def applyZ (q : QState2) : QState2 := ⟨q.x0, -q.x1⟩
def applyZX (q : QState2) : QState2 := applyZ (applyX q)

inductive AliceOutcome where
  | m00 | m01 | m10 | m11
  deriving DecidableEq, Repr

/-- Prescribed real branch states, not derived by projective measurement. -/
def bobCollapsedState (α β : ℝ) (m : AliceOutcome) : QState2 :=
  match m with
  | .m00 => ⟨α, β⟩
  | .m01 => ⟨β, α⟩
  | .m10 => ⟨α, -β⟩
  | .m11 => ⟨-β, α⟩

def bobCorrection (m : AliceOutcome) (q : QState2) : QState2 :=
  match m with
  | .m00 => applyI q
  | .m01 => applyX q
  | .m10 => applyZ q
  | .m11 => applyZX q

theorem teleport_m00 (α β : ℝ) :
    bobCorrection .m00 (bobCollapsedState α β .m00) = ⟨α, β⟩ := rfl

theorem teleport_m01 (α β : ℝ) :
    bobCorrection .m01 (bobCollapsedState α β .m01) = ⟨α, β⟩ := rfl

theorem teleport_m10 (α β : ℝ) :
    bobCorrection .m10 (bobCollapsedState α β .m10) = ⟨α, β⟩ := by
  simp [bobCorrection, bobCollapsedState, applyZ]

theorem teleport_m11 (α β : ℝ) :
    bobCorrection .m11 (bobCollapsedState α β .m11) = ⟨α, β⟩ := by
  simp [bobCorrection, bobCollapsedState, applyZX, applyZ, applyX]

theorem teleport_universal_exactness (α β : ℝ) (m : AliceOutcome) :
    bobCorrection m (bobCollapsedState α β m) = ⟨α, β⟩ := by
  cases m
  · exact teleport_m00 α β
  · exact teleport_m01 α β
  · exact teleport_m10 α β
  · exact teleport_m11 α β

/-- Normalization of an assigned scalar weight, not a measurement probability derivation. -/
theorem outcome_probability_uniform (α β : ℝ) (h_norm : α ^ 2 + β ^ 2 = 1) :
    (1 / 4 : ℝ) * (α ^ 2 + β ^ 2) = 1 / 4 := by
  rw [h_norm, mul_one]

structure QuantumTeleportationFormalSuite : Prop where
  h_phi_plus : ∀ psi, reconstructState BellMeasurement.phiPlus psi = psi
  h_phi_minus : ∀ psi, reconstructState BellMeasurement.phiMinus psi = psi
  h_psi_plus : ∀ psi, reconstructState BellMeasurement.psiPlus psi = psi
  h_psi_minus : ∀ psi, reconstructState BellMeasurement.psiMinus psi = psi
  h_universal : ∀ m psi, reconstructState m psi = psi
  h_prob_sum : (1 / 4 : ℝ) + 1 / 4 + 1 / 4 + 1 / 4 = 1

  h_rec_00 : ∀ (α β : ℝ), bobCorrection .m00 (bobCollapsedState α β .m00) = ⟨α, β⟩
  h_rec_01 : ∀ (α β : ℝ), bobCorrection .m01 (bobCollapsedState α β .m01) = ⟨α, β⟩
  h_rec_10 : ∀ (α β : ℝ), bobCorrection .m10 (bobCollapsedState α β .m10) = ⟨α, β⟩
  h_rec_11 : ∀ (α β : ℝ), bobCorrection .m11 (bobCollapsedState α β .m11) = ⟨α, β⟩
  h_rec_univ : ∀ (α β : ℝ) (m : AliceOutcome),
    bobCorrection m (bobCollapsedState α β m) = ⟨α, β⟩
  h_prob_uniform : ∀ (α β : ℝ), α ^ 2 + β ^ 2 = 1 →
    (1 / 4 : ℝ) * (α ^ 2 + β ^ 2) = 1 / 4

theorem quantum_teleportation_master_verification_suite : QuantumTeleportationFormalSuite := {
  h_phi_plus := teleport_recovery_phi_plus
  h_phi_minus := teleport_recovery_phi_minus
  h_psi_plus := teleport_recovery_psi_plus
  h_psi_minus := teleport_recovery_psi_minus
  h_universal := teleportation_fidelity_exact
  h_prob_sum := branch_probabilities_sum
  h_rec_00 := teleport_m00
  h_rec_01 := teleport_m01
  h_rec_10 := teleport_m10
  h_rec_11 := teleport_m11
  h_rec_univ := teleport_universal_exactness
  h_prob_uniform := outcome_probability_uniform
}

#print axioms quantum_teleportation_master_verification_suite

end QuantumTeleportationProtocol
