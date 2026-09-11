import Mathlib.Tactic.NormNum

set_option linter.style.header false

namespace QuantumCliffordTableau

/-- Binary Pauli label with phase omitted. -/
structure Pauli1 where
  x : Bool
  z : Bool
  deriving DecidableEq, Repr

def pauliI : Pauli1 := ⟨false, false⟩
def pauliX : Pauli1 := ⟨true, false⟩
def pauliZ : Pauli1 := ⟨false, true⟩
def pauliY : Pauli1 := ⟨true, true⟩

def symplectic1 (p1 p2 : Pauli1) : Bool :=
  (p1.x && p2.z) != (p1.z && p2.x)

structure Pauli2 where
  q1 : Pauli1
  q2 : Pauli1
  deriving DecidableEq, Repr

def symplectic2 (p1 p2 : Pauli2) : Bool :=
  symplectic1 p1.q1 p2.q1 != symplectic1 p1.q2 p2.q2

def applyH (p : Pauli1) : Pauli1 := ⟨p.z, p.x⟩
def applyS (p : Pauli1) : Pauli1 := ⟨p.x, p.x != p.z⟩

theorem H_preserves_symplectic (p1 p2 : Pauli1) :
    symplectic1 (applyH p1) (applyH p2) = symplectic1 p1 p2 := by
  rcases p1 with ⟨x1, z1⟩
  rcases p2 with ⟨x2, z2⟩
  cases x1 <;> cases z1 <;> cases x2 <;> cases z2 <;> rfl

theorem S_preserves_symplectic (p1 p2 : Pauli1) :
    symplectic1 (applyS p1) (applyS p2) = symplectic1 p1 p2 := by
  rcases p1 with ⟨x1, z1⟩
  rcases p2 with ⟨x2, z2⟩
  cases x1 <;> cases z1 <;> cases x2 <;> cases z2 <;> rfl

/-- Involution of phase-free labels only. -/
theorem H_involutive (p : Pauli1) : applyH (applyH p) = p := by
  rcases p with ⟨x, z⟩
  cases x <;> cases z <;> rfl

/-- Involution of phase-free labels only. -/
theorem S_square_identity_symplectic (p : Pauli1) : applyS (applyS p) = p := by
  rcases p with ⟨x, z⟩
  cases x <;> cases z <;> rfl

theorem H_action_X : applyH pauliX = pauliZ := rfl
theorem H_action_Z : applyH pauliZ = pauliX := rfl
theorem S_action_Z : applyS pauliZ = pauliZ := rfl
theorem S_action_X : applyS pauliX = pauliY := rfl

/-- Control on q1 and target on q2, ignoring conjugation phases. -/
def applyCNOT (p : Pauli2) : Pauli2 :=
  ⟨⟨p.q1.x, p.q1.z != p.q2.z⟩, ⟨p.q1.x != p.q2.x, p.q2.z⟩⟩

theorem CNOT_preserves_symplectic (p1 p2 : Pauli2) :
    symplectic2 (applyCNOT p1) (applyCNOT p2) = symplectic2 p1 p2 := by
  rcases p1 with ⟨⟨x11, z11⟩, ⟨x12, z12⟩⟩
  rcases p2 with ⟨⟨x21, z21⟩, ⟨x22, z22⟩⟩
  cases x11 <;> cases z11 <;> cases x12 <;> cases z12 <;>
    cases x21 <;> cases z21 <;> cases x22 <;> cases z22 <;> rfl

theorem CNOT_involutive (p : Pauli2) : applyCNOT (applyCNOT p) = p := by
  rcases p with ⟨⟨x1, z1⟩, ⟨x2, z2⟩⟩
  cases x1 <;> cases z1 <;> cases x2 <;> cases z2 <;> rfl

theorem CNOT_action_XI : applyCNOT ⟨pauliX, pauliI⟩ = ⟨pauliX, pauliX⟩ := rfl
theorem CNOT_action_IX : applyCNOT ⟨pauliI, pauliX⟩ = ⟨pauliI, pauliX⟩ := rfl
theorem CNOT_action_ZI : applyCNOT ⟨pauliZ, pauliI⟩ = ⟨pauliZ, pauliI⟩ := rfl
theorem CNOT_action_IZ : applyCNOT ⟨pauliI, pauliZ⟩ = ⟨pauliZ, pauliZ⟩ := rfl

def commute2 (p1 p2 : Pauli2) : Bool := !(symplectic2 p1 p2)

theorem CNOT_preserves_commutation (p1 p2 : Pauli2) (h_comm : commute2 p1 p2 = true) :
    commute2 (applyCNOT p1) (applyCNOT p2) = true := by
  dsimp [commute2] at h_comm ⊢
  rw [CNOT_preserves_symplectic]
  exact h_comm

structure QuantumCliffordFormalSuite : Prop where
  h_H_symp : ∀ p1 p2, symplectic1 (applyH p1) (applyH p2) = symplectic1 p1 p2
  h_S_symp : ∀ p1 p2, symplectic1 (applyS p1) (applyS p2) = symplectic1 p1 p2
  h_CNOT_symp : ∀ p1 p2, symplectic2 (applyCNOT p1) (applyCNOT p2) = symplectic2 p1 p2
  h_H_involutive : ∀ p, applyH (applyH p) = p
  h_S_sq_id : ∀ p, applyS (applyS p) = p
  h_CNOT_involutive : ∀ p, applyCNOT (applyCNOT p) = p
  h_H_basis : applyH pauliX = pauliZ ∧ applyH pauliZ = pauliX
  h_S_basis : applyS pauliZ = pauliZ ∧ applyS pauliX = pauliY
  h_CNOT_basis : applyCNOT ⟨pauliX, pauliI⟩ = ⟨pauliX, pauliX⟩ ∧
    applyCNOT ⟨pauliI, pauliZ⟩ = ⟨pauliZ, pauliZ⟩
  h_CNOT_comm_inv : ∀ p1 p2, commute2 p1 p2 = true →
    commute2 (applyCNOT p1) (applyCNOT p2) = true

theorem quantum_clifford_master_verification_suite : QuantumCliffordFormalSuite := {
  h_H_symp := H_preserves_symplectic
  h_S_symp := S_preserves_symplectic
  h_CNOT_symp := CNOT_preserves_symplectic
  h_H_involutive := H_involutive
  h_S_sq_id := S_square_identity_symplectic
  h_CNOT_involutive := CNOT_involutive
  h_H_basis := ⟨H_action_X, H_action_Z⟩
  h_S_basis := ⟨S_action_Z, S_action_X⟩
  h_CNOT_basis := ⟨CNOT_action_XI, CNOT_action_IZ⟩
  h_CNOT_comm_inv := CNOT_preserves_commutation
}

#print axioms quantum_clifford_master_verification_suite

end QuantumCliffordTableau
