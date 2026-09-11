import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false
noncomputable section

namespace QuantumToricCode

/-- Parity of a supplied overlap count; no lattice incidence is constructed. -/
def EvenEdgeOverlap (sharedEdges : ℕ) : Prop := sharedEdges % 2 = 0

def starPlaqCommutes (sharedEdges : ℕ) : Bool := (sharedEdges % 2) == 0

theorem star_plaq_comm_of_even_overlap (sharedEdges : ℕ) (h_even : EvenEdgeOverlap sharedEdges) :
    starPlaqCommutes sharedEdges = true := by
  dsimp [starPlaqCommutes, EvenEdgeOverlap] at h_even ⊢
  rw [h_even]
  rfl

theorem star_plaq_comm_zero_overlap : starPlaqCommutes 0 = true := by decide
theorem star_plaq_comm_two_overlap : starPlaqCommutes 2 = true := by decide

structure ToricCouplings where
  Je : ℝ
  Jm : ℝ
  hJe_pos : 0 < Je
  hJm_pos : 0 < Jm

/-- Prescribed scalar reference energy. -/
def groundStateEnergy (c : ToricCouplings) (Ns Np : ℕ) : ℝ :=
  -c.Je * (Ns : ℝ) - c.Jm * (Np : ℝ)

/-- Prescribed scalar energy; counts are not constrained by a lattice model. -/
def excitedStateEnergy (c : ToricCouplings) (Ns Np ne nm : ℕ) : ℝ :=
  -c.Je * ((Ns : ℝ) - 2 * (ne : ℝ)) - c.Jm * ((Np : ℝ) - 2 * (nm : ℝ))

theorem excited_energy_decomposition (c : ToricCouplings) (Ns Np ne nm : ℕ) :
    excitedStateEnergy c Ns Np ne nm =
      groundStateEnergy c Ns Np + 2 * c.Je * (ne : ℝ) + 2 * c.Jm * (nm : ℝ) := by
  dsimp [excitedStateEnergy, groundStateEnergy]
  ring

theorem electric_pair_energy_gap (c : ToricCouplings) (Ns Np : ℕ) :
    excitedStateEnergy c Ns Np 2 0 - groundStateEnergy c Ns Np = 4 * c.Je := by
  rw [excited_energy_decomposition]
  ring

theorem magnetic_pair_energy_gap (c : ToricCouplings) (Ns Np : ℕ) :
    excitedStateEnergy c Ns Np 0 2 - groundStateEnergy c Ns Np = 4 * c.Jm := by
  rw [excited_energy_decomposition]
  ring

theorem electric_pair_gap_pos (c : ToricCouplings) (Ns Np : ℕ) :
    0 < excitedStateEnergy c Ns Np 2 0 - groundStateEnergy c Ns Np := by
  rw [electric_pair_energy_gap]
  linarith [c.hJe_pos]

theorem magnetic_pair_gap_pos (c : ToricCouplings) (Ns Np : ℕ) :
    0 < excitedStateEnergy c Ns Np 0 2 - groundStateEnergy c Ns Np := by
  rw [magnetic_pair_energy_gap]
  linarith [c.hJm_pos]

structure DefectCount where
  electricDefects : ℕ
  magneticDefects : ℕ

/-- A stipulated pair increment, not the general action of a Pauli error. -/
def applyZError (d : DefectCount) : DefectCount :=
  ⟨d.electricDefects + 2, d.magneticDefects⟩

/-- A stipulated pair increment, not the general action of a Pauli error. -/
def applyXError (d : DefectCount) : DefectCount :=
  ⟨d.electricDefects, d.magneticDefects + 2⟩

theorem z_error_creates_two_e_anyons (d : DefectCount) :
    (applyZError d).electricDefects = d.electricDefects + 2 := rfl

theorem x_error_creates_two_m_anyons (d : DefectCount) :
    (applyXError d).magneticDefects = d.magneticDefects + 2 := rfl

structure QuantumToricFormalSuite : Prop where
  h_comm_even : ∀ k, EvenEdgeOverlap k → starPlaqCommutes k = true
  h_comm_zero : starPlaqCommutes 0 = true
  h_comm_two : starPlaqCommutes 2 = true
  h_energy_decomp : ∀ c Ns Np ne nm, excitedStateEnergy c Ns Np ne nm =
    groundStateEnergy c Ns Np + 2 * c.Je * (ne : ℝ) + 2 * c.Jm * (nm : ℝ)
  h_e_gap : ∀ c Ns Np, excitedStateEnergy c Ns Np 2 0 - groundStateEnergy c Ns Np = 4 * c.Je
  h_m_gap : ∀ c Ns Np, excitedStateEnergy c Ns Np 0 2 - groundStateEnergy c Ns Np = 4 * c.Jm
  h_e_gap_pos : ∀ c Ns Np, 0 < excitedStateEnergy c Ns Np 2 0 - groundStateEnergy c Ns Np
  h_z_defects : ∀ d, (applyZError d).electricDefects = d.electricDefects + 2
  h_x_defects : ∀ d, (applyXError d).magneticDefects = d.magneticDefects + 2

theorem quantum_toric_master_verification_suite : QuantumToricFormalSuite := {
  h_comm_even := star_plaq_comm_of_even_overlap
  h_comm_zero := star_plaq_comm_zero_overlap
  h_comm_two := star_plaq_comm_two_overlap
  h_energy_decomp := excited_energy_decomposition
  h_e_gap := electric_pair_energy_gap
  h_m_gap := magnetic_pair_energy_gap
  h_e_gap_pos := electric_pair_gap_pos
  h_z_defects := z_error_creates_two_e_anyons
  h_x_defects := x_error_creates_two_m_anyons
}

#print axioms quantum_toric_master_verification_suite

end QuantumToricCode
