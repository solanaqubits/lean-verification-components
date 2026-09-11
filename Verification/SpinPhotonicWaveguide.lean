import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option linter.style.header false

noncomputable section

namespace SpinPhotonicWaveguide

/-- Four real coordinates representing two mode amplitudes. -/
@[ext] structure ModeState where
  ar : ℝ
  ai : ℝ
  mr : ℝ
  mi : ℝ

/-- The prescribed sum of squared coordinates. -/
def energy (s : ModeState) : ℝ :=
  s.ar ^ 2 + s.ai ^ 2 + s.mr ^ 2 + s.mi ^ 2

theorem energy_nonneg (s : ModeState) : 0 ≤ energy s := by
  dsimp [energy]
  positivity

theorem energy_zero_iff (s : ModeState) : energy s = 0 ↔ s = ⟨0, 0, 0, 0⟩ := by
  constructor
  · intro h
    dsimp [energy] at h
    ext <;> dsimp <;>
      nlinarith [sq_nonneg s.ar, sq_nonneg s.ai, sq_nonneg s.mr, sq_nonneg s.mi]
  · intro h
    rw [h]
    norm_num [energy]

/-- Real rotation mixing the two modes, with normalization supplied separately. -/
def hybridEvolution (c s_ang : ℝ) (st : ModeState) : ModeState :=
  ⟨c * st.ar - s_ang * st.mr,
   c * st.ai - s_ang * st.mi,
   s_ang * st.ar + c * st.mr,
   s_ang * st.ai + c * st.mi⟩

/-- Preservation of the prescribed energy under normalized mixing. -/
theorem energy_conservation (c s_ang : ℝ) (h_cs : c ^ 2 + s_ang ^ 2 = 1) (st : ModeState) :
    energy (hybridEvolution c s_ang st) = energy st := by
  calc
    _ = (c ^ 2 + s_ang ^ 2) * energy st := by
      dsimp [energy, hybridEvolution]
      ring
    _ = energy st := by rw [h_cs, one_mul]

/-- Difference of the two prescribed propagation phases. -/
def nonReciprocalPhaseDiff (k0 dk L : ℝ) : ℝ :=
  ((k0 + dk) * L) - ((k0 - dk) * L)

theorem nonReciprocalPhase_eq (k0 dk L : ℝ) :
    nonReciprocalPhaseDiff k0 dk L = 2 * dk * L := by
  dsimp [nonReciprocalPhaseDiff]
  ring

theorem nonReciprocalPhase_pos (k0 dk L : ℝ) (h_dk : 0 < dk) (h_L : 0 < L) :
    0 < nonReciprocalPhaseDiff k0 dk L := by
  rw [nonReciprocalPhase_eq]
  positivity

/-- A prescribed geometric amplitude profile, without a lattice eigenvalue equation. -/
def edgeModeAmplitude (psi0 r : ℝ) (n : ℕ) : ℝ :=
  psi0 * r ^ n

/-- Strict stepwise decay of a positive geometric profile with ratio in (0,1). -/
theorem edgeMode_decay (psi0 r : ℝ) (h_psi0 : 0 < psi0)
    (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    edgeModeAmplitude psi0 r (n + 1) < edgeModeAmplitude psi0 r n := by
  dsimp [edgeModeAmplitude]
  rw [pow_succ, ← mul_assoc]
  have hp : 0 < psi0 * r ^ n := mul_pos h_psi0 (pow_pos hr0 n)
  simpa only [mul_one] using (mul_lt_mul_of_pos_left hr1 hp)

/-- Summary of the coordinate and scalar identities, retaining their hypotheses. -/
structure SpinPhotonicFormalSuite : Prop where
  h_energy_nonneg : ∀ s : ModeState, 0 ≤ energy s
  h_energy_zero : ∀ s : ModeState, energy s = 0 ↔ s = ⟨0, 0, 0, 0⟩
  h_unitary : ∀ (c s_ang : ℝ), c ^ 2 + s_ang ^ 2 = 1 → ∀ st : ModeState,
    energy (hybridEvolution c s_ang st) = energy st
  h_phase_shift : ∀ (k0 dk L : ℝ), 0 < dk → 0 < L →
    0 < nonReciprocalPhaseDiff k0 dk L
  h_edge_decay : ∀ (psi0 r : ℝ) (n : ℕ), 0 < psi0 → 0 < r → r < 1 →
    edgeModeAmplitude psi0 r (n + 1) < edgeModeAmplitude psi0 r n

theorem spin_photonic_master_verification_suite : SpinPhotonicFormalSuite := {
  h_energy_nonneg := energy_nonneg
  h_energy_zero := energy_zero_iff
  h_unitary := energy_conservation
  h_phase_shift := nonReciprocalPhase_pos
  h_edge_decay := fun psi0 r n hp hr0 hr1 => edgeMode_decay psi0 r hp hr0 hr1 n
}

#print axioms spin_photonic_master_verification_suite

end SpinPhotonicWaveguide
