import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.header false

namespace HopfObstruction

/-- The explicit scalar model `1/ε - 1`.
Its identification with an integral or a geometric tensor energy is not proved here.
-/
noncomputable def singularEnergy (ε : ℝ) : ℝ :=
  1 / ε - 1

/-- Positivity of the scalar energy model between zero and one. -/
theorem singular_energy_pos (ε : ℝ) (h_pos : 0 < ε) (h_lt1 : ε < 1) :
    0 < singularEnergy ε := by
  dsimp [singularEnergy]
  have h_inv : 1 < 1 / ε := by
    rw [lt_div_iff₀ h_pos]
    linarith
  linarith

/-- A lower bound for positive cutoffs at most one half. -/
theorem singular_energy_lower_half (ε : ℝ) (h_pos : 0 < ε) (h_le : ε ≤ 1 / 2) :
    1 / (2 * ε) ≤ singularEnergy ε := by
  dsimp [singularEnergy]
  have h_inv : 2 ≤ 1 / ε := by
    rw [le_div_iff₀ h_pos]
    linarith
  have h_split : 1 / (2 * ε) = (1 / ε) / 2 := by ring
  rw [h_split]
  linarith

/-- The scalar model exceeds every positive threshold at some cutoff in `(0,1)`.
This establishes unboundedness, not an obstruction for almost complex structures.
-/
theorem hopf_singular_obstruction_divergence (M : ℝ) (hM : 0 < M) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ M < singularEnergy ε := by
  let ε₀ := 1 / (M + 2)
  have h_den_pos : 0 < M + 2 := by linarith
  have h_eps_pos : 0 < ε₀ := by
    dsimp [ε₀]
    positivity
  have h_eps_lt1 : ε₀ < 1 := by
    dsimp [ε₀]
    rw [div_lt_iff₀ h_den_pos]
    linarith
  refine ⟨ε₀, h_eps_pos, h_eps_lt1, ?_⟩
  dsimp [singularEnergy, ε₀]
  rw [one_div_one_div]
  linarith

#print axioms singular_energy_pos
#print axioms singular_energy_lower_half
#print axioms hopf_singular_obstruction_divergence

end HopfObstruction
