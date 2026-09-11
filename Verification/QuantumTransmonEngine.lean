import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option linter.style.header false

noncomputable section

namespace QuantumTransmonEngine

/-- Positive parameters for the prescribed two-level gap formula. -/
structure TransmonParams where
  EC : ℝ
  EJ : ℝ
  hEC : 0 < EC
  hEJ : 0 < EJ

/-- Prescribed squared gap; no Hamiltonian eigenvalue calculation is performed here. -/
def eigenGapSq (p : TransmonParams) (ng : ℝ) : ℝ :=
  (4 * p.EC * (1 - 2 * ng)) ^ 2 + p.EJ ^ 2

def eigenGap (p : TransmonParams) (ng : ℝ) : ℝ :=
  Real.sqrt (eigenGapSq p ng)

theorem eigenGapSq_pos (p : TransmonParams) (ng : ℝ) : 0 < eigenGapSq p ng := by
  unfold eigenGapSq
  have hp : 0 < p.EJ ^ 2 := sq_pos_of_pos p.hEJ
  positivity

theorem eigenGapSq_ge_EJ_sq (p : TransmonParams) (ng : ℝ) :
    p.EJ ^ 2 ≤ eigenGapSq p ng := by
  unfold eigenGapSq
  linarith [sq_nonneg (4 * p.EC * (1 - 2 * ng))]

theorem eigenGap_ge_EJ (p : TransmonParams) (ng : ℝ) : p.EJ ≤ eigenGap p ng := by
  have h := Real.sqrt_le_sqrt (eigenGapSq_ge_EJ_sq p ng)
  rwa [Real.sqrt_sq (le_of_lt p.hEJ)] at h

theorem eigenGap_pos (p : TransmonParams) (ng : ℝ) : 0 < eigenGap p ng :=
  lt_of_lt_of_le p.hEJ (eigenGap_ge_EJ p ng)

theorem eigenGap_at_sweet_spot (p : TransmonParams) : eigenGap p (1 / 2) = p.EJ := by
  norm_num [eigenGap, eigenGapSq, Real.sqrt_sq (le_of_lt p.hEJ)]

/-- Deviation of the squared gap from its minimum, not of the gap itself. -/
def gapSqDeviation (p : TransmonParams) (ng : ℝ) : ℝ :=
  eigenGapSq p ng - p.EJ ^ 2

theorem gapSqDeviation_eq (p : TransmonParams) (ng : ℝ) :
    gapSqDeviation p ng = 16 * p.EC ^ 2 * (1 - 2 * ng) ^ 2 := by
  dsimp [gapSqDeviation, eigenGapSq]
  ring

theorem gapSqDeviation_nonneg (p : TransmonParams) (ng : ℝ) :
    0 ≤ gapSqDeviation p ng := by
  rw [gapSqDeviation_eq]
  positivity

theorem gapSqDeviation_zero_iff (p : TransmonParams) (ng : ℝ) :
    gapSqDeviation p ng = 0 ↔ ng = 1 / 2 := by
  rw [gapSqDeviation_eq]
  have hp : 16 * p.EC ^ 2 ≠ 0 := ne_of_gt (mul_pos (by norm_num) (sq_pos_of_pos p.hEC))
  rw [mul_eq_zero, or_iff_right hp, sq_eq_zero_iff]
  constructor <;> intro h <;> linarith

/-- Exact quadratic dependence on the displacement from one half. -/
theorem gapSqDeviation_centered (p : TransmonParams) (ng : ℝ) :
    gapSqDeviation p ng = 64 * p.EC ^ 2 * (ng - 1 / 2) ^ 2 := by
  rw [gapSqDeviation_eq]
  ring

theorem gapSqDeviation_bounded_near_sweet_spot (p : TransmonParams) (ng δ : ℝ)
    (hδ : |ng - 1 / 2| ≤ δ) :
    gapSqDeviation p ng ≤ 64 * p.EC ^ 2 * δ ^ 2 := by
  rw [gapSqDeviation_centered]
  have hs : (ng - 1 / 2) ^ 2 ≤ δ ^ 2 :=
    sq_le_sq.mpr (le_trans hδ (le_abs_self δ))
  exact mul_le_mul_of_nonneg_left hs (by positivity)

/-- Algebraic and square-root guarantees for the prescribed formula. -/
structure QuantumTransmonFormalSuite : Prop where
  h_gap_pos : ∀ (p : TransmonParams) (ng : ℝ), 0 < eigenGapSq p ng
  h_gap_lower_EJ : ∀ (p : TransmonParams) (ng : ℝ), p.EJ ≤ eigenGap p ng
  h_sweet_spot : ∀ p : TransmonParams, eigenGap p (1 / 2) = p.EJ
  h_dev_eq : ∀ (p : TransmonParams) (ng : ℝ),
    gapSqDeviation p ng = 16 * p.EC ^ 2 * (1 - 2 * ng) ^ 2
  h_dev_zero_iff : ∀ (p : TransmonParams) (ng : ℝ),
    gapSqDeviation p ng = 0 ↔ ng = 1 / 2
  h_dev_bound : ∀ (p : TransmonParams) (ng δ : ℝ),
    |ng - 1 / 2| ≤ δ → gapSqDeviation p ng ≤ 64 * p.EC ^ 2 * δ ^ 2

theorem quantum_transmon_master_verification_suite : QuantumTransmonFormalSuite := {
  h_gap_pos := eigenGapSq_pos
  h_gap_lower_EJ := eigenGap_ge_EJ
  h_sweet_spot := eigenGap_at_sweet_spot
  h_dev_eq := gapSqDeviation_eq
  h_dev_zero_iff := gapSqDeviation_zero_iff
  h_dev_bound := gapSqDeviation_bounded_near_sweet_spot
}

#print axioms quantum_transmon_master_verification_suite

end QuantumTransmonEngine
