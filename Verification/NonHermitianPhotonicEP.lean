import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false

noncomputable section

namespace NonHermitianPhotonicEP

/-- Parameters for prescribed scalar splitting formulas. -/
structure PhotonicEPParams where
  omega0 : ℝ
  kappa : ℝ
  gamma : ℝ
  hkappa_pos : 0 < kappa
  hgamma_pos : 0 < gamma

def spectralDiscrim (p : PhotonicEPParams) : ℝ := p.kappa ^ 2 - p.gamma ^ 2

/-- Real splitting formula; the real square root is zero for negative inputs. -/
def realEigenSplitting (p : PhotonicEPParams) : ℝ := 2 * Real.sqrt (spectralDiscrim p)

/-- Parameter equality only; no operator defectiveness is asserted. -/
def IsExceptionalPoint (p : PhotonicEPParams) : Prop := p.kappa = p.gamma

theorem discrim_zero_iff_ep (p : PhotonicEPParams) :
    spectralDiscrim p = 0 ↔ IsExceptionalPoint p := by
  dsimp [spectralDiscrim, IsExceptionalPoint]
  constructor
  · intro h
    nlinarith [p.hkappa_pos, p.hgamma_pos]
  · intro h
    rw [h]
    ring

theorem ep_eigenvalues_coalesce (p : PhotonicEPParams) (hep : IsExceptionalPoint p) :
    realEigenSplitting p = 0 := by
  dsimp [realEigenSplitting]
  rw [(discrim_zero_iff_ep p).mpr hep, Real.sqrt_zero, mul_zero]

theorem unbroken_phase_discrim_pos (p : PhotonicEPParams) (h_unbroken : p.gamma < p.kappa) :
    0 < spectralDiscrim p := by
  dsimp [spectralDiscrim]
  nlinarith [p.hgamma_pos]

theorem unbroken_phase_splitting_pos (p : PhotonicEPParams) (h_unbroken : p.gamma < p.kappa) :
    0 < realEigenSplitting p := by
  dsimp [realEigenSplitting]
  have hs := Real.sqrt_pos.mpr (unbroken_phase_discrim_pos p h_unbroken)
  linarith

theorem broken_phase_discrim_neg (p : PhotonicEPParams) (h_broken : p.kappa < p.gamma) :
    spectralDiscrim p < 0 := by
  dsimp [spectralDiscrim]
  nlinarith [p.hkappa_pos]

/-- This real-valued formula also vanishes in the negative-discriminant regime. -/
theorem broken_phase_real_splitting_zero (p : PhotonicEPParams) (h_broken : p.kappa < p.gamma) :
    realEigenSplitting p = 0 := by
  dsimp [realEigenSplitting]
  rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt (broken_phase_discrim_neg p h_broken)), mul_zero]

theorem splitting_sq_eq (p : PhotonicEPParams) (h_unbroken : p.gamma ≤ p.kappa) :
    (realEigenSplitting p) ^ 2 = 4 * spectralDiscrim p := by
  have hn : 0 ≤ spectralDiscrim p := by
    dsimp [spectralDiscrim]
    nlinarith [p.hgamma_pos]
  dsimp [realEigenSplitting]
  calc
    (2 * Real.sqrt (spectralDiscrim p)) ^ 2 = 4 * (Real.sqrt (spectralDiscrim p)) ^ 2 := by ring
    _ = 4 * spectralDiscrim p := by rw [Real.sq_sqrt hn]

/-- An arithmetic identity for two prescribed symmetric offsets. -/
theorem trace_mean_invariant (omega0 delta : ℝ) :
    ((omega0 + delta) + (omega0 - delta)) / 2 = omega0 := by ring

structure NonHermitianPhotonicFormalSuite : Prop where
  h_discrim_ep : ∀ p, spectralDiscrim p = 0 ↔ IsExceptionalPoint p
  h_ep_coalesce : ∀ p, IsExceptionalPoint p → realEigenSplitting p = 0
  h_unbroken_pos : ∀ p, p.gamma < p.kappa → 0 < spectralDiscrim p
  h_unbroken_split : ∀ p, p.gamma < p.kappa → 0 < realEigenSplitting p
  h_broken_neg : ∀ p, p.kappa < p.gamma → spectralDiscrim p < 0
  h_split_sq : ∀ p, p.gamma ≤ p.kappa → (realEigenSplitting p) ^ 2 = 4 * spectralDiscrim p
  h_trace_inv : ∀ (omega0 delta : ℝ), ((omega0 + delta) + (omega0 - delta)) / 2 = omega0

theorem non_hermitian_photonic_master_verification_suite : NonHermitianPhotonicFormalSuite := {
  h_discrim_ep := discrim_zero_iff_ep
  h_ep_coalesce := ep_eigenvalues_coalesce
  h_unbroken_pos := unbroken_phase_discrim_pos
  h_unbroken_split := unbroken_phase_splitting_pos
  h_broken_neg := broken_phase_discrim_neg
  h_split_sq := splitting_sq_eq
  h_trace_inv := trace_mean_invariant
}

#print axioms non_hermitian_photonic_master_verification_suite

end NonHermitianPhotonicEP
