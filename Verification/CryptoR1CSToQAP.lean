import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false
noncomputable section

namespace CryptoR1CSToQAP

/-- Two distinct real interpolation nodes. -/
structure QAPDomain where
  r1 : ℝ
  r2 : ℝ
  h_diff : r1 ≠ r2

def lagrangeL1 (d : QAPDomain) (x : ℝ) : ℝ := (x - d.r2) / (d.r1 - d.r2)
def lagrangeL2 (d : QAPDomain) (x : ℝ) : ℝ := (x - d.r1) / (d.r2 - d.r1)

theorem lagrange_L1_at_r1 (d : QAPDomain) : lagrangeL1 d d.r1 = 1 :=
  div_self (sub_ne_zero.mpr d.h_diff)

theorem lagrange_L1_at_r2 (d : QAPDomain) : lagrangeL1 d d.r2 = 0 := by
  simp [lagrangeL1]

theorem lagrange_L2_at_r1 (d : QAPDomain) : lagrangeL2 d d.r1 = 0 := by
  simp [lagrangeL2]

theorem lagrange_L2_at_r2 (d : QAPDomain) : lagrangeL2 d d.r2 = 1 :=
  div_self (sub_ne_zero.mpr d.h_diff.symm)

/-- Evaluation of the linear interpolant with prescribed values at the two nodes. -/
def interpPoly (d : QAPDomain) (v1 v2 x : ℝ) : ℝ :=
  v1 * lagrangeL1 d x + v2 * lagrangeL2 d x

theorem interp_at_r1 (d : QAPDomain) (v1 v2 : ℝ) : interpPoly d v1 v2 d.r1 = v1 := by
  simp [interpPoly, lagrange_L1_at_r1, lagrange_L2_at_r1]

theorem interp_at_r2 (d : QAPDomain) (v1 v2 : ℝ) : interpPoly d v1 v2 d.r2 = v2 := by
  simp [interpPoly, lagrange_L1_at_r2, lagrange_L2_at_r2]

def vanishingPoly (d : QAPDomain) (x : ℝ) : ℝ := (x - d.r1) * (x - d.r2)

theorem vanishing_at_r1 (d : QAPDomain) : vanishingPoly d d.r1 = 0 := by
  simp [vanishingPoly]

theorem vanishing_at_r2 (d : QAPDomain) : vanishingPoly d d.r2 = 0 := by
  simp [vanishingPoly]

/-- The constant quotient for two satisfied scalar row constraints. -/
def quotientPoly (d : QAPDomain) (a1 a2 b1 b2 : ℝ) : ℝ :=
  ((a1 - a2) * (b1 - b2)) / (d.r1 - d.r2) ^ 2

/-- Pointwise factorization of the interpolated residual for two satisfied rows. -/
theorem r1cs_to_qap_completeness (d : QAPDomain) (a1 a2 b1 b2 c1 c2 x : ℝ)
    (h_c1 : a1 * b1 = c1) (h_c2 : a2 * b2 = c2) :
    let A := interpPoly d a1 a2 x
    let B := interpPoly d b1 b2 x
    let C := interpPoly d c1 c2 x
    let H := quotientPoly d a1 a2 b1 b2
    let Z := vanishingPoly d x
    A * B - C = H * Z := by
  dsimp [interpPoly, quotientPoly, vanishingPoly, lagrangeL1, lagrangeL2]
  rw [← h_c1, ← h_c2]
  have h12 : d.r1 - d.r2 ≠ 0 := sub_ne_zero.mpr d.h_diff
  have h21 : d.r2 - d.r1 ≠ 0 := sub_ne_zero.mpr d.h_diff.symm
  field_simp
  ring

/-- Evaluating the identity at the two nodes recovers both scalar constraints. -/
theorem r1cs_to_qap_soundness (d : QAPDomain) (a1 a2 b1 b2 c1 c2 : ℝ)
    (h_id : ∀ x, interpPoly d a1 a2 x * interpPoly d b1 b2 x - interpPoly d c1 c2 x =
      quotientPoly d a1 a2 b1 b2 * vanishingPoly d x) :
    a1 * b1 = c1 ∧ a2 * b2 = c2 := by
  have h1 := h_id d.r1
  have h2 := h_id d.r2
  simp only [interp_at_r1, vanishing_at_r1, mul_zero, sub_eq_zero] at h1
  simp only [interp_at_r2, vanishing_at_r2, mul_zero, sub_eq_zero] at h2
  exact ⟨h1, h2⟩

structure CryptoR1CSQAPFormalSuite : Prop where
  h_lagrange1_r1 : ∀ d, lagrangeL1 d d.r1 = 1
  h_lagrange1_r2 : ∀ d, lagrangeL1 d d.r2 = 0
  h_lagrange2_r1 : ∀ d, lagrangeL2 d d.r1 = 0
  h_lagrange2_r2 : ∀ d, lagrangeL2 d d.r2 = 1
  h_interp_r1 : ∀ d v1 v2, interpPoly d v1 v2 d.r1 = v1
  h_interp_r2 : ∀ d v1 v2, interpPoly d v1 v2 d.r2 = v2
  h_vanish_r1 : ∀ d, vanishingPoly d d.r1 = 0
  h_vanish_r2 : ∀ d, vanishingPoly d d.r2 = 0
  h_complete : ∀ d a1 a2 b1 b2 c1 c2 x, a1 * b1 = c1 → a2 * b2 = c2 →
    interpPoly d a1 a2 x * interpPoly d b1 b2 x - interpPoly d c1 c2 x =
      quotientPoly d a1 a2 b1 b2 * vanishingPoly d x
  h_sound : ∀ d a1 a2 b1 b2 c1 c2,
    (∀ x, interpPoly d a1 a2 x * interpPoly d b1 b2 x - interpPoly d c1 c2 x =
      quotientPoly d a1 a2 b1 b2 * vanishingPoly d x) → a1 * b1 = c1 ∧ a2 * b2 = c2

theorem crypto_r1cs_to_qap_master_verification_suite : CryptoR1CSQAPFormalSuite := {
  h_lagrange1_r1 := lagrange_L1_at_r1
  h_lagrange1_r2 := lagrange_L1_at_r2
  h_lagrange2_r1 := lagrange_L2_at_r1
  h_lagrange2_r2 := lagrange_L2_at_r2
  h_interp_r1 := interp_at_r1
  h_interp_r2 := interp_at_r2
  h_vanish_r1 := vanishing_at_r1
  h_vanish_r2 := vanishing_at_r2
  h_complete := r1cs_to_qap_completeness
  h_sound := r1cs_to_qap_soundness
}

#print axioms crypto_r1cs_to_qap_master_verification_suite

end CryptoR1CSToQAP
