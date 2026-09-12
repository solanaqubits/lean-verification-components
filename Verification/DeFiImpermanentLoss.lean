import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option linter.style.header false
noncomputable section

namespace DeFiImpermanentLoss

/-- Supplied LP valuation; k is a relative price, not a reserve product. -/
def lpValue (k : ℝ) : ℝ := 2 * Real.sqrt k

/-- Supplied hold valuation in the same units (initial value is 2). -/
def hodlValue (k : ℝ) : ℝ := 1 + k

def impermanentLoss (k : ℝ) : ℝ := lpValue k / hodlValue k - 1

theorem lp_sub_hodl_eq_neg_sq (k : ℝ) (hk : 0 ≤ k) :
    lpValue k - hodlValue k = -(Real.sqrt k - 1) ^ 2 := by
  dsimp [lpValue, hodlValue]
  nlinarith [Real.sq_sqrt hk]

/-- Exact factorization of the relative loss, including the denominator. -/
theorem il_eq_neg_sq (k : ℝ) (hk : 0 ≤ k) :
    impermanentLoss k = -(Real.sqrt k - 1) ^ 2 / (1 + k) := by
  have hd : (1 + k : ℝ) ≠ 0 := by positivity
  dsimp [impermanentLoss, hodlValue]
  apply (eq_div_iff hd).mpr
  field_simp
  have h := lp_sub_hodl_eq_neg_sq k hk
  dsimp [hodlValue] at h
  linarith

theorem il_at_one : impermanentLoss 1 = 0 := by
  norm_num [impermanentLoss, lpValue, hodlValue]

theorem il_nonpositive (k : ℝ) (hk : 0 < k) : impermanentLoss k ≤ 0 := by
  rw [il_eq_neg_sq k (le_of_lt hk)]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)

theorem il_zero_iff_k_one (k : ℝ) (hk : 0 < k) :
    impermanentLoss k = 0 ↔ k = 1 := by
  constructor
  · intro h
    rw [il_eq_neg_sq k (le_of_lt hk)] at h
    have hd : (1 + k : ℝ) ≠ 0 := by positivity
    have hz := (div_eq_zero_iff).mp h
    have hsq : (Real.sqrt k - 1) ^ 2 = 0 := by
      rcases hz with hz | hz
      · exact neg_eq_zero.mp hz
      · exact False.elim (hd hz)
    have hs : Real.sqrt k - 1 = 0 := sq_eq_zero_iff.mp hsq
    nlinarith [Real.sq_sqrt (le_of_lt hk)]
  · rintro rfl
    exact il_at_one

theorem il_inv_symmetry (k : ℝ) (hk : 0 < k) :
    impermanentLoss (1 / k) = impermanentLoss k := by
  have hs : Real.sqrt k ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hk)
  have hn : k ≠ 0 := ne_of_gt hk
  have hd : (1 + k : ℝ) ≠ 0 := by positivity
  have hi : (1 + 1 / k : ℝ) ≠ 0 := by positivity
  dsimp [impermanentLoss, lpValue, hodlValue]
  rw [one_div, Real.sqrt_inv]
  field_simp
  nlinarith [Real.sq_sqrt (le_of_lt hk)]

structure DeFiImpermanentLossFormalSuite : Prop where
  h_il_one : impermanentLoss 1 = 0
  h_il_nonpos : ∀ k : ℝ, 0 < k → impermanentLoss k ≤ 0
  h_il_zero_iff : ∀ k : ℝ, 0 < k → (impermanentLoss k = 0 ↔ k = 1)
  h_il_symmetry : ∀ k : ℝ, 0 < k → impermanentLoss (1 / k) = impermanentLoss k
  h_il_factorization : ∀ k : ℝ, 0 ≤ k →
    impermanentLoss k = -(Real.sqrt k - 1) ^ 2 / (1 + k)

/-- Registry of identities for the supplied real-valued loss function. -/
theorem defi_impermanent_loss_master_verification_suite : DeFiImpermanentLossFormalSuite := {
  h_il_one := il_at_one
  h_il_nonpos := il_nonpositive
  h_il_zero_iff := il_zero_iff_k_one
  h_il_symmetry := il_inv_symmetry
  h_il_factorization := il_eq_neg_sq
}

end DeFiImpermanentLoss
