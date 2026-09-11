import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false
noncomputable section

namespace MechanismDesignEIP1559

/-- Parameters for a real-valued fee model. -/
structure EIP1559Config where
  targetGas : ℝ
  maxGasRate : ℝ
  htarget_pos : 0 < targetGas
  hmax_rate : maxGasRate = 2

def feeMultiplier (targetGas gasUsed : ℝ) : ℝ :=
  1 + (gasUsed - targetGas) / (8 * targetGas)

def nextBaseFee (baseFee targetGas gasUsed : ℝ) : ℝ :=
  baseFee * feeMultiplier targetGas gasUsed

theorem fee_multiplier_empty_block (targetGas : ℝ) (htarget : targetGas ≠ 0) :
    feeMultiplier targetGas 0 = 7 / 8 := by
  dsimp [feeMultiplier]
  field_simp
  ring

theorem fee_multiplier_target_block (targetGas : ℝ) (_htarget : targetGas ≠ 0) :
    feeMultiplier targetGas targetGas = 1 := by simp [feeMultiplier]

theorem fee_multiplier_full_block (targetGas : ℝ) (htarget : targetGas ≠ 0) :
    feeMultiplier targetGas (2 * targetGas) = 9 / 8 := by
  dsimp [feeMultiplier]
  field_simp
  ring

theorem fee_multiplier_bounds (targetGas gasUsed : ℝ)
    (htarget_pos : 0 < targetGas) (hgas_nonneg : 0 ≤ gasUsed)
    (hgas_max : gasUsed ≤ 2 * targetGas) :
    (7 / 8 : ℝ) ≤ feeMultiplier targetGas gasUsed ∧
      feeMultiplier targetGas gasUsed ≤ (9 / 8 : ℝ) := by
  have hd : 0 < 8 * targetGas := by linarith
  have hlo : -(1 / 8 : ℝ) ≤ (gasUsed - targetGas) / (8 * targetGas) := by
    apply (le_div_iff₀ hd).mpr
    linarith
  have hhi : (gasUsed - targetGas) / (8 * targetGas) ≤ (1 / 8 : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    linarith
  dsimp [feeMultiplier]
  constructor <;> linarith

theorem next_base_fee_pos (baseFee targetGas gasUsed : ℝ)
    (hbase_pos : 0 < baseFee) (htarget_pos : 0 < targetGas)
    (hgas_nonneg : 0 ≤ gasUsed) (hgas_max : gasUsed ≤ 2 * targetGas) :
    0 < nextBaseFee baseFee targetGas gasUsed := by
  have hb := fee_multiplier_bounds targetGas gasUsed htarget_pos hgas_nonneg hgas_max
  exact mul_pos hbase_pos (by linarith [hb.1])

theorem next_base_fee_eq_iff_target (baseFee targetGas gasUsed : ℝ)
    (hbase_pos : 0 < baseFee) (htarget_pos : 0 < targetGas) :
    nextBaseFee baseFee targetGas gasUsed = baseFee ↔ gasUsed = targetGas := by
  dsimp [nextBaseFee, feeMultiplier]
  have hd : 8 * targetGas ≠ 0 := by linarith
  constructor
  · intro h
    have hm : 1 + (gasUsed - targetGas) / (8 * targetGas) = 1 :=
      mul_left_cancel₀ (ne_of_gt hbase_pos) (by simpa using h)
    have hz : (gasUsed - targetGas) / (8 * targetGas) = 0 := by linarith
    have hn := (div_eq_zero_iff.mp hz).resolve_right hd
    linarith
  · intro h
    rw [h]
    simp

theorem next_base_fee_gt_of_gas_gt (baseFee targetGas gasUsed : ℝ)
    (hbase_pos : 0 < baseFee) (htarget_pos : 0 < targetGas)
    (h_gt : targetGas < gasUsed) : baseFee < nextBaseFee baseFee targetGas gasUsed := by
  have hd : 0 < 8 * targetGas := by linarith
  have hp := div_pos (sub_pos.mpr h_gt) hd
  have hm : 1 < feeMultiplier targetGas gasUsed := by dsimp [feeMultiplier]; linarith
  simpa [nextBaseFee] using mul_lt_mul_of_pos_left hm hbase_pos

theorem next_base_fee_lt_of_gas_lt (baseFee targetGas gasUsed : ℝ)
    (hbase_pos : 0 < baseFee) (htarget_pos : 0 < targetGas)
    (h_lt : gasUsed < targetGas) : nextBaseFee baseFee targetGas gasUsed < baseFee := by
  have hd : 0 < 8 * targetGas := by linarith
  have hn := div_neg_of_neg_of_pos (sub_neg.mpr h_lt) hd
  have hm : feeMultiplier targetGas gasUsed < 1 := by dsimp [feeMultiplier]; linarith
  simpa [nextBaseFee] using mul_lt_mul_of_pos_left hm hbase_pos

structure MechanismDesignEIP1559FormalSuite : Prop where
  h_empty_mult : ∀ t, t ≠ 0 → feeMultiplier t 0 = 7 / 8
  h_target_mult : ∀ t, t ≠ 0 → feeMultiplier t t = 1
  h_full_mult : ∀ t, t ≠ 0 → feeMultiplier t (2 * t) = 9 / 8
  h_bounds : ∀ t g, 0 < t → 0 ≤ g → g ≤ 2 * t →
    (7 / 8 : ℝ) ≤ feeMultiplier t g ∧ feeMultiplier t g ≤ (9 / 8 : ℝ)
  h_fee_pos : ∀ b t g, 0 < b → 0 < t → 0 ≤ g → g ≤ 2 * t → 0 < nextBaseFee b t g
  h_equil_iff : ∀ b t g, 0 < b → 0 < t → (nextBaseFee b t g = b ↔ g = t)
  h_fee_increase : ∀ b t g, 0 < b → 0 < t → t < g → b < nextBaseFee b t g
  h_fee_decrease : ∀ b t g, 0 < b → 0 < t → g < t → nextBaseFee b t g < b

theorem mechanism_design_eip1559_master_verification_suite : MechanismDesignEIP1559FormalSuite := {
  h_empty_mult := fee_multiplier_empty_block
  h_target_mult := fee_multiplier_target_block
  h_full_mult := fee_multiplier_full_block
  h_bounds := fee_multiplier_bounds
  h_fee_pos := next_base_fee_pos
  h_equil_iff := next_base_fee_eq_iff_target
  h_fee_increase := next_base_fee_gt_of_gas_gt
  h_fee_decrease := next_base_fee_lt_of_gas_lt
}

#print axioms mechanism_design_eip1559_master_verification_suite

end MechanismDesignEIP1559
