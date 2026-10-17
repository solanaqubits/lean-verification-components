/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.HCTKScalarPartition

/-! Exact arithmetic API applications and countermodels, not physical assertions. -/
open HCTKScalarPartition

noncomputable section

example : total (partition (159 / 100000000 : ℝ) (2 / 5) (10^16)) = 159 / 100000000 := by
  exact partition_total _ _ _
example : (partition (10 : ℝ) (3 / 10) 7).localAmount = 3 := by norm_num [partition]
example : (partition (10 : ℝ) (3 / 10) 7).reservoirAmount = 7 := by norm_num [partition]
example : partition (10 : ℝ) 0 7 = ⟨0, 10, 7⟩ := partition_stopped _ _
example : partition (10 : ℝ) 1 7 = ⟨10, 0, 7⟩ := partition_powered _ _
example : (transfer ⟨3, 7, 11⟩ (1 : ℝ)).localAmount = 2 ∧
    (transfer ⟨3, 7, 11⟩ (1 : ℝ)).reservoirAmount = 8 := by norm_num [transfer]
example : total (runTransfers ⟨10, 0, 11⟩ [2, 3, 5]) = 10 := by
  norm_num [runTransfers, transfer, total]
example : (runTransfers ⟨10, 0, 11⟩ [2, 3, 5]).label = 11 := by rfl
-- Too much transfer violates component positivity even though the total is preserved.
example : (transfer ⟨1, 0, 2⟩ (2 : ℝ)).localAmount < 0 := by norm_num [transfer]
-- A negative fraction likewise is outside the component-positivity contract.
example : (partition (1 : ℝ) (-1) 0).localAmount < 0 := by norm_num [partition]
-- Loss without the compensating addition is not the specified transfer.
example : total ⟨(3 : ℝ) - 1, 7, 11⟩ ≠ total ⟨3, 7, 11⟩ := by norm_num [total]
example : regularizedWindow (216 / 10^34 : ℝ) (1 / 10^12) 0 = 216 / 10^22 := by
  norm_num [regularizedWindow]
example : regularizedWindow (2 : ℝ) 1 1 = 1 := by norm_num [regularizedWindow]
example : regularizedWindow (2 : ℝ) 1 0 = 2 := by norm_num [regularizedWindow]
example : 0 < regularizedWindow (2 : ℝ) 1 (1 / 10) ∧
    regularizedWindow (2 : ℝ) 1 (1 / 10) ≤ 2 := by
  simpa using regularizedWindow_bounds (2 : ℝ) 1 (1 / 10) (by norm_num) (by norm_num) (by norm_num)
example : ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ 2 / p > 1000 := by
  exact idealWindow_unbounded _ _ (by norm_num) (by norm_num)
-- Label equality is not forced by conservation of the scalar amount alone.
example : total (partition (10 : ℝ) 1 3) = total (partition 10 0 4) ∧
    (partition (10 : ℝ) 1 3).label ≠ (partition 10 0 4).label := by
  norm_num [partition, total]
-- Arbitrary state fields need not conserve a supplied total.
example : total (⟨3, 8, 11⟩ : State) ≠ (10 : ℝ) := by norm_num [total]

example (p : Parameters) : 0 < frequency p 2 := frequency_pos _ _
example (p : Parameters) : 0 < metricScalar p (159 / 100000000) :=
  metricScalar_pos _ _ (by norm_num)
example (p : Parameters) : 0 < temperature p (10^9) :=
  temperature_pos _ _ (by norm_num)
example (p : Parameters) : informationBound p 0 = 0 := by simp [informationBound]
example (p : Parameters) : informationBound p 6 = 3 * informationBound p 2 := by
  convert informationBound_scale p 2 3 using 1; norm_num
example (p : Parameters) : temperature p 6 = temperature p 2 / 3 := by
  convert temperature_scale p 2 3 (by norm_num) (by norm_num) using 1; norm_num
