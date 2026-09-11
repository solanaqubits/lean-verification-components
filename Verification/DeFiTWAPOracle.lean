import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false
noncomputable section

namespace DeFiTWAPOracle

/-- Endpoints of a strictly positive observation window. -/
structure TimeWindow where
  t1 : ℝ
  t2 : ℝ
  h_time_order : t1 < t2

def timeDelta (w : TimeWindow) : ℝ := w.t2 - w.t1

theorem time_delta_pos (w : TimeWindow) : 0 < timeDelta w :=
  sub_pos.mpr w.h_time_order

theorem time_delta_ne_zero (w : TimeWindow) : timeDelta w ≠ 0 :=
  ne_of_gt (time_delta_pos w)

/-- Arithmetic average from two supplied cumulative observations. -/
def computeTWAP (c1 c2 : ℝ) (w : TimeWindow) : ℝ :=
  (c2 - c1) / timeDelta w

theorem twap_constant_price (c1 P : ℝ) (w : TimeWindow) :
    let c2 := c1 + P * timeDelta w
    computeTWAP c1 c2 w = P := by
  dsimp [computeTWAP]
  rw [add_sub_cancel_left, mul_div_cancel_right₀ _ (time_delta_ne_zero w)]

/-- Definitional identity for a supplied two-period accumulator. -/
theorem twap_two_period_weighted_average (P1 dt1 P2 dt2 : ℝ)
    (_h_dt1 : 0 < dt1) (_h_dt2 : 0 < dt2) :
    let totalDelta := dt1 + dt2
    let cumulativeGrowth := P1 * dt1 + P2 * dt2
    cumulativeGrowth / totalDelta = (P1 * dt1 + P2 * dt2) / (dt1 + dt2) := by
  rfl

/-- Exact scalar displacement; this is not a protocol attack-resistance theorem. -/
theorem twap_single_block_manipulation_bound (P0 P_spike dt_spike totalT : ℝ)
    (h_totalT : 0 < totalT) (_h_spike_le : dt_spike ≤ totalT)
    (_h_spike_pos : 0 ≤ dt_spike) :
    let dt_normal := totalT - dt_spike
    let totalAccum := P0 * dt_normal + P_spike * dt_spike
    let resultingTWAP := totalAccum / totalT
    resultingTWAP - P0 = (dt_spike / totalT) * (P_spike - P0) := by
  dsimp
  field_simp [ne_of_gt h_totalT]
  ring

structure DeFiTWAPFormalSuite : Prop where
  h_delta_pos : ∀ w : TimeWindow, 0 < timeDelta w
  h_const_price : ∀ (c1 P : ℝ) (w : TimeWindow),
    computeTWAP c1 (c1 + P * timeDelta w) w = P
  h_manipulation : ∀ (P0 P_spike dt_spike totalT : ℝ),
    0 < totalT → dt_spike ≤ totalT → 0 ≤ dt_spike →
    let dt_normal := totalT - dt_spike
    let totalAccum := P0 * dt_normal + P_spike * dt_spike
    let resultingTWAP := totalAccum / totalT
    resultingTWAP - P0 = (dt_spike / totalT) * (P_spike - P0)

/-- Registry of the stated scalar accumulator identities. -/
theorem defi_twap_master_verification_suite : DeFiTWAPFormalSuite := {
  h_delta_pos := time_delta_pos
  h_const_price := twap_constant_price
  h_manipulation := twap_single_block_manipulation_bound
}

end DeFiTWAPOracle
