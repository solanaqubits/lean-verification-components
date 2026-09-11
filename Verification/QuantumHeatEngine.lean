import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false

noncomputable section

namespace QuantumHeatEngine

/-- Positive ordered frequencies for the prescribed cycle formulas. -/
structure EngineFrequencies where
  wc : ℝ
  wh : ℝ
  hwc_pos : 0 < wc
  h_order : wc < wh

structure ReservoirTemperatures where
  Tc : ℝ
  Th : ℝ
  hTc_pos : 0 < Tc
  h_order : Tc < Th

/-- Prescribed heat input in units where the common factor hbar is omitted. -/
def heatIn (f : EngineFrequencies) (dp : ℝ) : ℝ := f.wh * dp
def heatOut (f : EngineFrequencies) (dp : ℝ) : ℝ := f.wc * dp
def netWork (f : EngineFrequencies) (dp : ℝ) : ℝ := heatIn f dp - heatOut f dp
def ottoEfficiency (f : EngineFrequencies) : ℝ := 1 - f.wc / f.wh
def carnotEfficiency (t : ReservoirTemperatures) : ℝ := 1 - t.Tc / t.Th

theorem wh_pos (f : EngineFrequencies) : 0 < f.wh := lt_trans f.hwc_pos f.h_order
theorem Th_pos (t : ReservoirTemperatures) : 0 < t.Th := lt_trans t.hTc_pos t.h_order

theorem netWork_eq (f : EngineFrequencies) (dp : ℝ) :
    netWork f dp = (f.wh - f.wc) * dp := by
  dsimp [netWork, heatIn, heatOut]
  ring

theorem netWork_pos (f : EngineFrequencies) (dp : ℝ) (hdp : 0 < dp) :
    0 < netWork f dp := by
  rw [netWork_eq]
  exact mul_pos (sub_pos.mpr f.h_order) hdp

theorem heatIn_pos (f : EngineFrequencies) (dp : ℝ) (hdp : 0 < dp) :
    0 < heatIn f dp := mul_pos (wh_pos f) hdp

theorem heatOut_pos (f : EngineFrequencies) (dp : ℝ) (hdp : 0 < dp) :
    0 < heatOut f dp := mul_pos f.hwc_pos hdp

theorem netWork_eq_efficiency_mul_heatIn (f : EngineFrequencies) (dp : ℝ) :
    netWork f dp = ottoEfficiency f * heatIn f dp := by
  dsimp [netWork, heatIn, heatOut, ottoEfficiency]
  have hwh : f.wh ≠ 0 := ne_of_gt (wh_pos f)
  field_simp

theorem otto_efficiency_bounds (f : EngineFrequencies) :
    0 < ottoEfficiency f ∧ ottoEfficiency f < 1 := by
  have hp := div_pos f.hwc_pos (wh_pos f)
  have hl := (div_lt_one (wh_pos f)).mpr f.h_order
  dsimp [ottoEfficiency]
  constructor <;> linarith

theorem carnot_efficiency_bounds (t : ReservoirTemperatures) :
    0 < carnotEfficiency t ∧ carnotEfficiency t < 1 := by
  have hp := div_pos t.hTc_pos (Th_pos t)
  have hl := (div_lt_one (Th_pos t)).mpr t.h_order
  dsimp [carnotEfficiency]
  constructor <;> linarith

/-- Conditional comparison of the two prescribed efficiency formulas. -/
theorem otto_lt_carnot (f : EngineFrequencies) (t : ReservoirTemperatures)
    (h_engine_mode : t.Tc / t.Th < f.wc / f.wh) :
    ottoEfficiency f < carnotEfficiency t := by
  dsimp [ottoEfficiency, carnotEfficiency]
  linarith

structure QuantumHeatEngineFormalSuite : Prop where
  h_net_work_eq : ∀ f dp, netWork f dp = (f.wh - f.wc) * dp
  h_work_pos : ∀ f dp, 0 < dp → 0 < netWork f dp
  h_work_eff : ∀ f dp, netWork f dp = ottoEfficiency f * heatIn f dp
  h_eff_bounds : ∀ f, 0 < ottoEfficiency f ∧ ottoEfficiency f < 1
  h_carnot_bound : ∀ f t,
    t.Tc / t.Th < f.wc / f.wh → ottoEfficiency f < carnotEfficiency t

theorem quantum_heat_engine_master_verification_suite : QuantumHeatEngineFormalSuite := {
  h_net_work_eq := netWork_eq
  h_work_pos := netWork_pos
  h_work_eff := netWork_eq_efficiency_mul_heatIn
  h_eff_bounds := otto_efficiency_bounds
  h_carnot_bound := otto_lt_carnot
}

#print axioms quantum_heat_engine_master_verification_suite

end QuantumHeatEngine
