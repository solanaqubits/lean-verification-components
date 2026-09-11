import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false

noncomputable section

namespace SpintronicTransport

/-- A positive conductance scale, supplied as a parameter. -/
structure TransportConstants where
  G0 : ℝ
  hG0 : 0 < G0

def klitzingConstant (tc : TransportConstants) : ℝ := 1 / tc.G0

theorem klitzing_pos (tc : TransportConstants) : 0 < klitzingConstant tc := by
  exact one_div_pos.mpr tc.hG0

/-- Four entries of a real two-dimensional linear response. -/
structure ConductivityTensor2D where
  sxx : ℝ
  sxy : ℝ
  syx : ℝ
  syy : ℝ

@[ext] structure Vector2D where
  x : ℝ
  y : ℝ

def applyConductivity (sigma : ConductivityTensor2D) (E : Vector2D) : Vector2D :=
  ⟨sigma.sxx * E.x + sigma.sxy * E.y, sigma.syx * E.x + sigma.syy * E.y⟩

def jouleDissipation (sigma : ConductivityTensor2D) (E : Vector2D) : ℝ :=
  let J := applyConductivity sigma E
  J.x * E.x + J.y * E.y

/-- A prescribed integer multiple; C is not derived from a topological construction. -/
def hallConductivity (tc : TransportConstants) (C : ℤ) : ℝ := (C : ℝ) * tc.G0

def chernConductivityTensor (tc : TransportConstants) (C : ℤ) : ConductivityTensor2D :=
  ⟨0, hallConductivity tc C, -hallConductivity tc C, 0⟩

theorem chern_tensor_antisymmetric (tc : TransportConstants) (C : ℤ) :
    (chernConductivityTensor tc C).syx = -(chernConductivityTensor tc C).sxy := rfl

theorem chern_tensor_longitudinal_zero (tc : TransportConstants) (C : ℤ) :
    (chernConductivityTensor tc C).sxx = 0 ∧ (chernConductivityTensor tc C).syy = 0 :=
  ⟨rfl, rfl⟩

/-- The quadratic power expression vanishes for the prescribed antisymmetric response. -/
theorem dissipationless_transport (tc : TransportConstants) (C : ℤ) (E : Vector2D) :
    jouleDissipation (chernConductivityTensor tc C) E = 0 := by
  dsimp [jouleDissipation, applyConductivity, chernConductivityTensor]
  ring

/-- Reciprocal scalar response; it is the yx entry of the inverse in this sign convention. -/
def hallResistivity (tc : TransportConstants) (C : ℤ) : ℝ :=
  klitzingConstant tc / (C : ℝ)

theorem hall_resistivity_conductance_inverse (tc : TransportConstants) (C : ℤ) (hC : C ≠ 0) :
    hallResistivity tc C * hallConductivity tc C = 1 := by
  have hc : (C : ℝ) ≠ 0 := by exact_mod_cast hC
  have hg : tc.G0 ≠ 0 := ne_of_gt tc.hG0
  dsimp [hallResistivity, hallConductivity, klitzingConstant]
  field_simp

theorem quantized_hall_resistance_eq (tc : TransportConstants) (C : ℤ) (_hC : C ≠ 0) :
    hallResistivity tc C = (1 / (C : ℝ)) * klitzingConstant tc := by
  dsimp [hallResistivity]
  ring

/-- Correct inverse sign convention: [[0, -1/sigma], [1/sigma, 0]]. -/
def resistivityTensor (tc : TransportConstants) (C : ℤ) : ConductivityTensor2D :=
  ⟨0, -hallResistivity tc C, hallResistivity tc C, 0⟩

theorem resistivity_left_inverse (tc : TransportConstants) (C : ℤ) (hC : C ≠ 0)
    (E : Vector2D) :
    applyConductivity (resistivityTensor tc C)
      (applyConductivity (chernConductivityTensor tc C) E) = E := by
  have h := hall_resistivity_conductance_inverse tc C hC
  ext <;> dsimp [applyConductivity, resistivityTensor, chernConductivityTensor] <;>
    nlinarith [congrArg (fun t : ℝ => t * E.x) h, congrArg (fun t : ℝ => t * E.y) h]

theorem resistivity_right_inverse (tc : TransportConstants) (C : ℤ) (hC : C ≠ 0)
    (J : Vector2D) :
    applyConductivity (chernConductivityTensor tc C)
      (applyConductivity (resistivityTensor tc C) J) = J := by
  have h := hall_resistivity_conductance_inverse tc C hC
  ext <;> dsimp [applyConductivity, resistivityTensor, chernConductivityTensor] <;>
    nlinarith [congrArg (fun t : ℝ => t * J.x) h, congrArg (fun t : ℝ => t * J.y) h]

structure SpintronicTransportFormalSuite : Prop where
  h_klitzing_pos : ∀ tc, 0 < klitzingConstant tc
  h_antisymm : ∀ tc C,
    (chernConductivityTensor tc C).syx = -(chernConductivityTensor tc C).sxy
  h_longitudinal : ∀ tc C,
    (chernConductivityTensor tc C).sxx = 0 ∧ (chernConductivityTensor tc C).syy = 0
  h_dissipationless : ∀ tc C E, jouleDissipation (chernConductivityTensor tc C) E = 0
  h_inverse : ∀ tc C, C ≠ 0 → hallResistivity tc C * hallConductivity tc C = 1
  h_quantized_R : ∀ tc C, C ≠ 0 →
    hallResistivity tc C = (1 / (C : ℝ)) * klitzingConstant tc
  h_left_inverse : ∀ tc C, C ≠ 0 → ∀ E,
    applyConductivity (resistivityTensor tc C)
      (applyConductivity (chernConductivityTensor tc C) E) = E
  h_right_inverse : ∀ tc C, C ≠ 0 → ∀ J,
    applyConductivity (chernConductivityTensor tc C)
      (applyConductivity (resistivityTensor tc C) J) = J

theorem spintronic_transport_master_verification_suite : SpintronicTransportFormalSuite := {
  h_klitzing_pos := klitzing_pos
  h_antisymm := chern_tensor_antisymmetric
  h_longitudinal := chern_tensor_longitudinal_zero
  h_dissipationless := dissipationless_transport
  h_inverse := hall_resistivity_conductance_inverse
  h_quantized_R := quantized_hall_resistance_eq
  h_left_inverse := resistivity_left_inverse
  h_right_inverse := resistivity_right_inverse
}

#print axioms spintronic_transport_master_verification_suite

end SpintronicTransport
