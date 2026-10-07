import Verification.QuantumShorOrderFindingCore
import Mathlib.Tactic.IntervalCases

open QuantumShorOrderFindingCore QuantumPhaseEstimationGeneral
open scoped BigOperators

namespace ShorRegression

def fifteen : Parameters := ⟨15, by decide, 2, by decide, 4, by decide⟩
def seven : Parameters := ⟨7, by decide, 2, by decide, 3, by decide⟩
def identityBase : Parameters := ⟨3, by decide, 1, by decide, 2, by decide⟩

theorem fifteen_period : fifteen.period = 4 := by
  change orderOf (2 : ZMod 15) = 4
  apply (orderOf_eq_iff (by decide : 0 < 4)).2
  constructor
  · decide
  · intro k hk hpos
    interval_cases k <;> decide

theorem seven_period : seven.period = 3 := by
  change orderOf (2 : ZMod 7) = 3
  apply (orderOf_eq_iff (by decide : 0 < 3)).2
  constructor
  · decide
  · intro k hk hpos
    interval_cases k <;> decide

example : identityBase.period = 1 := by
  change orderOf (1 : ZMod 3) = 1
  exact orderOf_one

-- Modular multiplication acts on every residue, not only on units.
example : (fifteen.registerPerm 3).val = 6 := by
  rw [fifteen.registerPerm_low 3 (by decide)]
  rfl
example : (fifteen.registerPerm 0).val = 0 := by
  rw [fifteen.registerPerm_low 0 (by decide)]
  rfl
-- The padded basis state is fixed.
example : fifteen.registerPerm 15 = 15 := fifteen.registerPerm_high 15 (by decide)
example (v : TargetState fifteen.dimension) :
    fifteen.inverseOperator (fifteen.modularOperator v) = v :=
  (fifteen.modularOperator_inverse v).1
example : IsUnitary fifteen.modularOperator := fifteen.modularOperator_unitary
example : IsUnitary seven.modularOperator := seven.modularOperator_unitary

-- Generic obligations retain all valid inputs, including order one.
example (c : Parameters) : c.input = scale c.period • ∑ s, c.eigenstate s :=
  c.shor_input_state_decomposition
example (c : Parameters) (s t : Fin c.period) :
    hermitian (c.eigenstate s) (c.eigenstate t) = if s = t then 1 else 0 :=
  c.shor_eigenstates_orthonormal s t
example (c : Parameters) (s : Fin c.period) :
    c.modularOperator (c.eigenstate s) = phase (s.val / c.period) • c.eigenstate s :=
  c.shor_eigenstate_action s
example (c : Parameters) (n : ℕ) :
    (∑ y : Fin (2^n), normSquared (runQPE c.modularOperator n c.input y)) = 1 :=
  c.shor_distribution_normalized n
example (c : Parameters) : normSquared (runQPE c.modularOperator 0 c.input 0) = 1 := by
  rw [c.shor_qpe_probability_mixture]
  have h : ∀ s : Fin c.period, probability (2^0) (s.val / c.period) 0 = 1 :=
    fun s => qpe_zero_qubit_probability (s.val / c.period) 0
  simp_rw [h]
  simp [c.period_pos.ne']

-- For r=4 and two control qubits the actual marginal is uniform, not a unit peak.
example (y : Fin 4) : normSquared (runQPE fifteen.modularOperator 2 fifteen.input y) = 1/4 := by
  rw [fifteen.shor_qpe_probability_mixture, fifteen_period]
  change (4 : ℝ)⁻¹ * (∑ x : Fin 4, probability 4 (x.val / 4) y) = 1/4
  have h : ∀ x : Fin 4, probability 4 (x.val / 4) y = if y = x then 1 else 0 :=
    fun x => qpe_exact_probability (by decide) x y
  simp_rw [h]
  simp

-- A non-dyadic component and its correctly weighted contribution to the mixture.
def oneOfThree : Fin seven.period := ⟨1, by rw [seven_period]; decide⟩
example : 4 / Real.pi ^ 2 ≤ probability 8 (1/3) 3 := by
  have h := seven.shor_phase_accuracy_bound 3 oneOfThree 3
  simpa [oneOfThree, seven_period] using h ⟨0, by norm_num [oneOfThree, seven_period]⟩
example : (1/3 : ℝ) * (4 / Real.pi ^ 2) ≤
    normSquared (runQPE seven.modularOperator 3 seven.input 3) := by
  have h := seven.shor_mixture_peak_lower_bound 3 oneOfThree 3
    ⟨0, by norm_num [oneOfThree, seven_period]⟩
  simpa [seven_period] using h

-- Recovering the reduced denominator is not recovering the order.
example : (2/4 : ℝ) = 1/2 ∧ fifteen.period ≠ 2 ∧ 2^2 % 15 ≠ 1 := by
  rw [fifteen_period]
  norm_num
-- The non-coprime case is excluded rather than silently treated as a permutation.
example : ¬ Nat.Coprime 3 15 := by decide

end ShorRegression
