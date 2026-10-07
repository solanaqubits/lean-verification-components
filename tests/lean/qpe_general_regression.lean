import Verification.QuantumPhaseEstimationGeneral

open QuantumPhaseEstimationGeneral
open scoped BigOperators ComplexConjugate

-- Exact interference at a nontrivial register size, including cancellation off the target.
example : amplitude 8 ((3 : Fin 8).val / 8) 3 = 1 := by
  simpa using qpe_exact_dyadic_phase (N := 8) (by decide) 3 3
example : probability 8 ((3 : Fin 8).val / 8) 7 = 0 := by
  simpa using qpe_exact_probability (N := 8) (by decide) 3 7

-- Two equally near outcomes, across the period boundary, both have the proved lower bound.
example : 4 / Real.pi ^ 2 ≤ probability 16 (31 / 32) 0 := by
  apply qpe_arbitrary_phase_lower_bound 16 (by decide)
  exact ⟨1, by norm_num⟩
example : 4 / Real.pi ^ 2 ≤ probability 16 (31 / 32) 15 := by
  apply qpe_arbitrary_phase_lower_bound 16 (by decide)
  exact ⟨0, by norm_num⟩
example : 4 / Real.pi ^ 2 ≤ probability 16 (-1 / 32) 0 := by
  apply qpe_arbitrary_phase_lower_bound 16 (by decide)
  exact ⟨0, by norm_num⟩
example : 4 / Real.pi ^ 2 ≤ probability 8 (1 / 3) 3 := by
  apply qpe_arbitrary_phase_lower_bound 8 (by decide)
  exact ⟨0, by norm_num⟩

-- Integral phase differences use a separate branch, never a divided-by-zero sine quotient.
example : amplitude 8 (2 : ℝ) 0 = 1 := by
  apply amplitude_of_integral 8 (by decide)
  simpa using phase_int 2
example (θ : ℝ) (y : Fin 8) : amplitude 8 (θ + 3) y = amplitude 8 θ y := by
  exact amplitude_periodic 8 θ y 3
example (θ : ℝ) : probability (2 ^ 0) θ 0 = 1 := qpe_zero_qubit_probability θ 0

-- These tests retain arbitrary register sizes and arbitrary real phases.
example (n : ℕ) (θ : ℝ) : (∑ y : Fin (2 ^ n), probability (2 ^ n) θ y) = 1 :=
  qpe_probability_normalized (by positivity) θ
example (n : ℕ) (θ : ℝ) :
    4 / Real.pi ^ 2 ≤ probability (2 ^ n) θ (nearestSample (2 ^ n) (by positivity) θ) :=
  qpe_arbitrary_phase_lower_bound _ (by positivity) _ _ (nearest_sample_valid _ _ _)
example (U : TargetOperator 3) (k : Fin (2 ^ 5)) : controlledCascade U 5 k = U ^ k.val :=
  controlled_cascade_eq_power U 5 k
example (U : TargetOperator 2) (ψ : TargetState 2) :
    runQPE U 2 ψ = QuantumPhaseEstimation.runQPE U ψ := qpe_bridge_to_two_qubit U ψ

-- Nonvacuous eigen-inputs exist at every real phase, including non-dyadic phases.
noncomputable def scalarInput (θ : ℝ) : UnitaryEigenInput 1 θ where
  operator := phase θ • (LinearMap.id : TargetOperator 1)
  target := fun _ => 1
  unitary := by
    intro u v
    have hp : conj (phase θ) * phase θ = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, phase_norm]
      norm_num
    simp only [hermitian, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply,
      smul_eq_mul, map_mul]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (conj (phase θ) * phase θ) * (conj (u j) * v j) := by ring
      _ = _ := by rw [hp, one_mul]
  normalized := by simp [normSquared]
  eigenstate := by simp

example : 4 / Real.pi ^ 2 ≤ normSquared
    (runQPE (scalarInput (1 / 3)).operator 3 (scalarInput (1 / 3)).target
      (nearestSample (2 ^ 3) (by positivity) (1 / 3))) :=
  qpe_nearest_sample_success (scalarInput (1 / 3)) 3

example (θ : ℝ) : jointNormSquared
    (runQPE (scalarInput θ).operator 4 (scalarInput θ).target) = 1 := by
  rw [qpe_circuit_norm _ (scalarInput θ).unitary, (scalarInput θ).normalized]

example (n : ℕ) (j : Fin (2 ^ n)) :
    hadamardControl n (zeroControl n) j = scale (2 ^ n) := hadamard_prepares_uniform n j

example : ‖amplitude 8 (1 / 3) 0‖ =
    |Real.sin (Real.pi * 8 * (1 / 3))| / (8 * |Real.sin (Real.pi * (1 / 3))|) := by
  have hn : ¬ ∃ z : ℤ, (1 / 3 : ℝ) - (0 : Fin 8).val / 8 = z := by
    rintro ⟨z, hz⟩
    norm_num at hz
    have hi : 3 * z = 1 := by exact_mod_cast (show (3 : ℝ) * z = 1 by linarith)
    omega
  simpa using qpe_geometric_sum_closed_form 8 (by decide) (1 / 3) 0 hn
