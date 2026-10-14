import Verification.QuantumPOVMInformationEntropy

open QuantumPOVMInformationEntropy QuantumPOVMNaimarkDilation
open scoped BigOperators Matrix.Norms.L2Operator

-- Each example is checked by the Lean kernel; no numerical log oracle is used.
example : QuantumPOVMInformationEntropySuite := verification_suite
example : xlogx 0 = 0 := xlogx_zero
example : shannon_entropy_bits (![1,0] : Fin 2 → ℝ) = 0 := binary_entropy_values.1
example : shannon_entropy_bits (![1/2,1/2] : Fin 2 → ℝ) = 1 := binary_entropy_values.2
example : c_overlap pauliZ pauliX = 1 / Real.sqrt 2 := pauli_xz_overlap_exact
example : uncertainty_bound (c_overlap pauliZ pauliX) = 1 := pauli_xz_entropy_bound_exact
example : QuantumNoBroadcastingMixed.IsDensityMatrix qubitZero := qubitZero_density
example : QuantumNoBroadcastingMixed.IsDensityMatrix qubitMixed := qubitMixed_density
example : shannon_entropy_bits (prob_dist pauliZ qubitZero) = 0 := pauli_entropy_regressions.1
example : shannon_entropy_bits (prob_dist pauliX qubitZero) = 1 := pauli_entropy_regressions.2.1
example : shannon_entropy_bits (prob_dist pauliZ qubitMixed) +
    shannon_entropy_bits (prob_dist pauliX qubitMixed) = 2 := pauli_entropy_regressions.2.2
example (ρ : Q 2) (hρ : QuantumNoBroadcastingMixed.IsDensityMatrix ρ) :
    1 ≤ shannon_entropy_bits (prob_dist pauliZ ρ) + shannon_entropy_bits (prob_dist pauliX ρ) := by
  simpa only [pauli_xz_entropy_bound_exact] using maassen_uffink_mixed_state pauliZ pauliX ρ hρ
example : c_overlap pauliZ pauliZ = 1 := identical_basis_overlap
example : uncertainty_bound (c_overlap pauliZ pauliZ) = 0 := by
  simp [identical_basis_overlap, uncertainty_bound]
example : qutritZ.effects 1 * qutritF.effects 1 ≠ qutritF.effects 1 * qutritZ.effects 1 := qutrit_noncommuting
example : c_overlap qutritZ qutritF = 1 := qutrit_overlap_one
example : QuantumNoBroadcastingMixed.IsDensityMatrix (qutritF.effects 0) := qutrit_zero_density
example : shannon_entropy_bits (prob_dist qutritZ (qutritF.effects 0)) = 0 := qutrit_entropy_zero.1
example : shannon_entropy_bits (prob_dist qutritF (qutritF.effects 0)) = 0 := qutrit_entropy_zero.2
example : c_overlap (prepend_zero pauliZ) pauliX = c_overlap pauliZ pauliX := prepend_zero_overlap _ _
example : shannon_entropy_bits (prob_dist (prepend_zero pauliX) qubitZero) = 1 := by
  rw [prepend_zero_entropy]; exact pauli_entropy_regressions.2.1
example : prob_dist (prepend_zero pauliX) qubitZero 0 = 0 := zero_effect_probability _ _ _ rfl
example : shannon_entropy_bits (prob_dist
    (QuantumPOVMInformationallyComplete.relabel pauliX (Equiv.swap 0 1)) qubitZero) = 1 := by
  rw [measurement_entropy_relabel]; exact pauli_entropy_regressions.2.1
example : c_overlap (QuantumPOVMInformationallyComplete.relabel pauliZ (Equiv.swap 0 1))
    (QuantumPOVMInformationallyComplete.relabel pauliX (Equiv.swap 0 1)) = c_overlap pauliZ pauliX :=
  overlap_relabel _ _ _ _
example {c : ℝ} (hc : 0 < c) (h1 : c < 1) : 0 < uncertainty_bound c := bound_strictly_positive hc h1
example {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : uncertainty_bound b ≤ uncertainty_bound a :=
  bound_monotone_in_c ha hab
example (c : ℝ) : -(Real.log (c^2) / Real.log 2) = uncertainty_bound c := squared_overlap_convention c
example {d m n : ℕ} [NeZero d] (E : FinitePOVM d m) (F : FinitePOVM d n)
    (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1) :
    uncertainty_bound (c_overlap E F) ≤ shannon_entropy_bits (pure_prob E ψ) + shannon_entropy_bits (pure_prob F ψ) :=
  maassen_uffink_pure_state E F ψ hψ
example {d m n : ℕ} [NeZero d] (E : FinitePOVM d m) (F : FinitePOVM d n)
    (ρ : Q d) (hρ : QuantumNoBroadcastingMixed.IsDensityMatrix ρ) :
    uncertainty_bound (c_overlap E F) ≤ shannon_entropy_bits (prob_dist E ρ) + shannon_entropy_bits (prob_dist F ρ) :=
  maassen_uffink_mixed_state E F ρ hρ
example {d m n : ℕ} [NeZero d] (E : FinitePOVM d m) (F : FinitePOVM d n) :
    0 < c_overlap E F ∧ c_overlap E F ≤ 1 := povm_overlap_bounds E F
