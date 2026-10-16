import Verification.QuantumChannelTraceDistanceContract

open scoped BigOperators ComplexOrder MatrixOrder
open QuantumPOVMNaimarkDilation QuantumPOVMInformationEntropy
open QuantumChannelClassicalDataProcessing QuantumHelstromStateDiscrimination
open QuantumHelstromStateDiscrimination.Examples QuantumChannelTraceDistanceContract
open QuantumChannelTraceDistanceContract.Regression

example : QuantumChannelTraceDistanceContractSuite :=
  QuantumChannelTraceDistanceContract.verification_suite
example : trace_distance qubitZero qubitZero = 0 := trace_distance_self _
example : trace_distance qubitMixed qubitMixed = 0 := trace_distance_self _
example : trace_distance qubitZero rhoOne = 1 := orthogonal_distance
example : trace_distance rhoOne qubitZero = 1 := by
  rw [trace_distance_symm rhoOne_density qubitZero_density, orthogonal_distance]
example : trace_distance qubitZero rhoPlus = 1 / Real.sqrt 2 := noncommuting_distance
example : trace_distance rhoPlus qubitZero = 1 / Real.sqrt 2 := by
  rw [trace_distance_symm rhoPlus_density qubitZero_density, noncommuting_distance]
example : qubitZero * rhoPlus ≠ rhoPlus * qubitZero := noncommuting_states
example : trace_distance qubitZero rhoOne ≠ 0 := by rw [orthogonal_distance]; norm_num
example : 0 ≤ trace_distance qubitZero rhoPlus ∧ trace_distance qubitZero rhoPlus ≤ 1 :=
  ⟨trace_distance_nonneg qubitZero_density rhoPlus_density,
    trace_distance_le_one qubitZero_density rhoPlus_density⟩
example : trace_distance qubitZero rhoOne ≤ trace_distance qubitZero qubitMixed +
    trace_distance qubitMixed rhoOne := trace_distance_triangle qubitZero_density
      rhoOne_density qubitMixed_density
example {d : ℕ} {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ)
    (hz : trace_distance ρ σ = 0) : ρ = σ := (trace_distance_eq_zero_iff hρ hσ).mp hz
example : optimal_success fair qubitZero rhoPlus = (1 + trace_distance qubitZero rhoPlus) / 2 :=
  trace_distance_helstrom_link qubitZero_density rhoPlus_density
example : IsGreatest {x : ℝ | ∃ E : Effect 2, |(E.matrix * (qubitZero - rhoPlus)).trace.re| = x}
    (trace_distance qubitZero rhoPlus) := trace_distance_variational_sup qubitZero_density rhoPlus_density
example : (distance_effect qubitZero_density rhoPlus_density).matrix *
    (distance_effect qubitZero_density rhoPlus_density).matrix =
    (distance_effect qubitZero_density rhoPlus_density).matrix := distance_effect_projective _ _
example (E : Effect 2) : |(E.matrix * (qubitZero - rhoPlus)).trace.re| ≤ 1 / Real.sqrt 2 := by
  simpa only [noncommuting_distance] using trace_distance_effect_bound qubitZero_density rhoPlus_density E
example : TV (prob_dist (optimal_povm qubitZero_density rhoPlus_density) qubitZero)
    (prob_dist (optimal_povm qubitZero_density rhoPlus_density) rhoPlus) = 1 / Real.sqrt 2 := by
  rw [tv_attains_trace_distance, noncommuting_distance]
example : TV (prob_dist (optimal_povm qubitZero_density rhoOne_density) qubitZero)
    (prob_dist (optimal_povm qubitZero_density rhoOne_density) rhoOne) = 1 := by
  rw [tv_attains_trace_distance, orthogonal_distance]
example : TV (prob_dist (optimal_povm qubitZero_density qubitZero_density) qubitZero)
    (prob_dist (optimal_povm qubitZero_density qubitZero_density) qubitZero) = 0 := tv_self _
example : TV (prob_dist pauliZ qubitZero) (prob_dist pauliZ rhoPlus) = 1 / 2 :=
  z_measurement_noncommuting_loss.1
example : TV (prob_dist pauliZ qubitZero) (prob_dist pauliZ rhoPlus) < trace_distance qubitZero rhoPlus :=
  z_measurement_noncommuting_loss.2
example : TV (prob_dist (effect_povm (QuantumHelstromStateDiscrimination.zero_effect 2)) qubitZero)
    (prob_dist (effect_povm (QuantumHelstromStateDiscrimination.zero_effect 2)) rhoOne) <
    trace_distance qubitZero rhoOne := strict_measurement_loss
example : TV (![1,0] : Fin 2 → ℝ) ![0,1] = 1 := by norm_num [TV, Fin.sum_univ_two]
example : TV (![1/2,1/2] : Fin 2 → ℝ) ![1,0] = 1/2 := by norm_num [TV, Fin.sum_univ_two]
example (p q : Fin 0 → ℝ) : TV p q = 0 := by simp [TV]
example (p : Fin 2 → ℝ) : TV p p = 0 := tv_self _
example (p q : Fin 2 → ℝ) : TV p q = 0 ↔ p = q := tv_eq_zero_iff _ _
example (p q r : Fin 3 → ℝ) : TV p q ≤ TV p r + TV r q := tv_triangle _ _ _
example (p q : Fin 2 → ℝ) : TV (apply_channel (identity_channel 2) p)
    (apply_channel (identity_channel 2) q) = TV p q := by rw [apply_identity, apply_identity]
example (p q : Fin 2 → ℝ) : TV (apply_channel bit_flip p) (apply_channel bit_flip q) = TV p q :=
  tv_permutation (Equiv.swap 0 1) _ _
example (p q : Fin 2 → ℝ) (hp : IsDistribution p) (hq : IsDistribution q) :
    TV (apply_channel (erasure_channel 2 point_mass point_mass_distribution) p)
      (apply_channel (erasure_channel 2 point_mass point_mass_distribution) q) = 0 :=
  tv_erasure hp hq _ _
example : TV (prob_dist (postprocess_povm (erasure_channel 2 point_mass point_mass_distribution)
    pauliZ) qubitZero) (prob_dist (postprocess_povm
      (erasure_channel 2 point_mass point_mass_distribution) pauliZ) rhoOne) = 0 :=
  measurement_tv_erasure qubitZero_density rhoOne_density _ _ _
example : TV (prob_dist (postprocess_povm bit_flip pauliZ) qubitZero)
    (prob_dist (postprocess_povm bit_flip pauliZ) rhoOne) = TV (prob_dist pauliZ qubitZero)
      (prob_dist pauliZ rhoOne) := measurement_tv_permutation (Equiv.swap 0 1) _ _ _
example (M : ClassicalChannel 2 3) (N : ClassicalChannel 3 1) (p q : Fin 2 → ℝ) :
    TV (apply_channel N (apply_channel M p)) (apply_channel N (apply_channel M q)) ≤ TV p q :=
  (tv_contractive_under_classical_channel N _ _).trans (tv_contractive_under_classical_channel M _ _)
example (M : ClassicalChannel 2 3) : TV (prob_dist (postprocess_povm M pauliZ) qubitZero)
    (prob_dist (postprocess_povm M pauliZ) rhoPlus) ≤ 1 / Real.sqrt 2 := by
  simpa only [noncommuting_distance] using tv_postprocess_le qubitZero_density rhoPlus_density pauliZ M
example : IsGreatest {x : ℝ | ∃ m, ∃ E : FinitePOVM 2 m,
    TV (prob_dist E qubitZero) (prob_dist E rhoPlus) = x} (trace_distance qubitZero rhoPlus) :=
  measurement_tv_isGreatest qubitZero_density rhoPlus_density
