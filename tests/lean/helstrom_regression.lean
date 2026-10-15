import Verification.QuantumHelstromStateDiscrimination

open scoped BigOperators ComplexOrder MatrixOrder
open QuantumPOVMNaimarkDilation QuantumPOVMInformationEntropy
open QuantumChannelClassicalDataProcessing QuantumHelstromStateDiscrimination
open QuantumHelstromStateDiscrimination.Examples

example : QuantumHelstromStateDiscriminationSuite := verification_suite
example : Density rhoOne := rhoOne_density
example : Density rhoPlus := rhoPlus_density
example : qubitZero * rhoPlus ≠ rhoPlus * qubitZero := noncommuting_states
example : trace_norm (helstrom_difference fair qubitZero rhoPlus) = 1 / Real.sqrt 2 := noncommuting_trace_norm
example : optimal_success fair qubitZero rhoPlus = (1+1/Real.sqrt 2)/2 := noncommuting_optimum
example : helstrom_succ_prob fair qubitZero rhoPlus
    (helstrom_effect fair qubitZero_density rhoPlus_density).matrix = (1+1/Real.sqrt 2)/2 := by
  rw [helstrom_bound_achievable _ qubitZero_density rhoPlus_density, noncommuting_optimum]
example : (helstrom_effect fair qubitZero_density rhoPlus_density).matrix *
    (helstrom_effect fair qubitZero_density rhoPlus_density).matrix =
    (helstrom_effect fair qubitZero_density rhoPlus_density).matrix := helstrom_effect_projective _ _ _
example : (effect_povm (helstrom_effect fair qubitZero_density rhoPlus_density)).effects 0 =
    (helstrom_effect fair qubitZero_density rhoPlus_density).matrix := rfl
example (p : Priors) : optimal_success p qubitZero rhoOne = 1 := orthogonal_optimum p
example (p : Priors) : trace_norm (helstrom_difference p qubitZero rhoOne) = 1 := orthogonal_trace_norm p
example (p : Priors) : optimal_success p qubitZero qubitZero = max p.p₀ p.p₁ := identical_states_optimum _ qubitZero_density
example : optimal_success fair qubitMixed qubitMixed = 1/2 := by
  rw [identical_states_optimum _ qubitMixed_density]
  norm_num [fair]
example : (zero_effect 2).matrix ≠ (one_effect 2).matrix := identical_fair_nonunique.1
example : helstrom_succ_prob fair qubitZero qubitZero (zero_effect 2).matrix =
    optimal_success fair qubitZero qubitZero := identical_fair_nonunique.2.1
example : helstrom_succ_prob fair qubitZero qubitZero (one_effect 2).matrix =
    optimal_success fair qubitZero qubitZero := identical_fair_nonunique.2.2

private def onlyOne : Priors := ⟨0,1,by norm_num,by norm_num,by norm_num⟩
private def onlyZero : Priors := ⟨1,0,by norm_num,by norm_num,by norm_num⟩
example : optimal_success onlyOne qubitZero rhoPlus = 1 :=
  zero_prior_optimum _ qubitZero_density rhoPlus_density (Or.inl rfl)
example : optimal_success onlyZero qubitZero rhoPlus = 1 :=
  zero_prior_optimum _ qubitZero_density rhoPlus_density (Or.inr rfl)
example (E : Effect 2) : helstrom_succ_prob fair qubitZero rhoPlus E.matrix ≤ (1+1/Real.sqrt 2)/2 := by
  simpa only [noncommuting_optimum] using helstrom_upper_bound fair qubitZero_density rhoPlus_density E
example : IsGreatest {s : ℝ | ∃ E : Effect 2, helstrom_succ_prob fair qubitZero rhoPlus E.matrix = s}
    (optimal_success fair qubitZero rhoPlus) := helstrom_isGreatest _ qubitZero_density rhoPlus_density
example (z : Fin 2 → Bool) : helstrom_succ_prob fair qubitZero qubitZero
    (spectral_effect (difference_hermitian fair qubitZero_density qubitZero_density)
      (zero_flexible_selector (difference_hermitian fair qubitZero_density qubitZero_density) z)).matrix =
    optimal_success fair qubitZero qubitZero := zero_eigenvalue_choice_irrelevant fair qubitZero_density qubitZero_density z

example : bayes_rule (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1) 0 = 1 := by norm_num [bayes_rule]
example : guessing (![1/2,0] : Fin 2 → ℝ) ![0,1/2] = 1 := by norm_num [guessing, Fin.sum_univ_two]
example : decision_success (![1/2,0] : Fin 2 → ℝ) ![0,1/2] ![1/2,1/2] = 1/2 := by
  norm_num [decision_success, Fin.sum_univ_two]
example (D : Fin 2 → ℝ) (hD : ∀ j, 0 ≤ D j ∧ D j ≤ 1) :
    decision_success ![1/2,0] ![0,1/2] D ≤ 1 := by
  convert bayes_decision_rule_optimal (![1/2,0] : Fin 2 → ℝ) ![0,1/2] D hD using 1
  norm_num [guessing, Fin.sum_univ_two]
example : guessing_prob fair qubitZero rhoOne pauliZ = 1 := by
  rw [guessing_prob, z_orthogonal_distributions.1, z_orthogonal_distributions.2]
  norm_num [guessing, fair, Fin.sum_univ_two]
example : guessing_prob fair qubitZero rhoPlus pauliZ ≤ (1+1/Real.sqrt 2)/2 := by
  simpa only [noncommuting_optimum] using guessing_prob_le_helstrom fair qubitZero_density rhoPlus_density pauliZ
example : guessing_prob fair qubitZero rhoOne (postprocess_povm bit_flip pauliZ) =
    guessing_prob fair qubitZero rhoOne pauliZ := guessing_prob_permutation _ _ _ _ _
example : guessing_prob fair qubitZero rhoOne
    (postprocess_povm (erasure_channel 2 point_mass point_mass_distribution) pauliZ) = 1/2 := by
  rw [guessing_prob_erasure _ qubitZero_density rhoOne_density]
  norm_num [fair]
example : decision_success (fun j => fair.p₀ * prob_dist pauliZ qubitZero j)
    (fun j => fair.p₁ * prob_dist pauliZ rhoOne j) ![0,1] <
    decision_success (fun j => fair.p₀ * prob_dist (postprocess_povm bit_flip pauliZ) qubitZero j)
    (fun j => fair.p₁ * prob_dist (postprocess_povm bit_flip pauliZ) rhoOne j) ![0,1] := by
  rw [suboptimal_rule_can_improve_counterexample.1, suboptimal_rule_can_improve_counterexample.2]
  norm_num
example (M : ClassicalChannel 2 1) : guessing_prob fair qubitZero rhoPlus (postprocess_povm M pauliX) ≤
    guessing_prob fair qubitZero rhoPlus pauliX := guessing_prob_postprocessing_le _ _ _ _ _
example (M : ClassicalChannel 2 3) (N : ClassicalChannel 3 1) :
    guessing_prob fair qubitZero rhoPlus (postprocess_povm (compose N M) pauliX) ≤
    guessing_prob fair qubitZero rhoPlus pauliX := guessing_prob_postprocessing_le _ _ _ _ _
example : trace_norm (0 : Q 2) = 0 := by simp [trace_norm]
example : guessing (fun _ : Fin 0 => (0:ℝ)) (fun _ => 0) = 0 := by simp [guessing]
example (p : Priors) : max p.p₀ p.p₁ ≤ optimal_success p qubitMixed rhoPlus :=
  prior_lower_bound p qubitMixed_density rhoPlus_density
example (p : Priors) : optimal_success p qubitMixed rhoPlus ≤ 1 :=
  optimal_success_le_one p qubitMixed_density rhoPlus_density
