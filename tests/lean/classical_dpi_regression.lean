import Verification.QuantumChannelClassicalDataProcessing

open QuantumPOVMNaimarkDilation QuantumPOVMInformationEntropy
open QuantumChannelClassicalDataProcessing
open scoped BigOperators

namespace ClassicalDPIRegression
noncomputable section

def p0 : Fin 2 → ℝ := ![1,0]
def p1 : Fin 2 → ℝ := ![0,1]

theorem p0_distribution : IsDistribution p0 := by
  constructor
  · intro i; fin_cases i <;> norm_num [p0]
  · norm_num [p0, Fin.sum_univ_two]
theorem p1_distribution : IsDistribution p1 := by
  constructor
  · intro i; fin_cases i <;> norm_num [p1]
  · norm_num [p1, Fin.sum_univ_two]

theorem p0_ac_fair : AbsContinuous p0 fair_bit := by
  intro i _; norm_num [fair_bit]
theorem p0_not_ac_p1 : ¬ AbsContinuous p0 p1 := by
  intro h
  have hh := h 0 (by norm_num [p0])
  norm_num [p1] at hh

def noisy : BistochasticChannel 2 := binary_symmetric (1/4) (by norm_num) (by norm_num)
def erase : ClassicalChannel 2 1 := erasure_channel 2 point_mass point_mass_distribution


example : QuantumChannelClassicalDataProcessingSuite := QuantumChannelClassicalDataProcessing.verification_suite
example (p : Fin 3 → ℝ) : apply_channel (identity_channel 3) p = p := apply_identity p
example (M : ClassicalChannel 2 3) : compose (identity_channel 3) M = M := compose_identity_left M
example (M : ClassicalChannel 2 3) : compose M (identity_channel 2) = M := compose_identity_right M
example (A : ClassicalChannel 2 3) (B : ClassicalChannel 3 4) (C : ClassicalChannel 4 2) :
    compose C (compose B A) = compose (compose C B) A := compose_associative C B A
example (A : ClassicalChannel 2 3) (B : ClassicalChannel 3 4) (p : Fin 2 → ℝ) :
    apply_channel (compose B A) p = apply_channel B (apply_channel A p) := apply_compose B A p
example : apply_channel noisy.toClassicalChannel p0 = ![3/4,1/4] := by
  funext i; fin_cases i <;> norm_num [apply_channel, noisy, binary_symmetric, p0, Fin.sum_univ_two]
example : IsDistribution (apply_channel noisy.toClassicalChannel p0) := apply_distribution _ p0_distribution
example : AbsContinuous (apply_channel noisy.toClassicalChannel p0)
    (apply_channel noisy.toClassicalChannel fair_bit) :=
  abs_continuous_preserved _ p0_distribution.1 fair_bit_distribution.1 p0_ac_fair
example : 0 ≤ kl_divergence p0 fair_bit :=
  kl_divergence_nonneg p0_distribution fair_bit_distribution p0_ac_fair
example : kl_divergence (apply_channel noisy.toClassicalChannel p0)
    (apply_channel noisy.toClassicalChannel fair_bit) ≤ kl_divergence p0 fair_bit :=
  kl_data_processing_inequality _ p0_distribution fair_bit_distribution p0_ac_fair
example : kl_divergence_bits (apply_channel noisy.toClassicalChannel p0)
    (apply_channel noisy.toClassicalChannel fair_bit) ≤ kl_divergence_bits p0 fair_bit :=
  kl_data_processing_bits _ p0_distribution fair_bit_distribution p0_ac_fair
example : kl_divergence (apply_channel (identity_channel 2) p0)
    (apply_channel (identity_channel 2) fair_bit) = kl_divergence p0 fair_bit := by
  rw [apply_identity, apply_identity]
example : shannon_entropy_bits (apply_channel (identity_channel 2) p0) = shannon_entropy_bits p0 := by
  rw [apply_identity]
example : kl_divergence (apply_channel (permutation_channel (Equiv.swap 0 1)).toClassicalChannel p0)
    (apply_channel (permutation_channel (Equiv.swap 0 1)).toClassicalChannel fair_bit) =
      kl_divergence p0 fair_bit := by rw [apply_permutation, apply_permutation, kl_permutation]
example : shannon_entropy_bits (apply_channel (permutation_channel (Equiv.swap 0 1)).toClassicalChannel p0) =
    shannon_entropy_bits p0 := by rw [apply_permutation, entropy_permutation]
example : apply_channel erase fair_bit = point_mass := apply_erasure fair_bit_distribution _ _
example : kl_divergence (apply_channel erase p0) (apply_channel erase fair_bit) = 0 :=
  erasure_kl_zero p0_distribution fair_bit_distribution _ _
-- Erasure may repair a support mismatch; the input singular KL is not assigned a finite semantics.
example : kl_divergence (apply_channel erase p0) (apply_channel erase p1) = 0 :=
  erasure_kl_zero p0_distribution p1_distribution _ _
example : checked_kl p0 p1 = none := checked_kl_singular p0_not_ac_p1
example : checked_kl p0 fair_bit = some (kl_divergence p0 fair_bit) :=
  checked_kl_valid p0_distribution fair_bit_distribution p0_ac_fair
example : kl_term 0 0 = 0 := kl_term_zero 0
example : kl_term 0 1 = 0 := kl_term_zero 1
example : kl_divergence p0 p0 = 0 := kl_self p0
example : kl_term (∑ _ : Fin 2, (0:ℝ)) (∑ _ : Fin 2, (0:ℝ)) ≤
    ∑ _ : Fin 2, kl_term 0 0 := by simp
example : kl_term (∑ _ : Fin 0, (0:ℝ)) (∑ _ : Fin 0, (0:ℝ)) ≤
    ∑ _ : Fin 0, kl_term 0 0 := by simp
example : shannon_entropy_bits p0 < shannon_entropy_bits (apply_channel noisy.toClassicalChannel p0) :=
  binary_symmetric_entropy_strict p0_distribution (by norm_num [p0]) (by norm_num) (by norm_num)
example : shannon_entropy_bits fair_bit ≤ shannon_entropy_bits (apply_channel noisy.toClassicalChannel fair_bit) :=
  bistochastic_entropy_nondecreasing noisy fair_bit_distribution
example : apply_channel noisy.toClassicalChannel fair_bit = fair_bit := by
  funext i; fin_cases i <;> norm_num [noisy, apply_channel, binary_symmetric, fair_bit, Fin.sum_univ_two]
example : shannon_entropy_bits fair_bit = 1 := fair_bit_entropy
example : shannon_entropy_bits (apply_channel erase fair_bit) = 0 :=
  coarse_graining_entropy_decrease_counterexample.2
example : shannon_entropy_bits (apply_channel erase fair_bit) < shannon_entropy_bits fair_bit := by
  change shannon_entropy_bits (apply_channel
    (erasure_channel 2 point_mass point_mass_distribution) fair_bit) < shannon_entropy_bits fair_bit
  rw [coarse_graining_entropy_decrease_counterexample.2, fair_bit_entropy]; norm_num
example : apply_channel (binary_symmetric 0 (by norm_num) (by norm_num)).toClassicalChannel p0 = p0 := by
  funext i; fin_cases i <;> norm_num [apply_channel, binary_symmetric, p0, Fin.sum_univ_two]
example : apply_channel (binary_symmetric (1/2) (by norm_num) (by norm_num)).toClassicalChannel p0 = fair_bit := by
  funext i; fin_cases i <;> norm_num [apply_channel, binary_symmetric, p0, fair_bit, Fin.sum_univ_two]
example : postprocess_povm (identity_channel 2) pauliZ = pauliZ := postprocess_identity pauliZ
example : (postprocess_povm (permutation_channel (Equiv.swap 0 1)).toClassicalChannel pauliZ).effects 0 =
    pauliZ.effects 1 := by rw [postprocess_permutation, Equiv.swap_apply_left]
example : ((postprocess_povm noisy.toClassicalChannel pauliZ).effects 0).IsHermitian :=
  postprocess_hermitian _ _ _
example : ∑ i, (postprocess_povm noisy.toClassicalChannel pauliZ).effects i = 1 :=
  (postprocess_povm noisy.toClassicalChannel pauliZ).completeness
example : (postprocess_povm (erasure_channel 2 p1 p1_distribution) pauliZ).effects 0 = 0 := by
  apply postprocess_zero_effect
  intro j; left; rfl
example : prob_dist (postprocess_povm noisy.toClassicalChannel pauliZ) qubitZero =
    apply_channel noisy.toClassicalChannel (prob_dist pauliZ qubitZero) := postprocess_prob _ _ _
example : postprocess_povm (compose erase noisy.toClassicalChannel) pauliZ =
    postprocess_povm erase (postprocess_povm noisy.toClassicalChannel pauliZ) := postprocess_compose _ _ _
example (ρ σ : Q 2) (hρ : QuantumNoBroadcastingMixed.IsDensityMatrix ρ)
    (hσ : QuantumNoBroadcastingMixed.IsDensityMatrix σ)
    (hac : AbsContinuous (prob_dist pauliZ ρ) (prob_dist pauliZ σ)) :
    kl_divergence (prob_dist (postprocess_povm noisy.toClassicalChannel pauliZ) ρ)
      (prob_dist (postprocess_povm noisy.toClassicalChannel pauliZ) σ) ≤
        kl_divergence (prob_dist pauliZ ρ) (prob_dist pauliZ σ) :=
  povm_kl_data_processing _ _ _ _ hρ hσ hac
example (ρ σ : Q 2) (hρ : QuantumNoBroadcastingMixed.IsDensityMatrix ρ)
    (hσ : QuantumNoBroadcastingMixed.IsDensityMatrix σ)
    (hac : AbsContinuous (prob_dist pauliZ ρ) (prob_dist pauliZ σ)) :
    AbsContinuous (prob_dist (postprocess_povm noisy.toClassicalChannel pauliZ) ρ)
      (prob_dist (postprocess_povm noisy.toClassicalChannel pauliZ) σ) :=
  povm_abs_continuous_preserved _ _ _ _ hρ hσ hac

end
end ClassicalDPIRegression
