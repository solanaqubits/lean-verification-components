import Verification.QuantumBB84ProtocolQBER
open QuantumBB84ProtocolQBER
open scoped BigOperators

example : QuantumBB84ProtocolQBERSuite := quantum_bb84_protocol_qber_master_suite
example (b : BB84Basis) (x : BB84Bit) : (ket b x).conjTranspose * ket b x = 1 :=
  ket_normalized b x
example (x y : BB84Bit) : (P 0 x * P 1 y).trace = 1/2 := mutually_unbiased x y
example (ρ : QMatrix) : (E_IR ρ).trace = ρ.trace := intercept_channel_trace ρ
example (a : BB84Bit) (A B E : BB84Basis) :
    (∑ e, ∑ y, attackWeight (a,A,B,E,e,y)) = 1/16 := attack_prior_uniform a A B E
example : attackLaw.probability Sifted = 1/2 := sifting_probability_half
example : attackLaw.probability (fun ω => Error ω ∧ Sifted ω) = 1/8 :=
  intercept_resend_joint_error_sifting
example : qber attackLaw = 1/4 := intercept_resend_error_exact
example (f : ℝ) (hf : 0 ≤ f) (hf1 : f ≤ 1) : qber (partialLaw f hf hf1) = f/4 :=
  partial_intercept_qber f hf hf1
example (f : ℝ) (hf : 0 ≤ f) (hf1 : f ≤ 1) :
    ENNReal.ofReal ((partialLaw f hf hf1).probability Error) =
      ∑ ω, if Error ω then (partialLaw f hf hf1).toPMF ω else 0 :=
  FiniteLaw.probability_pmf _ _
example (m : ℕ) : (sampleLaw m).probability (fun ω => ∃ i, Error (ω i)) =
    1-(3/4:ℝ)^m := sample_detection_probability m
example (m : ℕ) : 0 < (sampleLaw m).probability (fun ω => ∀ i, ¬ Error (ω i)) :=
  evasion_probability_positive m
example : qber (partialLaw 0 (by norm_num) (by norm_num)) = 0 := reg_no_intercept
example : qber (partialLaw 1 (by norm_num) (by norm_num)) = 1/4 := reg_full_intercept
example : (sampleLaw 0).probability (fun ω => ∃ i, Error (ω i)) = 0 := reg_empty_sample
example : (sampleLaw 2).probability (fun ω => ∃ i, Error (ω i)) = 7/16 := reg_two_sample
example : ((1/2 : ℂ) • E_IR (P 0 0)).trace = 1/2 ∧ (P 0 0).trace = 1 :=
  counterexample_quarter_channel
