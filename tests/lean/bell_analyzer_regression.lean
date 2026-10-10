import Verification.PhotonicsBellStateAnalyzer
open PhotonicsBellStateAnalyzer
open scoped BigOperators

example : PhotonicsBellStateAnalyzerSuite := photonics_bell_state_analyzer_master_suite
example : U₂.conjTranspose * U₂ = 1 := two_photon_unitary
example : J.conjTranspose * J = 1 := encoding_isometry

-- The effects are derived from the optical transfer for arbitrary coherent inputs.
example (ψ : CompBasis → ℂ) : quadratic (effect .psiMinus) ψ =
    ∑ k, if classify k = .psiMinus then (Complex.normSq (transfer.mulVec ψ k) : ℂ) else 0 :=
  detector_born_rule _ ψ
example (ψ : CompBasis → ℂ) : 0 ≤ (quadratic (effect .inconclusive) ψ).re :=
  effect_positive _ ψ

-- Distinct physical detector channels: same port/different polarization versus different ports.
example : classify 1 = .psiPlus ∧ classify 3 = .psiMinus ∧ classify 0 = .inconclusive := by decide
example : outcomeProbability .psiPlus 1 = 1/2 ∧ outcomeProbability .psiMinus 3 = 1/2 := by
  constructor <;> rw [probabilities_exact] <;> rfl
example (k : FockBasis) : outcomeProbability .phiPlus k = outcomeProbability .phiMinus k :=
  congrFun phi_pm_identical_distributions k
example (rule : FockBasis → Bool) :
    ¬ ((∀ k, 0 < outcomeProbability .phiPlus k → rule k = true) ∧
       (∀ k, 0 < outcomeProbability .phiMinus k → rule k = false)) :=
  phi_indistinguishability_classical rule

-- Fifty percent is specific to the uniform four-state prior.
def psiPrior : Prior where
  weight := fun b => if b = .psiMinus then 1 else 0
  nonnegative := by intro b; split <;> norm_num
  total := by rw [sum_bell]; simp +decide
example : successProbability uniformPrior = 1/2 := success_probability_uniform
example : successProbability psiPrior = 1 := by
  apply success_probability_psi_only <;> simp +decide [psiPrior]
example : (∑ k, star (output .psiMinus k) * output .psiPlus k) = 0 := psi_outputs_orthogonal
example (b : BellState) : ∑ k, outcomeProbability b k = 1 := output_normalized b
