import Verification.QuantumShorContinuedFractions
import Mathlib.Tactic.IntervalCases

open QuantumShorContinuedFractions QuantumShorOrderFindingCore QuantumPhaseEstimationGeneral

namespace ShorContinuedFractionsRegression

-- The two executable procedures agree with concrete Euclidean division.
example : partialQuotients (85 / 256) = [0, 3, 85] := by decide +kernel
example : convergents (85 / 256) = [0, 1 / 3, 85 / 256] := by decide +kernel
example : candidates 85 256 7 = [0, 1 / 3] := by decide +kernel
example : candidates 64 256 15 = [0, 1 / 4] := by decide +kernel
example : candidates 128 256 15 = [0, 1 / 2] := by decide +kernel
example : (reduced 2 4).den = 2 ∧ (reduced 2 4).den ≠ 4 := by decide +kernel
example : candidates 0 256 15 = [0] ∧ (reduced 0 4).den = 1 := by decide +kernel
example : convergents (0 : ℚ) = [0] ∧ convergents 5 = [5] := by decide +kernel
example : partialQuotients (-3 / 2) = [-2, 2] := by decide +kernel
-- Denominator bound is strict, and all filtered entries need not divide the true order.
example : candidates 85 256 3 = [0] := by decide +kernel
example : (1 / 2 : ℚ) ∈ candidates 102 256 11 ∧ ¬ 2 ∣ (5 : ℕ) := by decide +kernel
example : |(102 : ℝ) / 256 - 2 / 5| ≤ 1 / (2 * 256) := by norm_num
example : reduced 2 5 ∈ candidates 102 256 11 :=
  convergent_recovery_soundness (by decide) (by decide) (by decide) (by norm_num)
-- Reduced divisors can fail the modular check. Passing it alone need not mean minimal order.
example : passesModularCheck 2 15 2 = false ∧ passesModularCheck 2 15 4 = true := by decide
example : passesModularCheck 4 15 4 = true ∧ (4 : ZMod 15) ^ 2 = 1 := by decide
example : checkedCandidates 2 64 256 15 = [4] := by decide +kernel
example : checkedCandidates 2 128 256 15 = [] := by decide +kernel
example : checkedCandidates 1 0 16 3 = [1] := by decide +kernel
-- The boundary in Legendre cannot generally be weakened to non-strict inequality.
example : |(1/2 : ℝ) - 1| = 1/2 := by norm_num
example : (1 : ℚ) ∉ convergents (1/2) := by decide +kernel
example : ¬ (15^2 ≤ (2^0 : ℕ)) := by decide

example (x z : ℚ) : z ∈ convergents x ↔ ∃ k, Real.convergent (x : ℝ) k = z :=
  mem_convergents_iff x z
example (x : ℚ) : (partialQuotients x).length ≤ 2 * Nat.log 2 x.den + 1 :=
  euclidean_stages_log_bound x
example {N Q r s y : ℕ} (hr : 0 < r) (hs : s < r) (hrN : r < N)
    (hQ : N^2 ≤ Q) (hy : y < Q)
    (hn : ∃ z : ℤ, |(s : ℝ)/r - (y : ℝ)/Q - z| ≤ 1/(2*(Q : ℝ))) :
    |(y : ℝ)/Q - (s : ℝ)/r| ≤ 1/(2*(Q : ℝ)) :=
  nearest_has_no_wrap hr hs hrN hQ hy hn

def seven : Parameters := ⟨7, by decide, 2, by decide, 3, by decide⟩
theorem seven_period : seven.period = 3 := by
  change orderOf (2 : ZMod 7) = 3
  apply (orderOf_eq_iff (by decide : 0 < 3)).2
  constructor
  · decide
  · intro k hk hp; interval_cases k <;> decide

def oneOfThree : Fin seven.period := ⟨1, by rw [seven_period]; decide⟩
example : seven.period ∈ checkedCandidates seven.base 85 (2^8) seven.modulus := by
  apply shor_coprime_checked_candidate seven 8 (by decide) oneOfThree 85
  · exact ⟨0, by norm_num [oneOfThree, seven_period]⟩
  · simp [oneOfThree, seven_period]
example : reduced oneOfThree.val seven.period ∈ candidates 85 (2^8) seven.modulus ∧
    4 / ((seven.period : ℝ) * Real.pi^2) ≤
      normSquared (runQPE seven.modularOperator 8 seven.input 85) :=
  shor_recovery_peak seven 8 (by decide) oneOfThree 85
    ⟨0, by norm_num [oneOfThree, seven_period]⟩
-- A wrapped but coarse measurement exists outside the resolution contract.
example : Nearest 2 (9/10) 0 := ⟨1, by norm_num⟩
example : ¬ (|(0 : ℝ)/2 - 9/10| ≤ 1/(2*2)) := by norm_num

end ShorContinuedFractionsRegression
