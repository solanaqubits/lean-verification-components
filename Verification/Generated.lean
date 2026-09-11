import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

set_option linter.style.header false

open Real

noncomputable section

namespace CollatzDrift

/-- A refined contraction factor used for the baseline verification. -/
def gamma_factor_test (s : ℝ) : ℝ :=
  (3 ^ s) / (2 ^ (1 + s) - 1)

private lemma cubeRoot_upper :
    (16 / 5 : ℝ) ^ (1 / 3 : ℝ) ≤ (14737 / 10000 : ℝ) := by
  have hx : 0 ≤ (16 / 5 : ℝ) := by norm_num
  have hr : 0 ≤ (16 / 5 : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg hx _
  have hq : 0 ≤ (14737 / 10000 : ℝ) := by norm_num
  apply (pow_le_pow_iff_left₀ hr hq (by norm_num : (3 : ℕ) ≠ 0)).mp
  have hc : ((16 / 5 : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = 16 / 5 := by
    convert Real.rpow_inv_natCast_pow hx (by norm_num : (3 : ℕ) ≠ 0) using 1
    norm_num
  rw [hc]
  norm_num

private lemma cubeRoot_two_lower :
    (12599 / 10000 : ℝ) ≤ (2 : ℝ) ^ (1 / 3 : ℝ) := by
  have hq : 0 ≤ (12599 / 10000 : ℝ) := by norm_num
  have hx : 0 ≤ (2 : ℝ) := by norm_num
  have hr : 0 ≤ (2 : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg hx _
  apply (pow_le_pow_iff_left₀ hq hr (by norm_num : (3 : ℕ) ≠ 0)).mp
  have hc : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = 2 := by
    convert Real.rpow_inv_natCast_pow hx (by norm_num : (3 : ℕ) ≠ 0) using 1
    norm_num
  rw [hc]
  norm_num

/-- A numerical contraction bound with witnesses `s = 1/3`, `γ = 0.94566`, and `N₀ = 5`. -/
theorem foster_lyapunov_contraction_bound :
    ∃ (s : ℝ) (γ : ℝ) (N₀ : ℕ),
      0 < s ∧ s < 1 ∧
      γ < 1 ∧
      N₀ = 5 ∧
      (∀ n : ℕ, n ≥ N₀ → gamma_factor_test s * (1 + 1 / (3 * (n : ℝ))) ^ s ≤ (1 + γ) / 2) := by
  use 1/3, 0.94566, 5
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · rfl
  · intro n hn
    -- For n ≥ 5, reduce the numerical estimate to exact real inequalities.
    have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
    have hden : (15 : ℝ) ≤ 3 * n := by nlinarith
    have hrecip : 1 / (3 * (n : ℝ)) ≤ (1 / 15 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hden
    have hbase_nonneg : 0 ≤ (1 + 1 / (3 * (n : ℝ)) : ℝ) := by positivity
    have hbase : (3 : ℝ) * (1 + 1 / (3 * (n : ℝ))) ≤ 16 / 5 := by
      nlinarith
    have hnum :
        ((3 : ℝ) * (1 + 1 / (3 * (n : ℝ)))) ^ (1 / 3 : ℝ) ≤
          14737 / 10000 := by
      calc
        _ ≤ (16 / 5 : ℝ) ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hbase (by norm_num)
        _ ≤ _ := cubeRoot_upper
    have htwo :
        (2 : ℝ) ^ (1 + (1 / 3 : ℝ)) =
          2 * (2 : ℝ) ^ (1 / 3 : ℝ) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    have hdenLower :
        (2 * (12599 / 10000 : ℝ) - 1) ≤
          (2 : ℝ) ^ (1 + (1 / 3 : ℝ)) - 1 := by
      rw [htwo]
      nlinarith [cubeRoot_two_lower]
    calc
      gamma_factor_test (1 / 3 : ℝ) *
          (1 + 1 / (3 * (n : ℝ))) ^ (1 / 3 : ℝ) =
          (((3 : ℝ) * (1 + 1 / (3 * (n : ℝ)))) ^ (1 / 3 : ℝ)) /
            ((2 : ℝ) ^ (1 + (1 / 3 : ℝ)) - 1) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hbase_nonneg]
        simp only [gamma_factor_test]
        ring
      _ ≤ (14737 / 10000 : ℝ) / (2 * (12599 / 10000 : ℝ) - 1) := by
        exact div_le_div₀ (by norm_num) hnum (by norm_num) hdenLower
      _ ≤ (1 + (0.94566 : ℝ)) / 2 := by norm_num

#print axioms foster_lyapunov_contraction_bound

end CollatzDrift
