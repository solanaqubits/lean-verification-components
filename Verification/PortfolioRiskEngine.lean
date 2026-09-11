import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option linter.style.header false

noncomputable section

namespace PortfolioRiskEngine

/-- Nonnegative, normalized weights of two assets. -/
structure Portfolio2 where
  w1 : ℝ
  w2 : ℝ
  hw1 : 0 ≤ w1
  hw2 : 0 ≤ w2
  h_sum : w1 + w2 = 1

/-- Prescribed volatility and correlation parameters. -/
structure AssetRisk2 where
  s1 : ℝ
  s2 : ℝ
  rho : ℝ
  hs1 : 0 ≤ s1
  hs2 : 0 ≤ s2
  hrho_ge : -1 ≤ rho
  hrho_le : rho ≤ 1

def portfolioVariance (p : Portfolio2) (r : AssetRisk2) : ℝ :=
  p.w1 ^ 2 * r.s1 ^ 2 + 2 * p.w1 * p.w2 * r.rho * r.s1 * r.s2 + p.w2 ^ 2 * r.s2 ^ 2

def weightedLinearRisk (p : Portfolio2) (r : AssetRisk2) : ℝ :=
  p.w1 * r.s1 + p.w2 * r.s2

theorem variance_decomp (p : Portfolio2) (r : AssetRisk2) :
    weightedLinearRisk p r ^ 2 - portfolioVariance p r =
      2 * p.w1 * p.w2 * r.s1 * r.s2 * (1 - r.rho) := by
  dsimp [weightedLinearRisk, portfolioVariance]
  ring

theorem portfolio_variance_nonneg (p : Portfolio2) (r : AssetRisk2) :
    0 ≤ portfolioVariance p r := by
  have he : portfolioVariance p r =
      (p.w1 * r.s1 - p.w2 * r.s2) ^ 2 +
        2 * p.w1 * p.w2 * r.s1 * r.s2 * (1 + r.rho) := by
    dsimp [portfolioVariance]
    ring
  rw [he]
  have hr : 0 ≤ 1 + r.rho := by linarith [r.hrho_ge]
  have hp := mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      p.hw1) p.hw2) r.hs1) r.hs2) hr
  exact add_nonneg (sq_nonneg _) hp

/-- Upper bound by the square of the weighted volatility sum. -/
theorem diversification_effect_sq (p : Portfolio2) (r : AssetRisk2) :
    portfolioVariance p r ≤ weightedLinearRisk p r ^ 2 := by
  have he := variance_decomp p r
  have hr : 0 ≤ 1 - r.rho := sub_nonneg.mpr r.hrho_le
  have hp := mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      p.hw1) p.hw2) r.hs1) r.hs2) hr
  linarith

theorem strict_diversification_effect (p : Portfolio2) (r : AssetRisk2)
    (hw1 : 0 < p.w1) (hw2 : 0 < p.w2) (hs1 : 0 < r.s1) (hs2 : 0 < r.s2)
    (hrho : r.rho < 1) :
    portfolioVariance p r < weightedLinearRisk p r ^ 2 := by
  have he := variance_decomp p r
  have hr : 0 < 1 - r.rho := sub_pos.mpr hrho
  have hp : 0 < 2 * p.w1 * p.w2 * r.s1 * r.s2 * (1 - r.rho) := by positivity
  linarith

theorem perfect_hedging_variance (p : Portfolio2) (r : AssetRisk2) (h_rho : r.rho = -1) :
    portfolioVariance p r = (p.w1 * r.s1 - p.w2 * r.s2) ^ 2 := by
  dsimp [portfolioVariance]
  rw [h_rho]
  ring

/-- Negative unit correlation yields zero variance exactly when exposures match. -/
theorem perfect_hedging_zero_iff (p : Portfolio2) (r : AssetRisk2) (h_rho : r.rho = -1) :
    portfolioVariance p r = 0 ↔ p.w1 * r.s1 = p.w2 * r.s2 := by
  rw [perfect_hedging_variance p r h_rho, sq_eq_zero_iff, sub_eq_zero]

/-- Scalar guarantees under the explicitly supplied portfolio and risk constraints. -/
structure PortfolioRiskFormalSuite : Prop where
  h_var_nonneg : ∀ p r, 0 ≤ portfolioVariance p r
  h_diversif_le : ∀ p r, portfolioVariance p r ≤ weightedLinearRisk p r ^ 2
  h_strict_div : ∀ p r,
    0 < p.w1 → 0 < p.w2 → 0 < r.s1 → 0 < r.s2 → r.rho < 1 →
    portfolioVariance p r < weightedLinearRisk p r ^ 2
  h_perfect_hedge : ∀ p r,
    r.rho = -1 → portfolioVariance p r = (p.w1 * r.s1 - p.w2 * r.s2) ^ 2

theorem portfolio_risk_master_verification_suite : PortfolioRiskFormalSuite := {
  h_var_nonneg := portfolio_variance_nonneg
  h_diversif_le := diversification_effect_sq
  h_strict_div := strict_diversification_effect
  h_perfect_hedge := perfect_hedging_variance
}

#print axioms portfolio_risk_master_verification_suite

end PortfolioRiskEngine
