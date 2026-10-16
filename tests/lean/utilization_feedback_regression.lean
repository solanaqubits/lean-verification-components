import Verification.DeFiLendingUtilizationFeedbackStability

open DeFiLendingUtilizationFeedbackStability DeFiKinkedInterestRateUtilization Filter
open scoped Topology
namespace UtilizationFeedbackRegression

def kinkModel : KinkRateParams :=
  { linearModel with
    slope₂ := 3
    slope₂_nonneg := by norm_num }

def decreasingSlopes : KinkRateParams :=
  { linearModel with
    slope₁ := 3
    slope₁_nonneg := by norm_num }

def fixed : FixedParams where
  scale := 10
  base := 0
  slope₁ := 3
  slope₂ := 7
  kink := 5
  reserveFactor := 0
  scale_pos := by decide
  kink_pos := by decide
  kink_lt_scale := by decide
  reserve_le_scale := by decide

example : project_unit (-3) = 0 := by norm_num [project_unit]
example : project_unit 4 = 1 := by norm_num [project_unit]
example : project_unit (2/5) = 2/5 := by norm_num [project_unit]
example : |project_unit (-1) - project_unit 2| < |(-1 : ℝ)-2| := by norm_num [project_unit]
example : kappa kinkModel (1/4) = 3/4 := by norm_num [kappa, kinkModel, linearModel]
example : kappa decreasingSlopes (1/4) = 3/4 := by
  norm_num [kappa, decreasingSlopes, linearModel]
example : kappa kinkModel (1/2) < 1 := by norm_num [kappa, kinkModel, linearModel]
example : kappa linearModel 2 = 1 := by norm_num [kappa, linearModel]
example : kappa linearModel 3 = 2 := by norm_num [kappa, linearModel]
example : kappa flatModel (1/2) = 1 := by norm_num [kappa, flatModel]
example : feedback_step kinkModel (1/4) (1/2) (1/4) 0 = 5/16 := by
  norm_num [feedback_step, raw_step, rate, kinkModel, linearModel, project_unit]
example : feedback_step kinkModel (1/4) (1/2) (3/4) 0 = 9/16 := by
  norm_num [feedback_step, raw_step, rate, kinkModel, linearModel, project_unit]
example : |feedback_step kinkModel (1/4) (1/2) (1/4) 0 -
    feedback_step kinkModel (1/4) (1/2) (3/4) 0| ≤ (3/4 : ℝ)*|1/4-3/4| := by
  convert feedback_lipschitz kinkModel (1/4) (1/2) (1/4) (3/4) 0 using 1
  norm_num [kappa, kinkModel, linearModel]
example : IsEquilibrium kinkModel (1/4) (1/2) (1/2) := by
  apply target_rate_equilibrium <;> norm_num [rate, kinkModel, linearModel]
-- Projection can create boundary equilibria without r(u*) = d.
example : IsEquilibrium linearModel (1/2) (-1) 0 := by
  norm_num [IsEquilibrium, feedback_step, raw_step, linear_rate, project_unit]
example : IsEquilibrium linearModel (1/2) 2 1 := by
  norm_num [IsEquilibrium, feedback_step, raw_step, linear_rate, project_unit]
example (t : ℕ) : 0 ≤ trajectory kinkModel 10 (1/2) 0 (fun _ => 100) t ∧
    trajectory kinkModel 10 (1/2) 0 (fun _ => 100) t ≤ 1 :=
  trajectory_invariant _ _ _ _ _ (by norm_num) (by norm_num) t
example (u0 : ℝ) : Tendsto (trajectory linearModel (1/2) (1/2) u0 (fun _ => 0))
    atTop (𝓝 (1/2)) := stable_convergence u0
example (t : ℕ) : |trajectory linearModel (1/2) (1/2) 0 (fun _ => 0) t - 1/2| ≤
    (1/2 : ℝ)^t * (1/2) := by
  simpa only [stable_kappa, zero_sub, abs_neg,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)] using noiseless_error linearModel (1/2) (1/2) 0 (1/2)
    (by rw [stable_kappa]; norm_num) (linear_equilibrium _) t
example (t : ℕ) : |trajectory linearModel (1/2) (1/2) (3/4) (fun _ => 1/8) t - 1/2| =
    (1/4 : ℝ) := by rw [persistent_noise_equilibrium]; norm_num
example (t : ℕ) : |trajectory linearModel (1/2) (1/2) 0 (fun _ => 1/8) t - 1/2| ≤
    (1/2 : ℝ)^t * (1/2) + (1/8)*(1-(1/2)^t)/(1-1/2) := by
  simpa only [stable_kappa, zero_sub, abs_neg,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)] using bounded_perturbation_stability linearModel (1/2) (1/2)
    0 (1/2) (1/8) (fun _ => 1/8) (by rw [stable_kappa]; norm_num)
    (linear_equilibrium _) (by intro t; norm_num) t
example (t : ℕ) : trajectory linearModel 3 (1/2) 0 (fun _ => 0) (2*t) = 0 ∧
    trajectory linearModel 3 (1/2) 0 (fun _ => 0) (2*t+1) = 1 := large_step_cycle t
example : ¬ Tendsto (trajectory linearModel 3 (1/2) 0 (fun _ => 0)) atTop (𝓝 (1/2)) :=
  large_step_not_convergent
example (t : ℕ) : trajectory flatModel 7 0 (1/4) (fun _ => 0) t = 1/4 :=
  flat_stationary _ _ (by norm_num) (by norm_num) t
example : IsEquilibrium flatModel 1 0 0 ∧ IsEquilibrium flatModel 1 0 1 := by
  norm_num [IsEquilibrium, feedback_step, raw_step, rate, flatModel, linearModel, project_unit]
example : borrow_rate_int fixed 3 = 1 := by decide +kernel
example : borrow_rate fixed.lift (3/10) = 9/100 := by decide +kernel
example : fixed_rate_error fixed 3 = 1/100 := by
  norm_num [fixed_rate_error, fixed, borrow_rate_int, borrow_numerator, ceil_div,
    borrow_rate, FixedParams.lift]
example : 0 < fixed_rate_error fixed 3 ∧ fixed_rate_error fixed 3 < 1/10 := by
  norm_num [fixed_rate_error, fixed, borrow_rate_int, borrow_numerator, ceil_div,
    borrow_rate, FixedParams.lift]
example : project_unit ((3 : ℝ)/fixed.scale +
    (1/2)*(1/2 - (borrow_rate_int fixed 3 : ℝ)/fixed.scale)) =
    feedback_step fixed.lift (1/2) (1/2) ((3 : ℝ)/fixed.scale)
      (-(1/2)*fixed_rate_error fixed 3) := by
  simpa using rounded_rate_step_identity fixed 3 (1/2) (1/2) 0
example : |(1/10 : ℝ) - (1/2)*(1/100) + 1/1000| ≤ 1/10+(1/2)*(1/100)+1/1000 :=
  combined_disturbance_bound (by norm_num) (by norm_num) (by norm_num) (by norm_num)
example : (feedback_rat kinkModel (1/4) (1/2) (3/4) 0 : ℝ) =
    feedback_step kinkModel (1/4) (1/2) (3/4) 0 := by
  simpa using feedback_rat_cast kinkModel (1/4) (1/2) (3/4) 0
example (t : ℕ) : (trajectory_rat linearModel (1/2) (1/2) 0 (fun _ => 0) t : ℝ) =
    trajectory linearModel (1/2) (1/2) 0 (fun _ => 0) t := by
  simpa using trajectory_rat_cast linearModel (1/2) (1/2) 0 (fun _ => 0) t
example : DeFiLendingUtilizationFeedbackStabilitySuite := verification_suite

def scenarios : List (String × Bool) :=
  [("project below", decide (project_rat (-1) = 0)),
   ("project above", decide (project_rat 2 = 1)),
   ("project inside", decide (project_rat (2/5) = 2/5)),
   ("linear first", decide (feedback_rat linearModel (1/2) (1/2) 0 0 = 1/4)),
   ("linear fifth", decide (trajectory_rat linearModel (1/2) (1/2) 0 (fun _ => 0) 5 = 31/64)),
   ("positive noise first", decide (feedback_rat linearModel (1/2) (1/2) 0 (1/8) = 3/8)),
   ("persistent noise", decide
     (trajectory_rat linearModel (1/2) (1/2) (3/4) (fun _ => 1/8) 6 = 3/4)),
   ("negative noise first", decide (feedback_rat linearModel (1/2) (1/2) 0 (-1/8) = 1/8)),
   ("kink lower", decide (feedback_rat kinkModel (1/4) (1/2) (1/4) 0 = 5/16)),
   ("kink upper", decide (feedback_rat kinkModel (1/4) (1/2) (3/4) 0 = 9/16)),
   ("kink fixed", decide (feedback_rat kinkModel (1/4) (1/2) (1/2) 0 = 1/2)),
   ("decreasing slopes", decide (feedback_rat decreasingSlopes (1/4) (3/2) (3/4) 0 = 11/16)),
   ("cycle first", decide (trajectory_rat linearModel 3 (1/2) 0 (fun _ => 0) 1 = 1)),
   ("cycle even", decide (trajectory_rat linearModel 3 (1/2) 0 (fun _ => 0) 10 = 0)),
   ("cycle odd", decide (trajectory_rat linearModel 3 (1/2) 0 (fun _ => 0) 11 = 1)),
   ("flat stationary", decide (trajectory_rat flatModel 7 0 (1/4) (fun _ => 0) 5 = 1/4)),
   ("boundary low", decide (feedback_rat linearModel (1/2) (-1) 0 0 = 0)),
   ("boundary high", decide (feedback_rat linearModel (1/2) 2 1 0 = 1)),
   ("saturated noise", decide (feedback_rat linearModel (1/2) (1/2) 0 100 = 1)),
   ("integer rounding", decide (borrow_rate_int fixed 3 = 1)),
   ("rational exact rate", decide (borrow_rate fixed.lift (3/10) = 9/100)),
   ("nonzero residual", decide
     ((borrow_rate_int fixed 3 : ℚ)/fixed.scale - borrow_rate fixed.lift (3/10) = 1/100))]

#eval scenarios
end UtilizationFeedbackRegression
