/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DeFiKinkedInterestRateUtilization
import Verification.DeFiLendingLiquidationHealthFactor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp

/-! Conditional stability of a prescribed scalar feedback law. The market response
is an input model, not a consequence of pool accounting or economic solvency. -/
namespace DeFiLendingUtilizationFeedbackStability
open DeFiKinkedInterestRateUtilization Finset Filter
open scoped Topology

noncomputable section

def project_unit (x : ℝ) : ℝ := max 0 (min 1 x)

theorem project_unit_bounds (x : ℝ) : 0 ≤ project_unit x ∧ project_unit x ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem project_unit_eq {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : project_unit x = x := by
  simp [project_unit, min_eq_right h1, max_eq_right h0]

theorem project_unit_monotone : Monotone project_unit := by
  intro x y h
  exact max_le_max_left _ (min_le_min_left _ h)

theorem project_unit_nonexpansive (x y : ℝ) :
    |project_unit x - project_unit y| ≤ |x - y| := by
  wlog h : x ≤ y generalizing x y
  · simpa only [abs_sub_comm] using this y x (le_of_not_ge h)
  rw [abs_of_nonpos (sub_nonpos.mpr (project_unit_monotone h)),
    abs_of_nonpos (sub_nonpos.mpr h)]
  unfold project_unit
  rcases le_total x 0 with hx | hx
  · rw [min_eq_right (by linarith : x ≤ 1), max_eq_left hx]
    rcases le_total y 0 with hy | hy
    · rw [min_eq_right (by linarith : y ≤ 1), max_eq_left hy]; linarith
    · rcases le_total y 1 with hy1 | hy1
      · rw [min_eq_right hy1, max_eq_right hy]; linarith
      · rw [min_eq_left hy1, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]; linarith
  · rcases le_total x 1 with hx1 | hx1
    · rw [min_eq_right hx1, max_eq_right hx]
      rcases le_total y 1 with hy1 | hy1
      · rw [min_eq_right hy1, max_eq_right (by linarith : 0 ≤ y)]
      · rw [min_eq_left hy1, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]; linarith
    · rw [min_eq_left hx1, min_eq_left (by linarith : 1 ≤ y)]
      linarith

/-- Real extension of exactly the rational curve in module 167. -/
def rate (P : KinkRateParams) (u : ℝ) : ℝ :=
  if u ≤ (P.kink : ℝ) then P.base + (P.slope₁ : ℝ) * u
  else P.base + (P.slope₁ : ℝ) * P.kink + (P.slope₂ : ℝ) * (u - P.kink)

theorem rate_rat (P : KinkRateParams) (u : ℚ) : rate P u = (borrow_rate P u : ℝ) := by
  unfold rate borrow_rate
  by_cases h : u ≤ P.kink
  · have hr : (u : ℝ) ≤ P.kink := by exact_mod_cast h
    simp [h, hr]
  · have hr : ¬ (u : ℝ) ≤ P.kink := by exact_mod_cast h
    simp [h, hr]

def raw_step (P : KinkRateParams) (η d u : ℝ) : ℝ := u + η * (d - rate P u)
def feedback_step (P : KinkRateParams) (η d u ξ : ℝ) : ℝ :=
  project_unit (raw_step P η d u + ξ)
def kappa (P : KinkRateParams) (η : ℝ) : ℝ :=
  max |1 - η * (P.slope₁ : ℝ)| |1 - η * (P.slope₂ : ℝ)|

theorem kappa_nonneg (P : KinkRateParams) (η : ℝ) : 0 ≤ kappa P η :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem kappa_lt_one_iff (P : KinkRateParams) (η : ℝ) :
    kappa P η < 1 ↔
      (0 < η * (P.slope₁ : ℝ) ∧ η * (P.slope₁ : ℝ) < 2) ∧
      (0 < η * (P.slope₂ : ℝ) ∧ η * (P.slope₂ : ℝ) < 2) := by
  simp only [kappa, max_lt_iff, abs_lt]
  constructor <;> rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ <;> constructor <;> constructor <;> linarith

theorem suitable_step_contracts (P : KinkRateParams) {η : ℝ} (hη : 0 < η)
    (h1 : 0 < P.slope₁) (h2 : 0 < P.slope₂)
    (hstep : η * max (P.slope₁ : ℝ) (P.slope₂ : ℝ) < 2) : kappa P η < 1 := by
  have h1r : (0 : ℝ) < P.slope₁ := by exact_mod_cast h1
  have h2r : (0 : ℝ) < P.slope₂ := by exact_mod_cast h2
  exact (kappa_lt_one_iff P η).mpr
    ⟨⟨mul_pos hη h1r, (mul_le_mul_of_nonneg_left (le_max_left _ _) hη.le).trans_lt hstep⟩,
      ⟨mul_pos hη h2r, (mul_le_mul_of_nonneg_left (le_max_right _ _) hη.le).trans_lt hstep⟩⟩

theorem zero_slope_no_strict_bound (P : KinkRateParams) (η : ℝ)
    (h : P.slope₁ = 0 ∨ P.slope₂ = 0) : 1 ≤ kappa P η := by
  rcases h with h | h
  · simp [kappa, h]
  · simp [kappa, h]

theorem raw_step_lipschitz (P : KinkRateParams) (η d x y : ℝ) :
    |raw_step P η d x - raw_step P η d y| ≤ kappa P η * |x - y| := by
  wlog hxy : x ≤ y generalizing x y
  · simpa only [abs_sub_comm] using this y x (le_of_not_ge hxy)
  have h1 : |1 - η * (P.slope₁ : ℝ)| ≤ kappa P η := le_max_left _ _
  have h2 : |1 - η * (P.slope₂ : ℝ)| ≤ kappa P η := le_max_right _ _
  rw [abs_sub_comm (raw_step P η d x), abs_sub_comm x,
    abs_of_nonneg (sub_nonneg.mpr hxy)]
  by_cases hy : y ≤ (P.kink : ℝ)
  · have hx : x ≤ (P.kink : ℝ) := hxy.trans hy
    have he : raw_step P η d y - raw_step P η d x =
        (1 - η * (P.slope₁ : ℝ)) * (y - x) := by simp [raw_step, rate, hx, hy]; ring
    rw [he, abs_mul, abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact mul_le_mul_of_nonneg_right h1 (sub_nonneg.mpr hxy)
  · by_cases hx : x ≤ (P.kink : ℝ)
    · have he : raw_step P η d y - raw_step P η d x =
          (1 - η * (P.slope₁ : ℝ)) * ((P.kink : ℝ) - x) +
          (1 - η * (P.slope₂ : ℝ)) * (y - P.kink) := by
        simp [raw_step, rate, hx, hy]; ring
      rw [he]
      calc
        _ ≤ |(1 - η * (P.slope₁ : ℝ)) * ((P.kink : ℝ) - x)| +
            |(1 - η * (P.slope₂ : ℝ)) * (y - P.kink)| := abs_add_le _ _
        _ = |1 - η * (P.slope₁ : ℝ)| * ((P.kink : ℝ) - x) +
            |1 - η * (P.slope₂ : ℝ)| * (y - P.kink) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hx),
            abs_of_nonneg (by linarith : 0 ≤ y - (P.kink : ℝ))]
        _ ≤ kappa P η * ((P.kink : ℝ) - x) + kappa P η * (y - P.kink) :=
          add_le_add (mul_le_mul_of_nonneg_right h1 (sub_nonneg.mpr hx))
            (mul_le_mul_of_nonneg_right h2 (by linarith))
        _ = _ := by ring
    · have he : raw_step P η d y - raw_step P η d x =
          (1 - η * (P.slope₂ : ℝ)) * (y - x) := by simp [raw_step, rate, hx, hy]; ring
      rw [he, abs_mul, abs_of_nonneg (sub_nonneg.mpr hxy)]
      exact mul_le_mul_of_nonneg_right h2 (sub_nonneg.mpr hxy)

theorem invariant_bound (P : KinkRateParams) (η d u ξ : ℝ) :
    0 ≤ feedback_step P η d u ξ ∧ feedback_step P η d u ξ ≤ 1 := project_unit_bounds _

theorem feedback_lipschitz (P : KinkRateParams) (η d x y ξ : ℝ) :
    |feedback_step P η d x ξ - feedback_step P η d y ξ| ≤ kappa P η * |x - y| := by
  exact (project_unit_nonexpansive _ _).trans (by simpa using raw_step_lipschitz P η d x y)

theorem feedback_noise_bound (P : KinkRateParams) (η d u ξ ζ : ℝ) :
    |feedback_step P η d u ξ - feedback_step P η d u ζ| ≤ |ξ - ζ| := by
  simpa [feedback_step] using project_unit_nonexpansive
    (raw_step P η d u + ξ) (raw_step P η d u + ζ)

def trajectory (P : KinkRateParams) (η d u0 : ℝ) (ξ : ℕ → ℝ) : ℕ → ℝ
  | 0 => u0
  | t + 1 => feedback_step P η d (trajectory P η d u0 ξ t) (ξ t)

theorem trajectory_invariant (P : KinkRateParams) (η d u0 : ℝ) (ξ : ℕ → ℝ)
    (h0 : 0 ≤ u0) (h1 : u0 ≤ 1) (t : ℕ) :
    0 ≤ trajectory P η d u0 ξ t ∧ trajectory P η d u0 ξ t ≤ 1 := by
  cases t with
  | zero => exact ⟨h0, h1⟩
  | succ t => exact invariant_bound P η d _ _

def IsEquilibrium (P : KinkRateParams) (η d u : ℝ) : Prop := feedback_step P η d u 0 = u

theorem target_rate_equilibrium (P : KinkRateParams) (η d u : ℝ)
    (h0 : 0 ≤ u) (h1 : u ≤ 1) (hd : rate P u = d) : IsEquilibrium P η d u := by
  simp [IsEquilibrium, feedback_step, raw_step, hd, project_unit_eq h0 h1]

theorem equilibrium_unique (P : KinkRateParams) (η d : ℝ) (hk : kappa P η < 1)
    {u v : ℝ} (hu : IsEquilibrium P η d u) (hv : IsEquilibrium P η d v) : u = v := by
  have h := feedback_lipschitz P η d u v 0
  rw [hu, hv] at h
  have ha := abs_nonneg (u-v)
  have hz : |u-v| = 0 := by nlinarith
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

theorem one_step_error (P : KinkRateParams) (η d u star ξ : ℝ)
    (hs : IsEquilibrium P η d star) :
    |feedback_step P η d u ξ - star| ≤ kappa P η * |u - star| + |ξ| := by
  change feedback_step P η d star 0 = star at hs
  calc
    _ ≤ |feedback_step P η d u ξ - feedback_step P η d u 0| +
        |feedback_step P η d u 0 - star| := abs_sub_le _ _ _
    _ ≤ |ξ| + kappa P η * |u-star| := add_le_add
      (by simpa using feedback_noise_bound P η d u ξ 0)
      (by simpa only [hs] using feedback_lipschitz P η d u star 0)
    _ = _ := by ring

def error_bound (κ ε e : ℝ) (t : ℕ) : ℝ := κ^t * e + ε * (1 - κ^t) / (1 - κ)

theorem error_bound_succ (κ ε e : ℝ) (hκ : κ ≠ 1) (t : ℕ) :
    error_bound κ ε e (t+1) = κ * error_bound κ ε e t + ε := by
  unfold error_bound
  have hd : 1-κ ≠ 0 := sub_ne_zero.mpr (Ne.symm hκ)
  rw [pow_succ]
  field_simp
  ring

theorem bounded_perturbation_stability (P : KinkRateParams) (η d u0 star ε : ℝ)
    (ξ : ℕ → ℝ) (hk : kappa P η < 1) (hs : IsEquilibrium P η d star)
    (hξ : ∀ t, |ξ t| ≤ ε) (t : ℕ) :
    |trajectory P η d u0 ξ t - star| ≤
      (kappa P η)^t * |u0-star| + ε * (1-(kappa P η)^t)/(1-kappa P η) := by
  change _ ≤ error_bound (kappa P η) ε |u0-star| t
  induction t with
  | zero => simp [trajectory, error_bound]
  | succ t ih =>
    rw [trajectory, error_bound_succ _ _ _ (ne_of_lt hk)]
    exact (one_step_error P η d _ star _ hs).trans
      (add_le_add (mul_le_mul_of_nonneg_left ih (kappa_nonneg P η)) (hξ t))

theorem noiseless_error (P : KinkRateParams) (η d u0 star : ℝ)
    (hk : kappa P η < 1) (hs : IsEquilibrium P η d star) (t : ℕ) :
    |trajectory P η d u0 (fun _ => 0) t - star| ≤ (kappa P η)^t * |u0-star| := by
  simpa using bounded_perturbation_stability P η d u0 star 0 (fun _ => 0)
    hk hs (by intro t; simp) t


theorem noiseless_converges (P : KinkRateParams) (η d u0 star : ℝ)
    (hk : kappa P η < 1) (hs : IsEquilibrium P η d star) :
    Tendsto (trajectory P η d u0 (fun _ => 0)) atTop (𝓝 star) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (kappa_nonneg P η) hk).mul_const |u0-star|
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun t => ?_) (by simpa using hp)
  simpa only [Real.dist_eq] using noiseless_error P η d u0 star hk hs t

/-- Noise, a rate-computation residual, and an update-rounding residual are separate. -/
theorem combined_disturbance_bound {η ξ δ q ε er eq : ℝ} (hη : 0 ≤ η)
    (hξ : |ξ| ≤ ε) (hδ : |δ| ≤ er) (hq : |q| ≤ eq) :
    |ξ - η * δ + q| ≤ ε + η * er + eq := by
  calc
    _ ≤ |ξ - η * δ| + |q| := abs_add_le _ _
    _ ≤ |ξ| + |η * δ| + |q| := add_le_add (abs_sub _ _) le_rfl
    _ ≤ ε + η * er + eq := by
      rw [abs_mul, abs_of_nonneg hη]
      exact add_le_add (add_le_add hξ (mul_le_mul_of_nonneg_left hδ hη)) hq

/-- Actual error of module 167's executable integer rate, normalized by its scale. -/
def fixed_rate_error (P : FixedParams) (u : ℕ) : ℝ :=
  (((borrow_rate_int P u : ℚ) / P.scale - borrow_rate P.lift ((u : ℚ) / P.scale) : ℚ) : ℝ)

theorem fixed_rate_error_bounds (P : FixedParams) (u : ℕ) :
    0 ≤ fixed_rate_error P u ∧ fixed_rate_error P u < 1 / (P.scale : ℝ) := by
  have h := borrow_rate_int_error P u
  unfold fixed_rate_error
  constructor
  · exact_mod_cast h.1
  · have hr : (((borrow_rate_int P u : ℚ) / P.scale -
        borrow_rate P.lift ((u : ℚ) / P.scale) : ℚ) : ℝ) <
        ((1 / (P.scale : ℚ) : ℚ) : ℝ) := Rat.cast_lt.mpr h.2
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using hr

theorem fixed_rate_error_abs (P : FixedParams) (u : ℕ) :
    |fixed_rate_error P u| ≤ 1 / (P.scale : ℝ) := by
  rw [abs_of_nonneg (fixed_rate_error_bounds P u).1]
  exact (fixed_rate_error_bounds P u).2.le

theorem rounded_rate_step_identity (P : FixedParams) (u : ℕ) (η d ξ : ℝ) :
    project_unit ((u : ℝ) / P.scale +
      η * (d - (borrow_rate_int P u : ℝ) / P.scale) + ξ) =
    feedback_step P.lift η d ((u : ℝ) / P.scale) (ξ - η * fixed_rate_error P u) := by
  have hr := rate_rat P.lift ((u : ℚ) / P.scale)
  push_cast at hr
  unfold feedback_step raw_step fixed_rate_error
  rw [hr]
  push_cast
  congr 1
  ring


theorem rounding_and_noise_stability (P : KinkRateParams) (η d u0 star ε er eq : ℝ)
    (ξ δ q : ℕ → ℝ) (hη : 0 ≤ η) (hk : kappa P η < 1)
    (hs : IsEquilibrium P η d star) (hξ : ∀ t, |ξ t| ≤ ε)
    (hδ : ∀ t, |δ t| ≤ er) (hq : ∀ t, |q t| ≤ eq) (t : ℕ) :
    |trajectory P η d u0 (fun t => ξ t - η * δ t + q t) t - star| ≤
      (kappa P η)^t * |u0-star| +
        (ε + η * er + eq) * (1-(kappa P η)^t)/(1-kappa P η) :=
  bounded_perturbation_stability P η d u0 star _ _ hk hs
    (fun t => combined_disturbance_bound hη (hξ t) (hδ t) (hq t)) t

end

/-- Executable exact-rational counterpart; no floating-point implementation is assumed. -/
def project_rat (x : ℚ) : ℚ := max 0 (min 1 x)
def feedback_rat (P : KinkRateParams) (η d u ξ : ℚ) : ℚ :=
  project_rat (u + η * (d - borrow_rate P u) + ξ)
def trajectory_rat (P : KinkRateParams) (η d u0 : ℚ) (ξ : ℕ → ℚ) : ℕ → ℚ
  | 0 => u0
  | t+1 => feedback_rat P η d (trajectory_rat P η d u0 ξ t) (ξ t)

theorem project_rat_cast (x : ℚ) : (project_rat x : ℝ) = project_unit x := by
  simp [project_rat, project_unit]

theorem feedback_rat_cast (P : KinkRateParams) (η d u ξ : ℚ) :
    (feedback_rat P η d u ξ : ℝ) = feedback_step P η d u ξ := by
  simp [feedback_rat, project_rat_cast, feedback_step, raw_step, rate_rat]

theorem trajectory_rat_cast (P : KinkRateParams) (η d u0 : ℚ) (ξ : ℕ → ℚ) (t : ℕ) :
    (trajectory_rat P η d u0 ξ t : ℝ) =
      trajectory P η d u0 (fun k => (ξ k : ℝ)) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [trajectory_rat, trajectory, feedback_rat_cast, ih]


/-- Exact fixtures shared with executable regressions. -/
def linearModel : KinkRateParams where
  base := 0
  slope₁ := 1
  slope₂ := 1
  kink := 1/2
  reserveFactor := 0
  base_nonneg := by norm_num
  slope₁_nonneg := by norm_num
  slope₂_nonneg := by norm_num
  kink_pos := by norm_num
  kink_lt_one := by norm_num
  reserve_nonneg := by norm_num
  reserve_le_one := by norm_num

def flatModel : KinkRateParams :=
  { linearModel with
    slope₁ := 0
    slope₂ := 0
    slope₁_nonneg := le_rfl
    slope₂_nonneg := le_rfl }

theorem linear_rate (u : ℝ) : rate linearModel u = u := by
  unfold rate
  split <;> norm_num [linearModel]

theorem stable_kappa : kappa linearModel (1/2) = 1/2 := by norm_num [kappa, linearModel]

theorem linear_equilibrium (η : ℝ) : IsEquilibrium linearModel η (1/2) (1/2) :=
  target_rate_equilibrium _ _ _ _ (by norm_num) (by norm_num) (linear_rate _)

theorem stable_convergence (u0 : ℝ) :
    Tendsto (trajectory linearModel (1/2) (1/2) u0 (fun _ => 0)) atTop (𝓝 (1/2)) :=
  noiseless_converges _ _ _ _ _ (by rw [stable_kappa]; norm_num) (linear_equilibrium _)

theorem persistent_noise_equilibrium (t : ℕ) :
    trajectory linearModel (1/2) (1/2) (3/4) (fun _ => 1/8) t = 3/4 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [trajectory, ih]
    norm_num [feedback_step, raw_step, linear_rate, project_unit]

theorem large_step_cycle (t : ℕ) :
    trajectory linearModel 3 (1/2) 0 (fun _ => 0) (2*t) = 0 ∧
    trajectory linearModel 3 (1/2) 0 (fun _ => 0) (2*t+1) = 1 := by
  induction t with
  | zero => norm_num [trajectory, feedback_step, raw_step, linear_rate, project_unit]
  | succ t ih =>
    have he : 2*(t+1) = (2*t+1)+1 := by omega
    rw [he, trajectory, ih.2]
    norm_num [feedback_step, raw_step, linear_rate, project_unit]
    rw [trajectory, trajectory, ih.2]
    norm_num [feedback_step, raw_step, linear_rate, project_unit]

theorem large_step_distance (t : ℕ) :
    |trajectory linearModel 3 (1/2) 0 (fun _ => 0) t - 1/2| = 1/2 := by
  have hb : trajectory linearModel 3 (1/2) 0 (fun _ => 0) t = 0 ∨
      trajectory linearModel 3 (1/2) 0 (fun _ => 0) t = 1 := by
    induction t with
    | zero => exact Or.inl rfl
    | succ t ih =>
      rcases ih with h | h
      · right; rw [trajectory, h]
        norm_num [feedback_step, raw_step, linear_rate, project_unit]
      · left; rw [trajectory, h]
        norm_num [feedback_step, raw_step, linear_rate, project_unit]
  rcases hb with h | h <;> rw [h] <;> norm_num

theorem large_step_not_convergent :
    ¬ Tendsto (trajectory linearModel 3 (1/2) 0 (fun _ => 0)) atTop (𝓝 (1/2)) := by
  intro h
  have hd := tendsto_iff_dist_tendsto_zero.mp h
  have he : (fun t => dist (trajectory linearModel 3 (1/2) 0 (fun _ => 0) t) (1/2)) =
      fun _ : ℕ => (1/2 : ℝ) := by
    funext t; simpa only [Real.dist_eq] using large_step_distance t
  rw [he] at hd
  have hz : (1/2 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hd
  norm_num at hz

theorem flat_stationary (η u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) (t : ℕ) :
    trajectory flatModel η 0 u (fun _ => 0) t = u := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [trajectory, ih]
    have hr : rate flatModel u = 0 := by unfold rate; split <;> simp [flatModel, linearModel]
    simpa [feedback_step, raw_step, hr] using project_unit_eq h0 h1

structure DeFiLendingUtilizationFeedbackStabilitySuite : Prop where
  rational_bridge : ∀ P (u : ℚ), rate P u = (borrow_rate P u : ℝ)
  step_condition : ∀ P η, kappa P η < 1 ↔
    (0 < η * (P.slope₁ : ℝ) ∧ η * (P.slope₁ : ℝ) < 2) ∧
    (0 < η * (P.slope₂ : ℝ) ∧ η * (P.slope₂ : ℝ) < 2)
  roundoff : ∀ P u, 0 ≤ fixed_rate_error P u ∧ fixed_rate_error P u < 1/(P.scale : ℝ)
  projection : ∀ x y, |project_unit x - project_unit y| ≤ |x-y|
  contraction : ∀ P η d x y ξ,
    |feedback_step P η d x ξ - feedback_step P η d y ξ| ≤ kappa P η * |x-y|
  invariant : ∀ P η d u0 ξ, 0 ≤ u0 → u0 ≤ 1 → ∀ t,
    0 ≤ trajectory P η d u0 ξ t ∧ trajectory P η d u0 ξ t ≤ 1
  robust : ∀ P η d u0 star ε ξ, kappa P η < 1 → IsEquilibrium P η d star →
    (∀ t, |ξ t| ≤ ε) → ∀ t, |trajectory P η d u0 ξ t-star| ≤
      (kappa P η)^t * |u0-star| + ε * (1-(kappa P η)^t)/(1-kappa P η)
  convergence : ∀ P η d u0 star, kappa P η < 1 → IsEquilibrium P η d star →
    Tendsto (trajectory P η d u0 (fun _ => 0)) atTop (𝓝 star)
  cycle : ∀ t, trajectory linearModel 3 (1/2) 0 (fun _ => 0) (2*t) = 0 ∧
    trajectory linearModel 3 (1/2) 0 (fun _ => 0) (2*t+1) = 1

theorem verification_suite : DeFiLendingUtilizationFeedbackStabilitySuite where
  rational_bridge := rate_rat
  step_condition := kappa_lt_one_iff
  roundoff := fixed_rate_error_bounds
  projection := project_unit_nonexpansive
  contraction := feedback_lipschitz
  invariant := trajectory_invariant
  robust := bounded_perturbation_stability
  convergence := noiseless_converges
  cycle := large_step_cycle

end DeFiLendingUtilizationFeedbackStability
