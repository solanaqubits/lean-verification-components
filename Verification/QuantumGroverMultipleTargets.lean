/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumGroverSearch
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Matrix.Basic

/-!
# Multiple marked targets in four real coordinates

The diagonal phase oracle marks a finite set. The symmetric marked / unmarked
plane is invariant, but is not a decomposition of the whole four - dimensional
space into two lines. Measurement weights are sums of squared real amplitudes.
-/
noncomputable section
namespace QuantumGroverMultipleTargets
open scoped BigOperators

abbrev State := Fin 4 → ℝ

def inner (u v : State) : ℝ := ∑ i, u i * v i
def normSquared (v : State) : ℝ := inner v v
def uniform : State := fun _ => 1 / 2

def multiTargetOracle (T : Finset (Fin 4)) (v : State) : State :=
  fun i => if i ∈ T then - v i else v i

def diffusion (v : State) : State := fun i => 2 * ((∑ j, v j) / 4) - v i
def groverStep (T : Finset (Fin 4)) (v : State) : State := diffusion (multiTargetOracle T v)
def successWeight (T : Finset (Fin 4)) (v : State) : ℝ := ∑ i ∈ T, (v i) ^ 2

def stateAt (T : Finset (Fin 4)) : ℕ → State
  | 0 => uniform
  | k + 1 => groverStep T (stateAt T k)

def twoLevel (T : Finset (Fin 4)) (a b : ℝ) : State := fun i => if i ∈ T then a else b

theorem card_le_four (T : Finset (Fin 4)) : T.card ≤ 4 := by
  simpa using Finset.card_le_univ T

theorem sum_twoLevel (T : Finset (Fin 4)) (a b : ℝ) :
    (∑ i, twoLevel T a b i) = T.card * a + (4 - (T.card : ℝ)) * b := by
  have h : twoLevel T a b = fun i => b + if i ∈ T then a - b else 0 := by
    funext i; simp only [twoLevel]; split <;> ring
  rw [h, Finset.sum_add_distrib]
  simp
  ring

theorem inner_twoLevel (T : Finset (Fin 4)) (a b c d : ℝ) :
    inner (twoLevel T a b) (twoLevel T c d) = T.card * a * c + (4 - (T.card : ℝ)) * b * d := by
  have h : (fun i => twoLevel T a b i * twoLevel T c d i) = twoLevel T (a * c) (b * d) := by
    funext i; simp only [twoLevel]; split <;> rfl
  rw [inner, h, sum_twoLevel]
  ring

theorem success_twoLevel (T : Finset (Fin 4)) (a b : ℝ) :
    successWeight T (twoLevel T a b) = T.card * a ^ 2 := by
  unfold successWeight
  calc
    _ = ∑ _i ∈ T, a ^ 2 := Finset.sum_congr rfl (fun i hi => by simp [twoLevel, hi])
    _ = _ := by simp

theorem oracle_involution (T : Finset (Fin 4)) (v : State) :
    multiTargetOracle T (multiTargetOracle T v) = v := by
  funext i; by_cases h : i ∈ T <;> simp [multiTargetOracle, h]

theorem oracle_norm (T : Finset (Fin 4)) (v : State) :
    normSquared (multiTargetOracle T v) = normSquared v := by
  unfold normSquared inner
  apply Finset.sum_congr rfl
  intro i _
  simp only [multiTargetOracle]
  split <;> ring

theorem diffusion_involution (v : State) : diffusion (diffusion v) = v := by
  funext i
  simp [diffusion, Fin.sum_univ_succ]
  ring

theorem diffusion_norm (v : State) : normSquared (diffusion v) = normSquared v := by
  simp [normSquared, inner, diffusion, Fin.sum_univ_succ]
  ring

theorem grover_step_preserves_norm (T : Finset (Fin 4)) (v : State) :
    normSquared (groverStep T v) = normSquared v := by
  rw [groverStep, diffusion_norm, oracle_norm]

theorem uniform_norm : normSquared uniform = 1 := by
  norm_num [normSquared, inner, uniform, Fin.sum_univ_succ]

theorem stateAt_normalized (T : Finset (Fin 4)) (k : ℕ) : normSquared (stateAt T k) = 1 := by
  induction k with
  | zero => exact uniform_norm
  | succ k ih => simpa only [stateAt, grover_step_preserves_norm] using ih

theorem step_twoLevel (T : Finset (Fin 4)) (a b : ℝ) :
    groverStep T (twoLevel T a b) =
      twoLevel T ((1 - T.card / 2) * a + ((4 - (T.card : ℝ)) / 2) * b)
        (-(T.card : ℝ) / 2 * a + (1 - T.card / 2) * b) := by
  have ho : multiTargetOracle T (twoLevel T a b) = twoLevel T (-a) b := by
    funext i; simp only [multiTargetOracle, twoLevel]; split <;> rfl
  rw [groverStep, ho]
  funext i
  change 2 * ((∑ j, twoLevel T (-a) b j) / 4) - twoLevel T (-a) b i = _
  rw [sum_twoLevel]
  simp only [twoLevel]
  split <;> ring

def amplitudePair (m : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1 / 2, 1 / 2)
  | k + 1 => let p := amplitudePair m k
           ((1 - m / 2) * p.1 + (4 - m) / 2 * p.2, -m / 2 * p.1 + (1 - m / 2) * p.2)

theorem stateAt_twoLevel (T : Finset (Fin 4)) (k : ℕ) :
    stateAt T k = twoLevel T (amplitudePair T.card k).1 (amplitudePair T.card k).2 := by
  induction k with
  | zero => funext i; simp [stateAt, uniform, twoLevel, amplitudePair]
  | succ k ih => rw [stateAt, ih, step_twoLevel]; rfl

theorem success_recurrence (T : Finset (Fin 4)) (k : ℕ) :
    successWeight T (stateAt T k) = T.card * (amplitudePair T.card k).1 ^ 2 := by
  rw [stateAt_twoLevel, success_twoLevel]

theorem step_uniform (T : Finset (Fin 4)) :
    groverStep T uniform = twoLevel T ((3 - (T.card : ℝ)) / 2) ((1 - (T.card : ℝ)) / 2) := by
  have h : uniform = twoLevel T (1 / 2) (1 / 2) := by funext i; simp [uniform, twoLevel]
  rw [h, step_twoLevel]
  congr 1 <;> ring

theorem one_step_success (T : Finset (Fin 4)) :
    successWeight T (groverStep T uniform) = T.card * (3 - (T.card : ℝ)) ^ 2 / 4 := by
  rw [step_uniform, success_twoLevel]; ring

theorem grover_targets_M0 : groverStep ∅ uniform = uniform := by
  funext i; norm_num [groverStep, diffusion, multiTargetOracle, uniform]

theorem grover_targets_M4 : groverStep Finset.univ uniform = -uniform := by
  funext i; norm_num [groverStep, diffusion, multiTargetOracle, uniform]

theorem grover_targets_M1 (T : Finset (Fin 4)) (h : T.card = 1) :
    successWeight T (groverStep T uniform) = 1 := by rw [one_step_success, h]; norm_num

theorem grover_targets_M3_overshoot (T : Finset (Fin 4)) (h : T.card = 3) :
    successWeight T (groverStep T uniform) = 0 := by rw [one_step_success, h]; norm_num

theorem pair_two_squares (k : ℕ) :
    (amplitudePair 2 k).1 ^ 2 = 1 / 4 ∧ (amplitudePair 2 k).2 ^ 2 = 1 / 4 := by
  induction k with
  | zero => norm_num [amplitudePair]
  | succ k ih => norm_num [amplitudePair] at ⊢; exact ⟨ih.2, ih.1⟩

theorem grover_targets_M2_stationary (T : Finset (Fin 4)) (h : T.card = 2) (k : ℕ) :
    successWeight T (stateAt T k) = 1 / 2 := by
  rw [success_recurrence, h]
  norm_num [pair_two_squares k]


theorem success_bounds (T : Finset (Fin 4)) (v : State) :
    0 ≤ successWeight T v ∧ successWeight T v ≤ normSquared v := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  · unfold successWeight normSquared inner
    simpa only [pow_two] using
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
        (fun i _ _ => sq_nonneg (v i)))

theorem oracle_add (T : Finset (Fin 4)) (u v : State) :
    multiTargetOracle T (u + v) = multiTargetOracle T u + multiTargetOracle T v := by
  funext i; by_cases h : i ∈ T <;> simp [multiTargetOracle, h]; ring

theorem step_scale (T : Finset (Fin 4)) (c : ℝ) (v : State) :
    groverStep T (fun i => c * v i) = fun i => c * groverStep T v i := by
  have h : multiTargetOracle T (fun i => c * v i) = fun i => c * multiTargetOracle T v i := by
    funext i; by_cases h : i ∈ T <;> simp [multiTargetOracle, h]
  unfold groverStep
  rw [h]
  funext i
  simp only [diffusion, ← Finset.mul_sum]
  ring

theorem stateAt_empty (k : ℕ) : stateAt ∅ k = uniform := by
  induction k with
  | zero => rfl
  | succ k ih => rw [stateAt, ih, grover_targets_M0]

theorem stateAt_full (k : ℕ) : stateAt Finset.univ k = fun i => (-1 : ℝ) ^ k * uniform i := by
  induction k with
  | zero => funext i; simp [stateAt]
  | succ k ih =>
    rw [stateAt, ih, step_scale, grover_targets_M4]
    funext i
    simp only [Pi.neg_apply, pow_succ]
    ring

def toLegacy (v : State) : QuantumGroverSearch.QState4 := ⟨v 0, v 1, v 2, v 3⟩
def fromLegacy (v : QuantumGroverSearch.QState4) : State := ![v.x0, v.x1, v.x2, v.x3]

theorem legacy_roundtrip (v : QuantumGroverSearch.QState4) : toLegacy (fromLegacy v) = v := by
  cases v; rfl

theorem state_roundtrip (v : State) : fromLegacy (toLegacy v) = v := by
  funext i; fin_cases i <;> rfl

theorem legacy_inner (u v : State) :
    QuantumGroverSearch.dot (toLegacy u) (toLegacy v) = inner u v := by
  simp [QuantumGroverSearch.dot, toLegacy, inner, Fin.sum_univ_succ]
  ring

theorem legacy_diffusion (v : State) :
    toLegacy (diffusion v) = QuantumGroverSearch.diffusion (toLegacy v) := by
  ext <;> simp [toLegacy, diffusion, QuantumGroverSearch.diffusion,
    QuantumGroverSearch.vsub, QuantumGroverSearch.smul, QuantumGroverSearch.dot,
    QuantumGroverSearch.stateS, Fin.sum_univ_succ] <;> ring

def itemIndex : QuantumGroverSearch.TargetItem → Fin 4
  | .t00 => 0 | .t01 => 1 | .t10 => 2 | .t11 => 3

theorem singleton_oracle_legacy (t : QuantumGroverSearch.TargetItem) (v : State) :
    toLegacy (multiTargetOracle {itemIndex t} v) =
      QuantumGroverSearch.phaseOracle t (toLegacy v) := by
  cases t <;> ext <;> norm_num [itemIndex, toLegacy, multiTargetOracle,
    QuantumGroverSearch.phaseOracle, Fin.ext_iff]

theorem singleton_step_legacy (t : QuantumGroverSearch.TargetItem) (v : State) :
    toLegacy (groverStep {itemIndex t} v) =
      QuantumGroverSearch.groverStep (QuantumGroverSearch.targetToBasis t) (toLegacy v) := by
  rw [groverStep, legacy_diffusion, singleton_oracle_legacy,
    QuantumGroverSearch.phase_oracle_eq_reflection]
  rfl

theorem singleton_exact_legacy (t : QuantumGroverSearch.TargetItem) :
    toLegacy (groverStep {itemIndex t} uniform) = QuantumGroverSearch.targetToBasis t := by
  rw [groverStep, legacy_diffusion, singleton_oracle_legacy]
  exact QuantumGroverSearch.grover_universal_exactness t

def marked (T : Finset (Fin 4)) : State := twoLevel T (1 / Real.sqrt T.card) 0
def unmarked (T : Finset (Fin 4)) : State := twoLevel T 0 (1 / Real.sqrt (4 - (T.card : ℝ)))
def planeState (T : Finset (Fin 4)) (a b : ℝ) : State :=
  fun i => a * marked T i + b * unmarked T i

theorem plane_as_twoLevel (T : Finset (Fin 4)) (a b : ℝ) :
    planeState T a b = twoLevel T (a / Real.sqrt T.card) (b / Real.sqrt (4 - (T.card : ℝ))) := by
  funext i
  by_cases h : i ∈ T <;> simp [planeState, marked, unmarked, twoLevel, h, div_eq_mul_inv]

theorem plane_orthonormal (T : Finset (Fin 4)) (h0 : 0 < T.card) (h4 : T.card < 4) :
    inner (marked T) (marked T) = 1 ∧ inner (unmarked T) (unmarked T) = 1 ∧
      inner (marked T) (unmarked T) = 0 := by
  have hm : 0 < (T.card : ℝ) := by exact_mod_cast h0
  have hn : 0 < 4 - (T.card : ℝ) := by
    have h : (T.card : ℝ) < 4 := by exact_mod_cast h4
    linarith
  have hs := Real.sq_sqrt hm.le
  have ht := Real.sq_sqrt hn.le
  have hsn := (Real.sqrt_pos.2 hm).ne'
  have htn := (Real.sqrt_pos.2 hn).ne'
  simp only [marked, unmarked, inner_twoLevel]
  constructor
  · field_simp
    nlinarith
  constructor
  · field_simp
    nlinarith
  · ring

def rotationC (T : Finset (Fin 4)) : ℝ := 1 - (T.card : ℝ) / 2
def rotationS (T : Finset (Fin 4)) : ℝ :=
  Real.sqrt T.card * Real.sqrt (4 - (T.card : ℝ)) / 2

theorem plane_step (T : Finset (Fin 4)) (h0 : 0 < T.card) (h4 : T.card < 4) (a b : ℝ) :
    groverStep T (planeState T a b) =
      planeState T (rotationC T * a + rotationS T * b) (-rotationS T * a + rotationC T * b) := by
  have hm : 0 < (T.card : ℝ) := by exact_mod_cast h0
  have hn : 0 < 4 - (T.card : ℝ) := by
    have h : (T.card : ℝ) < 4 := by exact_mod_cast h4
    linarith
  have hs := Real.sq_sqrt hm.le
  have ht := Real.sq_sqrt hn.le
  have hsn := (Real.sqrt_pos.2 hm).ne'
  have htn := (Real.sqrt_pos.2 hn).ne'
  rw [plane_as_twoLevel, step_twoLevel, plane_as_twoLevel]
  congr 1 <;> dsimp [rotationC, rotationS] <;> field_simp <;>
    nlinarith [congrArg (fun x : ℝ => x * Real.sqrt T.card * b) ht,
      congrArg (fun x : ℝ => x * a * Real.sqrt (4 - (T.card : ℝ))) hs]

theorem rotation_unit (T : Finset (Fin 4)) (h0 : 0 < T.card) (h4 : T.card < 4) :
    rotationC T ^ 2 + rotationS T ^ 2 = 1 := by
  have hm : 0 ≤ (T.card : ℝ) := le_of_lt (by exact_mod_cast h0)
  have hn : 0 ≤ 4 - (T.card : ℝ) := by
    have h : (T.card : ℝ) < 4 := by exact_mod_cast h4
    linarith
  have hs := Real.sq_sqrt hm
  have ht := Real.sq_sqrt hn
  dsimp [rotationC, rotationS]
  nlinarith [sq_nonneg (Real.sqrt T.card - Real.sqrt (4 - (T.card : ℝ)))]


theorem inner_comm (u v : State) : inner u v = inner v u := by
  simp [inner, mul_comm]

theorem inner_plane (T : Finset (Fin 4)) (a b : ℝ) (v : State) :
    inner (planeState T a b) v = a * inner (marked T) v + b * inner (unmarked T) v := by
  simp [inner, planeState, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

theorem plane_coordinates (T : Finset (Fin 4)) (h0 : 0 < T.card) (h4 : T.card < 4) (a b : ℝ) :
    inner (planeState T a b) (marked T) = a ∧ inner (planeState T a b) (unmarked T) = b := by
  obtain ⟨hw, hb, hwb⟩ := plane_orthonormal T h0 h4
  have hbw : inner (unmarked T) (marked T) = 0 := by rw [inner_comm]; exact hwb
  simp [inner_plane, hw, hb, hwb, hbw]

theorem plane_coordinates_unique (T : Finset (Fin 4)) (h0 : 0 < T.card) (h4 : T.card < 4)
    (a b c d : ℝ) (h : planeState T a b = planeState T c d) : a = c ∧ b = d := by
  have h1 := congrArg (fun v => inner v (marked T)) h
  have h2 := congrArg (fun v => inner v (unmarked T)) h
  rw [(plane_coordinates T h0 h4 a b).1, (plane_coordinates T h0 h4 c d).1] at h1
  rw [(plane_coordinates T h0 h4 a b).2, (plane_coordinates T h0 h4 c d).2] at h2
  exact ⟨h1,h2⟩

def InPlane (T : Finset (Fin 4)) (v : State) : Prop := ∃ a b, v = planeState T a b

theorem plane_linear_closed (T : Finset (Fin 4)) (u v : State) (c d : ℝ)
    (hu : InPlane T u) (hv : InPlane T v) : InPlane T (fun i => c * u i + d * v i) := by
  obtain ⟨a,b,rfl⟩ := hu
  obtain ⟨e,f,rfl⟩ := hv
  refine ⟨c * a + d * e,c * b + d * f,?_⟩
  funext i; dsimp [planeState]; ring

theorem uniform_in_plane (T : Finset (Fin 4)) (h0 : 0 < T.card) (h4 : T.card < 4) :
    uniform = planeState T (Real.sqrt T.card / 2) (Real.sqrt (4 - (T.card : ℝ)) / 2) := by
  have hm : 0 < (T.card : ℝ) := by exact_mod_cast h0
  have hn : 0 < 4 - (T.card : ℝ) := by
    have h : (T.card : ℝ) < 4 := by exact_mod_cast h4
    linarith
  have hs := (Real.sqrt_pos.2 hm).ne'
  have ht := (Real.sqrt_pos.2 hn).ne'
  rw [plane_as_twoLevel]
  have ha : (Real.sqrt T.card / 2) / Real.sqrt T.card = (1 : ℝ) / 2 := by
    field_simp
  have hb : (Real.sqrt (4 - (T.card : ℝ)) / 2) / Real.sqrt (4 - (T.card : ℝ)) = (1 : ℝ) / 2 := by
    field_simp
  rw [ha,hb]
  funext i; simp [uniform, twoLevel]

theorem plane_invariant (T : Finset (Fin 4)) (h0 : 0 < T.card) (h4 : T.card < 4)
    (v : State) (hv : InPlane T v) : InPlane T (groverStep T v) := by
  obtain ⟨a,b,rfl⟩ := hv
  exact ⟨_,_,plane_step T h0 h4 a b⟩

theorem stateAt_in_plane (T : Finset (Fin 4)) (h0 : 0 < T.card) (h4 : T.card < 4) (k : ℕ) :
    InPlane T (stateAt T k) := by
  induction k with
  | zero => exact ⟨_,_,uniform_in_plane T h0 h4⟩
  | succ k ih => exact plane_invariant T h0 h4 _ ih

/-- The two orthonormal coordinates and invariant plane, not a basis of all of ℝ⁴. -/
theorem grover_subspace_2d_valid (T : Finset (Fin 4)) (h0 : 0 < T.card) (h4 : T.card < 4) :
    inner (marked T) (marked T) = 1 ∧ inner (unmarked T) (unmarked T) = 1 ∧
    inner (marked T) (unmarked T) = 0 ∧
    (∀ a b c d, planeState T a b = planeState T c d → a = c ∧ b = d) ∧
    (∀ v, InPlane T v → InPlane T (groverStep T v)) := by
  obtain ⟨hw,hb,hwb⟩ := plane_orthonormal T h0 h4
  exact ⟨hw,hb,hwb,plane_coordinates_unique T h0 h4,plane_invariant T h0 h4⟩

def rankOneOracle (T : Finset (Fin 4)) (v : State) : State :=
  fun i => v i - 2 * inner (marked T) v * marked T i

theorem oracle_on_plane (T : Finset (Fin 4)) (a b : ℝ) :
    multiTargetOracle T (planeState T a b) = planeState T (-a) b := by
  funext i
  by_cases h : i ∈ T <;> simp [multiTargetOracle, planeState, marked, unmarked, twoLevel, h]

theorem plane_rankOne_agrees (T : Finset (Fin 4)) (h0 : 0 < T.card) (h4 : T.card < 4)
    (v : State) (hv : InPlane T v) : multiTargetOracle T v = rankOneOracle T v := by
  obtain ⟨a,b,rfl⟩ := hv
  have h : inner (marked T) (planeState T a b) = a := by
    rw [inner_comm]; exact (plane_coordinates T h0 h4 a b).1
  rw [oracle_on_plane]
  funext i
  dsimp only [rankOneOracle]
  rw [h]
  dsimp [planeState]
  ring

theorem rankOne_not_general :
    multiTargetOracle {0,1} ![1,-1,0,0] ≠ rankOneOracle {0,1} ![1,-1,0,0] := by
  have hd : inner (marked {0,1}) ![1,-1,0,0] = 0 := by
    simp only [inner, Fin.sum_univ_four]
    norm_num [marked, twoLevel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff]
  intro h
  have he := congrFun h 0
  change (-1 : ℝ) = 1 - 2 * inner (marked {0,1}) ![1,-1,0,0]*(1 / Real.sqrt 2) at he
  rw [hd] at he
  norm_num at he

/-- Equality can also hold outside the symmetric plane: its sufficient condition is not an iff. -/
theorem rankOne_agrees_outside_plane :
    multiTargetOracle {0} ![0,1,-1,0] = rankOneOracle {0} ![0,1,-1,0] ∧
    ¬ InPlane {0} ![0,1,-1,0] := by
  have hd : inner (marked {0}) ![0,1,-1,0] = 0 := by
    simp only [inner, Fin.sum_univ_four]
    norm_num [marked, twoLevel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff]
  constructor
  · funext i
    dsimp only [rankOneOracle]
    rw [hd]
    fin_cases i <;> norm_num [multiTargetOracle, Fin.ext_iff]
  · rintro ⟨a,b,h⟩
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    norm_num [planeState, marked, unmarked, twoLevel, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_zero, Fin.ext_iff] at h1 h2
    linarith

theorem pair_one_period (k : ℕ) :
    amplitudePair 1 (k + 3) = (-(amplitudePair 1 k).1, -(amplitudePair 1 k).2) := by
  ext <;> simp [amplitudePair] <;> ring

theorem pair_three_period (k : ℕ) : amplitudePair 3 (k + 3) = amplitudePair 3 k := by
  ext <;> simp [amplitudePair] <;> ring

theorem period_three_mod (f : ℕ → ℝ) (h : ∀ k, f (k + 3) = f k) (k : ℕ) : f k = f (k % 3) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < 3
    · rw [Nat.mod_eq_of_lt hk]
    · have he : k - 3 + 3 = k := by omega
      have hi := ih (k - 3) (by omega)
      have hm : (k - 3) % 3 = k % 3 := by omega
      calc
        f k = f (k - 3) := by conv_lhs => rw [← he]; exact h (k - 3)
        _ = f (k % 3) := by rw [hi, hm]

theorem success_M1_all (T : Finset (Fin 4)) (h : T.card = 1) (k : ℕ) :
    successWeight T (stateAt T k) = if k % 3 = 1 then 1 else 1 / 4 := by
  rw [success_recurrence, h]
  norm_num only [Nat.cast_one, one_mul]
  have hp : ∀ j, (amplitudePair 1 (j + 3)).1 ^ 2 = (amplitudePair 1 j).1 ^ 2 := by
    intro j; rw [pair_one_period]; simp
  rw [period_three_mod (fun j => (amplitudePair 1 j).1 ^ 2) hp k]
  have hm : k % 3 < 3 := Nat.mod_lt _ (by omega)
  interval_cases hmod : k % 3 <;> norm_num [amplitudePair]

theorem success_M3_all (T : Finset (Fin 4)) (h : T.card = 3) (k : ℕ) :
    successWeight T (stateAt T k) = if k % 3 = 1 then 0 else 3 / 4 := by
  rw [success_recurrence, h]
  norm_num only [Nat.cast_ofNat]
  have hp : ∀ j, (amplitudePair 3 (j + 3)).1 ^ 2 = (amplitudePair 3 j).1 ^ 2 := by
    intro j; rw [pair_three_period]
  rw [period_three_mod (fun j => (amplitudePair 3 j).1 ^ 2) hp k]
  have hm : k % 3 < 3 := Nat.mod_lt _ (by omega)
  interval_cases hmod : k % 3 <;> norm_num [amplitudePair]


theorem success_M0_all (k : ℕ) : successWeight ∅ (stateAt ∅ k) = 0 := by
  simp [successWeight]

theorem success_M4_all (k : ℕ) : successWeight Finset.univ (stateAt Finset.univ k) = 1 := by
  have h := stateAt_normalized Finset.univ k
  simpa [successWeight, normSquared, inner, pow_two] using h

theorem M3_output (T : Finset (Fin 4)) (h : T.card = 3) :
    groverStep T uniform = twoLevel T 0 (-1) := by
  rw [step_uniform, h]; norm_num

theorem success_complement (T : Finset (Fin 4)) (v : State) :
    successWeight T v + successWeight Tᶜ v = normSquared v := by
  unfold successWeight normSquared inner
  simp only [← pow_two]
  exact Finset.sum_add_sum_compl T (fun i => (v i) ^ 2)

theorem M3_unmarked_success (T : Finset (Fin 4)) (h : T.card = 3) :
    successWeight Tᶜ (groverStep T uniform) = 1 := by
  have he := success_complement T (groverStep T uniform)
  rw [grover_targets_M3_overshoot T h, grover_step_preserves_norm, uniform_norm] at he
  simpa using he

structure QuantumGroverMultipleTargetsSuite : Prop where
  norm_preserved : ∀ T v, normSquared (groverStep T v) = normSquared v
  normalized_iterates : ∀ T k, normSquared (stateAt T k) = 1
  recurrence : ∀ T k, stateAt T k =
    twoLevel T (amplitudePair T.card k).1 (amplitudePair T.card k).2
  empty_fixed : ∀ k, stateAt ∅ k = uniform
  full_phase : ∀ k, stateAt Finset.univ k = fun i => (-1 : ℝ) ^ k * uniform i
  single_target : ∀ T, T.card = 1 → ∀ k,
    successWeight T (stateAt T k) = if k % 3 = 1 then 1 else 1 / 4
  half_stationary : ∀ T, T.card = 2 → ∀ k, successWeight T (stateAt T k) = 1 / 2
  three_targets : ∀ T, T.card = 3 → ∀ k,
    successWeight T (stateAt T k) = if k % 3 = 1 then 0 else 3 / 4
  overshoot : ∀ T, T.card = 3 → successWeight Tᶜ (groverStep T uniform) = 1
  plane_basis : ∀ T, 0 < T.card → T.card < 4 →
    inner (marked T) (marked T) = 1 ∧ inner (unmarked T) (unmarked T) = 1 ∧
      inner (marked T) (unmarked T) = 0
  plane_dynamics : ∀ T, 0 < T.card → T.card < 4 → ∀ a b,
    groverStep T (planeState T a b) =
      planeState T (rotationC T * a + rotationS T * b) (-rotationS T * a + rotationC T * b)
  plane_unique : ∀ T, 0 < T.card → T.card < 4 → ∀ a b c d,
    planeState T a b = planeState T c d → a = c ∧ b = d
  legacy_compatibility : ∀ t v, toLegacy (groverStep {itemIndex t} v) =
    QuantumGroverSearch.groverStep (QuantumGroverSearch.targetToBasis t) (toLegacy v)

theorem quantum_grover_multiple_targets_master_suite : QuantumGroverMultipleTargetsSuite := {
  norm_preserved := grover_step_preserves_norm
  normalized_iterates := stateAt_normalized
  recurrence := stateAt_twoLevel
  empty_fixed := stateAt_empty
  full_phase := stateAt_full
  single_target := success_M1_all
  half_stationary := grover_targets_M2_stationary
  three_targets := success_M3_all
  overshoot := M3_unmarked_success
  plane_basis := plane_orthonormal
  plane_dynamics := plane_step
  plane_unique := plane_coordinates_unique
  legacy_compatibility := singleton_step_legacy
}

end QuantumGroverMultipleTargets
