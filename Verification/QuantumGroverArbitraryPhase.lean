/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumGroverMultipleTargets
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Arbitrary phases for one marked item in four dimensions

The complex symmetric plane is invariant for all phase pairs. Our diffusion
convention is I + (exp(iψ)-1) P_s; at π this is the negative of the legacy
inversion about the mean. Exact one-step success for equal phases occurs precisely
when cos φ = -1; the canonical case already succeeds for one target out of four.
-/
noncomputable section
namespace QuantumGroverArbitraryPhase
open scoped BigOperators ComplexConjugate

abbrev State := Fin 4 → ℂ

def phase (φ : ℝ) : ℂ := Complex.exp (Complex.I * (φ : ℂ))
def hermitian (u v : State) : ℂ := ∑ i, conj (u i) * v i
def normSquared (v : State) : ℝ := ∑ i, Complex.normSq (v i)
def uniform : State := fun _ => 1 / 2

def oracle (ω : Fin 4) (z : ℂ) (v : State) : State :=
  fun i => if i = ω then z * v i else v i

def diffusion (z : ℂ) (v : State) : State :=
  fun i => v i + (z - 1) * (∑ j, v j) / 4

def phaseOracle (ω : Fin 4) (φ : ℝ) : State → State := oracle ω (phase φ)
def phaseDiffusion (ψ : ℝ) : State → State := diffusion (phase ψ)
def arbitraryGroverStep (ω : Fin 4) (φ ψ : ℝ) (v : State) : State :=
  phaseDiffusion ψ (phaseOracle ω φ v)

theorem phase_conj_mul (φ : ℝ) : conj (phase φ) * phase φ = 1 := by
  rw [phase, ← Complex.exp_conj, ← Complex.exp_add]
  simp

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]
@[simp] theorem phase_pi : phase Real.pi = -1 := by
  simpa [phase, mul_comm] using Complex.exp_pi_mul_I

theorem phase_conj (φ : ℝ) : conj (phase φ) = phase (-φ) := by
  simp [phase, ← Complex.exp_conj]

theorem phase_re (φ : ℝ) : (phase φ).re = Real.cos φ := by
  simp [phase, Complex.exp_re]

theorem hermitian_norm (v : State) : hermitian v v = (normSquared v : ℂ) := by
  simp [hermitian, normSquared, Complex.normSq_eq_conj_mul_self]

theorem oracle_inner (ω : Fin 4) (z : ℂ) (hz : conj z * z = 1) (u v : State) :
    hermitian (oracle ω z u) (oracle ω z v) = hermitian u v := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i = ω
  · simp only [oracle, h, if_true, map_mul]
    calc
      conj z * conj (u ω) * (z * v ω) = (conj z * z) * (conj (u ω) * v ω) := by ring
      _ = conj (u ω) * v ω := by rw [hz, one_mul]
  · simp [oracle, h]

theorem diffusion_inner_formula (z : ℂ) (u v : State) :
    hermitian (diffusion z u) (diffusion z v) = hermitian u v +
      (conj z * z - 1) * conj (∑ i, u i) * (∑ i, v i) / 4 := by
  simp [hermitian, diffusion, Fin.sum_univ_succ, map_add, map_mul, map_sub, map_ofNat]
  ring

theorem diffusion_inner (z : ℂ) (hz : conj z * z = 1) (u v : State) :
    hermitian (diffusion z u) (diffusion z v) = hermitian u v := by
  rw [diffusion_inner_formula, hz]
  simp

theorem arbitrary_grover_inner_preservation (ω : Fin 4) (φ ψ : ℝ) (u v : State) :
    hermitian (arbitraryGroverStep ω φ ψ u) (arbitraryGroverStep ω φ ψ v) =
      hermitian u v := by
  unfold arbitraryGroverStep phaseDiffusion phaseOracle
  rw [diffusion_inner _ (phase_conj_mul ψ), oracle_inner _ _ (phase_conj_mul φ)]

theorem arbitrary_grover_norm_preservation (ω : Fin 4) (φ ψ : ℝ) (v : State) :
    normSquared (arbitraryGroverStep ω φ ψ v) = normSquared v := by
  apply Complex.ofReal_injective
  simpa only [← hermitian_norm] using arbitrary_grover_inner_preservation ω φ ψ v v

theorem arbitrary_grover_l2_preservation (ω : Fin 4) (φ ψ : ℝ) (v : State) :
    (∑ i, ‖arbitraryGroverStep ω φ ψ v i‖ ^ 2) = ∑ i, ‖v i‖ ^ 2 := by
  simpa only [normSquared, Complex.normSq_eq_norm_sq] using
    arbitrary_grover_norm_preservation ω φ ψ v

theorem oracle_linear (ω : Fin 4) (z a b : ℂ) (u v : State) :
    oracle ω z (fun i => a * u i + b * v i) =
      fun i => a * oracle ω z u i + b * oracle ω z v i := by
  funext i
  by_cases h : i = ω <;> simp [oracle, h]
  ring

theorem diffusion_linear (z a b : ℂ) (u v : State) :
    diffusion z (fun i => a * u i + b * v i) =
      fun i => a * diffusion z u i + b * diffusion z v i := by
  funext i
  simp only [diffusion, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem diffusion_comp (z w : ℂ) (v : State) :
    diffusion z (diffusion w v) = diffusion (z * w) v := by
  funext i
  simp [diffusion, Fin.sum_univ_succ]
  ring

@[simp] theorem diffusion_one (v : State) : diffusion 1 v = v := by
  funext i; simp [diffusion]

theorem oracle_comp (ω : Fin 4) (z w : ℂ) (v : State) :
    oracle ω z (oracle ω w v) = oracle ω (z * w) v := by
  funext i; by_cases h : i = ω <;> simp [oracle, h, mul_assoc]

@[simp] theorem oracle_one (ω : Fin 4) (v : State) : oracle ω 1 v = v := by
  funext i; simp [oracle]

theorem oracle_adjoint (ω : Fin 4) (z : ℂ) (u v : State) :
    hermitian u (oracle ω z v) = hermitian (oracle ω (conj z) u) v := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i = ω <;> simp [oracle, h]
  ring

theorem diffusion_adjoint (z : ℂ) (u v : State) :
    hermitian u (diffusion z v) = hermitian (diffusion (conj z) u) v := by
  simp [hermitian, diffusion, Fin.sum_univ_succ, map_add, map_mul, map_sub, map_ofNat]
  ring

/-- The explicit adjoint is a two-sided inverse: the finite-dimensional unitarity identity. -/
theorem phase_operators_unitary (ω : Fin 4) (φ ψ : ℝ) (v : State) :
    phaseOracle ω (-φ) (phaseOracle ω φ v) = v ∧
    phaseOracle ω φ (phaseOracle ω (-φ) v) = v ∧
    phaseDiffusion (-ψ) (phaseDiffusion ψ v) = v ∧
    phaseDiffusion ψ (phaseDiffusion (-ψ) v) = v := by
  have hf := phase_conj_mul φ
  have hg := phase_conj_mul ψ
  simp only [phaseOracle, phaseDiffusion, ← phase_conj, oracle_comp, diffusion_comp]
  simp [hf, hg, mul_comm (phase φ) (conj (phase φ)),
    mul_comm (phase ψ) (conj (phase ψ))]

def twoLevel (ω : Fin 4) (a b : ℂ) : State := fun i => if i = ω then a else b

def InPlane (ω : Fin 4) (v : State) : Prop := ∃ a b : ℂ, v = twoLevel ω a b

theorem sum_twoLevel (ω : Fin 4) (a b : ℂ) : ∑ i, twoLevel ω a b i = a + 3 * b := by
  fin_cases ω <;> simp [twoLevel, Fin.sum_univ_succ] <;> ring

theorem norm_twoLevel (ω : Fin 4) (a b : ℂ) :
    normSquared (twoLevel ω a b) = Complex.normSq a + 3 * Complex.normSq b := by
  fin_cases ω <;> simp [normSquared, twoLevel, Fin.sum_univ_succ] <;> ring

theorem inner_twoLevel (ω : Fin 4) (a b c d : ℂ) :
    hermitian (twoLevel ω a b) (twoLevel ω c d) = conj a * c + 3 * conj b * d := by
  fin_cases ω <;> simp [hermitian, twoLevel, Fin.sum_univ_succ] <;> ring

theorem twoLevel_unique (ω : Fin 4) (a b c d : ℂ) (h : twoLevel ω a b = twoLevel ω c d) :
    a = c ∧ b = d := by
  have ha : a = c := by simpa [twoLevel] using congrFun h ω
  have hs := congrArg (fun v : State => ∑ i, v i) h
  rw [sum_twoLevel, sum_twoLevel, ha] at hs
  constructor
  · exact ha
  · linear_combination hs / 3

theorem plane_linear_closed (ω : Fin 4) (u v : State) (a b : ℂ)
    (hu : InPlane ω u) (hv : InPlane ω v) : InPlane ω (fun i => a * u i + b * v i) := by
  obtain ⟨c,d,rfl⟩ := hu
  obtain ⟨e,f,rfl⟩ := hv
  refine ⟨a*c+b*e, a*d+b*f, ?_⟩
  funext i
  by_cases h : i = ω <;> simp [twoLevel, h]

def marked (ω : Fin 4) : State := twoLevel ω 1 0
def unmarked (ω : Fin 4) : State := twoLevel ω 0 (1 / (Real.sqrt 3 : ℂ))
def planeState (ω : Fin 4) (a b : ℂ) : State := fun i => a * marked ω i + b * unmarked ω i

theorem plane_as_twoLevel (ω : Fin 4) (a b : ℂ) :
    planeState ω a b = twoLevel ω a (b / (Real.sqrt 3 : ℂ)) := by
  funext i; by_cases h : i = ω <;> simp [planeState, marked, unmarked, twoLevel, h, div_eq_mul_inv]

theorem plane_orthonormal (ω : Fin 4) :
    hermitian (marked ω) (marked ω) = 1 ∧
    hermitian (unmarked ω) (unmarked ω) = 1 ∧
    hermitian (marked ω) (unmarked ω) = 0 := by
  have hs : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hn : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)).ne'
  simp only [marked, unmarked, inner_twoLevel]
  norm_num
  field_simp
  linear_combination -hs

theorem inPlane_iff_normalized_span (ω : Fin 4) (v : State) :
    InPlane ω v ↔ ∃ a b : ℂ, v = planeState ω a b := by
  have hn : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)).ne'
  constructor
  · rintro ⟨a,b,rfl⟩
    refine ⟨a, b * (Real.sqrt 3 : ℂ), ?_⟩
    rw [plane_as_twoLevel, mul_div_cancel_right₀ _ hn]
  · rintro ⟨a,b,rfl⟩
    exact ⟨_,_,plane_as_twoLevel ω a b⟩

theorem oracle_twoLevel (ω : Fin 4) (z a b : ℂ) :
    oracle ω z (twoLevel ω a b) = twoLevel ω (z*a) b := by
  funext i; by_cases h : i = ω <;> simp [oracle, twoLevel, h]

theorem step_twoLevel (ω : Fin 4) (φ ψ : ℝ) (a b : ℂ) :
    arbitraryGroverStep ω φ ψ (twoLevel ω a b) =
      twoLevel ω (phase φ*a + (phase ψ-1)*(phase φ*a+3*b)/4)
        (b+(phase ψ-1)*(phase φ*a+3*b)/4) := by
  unfold arbitraryGroverStep phaseOracle phaseDiffusion
  rw [oracle_twoLevel]
  funext i
  simp only [diffusion, sum_twoLevel]
  by_cases h : i = ω <;> simp [twoLevel, h]

/-- No equality assumption on the phases is needed for complex-plane invariance. -/
theorem arbitrary_grover_plane_invariant (ω : Fin 4) (φ ψ : ℝ) (v : State)
    (hv : InPlane ω v) : InPlane ω (arbitraryGroverStep ω φ ψ v) := by
  obtain ⟨a,b,rfl⟩ := hv
  exact ⟨_,_,step_twoLevel ω φ ψ a b⟩

theorem arbitrary_grover_phase_matching_invariant (ω : Fin 4) (φ : ℝ) (v : State)
    (hv : InPlane ω v) : InPlane ω (arbitraryGroverStep ω φ φ v) :=
  arbitrary_grover_plane_invariant ω φ φ v hv

theorem unequal_phases_still_invariant (ω : Fin 4) :
    (0 : ℝ) ≠ Real.pi ∧ ∀ v, InPlane ω v →
      InPlane ω (arbitraryGroverStep ω 0 Real.pi v) := by
  exact ⟨ne_of_lt Real.pi_pos, arbitrary_grover_plane_invariant ω 0 Real.pi⟩

def stateAt (ω : Fin 4) (φ ψ : ℝ) : ℕ → State
  | 0 => uniform
  | k+1 => arbitraryGroverStep ω φ ψ (stateAt ω φ ψ k)

theorem uniform_twoLevel (ω : Fin 4) : uniform = twoLevel ω (1/2) (1/2) := by
  funext i; simp [uniform, twoLevel]

theorem uniform_norm : normSquared uniform = 1 := by
  norm_num [normSquared, uniform, Fin.sum_univ_succ, Complex.normSq_apply]

theorem stateAt_normalized (ω : Fin 4) (φ ψ : ℝ) (k : ℕ) :
    normSquared (stateAt ω φ ψ k) = 1 := by
  induction k with
  | zero => exact uniform_norm
  | succ k ih => rw [stateAt, arbitrary_grover_norm_preservation, ih]

theorem stateAt_in_plane (ω : Fin 4) (φ ψ : ℝ) (k : ℕ) :
    InPlane ω (stateAt ω φ ψ k) := by
  induction k with
  | zero => exact ⟨_,_,uniform_twoLevel ω⟩
  | succ k ih => exact arbitrary_grover_plane_invariant ω φ ψ _ ih

theorem equal_phase_uniform (ω : Fin 4) (φ : ℝ) :
    arbitraryGroverStep ω φ φ uniform =
      twoLevel ω ((phase φ ^ 2 + 6 * phase φ - 3)/8) ((phase φ+1)^2/8) := by
  rw [uniform_twoLevel ω, step_twoLevel]
  congr 1 <;> ring

def successWeight (ω : Fin 4) (v : State) : ℝ := Complex.normSq (v ω)

theorem success_twoLevel (ω : Fin 4) (a b : ℂ) :
    successWeight ω (twoLevel ω a b) = Complex.normSq a := by simp [successWeight, twoLevel]

theorem phase_normSq (φ : ℝ) : Complex.normSq (phase φ) = 1 := by
  apply Complex.ofReal_injective
  rw [Complex.normSq_eq_conj_mul_self, phase_conj_mul]
  rfl

theorem unmarked_weight (φ : ℝ) :
    Complex.normSq ((phase φ + 1)^2/8) = (1 + Real.cos φ)^2/16 := by
  have h : Complex.normSq (phase φ+1) = 2*(1+Real.cos φ) := by
    rw [Complex.normSq_add, phase_normSq]
    simp [phase_re]
    ring
  rw [map_div₀, map_pow, h]
  norm_num
  ring

theorem arbitrary_grover_success_formula (ω : Fin 4) (φ : ℝ) :
    successWeight ω (arbitraryGroverStep ω φ φ uniform) =
      1 - 3 * (1 + Real.cos φ)^2/16 := by
  have hn := arbitrary_grover_norm_preservation ω φ φ uniform
  rw [uniform_norm, equal_phase_uniform, norm_twoLevel, unmarked_weight] at hn
  rw [equal_phase_uniform, success_twoLevel]
  linarith

theorem arbitrary_grover_success_iff (ω : Fin 4) (φ : ℝ) :
    successWeight ω (arbitraryGroverStep ω φ φ uniform) = 1 ↔ Real.cos φ = -1 := by
  rw [arbitrary_grover_success_formula]
  constructor
  · intro h
    nlinarith [sq_nonneg (1 + Real.cos φ)]
  · intro h; rw [h]; norm_num

/-- The exact phase here is the canonical π; no noncanonical one-step improvement is asserted. -/
theorem arbitrary_grover_zero_overshoot_exact (ω : Fin 4) :
    successWeight ω (arbitraryGroverStep ω Real.pi Real.pi uniform) = 1 ∧
      ∃ φ : ℝ, successWeight ω (arbitraryGroverStep ω φ φ uniform) = 1 := by
  have h : successWeight ω (arbitraryGroverStep ω Real.pi Real.pi uniform) = 1 := by
    rw [arbitrary_grover_success_iff, Real.cos_pi]
  exact ⟨h, Real.pi, h⟩

theorem arbitrary_grover_linear (ω : Fin 4) (φ ψ : ℝ) (a b : ℂ) (u v : State) :
    arbitraryGroverStep ω φ ψ (fun i => a * u i + b * v i) =
      fun i => a * arbitraryGroverStep ω φ ψ u i + b * arbitraryGroverStep ω φ ψ v i := by
  unfold arbitraryGroverStep phaseOracle phaseDiffusion
  rw [oracle_linear, diffusion_linear]

def adjointStep (ω : Fin 4) (φ ψ : ℝ) (v : State) : State :=
  phaseOracle ω (-φ) (phaseDiffusion (-ψ) v)

theorem arbitrary_grover_adjoint (ω : Fin 4) (φ ψ : ℝ) (u v : State) :
    hermitian u (arbitraryGroverStep ω φ ψ v) = hermitian (adjointStep ω φ ψ u) v := by
  unfold arbitraryGroverStep adjointStep phaseOracle phaseDiffusion
  rw [diffusion_adjoint, oracle_adjoint, phase_conj, phase_conj]

theorem arbitrary_grover_unitary (ω : Fin 4) (φ ψ : ℝ) (v : State) :
    adjointStep ω φ ψ (arbitraryGroverStep ω φ ψ v) = v ∧
      arbitraryGroverStep ω φ ψ (adjointStep ω φ ψ v) = v := by
  constructor
  · unfold adjointStep arbitraryGroverStep
    rw [(phase_operators_unitary ω φ ψ _).2.2.1, (phase_operators_unitary ω φ ψ v).1]
  · unfold adjointStep arbitraryGroverStep
    rw [(phase_operators_unitary ω φ ψ _).2.1, (phase_operators_unitary ω φ ψ v).2.2.2]

theorem plane_coordinates_unique (ω : Fin 4) (a b c d : ℂ)
    (h : planeState ω a b = planeState ω c d) : a = c ∧ b = d := by
  rw [plane_as_twoLevel, plane_as_twoLevel] at h
  obtain ⟨ha,hb⟩ := twoLevel_unique ω _ _ _ _ h
  have hn : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)).ne'
  exact ⟨ha, (div_left_inj' hn).mp hb⟩

theorem arbitrary_grover_success_continuous (ω : Fin 4) :
    Continuous (fun φ : ℝ => successWeight ω (arbitraryGroverStep ω φ φ uniform)) := by
  simp_rw [arbitrary_grover_success_formula]
  exact continuous_const.sub ((continuous_const.mul
    ((continuous_const.add Real.continuous_cos).pow 2)).div_const 16)

def embed (v : Fin 4 → ℝ) : State := fun i => (v i : ℂ)
def embedLegacy (v : QuantumGroverSearch.QState4) : State :=
  embed (QuantumGroverMultipleTargets.fromLegacy v)

theorem phase_oracle_pi (ω : Fin 4) (v : Fin 4 → ℝ) :
    phaseOracle ω Real.pi (embed v) =
      embed (QuantumGroverMultipleTargets.multiTargetOracle {ω} v) := by
  funext i
  by_cases h : i = ω <;>
    simp [phaseOracle, phase_pi, oracle, embed, QuantumGroverMultipleTargets.multiTargetOracle, h]

/-- At π this diffusion is the negative of the legacy inversion about the mean. -/
theorem phase_diffusion_pi (v : Fin 4 → ℝ) :
    phaseDiffusion Real.pi (embed v) = -embed (QuantumGroverMultipleTargets.diffusion v) := by
  funext i
  simp [phaseDiffusion, phase_pi, diffusion, embed, QuantumGroverMultipleTargets.diffusion]
  ring

theorem arbitrary_grover_reduction_to_canonical (ω : Fin 4) (v : Fin 4 → ℝ) :
    arbitraryGroverStep ω Real.pi Real.pi (embed v) =
      -embed (QuantumGroverMultipleTargets.groverStep {ω} v) := by
  unfold arbitraryGroverStep
  rw [phase_oracle_pi, phase_diffusion_pi]
  rfl

theorem arbitrary_grover_reduction_to_legacy (t : QuantumGroverSearch.TargetItem)
    (v : QuantumGroverSearch.QState4) :
    arbitraryGroverStep (QuantumGroverMultipleTargets.itemIndex t) Real.pi Real.pi (embedLegacy v) =
      -embedLegacy (QuantumGroverSearch.groverStep (QuantumGroverSearch.targetToBasis t) v) := by
  have h := congrArg QuantumGroverMultipleTargets.fromLegacy
    (QuantumGroverMultipleTargets.singleton_step_legacy t
      (QuantumGroverMultipleTargets.fromLegacy v))
  rw [QuantumGroverMultipleTargets.state_roundtrip,
    QuantumGroverMultipleTargets.legacy_roundtrip] at h
  unfold embedLegacy
  rw [arbitrary_grover_reduction_to_canonical, h]

theorem global_phase_weights (z : ℂ) (hz : Complex.normSq z = 1) (v : State) (i : Fin 4) :
    Complex.normSq (z * v i) = Complex.normSq (v i) := by rw [map_mul, hz, one_mul]

theorem canonical_measurement_weights (ω : Fin 4) (v : Fin 4 → ℝ) (i : Fin 4) :
    Complex.normSq (arbitraryGroverStep ω Real.pi Real.pi (embed v) i) =
      (QuantumGroverMultipleTargets.groverStep {ω} v i)^2 := by
  rw [arbitrary_grover_reduction_to_canonical]
  simp [embed, Complex.normSq_apply, pow_two]

theorem canonical_uniform_signed (ω : Fin 4) :
    arbitraryGroverStep ω Real.pi Real.pi uniform = -marked ω := by
  rw [equal_phase_uniform, phase_pi]
  funext i
  by_cases h : i = ω <;> norm_num [twoLevel, marked, h]

theorem canonical_sign_not_literal (ω : Fin 4) :
    arbitraryGroverStep ω Real.pi Real.pi uniform ≠ marked ω := by
  rw [canonical_uniform_signed]
  intro h
  have hh := congrFun h ω
  norm_num [marked, twoLevel] at hh

/-- All fields concern one marked item in dimension four, not general amplitude amplification. -/
structure QuantumGroverArbitraryPhaseSuite : Prop where
  linearity : ∀ ω φ ψ a b u v, arbitraryGroverStep ω φ ψ (fun i => a*u i+b*v i) =
    fun i => a*arbitraryGroverStep ω φ ψ u i+b*arbitraryGroverStep ω φ ψ v i
  adjoint : ∀ ω φ ψ u v, hermitian u (arbitraryGroverStep ω φ ψ v) =
    hermitian (adjointStep ω φ ψ u) v
  unitary : ∀ ω φ ψ v, adjointStep ω φ ψ (arbitraryGroverStep ω φ ψ v) = v ∧
    arbitraryGroverStep ω φ ψ (adjointStep ω φ ψ v) = v
  norm_preservation : ∀ ω φ ψ v, normSquared (arbitraryGroverStep ω φ ψ v) = normSquared v
  orthonormal_plane : ∀ ω, hermitian (marked ω) (marked ω) = 1 ∧
    hermitian (unmarked ω) (unmarked ω) = 1 ∧ hermitian (marked ω) (unmarked ω) = 0
  plane_invariance : ∀ ω φ ψ v, InPlane ω v → InPlane ω (arbitraryGroverStep ω φ ψ v)
  exact_probability : ∀ ω φ, successWeight ω (arbitraryGroverStep ω φ φ uniform) =
    1 - 3*(1+Real.cos φ)^2/16
  exact_success_criterion : ∀ ω φ,
    successWeight ω (arbitraryGroverStep ω φ φ uniform) = 1 ↔ Real.cos φ = -1
  success_at_pi : ∀ ω, successWeight ω (arbitraryGroverStep ω Real.pi Real.pi uniform) = 1
  canonical_bridge : ∀ ω v, arbitraryGroverStep ω Real.pi Real.pi (embed v) =
    -embed (QuantumGroverMultipleTargets.groverStep {ω} v)
  legacy_bridge : ∀ t v,
    arbitraryGroverStep (QuantumGroverMultipleTargets.itemIndex t) Real.pi Real.pi (embedLegacy v) =
      -embedLegacy (QuantumGroverSearch.groverStep (QuantumGroverSearch.targetToBasis t) v)

theorem quantum_grover_arbitrary_phase_master_suite : QuantumGroverArbitraryPhaseSuite where
  linearity := arbitrary_grover_linear
  adjoint := arbitrary_grover_adjoint
  unitary := arbitrary_grover_unitary
  norm_preservation := arbitrary_grover_norm_preservation
  orthonormal_plane := plane_orthonormal
  plane_invariance := arbitrary_grover_plane_invariant
  exact_probability := arbitrary_grover_success_formula
  exact_success_criterion := arbitrary_grover_success_iff
  success_at_pi := fun ω => (arbitrary_grover_zero_overshoot_exact ω).1
  canonical_bridge := arbitrary_grover_reduction_to_canonical
  legacy_bridge := arbitrary_grover_reduction_to_legacy

end QuantumGroverArbitraryPhase
