/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumPOVMNaimarkDilation
import Verification.QuantumNoBroadcastingMixed
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Exact finite-dimensional tomography. Probabilities are theoretical, not sample frequencies. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
namespace QuantumPOVMInformationallyComplete

abbrev Q (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
/-- A separate type permits the Hilbert--Schmidt norm instead of the matrix operator norm. -/
def HermMat (d : ℕ) := selfAdjoint (Q d)
instance (d : ℕ) : AddCommGroup (HermMat d) := inferInstanceAs (AddCommGroup (selfAdjoint (Q d)))
instance (d : ℕ) : Module ℝ (HermMat d) := inferInstanceAs (Module ℝ (selfAdjoint (Q d)))

def val {d : ℕ} (X : HermMat d) : Q d := X.val
@[ext] theorem herm_ext {d : ℕ} {X Y : HermMat d} (h : val X = val Y) : X = Y := Subtype.ext h
@[simp] theorem val_add {d : ℕ} (X Y : HermMat d) : val (X + Y) = val X + val Y := rfl
@[simp] theorem val_smul {d : ℕ} (a : ℝ) (X : HermMat d) : val (a • X) = a • val X := rfl
@[simp] theorem val_zero {d : ℕ} : val (0 : HermMat d) = 0 := rfl

def valLM (d : ℕ) : HermMat d →ₗ[ℝ] Q d where
  toFun := val
  map_add' := val_add
  map_smul' := val_smul

instance (d : ℕ) : FiniteDimensional ℝ (HermMat d) :=
  FiniteDimensional.of_injective (valLM d) (fun _ _ h => herm_ext h)

def hs_inner {d : ℕ} (A B : HermMat d) : ℝ := (Matrix.trace (val A * val B)).re

theorem val_hermitian {d : ℕ} (A : HermMat d) : (val A).conjTranspose = val A := A.property

abbrev hsCore (d : ℕ) : InnerProductSpace.Core ℝ (HermMat d) where
  inner := hs_inner
  conj_inner_symm A B := by
    change (Matrix.trace (val B * val A)).re = (Matrix.trace (val A * val B)).re
    rw [Matrix.trace_mul_comm]
  re_inner_nonneg A := by
    have h := (Matrix.posSemidef_conjTranspose_mul_self (val A)).trace_nonneg
    rw [val_hermitian] at h
    exact (Complex.nonneg_iff.mp h).1
  add_left A B C := by simp [hs_inner, Matrix.add_mul, Matrix.trace_add]
  smul_left A B r := by simp [hs_inner, Matrix.trace_smul]
  definite A h := by
    apply herm_ext
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    rw [val_hermitian]
    have hp := (Matrix.posSemidef_conjTranspose_mul_self (val A)).trace_nonneg
    rw [val_hermitian] at hp
    apply Complex.ext
    · exact h
    · exact (Complex.nonneg_iff.mp hp).2.symm

instance (d : ℕ) : NormedAddCommGroup (HermMat d) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (HermMat d) _ _ _ (hsCore d)
instance (d : ℕ) : InnerProductSpace ℝ (HermMat d) := InnerProductSpace.ofCore (hsCore d).toCore

abbrev POVM := QuantumPOVMNaimarkDilation.FinitePOVM

def effect {d k : ℕ} (E : POVM d k) (m : Fin k) : HermMat d :=
  ⟨E.effects m, (E.pos_semidef m).isHermitian⟩
def is_ic_povm {d k : ℕ} (E : POVM d k) : Prop :=
  Submodule.span ℝ (Set.range (effect E)) = ⊤

def measurement {d k : ℕ} (E : POVM d k) : HermMat d →ₗ[ℝ] (Fin k → ℝ) where
  toFun X m := hs_inner X (effect E m)
  map_add' X Y := by ext m; simp [hs_inner, Matrix.add_mul, Matrix.trace_add]
  map_smul' a X := by ext m; simp [hs_inner, Matrix.trace_smul]

def frame_operator {d k : ℕ} (E : POVM d k) : HermMat d →ₗ[ℝ] HermMat d :=
  ∑ m : Fin k, ((LinearMap.proj m).comp (measurement E)).smulRight (effect E m)



@[simp] theorem hs_eq_inner {d : ℕ} (X Y : HermMat d) : hs_inner X Y = inner ℝ X Y := rfl

lemma measurement_zero_iff {d k : ℕ} (E : POVM d k) (X : HermMat d) :
    measurement E X = 0 ↔ X ∈ (Submodule.span ℝ (Set.range (effect E)))ᗮ := by
  rw [Submodule.mem_orthogonal']
  constructor
  · intro h Y hY
    induction hY using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, rfl⟩ := hy
      exact congrFun h m
    | zero => simp
    | add y z _ _ hy hz => simp [inner_add_right, hy, hz]
    | smul a y _ hy => simp [inner_smul_right, hy]
  · intro h
    funext m
    exact h _ (Submodule.subset_span ⟨m, rfl⟩)

theorem ic_povm_iff_injective {d k : ℕ} (E : POVM d k) :
    is_ic_povm E ↔ Function.Injective (measurement E) := by
  rw [is_ic_povm, ← Submodule.orthogonal_eq_bot_iff]
  constructor
  · intro h
    apply (measurement E).ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro X hX
    have hx := (measurement_zero_iff E X).mp hX
    simpa [h] using hx
  · intro h
    apply (Submodule.eq_bot_iff _).mpr
    intro X hX
    apply h
    simpa using (measurement_zero_iff E X).mpr hX

@[simp] theorem frame_operator_apply {d k : ℕ} (E : POVM d k) (X : HermMat d) :
    frame_operator E X = ∑ m, hs_inner X (effect E m) • effect E m := by
  simp [frame_operator, measurement]

theorem frame_operator_quadratic {d k : ℕ} (E : POVM d k) (X : HermMat d) :
    hs_inner X (frame_operator E X) = ∑ m, (hs_inner X (effect E m)) ^ 2 := by
  simp [inner_sum, inner_smul_right, pow_two]

theorem frame_operator_pos_def {d k : ℕ} (E : POVM d k) (h : is_ic_povm E)
    (X : HermMat d) (hX : X ≠ 0) : 0 < hs_inner X (frame_operator E X) := by
  rw [frame_operator_quadratic]
  have hn : ∃ m, hs_inner X (effect E m) ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hX
    apply (ic_povm_iff_injective E).mp h
    ext m
    simpa [measurement] using hn m
  obtain ⟨m, hm⟩ := hn
  exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨m, Finset.mem_univ m, sq_pos_of_ne_zero hm⟩

theorem frame_operator_invertible {d k : ℕ} (E : POVM d k) (h : is_ic_povm E) :
    Function.Bijective (frame_operator E) := by
  have hinj : Function.Injective (frame_operator E) := by
    apply (frame_operator E).ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro X hx
    by_contra hn
    have hp := frame_operator_pos_def E h X hn
    have hz : frame_operator E X = 0 := hx
    simp [hz] at hp
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

def frame_equiv {d k : ℕ} (E : POVM d k) (h : is_ic_povm E) : HermMat d ≃ₗ[ℝ] HermMat d :=
  LinearEquiv.ofBijective (frame_operator E) (frame_operator_invertible E h)

def dual_frame {d k : ℕ} (E : POVM d k) (h : is_ic_povm E) (m : Fin k) : HermMat d :=
  (frame_equiv E h).symm (effect E m)

theorem dual_frame_reconstruction_identity {d k : ℕ} (E : POVM d k) (h : is_ic_povm E)
    (X : HermMat d) : X = ∑ m, hs_inner X (effect E m) • dual_frame E h m := by
  calc
    X = (frame_equiv E h).symm (frame_operator E X) := ((frame_equiv E h).symm_apply_apply X).symm
    _ = _ := by rw [frame_operator_apply, map_sum]; simp [dual_frame]



/-- Multiplication by i identifies skew-adjoint and self-adjoint matrices over the reals. -/
def skewToHerm (d : ℕ) : skewAdjoint (Q d) →ₗ[ℝ] HermMat d where
  toFun X := ⟨Complex.I • X.val, by
    change star (Complex.I • X.val) = Complex.I • X.val
    rw [star_smul, Complex.star_def, Complex.conj_I, X.property]
    simp⟩
  map_add' X Y := by apply herm_ext; simp [val, smul_add]
  map_smul' r X := by apply herm_ext; exact smul_comm _ _ _

def hermToSkew (d : ℕ) : HermMat d →ₗ[ℝ] skewAdjoint (Q d) where
  toFun X := ⟨(-Complex.I) • val X, by
    change star ((-Complex.I) • val X) = -((-Complex.I) • val X)
    rw [star_smul, star_neg, Complex.star_def, Complex.conj_I]
    change - -Complex.I • (val X).conjTranspose = _
    rw [val_hermitian]; simp⟩
  map_add' X Y := by apply Subtype.ext; simp [smul_add]
  map_smul' r X := by apply Subtype.ext; exact smul_comm _ _ _

def skewHermEquiv (d : ℕ) : skewAdjoint (Q d) ≃ₗ[ℝ] HermMat d :=
  LinearEquiv.ofLinearMap (skewToHerm d) (hermToSkew d)
    (by ext X : 1; apply herm_ext; simp [skewToHerm, hermToSkew, val, smul_smul])
    (by ext X : 1; apply Subtype.ext; simp [skewToHerm, hermToSkew, val, smul_smul])

theorem herm_finrank (d : ℕ) : Module.finrank ℝ (HermMat d) = d ^ 2 := by
  let : FiniteDimensional ℝ (selfAdjoint (Q d)) :=
    FiniteDimensional.of_injective (selfAdjoint.submodule ℝ (Q d)).subtype Subtype.val_injective
  let : FiniteDimensional ℝ (skewAdjoint (Q d)) :=
    FiniteDimensional.of_injective (skewAdjoint.submodule ℝ (Q d)).subtype Subtype.val_injective
  have h := (StarModule.decomposeProdAdjoint ℝ (Q d)).finrank_eq
  have he := (skewHermEquiv d).finrank_eq
  have hh : Module.finrank ℝ (selfAdjoint (Q d)) = Module.finrank ℝ (HermMat d) := rfl
  rw [Module.finrank_prod, hh, he] at h
  simp only [Q, Module.finrank_matrix, Fintype.card_fin, Complex.finrank_real_complex] at h
  nlinarith

theorem ic_povm_outcome_bound {d k : ℕ} (E : POVM d k) (h : is_ic_povm E) : d ^ 2 ≤ k := by
  have hb := LinearMap.finrank_le_finrank_of_injective ((ic_povm_iff_injective E).mp h)
  simpa [herm_finrank, Module.finrank_pi] using hb

/-- Probabilities are real: the imaginary part of the trace vanishes. -/
theorem density_probability_nonneg {d k : ℕ} (E : POVM d k) (ρ : Q d)
    (hρ : ρ.PosSemidef) (m : Fin k) : 0 ≤ (Matrix.trace (ρ * E.effects m)).re := by
  let B := QuantumPOVMNaimarkDilation.sqrt_effects E m
  have hb : B * B = E.effects m := QuantumPOVMNaimarkDilation.sqrt_square E m
  have hh : B.conjTranspose = B := QuantumPOVMNaimarkDilation.sqrt_hermitian E m
  have hp := (hρ.mul_mul_conjTranspose_same B).trace_nonneg
  rw [hh, Matrix.trace_mul_cycle, hb] at hp
  rw [Matrix.trace_mul_comm] at hp
  exact (Complex.nonneg_iff.mp hp).1

theorem quantum_state_tomography {d k : ℕ} (E : POVM d k) (h : is_ic_povm E)
    (ρ : Q d) (hρ : QuantumNoBroadcastingMixed.IsDensityMatrix ρ) :
    (∀ m, 0 ≤ (Matrix.trace (ρ * E.effects m)).re) ∧
    (∑ m, (Matrix.trace (ρ * E.effects m)).re) = 1 ∧
    (⟨ρ, hρ.1.isHermitian⟩ : HermMat d) =
      ∑ m, (Matrix.trace (ρ * E.effects m)).re • dual_frame E h m := by
  refine ⟨density_probability_nonneg E ρ hρ.1, ?_, ?_⟩
  · rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.mul_sum, E.completeness,
      Matrix.mul_one, hρ.2]
    rfl
  · exact dual_frame_reconstruction_identity E h ⟨ρ, hρ.1.isHermitian⟩



/-- A quarter of I + x sigma_x + y sigma_y + z sigma_z. -/
def blochEffect (x y z : ℝ) : Q 2 :=
  !![(1 + (z : ℂ)) / 4, ((x : ℂ) - y * Complex.I) / 4;
     ((x : ℂ) + y * Complex.I) / 4, (1 - (z : ℂ)) / 4]

theorem bloch_hermitian (x y z : ℝ) : (blochEffect x y z).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blochEffect, Matrix.conjTranspose_apply, sub_eq_add_neg]

theorem bloch_square (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    blochEffect x y z * blochEffect x y z = (1 / 2 : ℂ) • blochEffect x y z := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [blochEffect, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im] <;> nlinarith

theorem bloch_positive (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    (blochEffect x y z).PosSemidef := by
  have hh := bloch_hermitian x y z
  have hp := (Matrix.posSemidef_conjTranspose_mul_self (blochEffect x y z)).smul
    (show (0 : ℂ) ≤ 2 by norm_num)
  rw [hh, bloch_square x y z h, smul_smul] at hp
  norm_num at hp
  exact hp

def tetraScale : ℝ := (Real.sqrt 3)⁻¹

theorem tetraScale_square : tetraScale ^ 2 = 1 / 3 := by
  rw [tetraScale, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

def tetraEffect : Fin 4 → Q 2 :=
  ![blochEffect tetraScale tetraScale tetraScale,
    blochEffect tetraScale (-tetraScale) (-tetraScale),
    blochEffect (-tetraScale) tetraScale (-tetraScale),
    blochEffect (-tetraScale) (-tetraScale) tetraScale]

def qubitTetrahedron : POVM 2 4 where
  effects := tetraEffect
  pos_semidef m := by
    fin_cases m <;> apply bloch_positive <;> simp [tetraScale_square] <;> norm_num
  completeness := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [tetraEffect, blochEffect, Fin.sum_univ_succ] <;> ring

/-- The four effects have the tetrahedral frame operator, on all complex matrices. -/
theorem tetra_frame_formula (A : Q 2) :
    (∑ m : Fin 4, Matrix.trace (A * tetraEffect m) • tetraEffect m) =
      (1 / 6 : ℂ) • (A + Matrix.trace A • (1 : Q 2)) := by
  have hs := tetraScale_square
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [tetraEffect, blochEffect, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im] <;>
    ring_nf <;> rw [hs] <;> ring



theorem hermitian_trace_real {d : ℕ} (A B : HermMat d) :
    ((hs_inner A B : ℝ) : ℂ) = Matrix.trace (val A * val B) := by
  apply Complex.conj_eq_iff_re.mp
  change star (Matrix.trace (val A * val B)) = _
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    val_hermitian, val_hermitian, Matrix.trace_mul_comm]

theorem qubit_tetrahedron_ic_povm : is_ic_povm qubitTetrahedron := by
  apply (ic_povm_iff_injective _).mpr
  apply (measurement qubitTetrahedron).ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro X hX
  have hz (m : Fin 4) : Matrix.trace (val X * tetraEffect m) = 0 := by
    have hm : hs_inner X (effect qubitTetrahedron m) = 0 := congrFun hX m
    have hh := hermitian_trace_real X (effect qubitTetrahedron m)
    rw [hm] at hh
    exact hh.symm
  have hsum := tetra_frame_formula (val X)
  simp only [hz, zero_smul, Finset.sum_const_zero] at hsum
  have ha : val X + Matrix.trace (val X) • (1 : Q 2) = 0 :=
    (smul_eq_zero.mp hsum.symm).resolve_left (by norm_num)
  have ht : Matrix.trace (val X) = 0 := by
    have ht := congrArg Matrix.trace ha
    simp [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one] at ht
    linear_combination (1 / 3 : ℂ) * ht
  apply herm_ext
  simpa [ht] using ha

/-- The effects are half of trace-one projectors. -/
theorem tetra_projector (m : Fin 4) :
    ((2 : ℂ) • tetraEffect m) * ((2 : ℂ) • tetraEffect m) = (2 : ℂ) • tetraEffect m ∧
    Matrix.trace ((2 : ℂ) • tetraEffect m) = 1 := by
  constructor
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hh : tetraEffect m * tetraEffect m = (1 / 2 : ℂ) • tetraEffect m := by
      fin_cases m <;> apply bloch_square <;> simp [tetraScale_square] <;> norm_num
    rw [hh, smul_smul]; norm_num
  · fin_cases m <;> norm_num [tetraEffect, blochEffect, Matrix.trace, Fin.sum_univ_succ] <;> ring

theorem tetra_symmetric_overlap (i j : Fin 4) :
    Matrix.trace (tetraEffect i * tetraEffect j) = if i = j then 1 / 4 else 1 / 12 := by
  have hs := tetraScale_square
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [tetraEffect, blochEffect, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im] <;> ring_nf <;> rw [hs] <;> norm_num

/-- Any d-outcome measurement fails to be IC in dimension at least two. -/
theorem onb_measurement_not_ic {d : ℕ} (hd : 2 ≤ d) (E : POVM d d) : ¬ is_ic_povm E := by
  intro h
  have hb := ic_povm_outcome_bound E h
  nlinarith

/-- Relabeling outcomes transports the effects without changing the measurement. -/
def relabel {d k : ℕ} (E : POVM d k) (π : Fin k ≃ Fin k) : POVM d k where
  effects m := E.effects (π m)
  pos_semidef m := E.pos_semidef (π m)
  completeness := by rw [Equiv.sum_comp π]; exact E.completeness

theorem relabel_ic {d k : ℕ} (E : POVM d k) (π : Fin k ≃ Fin k) :
    is_ic_povm (relabel E π) ↔ is_ic_povm E := by
  unfold is_ic_povm
  have hr : Set.range (effect (relabel E π)) = Set.range (effect E) := by
    change Set.range (effect E ∘ π) = Set.range (effect E)
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨π i, rfl⟩
    · rintro ⟨i, rfl⟩; obtain ⟨j, rfl⟩ := π.surjective i; exact ⟨j, rfl⟩
  rw [hr]

theorem relabel_frame {d k : ℕ} (E : POVM d k) (π : Fin k ≃ Fin k) (X : HermMat d) :
    frame_operator (relabel E π) X = frame_operator E X := by
  simp only [frame_operator_apply]
  exact Equiv.sum_comp π (fun m => hs_inner X (effect E m) • effect E m)



def scalarPOVM : POVM 1 1 where
  effects _ := 1
  pos_semidef _ := Matrix.PosSemidef.one
  completeness := by simp

theorem scalar_ic : is_ic_povm scalarPOVM := by
  apply (ic_povm_iff_injective _).mpr
  apply (measurement scalarPOVM).ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro X hX
  have hz : hs_inner X (effect scalarPOVM 0) = 0 := congrFun hX 0
  have ht := hermitian_trace_real X (effect scalarPOVM 0)
  rw [hz] at ht
  apply herm_ext
  ext i j
  fin_cases i; fin_cases j
  simpa [effect, scalarPOVM, val, Matrix.trace, Fin.sum_univ_succ] using ht.symm

def basisPOVM (d : ℕ) : POVM d d where
  effects m := Matrix.diagonal (fun i => if i = m then 1 else 0)
  pos_semidef m := Matrix.PosSemidef.diagonal (by intro i; dsimp; split_ifs <;> simp)
  completeness := by
    ext i j
    simp [Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]

def phasePlus : Q 2 := (2 : ℂ) • blochEffect 1 0 0
def phaseMinus : Q 2 := (2 : ℂ) • blochEffect (-1) 0 0

theorem phase_pair_density : QuantumNoBroadcastingMixed.IsDensityMatrix phasePlus ∧
    QuantumNoBroadcastingMixed.IsDensityMatrix phaseMinus := by
  constructor
  · refine ⟨(bloch_positive 1 0 0 (by norm_num)).smul (show (0 : ℂ) ≤ 2 by norm_num), ?_⟩
    norm_num [phasePlus, blochEffect, Matrix.trace, Fin.sum_univ_succ]
  · refine ⟨(bloch_positive (-1) 0 0 (by norm_num)).smul (show (0 : ℂ) ≤ 2 by norm_num), ?_⟩
    norm_num [phaseMinus, blochEffect, Matrix.trace, Fin.sum_univ_succ]

theorem projective_phase_counterexample : phasePlus ≠ phaseMinus ∧
    ∀ m, Matrix.trace (phasePlus * (basisPOVM 2).effects m) =
      Matrix.trace (phaseMinus * (basisPOVM 2).effects m) := by
  constructor
  · intro h
    have he := congrArg (fun A : Q 2 => A 0 1) h
    norm_num [phasePlus, phaseMinus, blochEffect] at he
  · intro m; fin_cases m <;>
      norm_num [phasePlus, phaseMinus, blochEffect, basisPOVM, Matrix.trace,
        Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal_apply, Matrix.vecMul, dotProduct]

theorem tomography_unique {d k : ℕ} (E : POVM d k) (h : is_ic_povm E)
    (ρ σ : HermMat d) (hp : measurement E ρ = measurement E σ) : ρ = σ :=
  (ic_povm_iff_injective E).mp h hp

theorem relabel_dual {d k : ℕ} (E : POVM d k) (h : is_ic_povm E)
    (π : Fin k ≃ Fin k) (m : Fin k) :
    dual_frame (relabel E π) ((relabel_ic E π).mpr h) m = dual_frame E h (π m) := by
  apply (frame_operator_invertible E h).injective
  rw [← relabel_frame E π]
  change (frame_equiv (relabel E π) ((relabel_ic E π).mpr h))
    ((frame_equiv (relabel E π) ((relabel_ic E π).mpr h)).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  change _ = (frame_equiv E h) ((frame_equiv E h).symm _)
  rw [LinearEquiv.apply_symm_apply]
  rfl

structure QuantumPOVMInformationallyCompleteSuite : Prop where
  ic_injective : ∀ {d k} (E : POVM d k), is_ic_povm E ↔ Function.Injective (measurement E)
  frame_positive : ∀ {d k} (E : POVM d k), is_ic_povm E →
    ∀ X : HermMat d, X ≠ 0 → 0 < hs_inner X (frame_operator E X)
  frame_invertible : ∀ {d k} (E : POVM d k), is_ic_povm E → Function.Bijective (frame_operator E)
  reconstruction : ∀ {d k} (E : POVM d k) (h : is_ic_povm E) (X : HermMat d),
    X = ∑ m, hs_inner X (effect E m) • dual_frame E h m
  tomography : ∀ {d k} (E : POVM d k) (h : is_ic_povm E) (ρ : Q d),
    QuantumNoBroadcastingMixed.IsDensityMatrix ρ →
    (∀ m, 0 ≤ (Matrix.trace (ρ * E.effects m)).re) ∧
    (∑ m, (Matrix.trace (ρ * E.effects m)).re) = 1 ∧
    ∃ X : HermMat d, val X = ρ ∧
      X = ∑ m, (Matrix.trace (ρ * E.effects m)).re • dual_frame E h m
  relabeling : ∀ {d k} (E : POVM d k) (π : Fin k ≃ Fin k),
    is_ic_povm (relabel E π) ↔ is_ic_povm E
  sic_overlap : ∀ i j, Matrix.trace (tetraEffect i * tetraEffect j) =
    if i = j then 1 / 4 else 1 / 12
  outcome_bound : ∀ {d k} (E : POVM d k), is_ic_povm E → d ^ 2 ≤ k
  qubit_model : is_ic_povm qubitTetrahedron
  scalar_model : is_ic_povm scalarPOVM
  projective_incomplete : ∀ {d}, 2 ≤ d → ¬ is_ic_povm (basisPOVM d)

theorem verification_suite : QuantumPOVMInformationallyCompleteSuite where
  ic_injective := ic_povm_iff_injective
  frame_positive := frame_operator_pos_def
  frame_invertible := frame_operator_invertible
  reconstruction := dual_frame_reconstruction_identity
  tomography E h ρ hρ := by
    obtain ⟨hp, hs, hr⟩ := quantum_state_tomography E h ρ hρ
    exact ⟨hp, hs, ⟨ρ, hρ.1.isHermitian⟩, rfl, hr⟩
  relabeling := relabel_ic
  sic_overlap := tetra_symmetric_overlap
  outcome_bound := ic_povm_outcome_bound
  qubit_model := qubit_tetrahedron_ic_povm
  scalar_model := scalar_ic
  projective_incomplete hd := onb_measurement_not_ic hd _

end QuantumPOVMInformationallyComplete
