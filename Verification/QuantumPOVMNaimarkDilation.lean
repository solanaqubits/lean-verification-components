/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.PhotonicsBellStateAnalyzer
import Verification.QuantumDepolarizingChannel
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Finite POVMs, their canonical Naimark dilation and measurement instruments. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
namespace QuantumPOVMNaimarkDilation
abbrev Q (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
abbrev Ext (d k : ℕ) := Matrix (Fin d × Fin k) (Fin d × Fin k) ℂ
structure FinitePOVM (d k : ℕ) where
  effects : Fin k → Q d
  pos_semidef : ∀ m, (effects m).PosSemidef
  completeness : ∑ m, effects m = 1

variable {d k : ℕ}

def sqrt_effects (E : FinitePOVM d k) (m : Fin k) : Q d := CFC.sqrt (E.effects m)

theorem sqrt_positive (E : FinitePOVM d k) (m : Fin k) :
    (sqrt_effects E m).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (E.effects m))

theorem sqrt_hermitian (E : FinitePOVM d k) (m : Fin k) :
    (sqrt_effects E m).conjTranspose = sqrt_effects E m := (sqrt_positive E m).isHermitian

theorem sqrt_square (E : FinitePOVM d k) (m : Fin k) :
    sqrt_effects E m * sqrt_effects E m = E.effects m := by
  simpa [sqrt_effects, pow_two] using CFC.sq_sqrt (E.effects m) (E.pos_semidef m).nonneg

def V (E : FinitePOVM d k) : Matrix (Fin d × Fin k) (Fin d) ℂ :=
  fun a j => sqrt_effects E a.2 a.1 j

def outcomeProjector (m : Fin k) : Q k := Matrix.diagonal (fun a => if a = m then 1 else 0)
def projector (d : ℕ) (m : Fin k) : Ext d k := (1:Q d) ⊗ₖ outcomeProjector m

theorem projector_apply (m : Fin k) (a b : Fin d × Fin k) :
    projector d m a b = if a = b ∧ a.2 = m then 1 else 0 := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  by_cases hi : i = j <;> by_cases ha : a = b <;> by_cases hm : a = m <;>
    simp [projector, outcomeProjector, Matrix.diagonal, Prod.ext_iff, hi, ha, hm]

theorem projector_hermitian (m : Fin k) : (projector d m).conjTranspose = projector d m := by
  ext a b : 2
  simp only [Matrix.conjTranspose_apply, projector_apply]
  split_ifs <;> simp_all <;> aesop

theorem projector_mul (m n : Fin k) :
    projector d m * projector d n = if m = n then projector d m else 0 := by
  ext a b : 2
  simp [Matrix.mul_apply, projector_apply, ite_and, mul_ite]
  split_ifs <;> simp_all [projector_apply]

theorem projectors_complete : ∑ m : Fin k, projector d m = 1 := by
  ext a b : 2
  simp [Matrix.sum_apply, projector_apply, ite_and, Matrix.one_apply]

theorem projector_V (E : FinitePOVM d k) (m : Fin k) (a : Fin d × Fin k) (j : Fin d) :
    (projector d m * V E) a j = if a.2 = m then sqrt_effects E m a.1 j else 0 := by
  simp [Matrix.mul_apply, projector_apply, ite_and, ite_mul, V]
  split_ifs <;> simp_all

theorem isometry_v (E : FinitePOVM d k) : (V E).conjTranspose * V E = 1 := by
  calc
    (V E).conjTranspose * V E = ∑ m, (sqrt_effects E m).conjTranspose * sqrt_effects E m := by
      ext i j : 2
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, V, Fintype.sum_prod_type,
        Matrix.sum_apply]
      exact Finset.sum_comm
    _ = ∑ m, E.effects m := by simp [sqrt_hermitian, sqrt_square]
    _ = 1 := E.completeness

theorem naimark_dilation_exact (E : FinitePOVM d k) (m : Fin k) :
    (V E).conjTranspose * projector d m * V E = E.effects m := by
  rw [Matrix.mul_assoc]
  calc
    (V E).conjTranspose * (projector d m * V E) = (sqrt_effects E m).conjTranspose *
      sqrt_effects E m := by
      ext i j : 2
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, projector_apply, V,
        Fintype.sum_prod_type, mul_ite, ite_and]
    _ = E.effects m := by rw [sqrt_hermitian, sqrt_square]

theorem born_rule_preservation (E : FinitePOVM d k) (m : Fin k) (M : Q d) :
    (projector d m * V E * M * (V E).conjTranspose).trace = (E.effects m * M).trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, naimark_dilation_exact]

def dilate (E : FinitePOVM d k) (M : Q d) : Ext d k := V E * M * (V E).conjTranspose

theorem dilation_trace (E : FinitePOVM d k) (M : Q d) : (dilate E M).trace = M.trace := by
  rw [dilate, Matrix.trace_mul_comm, ← Matrix.mul_assoc, isometry_v, Matrix.one_mul]

theorem density_matrix_dilation (E : FinitePOVM d k) (ρ : Q d)
    (hρ : ρ.PosSemidef ∧ ρ.trace = 1) :
    (dilate E ρ).PosSemidef ∧ (dilate E ρ).trace = 1 :=
  ⟨hρ.1.mul_mul_conjTranspose_same _, (dilation_trace E ρ).trans hρ.2⟩


/-- Rectangular matrix multiplication agrees with composition on Euclidean spaces. -/
theorem euclidean_mul {a b c : Type*} [Finite a] [Fintype b] [Fintype c]
    [DecidableEq b] [DecidableEq c]
    (A : Matrix a b ℂ) (B : Matrix b c ℂ) :
    (A * B).toEuclideanLin = A.toEuclideanLin.comp B.toEuclideanLin := by
  classical
  let := Fintype.ofFinite a
  simp only [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.toLin_mul _ (EuclideanSpace.basisFun b ℂ).toBasis _ A B

theorem euclidean_one {a : Type*} [Fintype a] [DecidableEq a] :
    (1 : Matrix a a ℂ).toEuclideanLin = LinearMap.id := by
  simp [Matrix.toEuclideanLin_eq_toLin_orthonormal]

set_option maxHeartbeats 1000000 in
-- Euclidean-space norm instances require additional elaboration work.
def matrixIsometry {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (A : Matrix a b ℂ) (hA : A.conjTranspose * A = 1) :
    EuclideanSpace ℂ b →ₗᵢ[ℂ] EuclideanSpace ℂ a where
  toLinearMap := A.toEuclideanLin
  norm_map' := by
    apply (LinearMap.norm_map_iff_inner_map_map A.toEuclideanLin).mpr
    intro x y
    rw [← LinearMap.adjoint_inner_right]
    have h := congrArg Matrix.toEuclideanLin hA
    rw [euclidean_mul, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, euclidean_one] at h
    exact congrArg (fun T : EuclideanSpace ℂ b →ₗ[ℂ] EuclideanSpace ℂ b => inner ℂ x (T y)) h

set_option maxHeartbeats 1000000 in
-- Transport the subspace extension through Euclidean matrix representations.
theorem unitary_between_isometries {a b : Type*} [Fintype a] [Finite b]
    [DecidableEq a] [DecidableEq b] (J W : Matrix a b ℂ)
    (hJ : J.conjTranspose * J = 1) (hW : W.conjTranspose * W = 1) :
    ∃ U : Matrix a a ℂ, U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧ U * J = W := by
  let := Fintype.ofFinite b
  let j := matrixIsometry J hJ
  let w := matrixIsometry W hW
  let L := w.comp j.equivRange.symm.toLinearIsometry
  let T := L.extend
  let U := Matrix.toEuclideanLin.symm T.toLinearMap
  have hu : U.toEuclideanLin = T.toLinearMap := Matrix.toEuclideanLin.apply_symm_apply _
  have hleft : U.conjTranspose * U = 1 := by
    apply Matrix.toEuclideanLin.injective
    rw [euclidean_mul, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hu, euclidean_one]
    exact T.adjoint_comp_self'
  refine ⟨U, hleft, ?_, ?_⟩
  · exact mul_eq_one_comm.mp hleft
  · apply Matrix.toEuclideanLin.injective
    rw [euclidean_mul, hu]
    apply LinearMap.ext
    intro x
    change L.extend (j x) = w x
    have hx := L.extend_apply (j.equivRange x)
    simpa [L] using hx

def J (d k : ℕ) [NeZero k] : Matrix (Fin d × Fin k) (Fin d) ℂ :=
  fun a j => if a.2 = 0 then (1:Q d) a.1 j else 0

theorem ancilla_isometry [NeZero k] : (J d k).conjTranspose * J d k = 1 := by
  ext i j : 2
  simp [J, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.one_apply, apply_ite (starRingEnd ℂ), mul_ite, eq_comm]

theorem ancilla_density [NeZero k] (M : Q d) :
    J d k * M * (J d k).conjTranspose = M ⊗ₖ outcomeProjector (0 : Fin k) := by
  ext a b : 2
  simp [J, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    outcomeProjector, Matrix.diagonal, apply_ite (starRingEnd ℂ), ite_mul, mul_ite]
  split_ifs <;> simp_all

theorem unitary_dilation_extension [NeZero k] (E : FinitePOVM d k) :
    ∃ U : Ext d k, U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧ U * J d k = V E ∧
      ∀ M : Q d, dilate E M = U * (M ⊗ₖ outcomeProjector (0 : Fin k)) * U.conjTranspose := by
  obtain ⟨U, hU, hU',
    hUV⟩ := unitary_between_isometries (J d k) (V E) ancilla_isometry (isometry_v E)
  refine ⟨U, hU, hU', hUV, fun M => ?_⟩
  rw [← ancilla_density, dilate, ← hUV]
  simp [Matrix.mul_assoc, Matrix.conjTranspose_mul]

def partialTrace (R : Ext d k) : Q d := fun i j => ∑ m, R (i, m) (j, m)

theorem lueders_instrument_reduction (E : FinitePOVM d k) (m : Fin k) (M : Q d) :
    partialTrace (projector d m * dilate E M * projector d m) = sqrt_effects E m * M *
      sqrt_effects E m := by
  calc
    _ = sqrt_effects E m * M * (sqrt_effects E m).conjTranspose := by
      ext i j : 2
      simp [partialTrace, dilate, Matrix.mul_apply, Matrix.conjTranspose_apply,
        projector_apply, V, ite_and, ite_mul, mul_ite]
    _ = _ := by rw [sqrt_hermitian]

def probability (E : FinitePOVM d k) (ρ : Q d) (m : Fin k) : ℂ :=
  (projector d m * V E * ρ * (V E).conjTranspose).trace

theorem probability_lueders (E : FinitePOVM d k) (M : Q d) (m : Fin k) :
    probability E M m = (sqrt_effects E m * M * (sqrt_effects E m).conjTranspose).trace := by
  rw [probability, born_rule_preservation, Matrix.trace_mul_cycle, sqrt_hermitian, sqrt_square]

theorem probability_nonneg (E : FinitePOVM d k) (ρ : Q d) (hρ : ρ.PosSemidef) (m : Fin k) :
    0 ≤ probability E ρ m := by
  rw [probability_lueders]
  exact (hρ.mul_mul_conjTranspose_same _).trace_nonneg

theorem probability_real (E : FinitePOVM d k) (ρ : Q d) (hρ : ρ.PosSemidef) (m : Fin k) :
    (probability E ρ m).im = 0 := (Complex.nonneg_iff.mp (probability_nonneg E ρ hρ m)).2.symm

theorem probabilities_sum (E : FinitePOVM d k) (M : Q d) :
    ∑ m, probability E M m = M.trace := by
  simp only [probability, born_rule_preservation]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, E.completeness, Matrix.one_mul]

theorem probability_distribution (E : FinitePOVM d k) (ρ : Q d)
    (hρ : ρ.PosSemidef ∧ ρ.trace = 1) :
    (∀ m, 0 ≤ (probability E ρ m).re ∧ (probability E ρ m).im = 0) ∧
      ∑ m, (probability E ρ m).re = 1 := by
  refine ⟨fun m => ⟨(Complex.nonneg_iff.mp (probability_nonneg E ρ hρ.1 m)).1,
    probability_real E ρ hρ.1 m⟩, ?_⟩
  have h := congrArg Complex.re (probabilities_sum E ρ)
  simpa [hρ.2] using h

def bellOutcome : Fin 3 → PhotonicsBellStateAnalyzer.DetectorOutcome :=
  ![.psiMinus, .psiPlus, .inconclusive]

theorem bell_effect_positive (o : PhotonicsBellStateAnalyzer.DetectorOutcome) :
    (PhotonicsBellStateAnalyzer.effect o).PosSemidef := by
  have h (b : PhotonicsBellStateAnalyzer.BellState) :
      (PhotonicsBellStateAnalyzer.bellProjector b).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star _
  cases o <;> rw [PhotonicsBellStateAnalyzer.effects_exact]
  · exact h _
  · exact h _
  · exact (h _).add (h _)

def bellPOVM : FinitePOVM 4 3 where
  effects m := PhotonicsBellStateAnalyzer.effect (bellOutcome m)
  pos_semidef m := bell_effect_positive _
  completeness := by
    simpa [bellOutcome, Fin.sum_univ_succ,
      add_assoc] using PhotonicsBellStateAnalyzer.povm_completeness

theorem bridge_to_bell_state_analyzer (m : Fin 3) (M : Q 4) :
    (V bellPOVM).conjTranspose * projector 4 m * V bellPOVM = PhotonicsBellStateAnalyzer.effect
      (bellOutcome m) ∧
    probability bellPOVM M m = (PhotonicsBellStateAnalyzer.effect (bellOutcome m) * M).trace :=
  ⟨naimark_dilation_exact bellPOVM m, born_rule_preservation bellPOVM m M⟩

def depolarizingPOVM (p : ℝ) (hp : QuantumDepolarizingChannel.Physical p) : FinitePOVM 2 4 where
  effects j := (QuantumDepolarizingChannel.K p j).conjTranspose * QuantumDepolarizingChannel.K p j
  pos_semidef _ := Matrix.posSemidef_conjTranspose_mul_self _
  completeness := QuantumDepolarizingChannel.kraus_completeness p hp

theorem bridge_to_depolarizing_channel (p : ℝ) (hp : QuantumDepolarizingChannel.Physical p)
    (j : Fin 4) (M : Q 2) :
    probability (depolarizingPOVM p hp) M j = (QuantumDepolarizingChannel.K p j * M *
      (QuantumDepolarizingChannel.K p j).conjTranspose).trace := by
  rw [probability, born_rule_preservation, Matrix.trace_mul_cycle]
  rfl

theorem projective_sqrt (E : FinitePOVM d k) (m : Fin k)
    (h : E.effects m * E.effects m = E.effects m) : sqrt_effects E m = E.effects m := by
  unfold sqrt_effects
  conv_lhs => rw [← h]
  exact CFC.sqrt_mul_self _ (E.pos_semidef m).nonneg

theorem zero_effect (E : FinitePOVM d k) (m : Fin k) (h : E.effects m = 0) :
    sqrt_effects E m = 0 ∧ ∀ M, probability E M m = 0 := by
  constructor
  · simp [sqrt_effects, h]
  · intro M; simp [probability, born_rule_preservation, h]

/-- The output index is canonically reindexed along Fin d × Fin 1 ≃ Fin d. -/
theorem singleton_isometry (E : FinitePOVM d 1) :
    Matrix.of (fun i j => V E (i, 0) j) = (1:Q d) := by
  have h : E.effects 0 = 1 := by simpa [Fin.sum_univ_succ] using E.completeness
  ext i j : 2
  simp [V, sqrt_effects, h]

def binaryPOVM (d : ℕ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) : FinitePOVM d 2 where
  effects := ![(t:ℂ) • (1:Q d), ((1-t:ℝ):ℂ) • (1:Q d)]
  pos_semidef m := by
    fin_cases m
    · exact Matrix.PosSemidef.one.smul (by exact_mod_cast ht.1 : (0:ℂ) ≤ t)
    · exact Matrix.PosSemidef.one.smul (by exact_mod_cast sub_nonneg.mpr ht.2 : (0:ℂ) ≤ (1-t:ℝ))
  completeness := by
    rw [Fin.sum_univ_two]
    change (t:ℂ) • (1:Q d) + ((1-t:ℝ):ℂ) • (1:Q d) = 1
    rw [← add_smul]
    norm_num

theorem binary_nonprojective [NeZero d] (t : ℝ) (ht : 0 < t ∧ t < 1) :
    let E := binaryPOVM d t ⟨ht.1.le, ht.2.le⟩
    E.effects 0 * E.effects 0 ≠ E.effects 0 := by
  intro E h
  have hentry := congrArg (fun M : Q d => (M 0 0).re) h
  simp [E, binaryPOVM] at hentry
  nlinarith

theorem binary_probability (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (ρ : Q d) (hρ : ρ.trace = 1) :
    probability (binaryPOVM d t ht) ρ 0 = t ∧
      probability (binaryPOVM d t ht) ρ 1 = (1-t:ℝ) := by
  constructor <;>
    simp [probability, born_rule_preservation, binaryPOVM, hρ]

def qubitX : Q 2 := !![0, 1;1, 0]
def zeroDensity : Q 2 := !![1, 0;0, 0]
def oneDensity : Q 2 := !![0, 0;0, 1]

theorem counterexample_povm_not_instrument :
    (1:Q 2).conjTranspose * 1 = 1 ∧ qubitX.conjTranspose * qubitX = 1 ∧
    (1:Q 2) * zeroDensity * (1:Q 2).conjTranspose = zeroDensity ∧
    qubitX * zeroDensity * qubitX.conjTranspose = oneDensity ∧ zeroDensity ≠ oneDensity := by
  refine ⟨by simp, ?_, by simp, ?_, ?_⟩
  · ext i j : 2; fin_cases i <;> fin_cases j <;>
      norm_num [qubitX, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  · ext i j : 2; fin_cases i <;> fin_cases j <;>
      norm_num [qubitX, zeroDensity, oneDensity, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two]
  · intro h
    have := congrArg (fun M : Q 2 => M 0 0) h
    norm_num [zeroDensity, oneDensity] at this

structure QuantumPOVMNaimarkDilationSuite : Prop where
  roots : ∀ d k (E : FinitePOVM d k) m,
    (sqrt_effects E m).PosSemidef ∧ (sqrt_effects E m).conjTranspose = sqrt_effects E m ∧
      sqrt_effects E m * sqrt_effects E m = E.effects m
  isometry : ∀ d k (E : FinitePOVM d k), (V E).conjTranspose * V E = 1
  projectors : ∀ d k, (∀ m : Fin k, (projector d m).conjTranspose = projector d m) ∧
    (∀ m n : Fin k, projector d m * projector d n = if m = n then projector d m else 0) ∧
    ∑ m : Fin k, projector d m = 1
  compression : ∀ d k (E : FinitePOVM d k) m,
    (V E).conjTranspose * projector d m * V E = E.effects m
  born : ∀ d k (E : FinitePOVM d k) m M,
    (projector d m * V E * M * (V E).conjTranspose).trace = (E.effects m * M).trace
  density : ∀ d k (E : FinitePOVM d k) ρ, ρ.PosSemidef ∧ ρ.trace = 1 →
    (dilate E ρ).PosSemidef ∧ (dilate E ρ).trace = 1
  probabilities : ∀ d k (E : FinitePOVM d k) ρ, ρ.PosSemidef ∧ ρ.trace = 1 →
    (∀ m, 0 ≤ (probability E ρ m).re ∧ (probability E ρ m).im = 0) ∧
    ∑ m, (probability E ρ m).re = 1
  unitary : ∀ d k [NeZero k] (E : FinitePOVM d k),
    ∃ U : Ext d k, U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧ U * J d k = V E ∧
      ∀ M : Q d, dilate E M = U * (M ⊗ₖ outcomeProjector (0 : Fin k)) * U.conjTranspose
  lueders : ∀ d k (E : FinitePOVM d k) m M,
    partialTrace (projector d m * dilate E M * projector d m) = sqrt_effects E m * M *
      sqrt_effects E m
  projective : ∀ d k (E : FinitePOVM d k) m, E.effects m * E.effects m = E.effects m →
    sqrt_effects E m = E.effects m
  singleton : ∀ d (E : FinitePOVM d 1), Matrix.of (fun i j => V E (i, 0) j) = (1:Q d)
  bell : ∀ m M,
    probability bellPOVM M m = (PhotonicsBellStateAnalyzer.effect (bellOutcome m) * M).trace
  depolarizing : ∀ p (hp : QuantumDepolarizingChannel.Physical p) j M,
    probability (depolarizingPOVM p hp) M j = (QuantumDepolarizingChannel.K p j * M *
      (QuantumDepolarizingChannel.K p j).conjTranspose).trace
  instruments_differ : qubitX.conjTranspose * qubitX = 1 ∧
    qubitX * zeroDensity * qubitX.conjTranspose = oneDensity ∧ zeroDensity ≠ oneDensity

theorem quantum_povm_naimark_dilation_master_suite : QuantumPOVMNaimarkDilationSuite := {
  roots := fun _ _ E m => ⟨sqrt_positive E m, sqrt_hermitian E m, sqrt_square E m⟩
  isometry := fun _ _ => isometry_v
  projectors := fun _ _ => ⟨projector_hermitian, projector_mul, projectors_complete⟩
  compression := fun _ _ => naimark_dilation_exact
  born := fun _ _ => born_rule_preservation
  density := fun _ _ => density_matrix_dilation
  probabilities := fun _ _ => probability_distribution
  unitary := fun _ _ _ => unitary_dilation_extension
  lueders := fun _ _ => lueders_instrument_reduction
  projective := fun _ _ => projective_sqrt
  singleton := fun _ => singleton_isometry
  bell := fun m M => (bridge_to_bell_state_analyzer m M).2
  depolarizing := bridge_to_depolarizing_channel
  instruments_differ := ⟨counterexample_povm_not_instrument.2.1,
    counterexample_povm_not_instrument.2.2.2⟩
}

end QuantumPOVMNaimarkDilation
