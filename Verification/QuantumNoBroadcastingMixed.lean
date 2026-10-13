/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumNoCloningUnitary
import Verification.QuantumPOVMNaimarkDilation
import Mathlib.Analysis.InnerProductSpace.JointEigenspace

/-! Finite-dimensional no-broadcasting: a pair of density matrices admits one
complex-linear CPTP broadcaster exactly when the matrices commute. Complete
positivity is defined by all finite matrix amplifications; correlated outputs
are allowed. Necessity uses a derived Kraus representation and a symmetric
logarithmic derivative, with no invertibility assumptions on the states. -/
noncomputable section
open scoped BigOperators ComplexOrder Kronecker
namespace QuantumNoBroadcastingMixed

abbrev Mat (ι : Type*) := Matrix ι ι ℂ
abbrev Q (d : ℕ) := Mat (Fin d)
abbrev Joint (d : ℕ) := Mat (Fin d × Fin d)

def IsDensityMatrix {ι : Type*} [Fintype ι] (ρ : Mat ι) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1
abbrev State (d : ℕ) := {ρ : Q d // IsDensityMatrix ρ}

/-- Matrix-block amplification, independently defined of any Kraus representation. -/
def amplify {ι κ : Type*} (E : Mat ι →ₗ[ℂ] Mat κ) (a : ℕ)
    (X : Mat (Fin a × ι)) : Mat (Fin a × κ) :=
  fun i j => E (fun u v => X (i.1, u) (j.1, v)) i.2 j.2

/-- Complete positivity quantifies over every finite ancilla dimension. -/
def IsCompletelyPositive {ι κ : Type*} (E : Mat ι →ₗ[ℂ] Mat κ) : Prop :=
  ∀ (a : ℕ) (X : Mat (Fin a × ι)), X.PosSemidef → (amplify E a X).PosSemidef

structure Channel (ι κ : Type*) [Fintype ι] [Fintype κ] where
  toLinearMap : Mat ι →ₗ[ℂ] Mat κ
  completely_positive : IsCompletelyPositive toLinearMap
  trace_preserving : ∀ X, (toLinearMap X).trace = X.trace

abbrev CPTPMap (d : ℕ) := Channel (Fin d) (Fin d × Fin d)

section Kraus
variable {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
  [DecidableEq ι]

def krausMap (K : η → Matrix κ ι ℂ) : Mat ι →ₗ[ℂ] Mat κ where
  toFun X := ∑ j, K j * X * (K j).conjTranspose
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' z X := by simp [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

omit [Fintype κ] [DecidableEq ι] in
theorem amplify_kraus (K : η → Matrix κ ι ℂ) (a : ℕ) (X : Mat (Fin a × ι)) :
    amplify (krausMap K) a X = ∑ j,
      ((1 : Mat (Fin a)) ⊗ₖ K j) * X * ((1 : Mat (Fin a)) ⊗ₖ K j).conjTranspose := by
  ext u v
  simp [amplify, krausMap, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.one_apply,
    apply_ite (starRingEnd ℂ), mul_ite]
  rfl

omit [Fintype κ] [DecidableEq ι] in
theorem kraus_completely_positive [Finite κ] (K : η → Matrix κ ι ℂ) :
    IsCompletelyPositive (krausMap K) := by
  intro a X hX
  rw [amplify_kraus]
  exact Matrix.posSemidef_sum _ fun j _ => hX.mul_mul_conjTranspose_same _

theorem kraus_trace_preserving (K : η → Matrix κ ι ℂ)
    (hK : ∑ j, (K j).conjTranspose * K j = 1) (X : Mat ι) :
    (krausMap K X).trace = X.trace := by
  change (∑ j, K j * X * (K j).conjTranspose).trace = X.trace
  rw [Matrix.trace_sum]
  conv_lhs => arg 2; ext j; rw [Matrix.trace_mul_cycle]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]

def krausChannel (K : η → Matrix κ ι ℂ)
    (hK : ∑ j, (K j).conjTranspose * K j = 1) : Channel ι κ :=
  ⟨krausMap K, kraus_completely_positive K, kraus_trace_preserving K hK⟩

end Kraus

section Composition
variable {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]

def Channel.comp (F : Channel κ η) (E : Channel ι κ) : Channel ι η where
  toLinearMap := F.toLinearMap.comp E.toLinearMap
  completely_positive a X hX := F.completely_positive a _ (E.completely_positive a X hX)
  trace_preserving X := (F.trace_preserving _).trans (E.trace_preserving X)

def unitaryChannel [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) : Channel ι ι :=
  krausChannel (fun _ : Fin 1 => (U : Mat ι)) (by
    simp only [Fin.sum_univ_one]
    exact Unitary.coe_star_mul_self U)

theorem unitaryChannel_apply [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) (X : Mat ι) :
    (unitaryChannel U).toLinearMap X = (U : Mat ι) * X * (U : Mat ι).conjTranspose := by
  simp [unitaryChannel, krausChannel, krausMap]

end Composition

/-- Trace out the second tensor factor, reusing the Naimark module. -/
def partial_trace_B {d : ℕ} (X : Joint d) : Q d :=
  QuantumPOVMNaimarkDilation.partialTrace X

def partial_trace_A {d : ℕ} (X : Joint d) : Q d :=
  fun i j => ∑ a, X (a, i) (a, j)

def Broadcasts {d : ℕ} (E : CPTPMap d) (ρ : Q d) : Prop :=
  partial_trace_B (E.toLinearMap ρ) = ρ ∧ partial_trace_A (E.toLinearMap ρ) = ρ

def CanBroadcast {d : ℕ} (ρ σ : Q d) : Prop :=
  ∃ E : CPTPMap d, Broadcasts E ρ ∧ Broadcasts E σ

theorem partial_trace_B_tensor {d : ℕ} (X Y : Q d) :
    partial_trace_B (X ⊗ₖ Y) = Y.trace • X := by
  ext i j
  simp [partial_trace_B, QuantumPOVMNaimarkDilation.partialTrace, Matrix.trace,
    ← Finset.mul_sum, mul_comm]

theorem partial_trace_A_tensor {d : ℕ} (X Y : Q d) :
    partial_trace_A (X ⊗ₖ Y) = X.trace • Y := by
  ext i j
  simp [partial_trace_A, Matrix.trace, ← Finset.sum_mul]

theorem Channel.positive {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : Channel ι κ) (X : Mat ι) (hX : X.PosSemidef) :
    (E.toLinearMap X).PosSemidef := by
  have h := E.completely_positive 1 _ (hX.submatrix (fun i : Fin 1 × ι => i.2))
  exact h.submatrix (fun i : κ => ((0 : Fin 1), i))

theorem Channel.density_preserved {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : Channel ι κ) (ρ : Mat ι) (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (E.toLinearMap ρ) :=
  ⟨E.positive ρ hρ.1, (E.trace_preserving ρ).trans hρ.2⟩

theorem partial_trace_B_positive {d : ℕ} (X : Joint d) (hX : X.PosSemidef) :
    (partial_trace_B X).PosSemidef := by
  have he : partial_trace_B X = ∑ a : Fin d, X.submatrix (fun i => (i, a)) (fun i => (i, a)) := by
    ext i j
    simp [partial_trace_B, QuantumPOVMNaimarkDilation.partialTrace, Matrix.sum_apply]
  rw [he]
  exact Matrix.posSemidef_sum _ fun a _ => hX.submatrix _

theorem partial_trace_A_positive {d : ℕ} (X : Joint d) (hX : X.PosSemidef) :
    (partial_trace_A X).PosSemidef := by
  have he : partial_trace_A X = ∑ a : Fin d, X.submatrix (fun i => (a, i)) (fun i => (a, i)) := by
    ext i j
    simp [partial_trace_A, Matrix.sum_apply]
  rw [he]
  exact Matrix.posSemidef_sum _ fun a _ => hX.submatrix _

theorem partial_trace_B_trace {d : ℕ} (X : Joint d) : (partial_trace_B X).trace = X.trace := by
  simp [Matrix.trace, partial_trace_B, QuantumPOVMNaimarkDilation.partialTrace,
    Fintype.sum_prod_type]

theorem partial_trace_A_trace {d : ℕ} (X : Joint d) : (partial_trace_A X).trace = X.trace := by
  simp only [Matrix.trace, partial_trace_A, Matrix.diag_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Appending a fixed state is linear in the input, unlike X ↦ X ⊗ X. -/
def appendStateMap {d : ℕ} (ρ : Q d) : Q d →ₗ[ℂ] Joint d where
  toFun X := X ⊗ₖ ρ
  map_add' X Y := Matrix.add_kronecker X Y ρ
  map_smul' z X := by
    ext i j
    simp [Matrix.kroneckerMap_apply, mul_assoc]

theorem appendState_completely_positive {d : ℕ} (ρ : Q d) (hρ : ρ.PosSemidef) :
    IsCompletelyPositive (appendStateMap ρ) := by
  intro a X hX
  exact (hX.kronecker hρ).submatrix (fun i : Fin a × (Fin d × Fin d) => ((i.1, i.2.1), i.2.2))

def appendStateChannel {d : ℕ} (ρ : Q d) (hρ : IsDensityMatrix ρ) : CPTPMap d where
  toLinearMap := appendStateMap ρ
  completely_positive := appendState_completely_positive ρ hρ.1
  trace_preserving X := by simp [appendStateMap, Matrix.trace_kronecker, hρ.2]

theorem quantum_identical_states_broadcasting {d : ℕ} (ρ : Q d)
    (hρ : IsDensityMatrix ρ) : CanBroadcast ρ ρ := by
  have h : Broadcasts (appendStateChannel ρ hρ) ρ := by
    constructor
    · change partial_trace_B (ρ ⊗ₖ ρ) = ρ
      simp [partial_trace_B_tensor, hρ.2]
    · change partial_trace_A (ρ ⊗ₖ ρ) = ρ
      simp [partial_trace_A_tensor, hρ.2]
  exact ⟨appendStateChannel ρ hρ, h, h⟩

/-- Kraus operators |jj⟩⟨j| in the computational basis. -/
def diagonalKraus {d : ℕ} (j : Fin d) : Matrix (Fin d × Fin d) (Fin d) ℂ :=
  fun a b => if a.1 = j ∧ a.2 = j ∧ b = j then 1 else 0

theorem diagonalKraus_complete (d : ℕ) :
    ∑ j : Fin d, (diagonalKraus j).conjTranspose * diagonalKraus j = 1 := by
  ext a b
  simp [diagonalKraus, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, ite_and, mul_ite]

def diagonalChannel (d : ℕ) : CPTPMap d :=
  krausChannel diagonalKraus (diagonalKraus_complete d)

theorem diagonalChannel_apply {d : ℕ} (X : Q d) (a b : Fin d × Fin d) :
    (diagonalChannel d).toLinearMap X a b =
      if a.1 = a.2 ∧ a.1 = b.1 ∧ a.1 = b.2 then X a.1 a.1 else 0 := by
  simp [diagonalChannel, krausChannel, krausMap, diagonalKraus, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, ite_and]
  split_ifs <;> simp_all

theorem diagonalChannel_marginals {d : ℕ} (X : Q d) :
    partial_trace_B ((diagonalChannel d).toLinearMap X) = Matrix.diagonal (fun i => X i i) ∧
    partial_trace_A ((diagonalChannel d).toLinearMap X) = Matrix.diagonal (fun i => X i i) := by
  constructor <;> ext a b <;>
    simp [partial_trace_A, partial_trace_B, QuantumPOVMNaimarkDilation.partialTrace,
      diagonalChannel_apply, Matrix.diagonal, ite_and]

theorem diagonal_pair_broadcasting {d : ℕ} (p q : Fin d → ℂ) :
    CanBroadcast (Matrix.diagonal p) (Matrix.diagonal q) := by
  refine ⟨diagonalChannel d, ?_, ?_⟩
  · simpa [Broadcasts] using diagonalChannel_marginals (Matrix.diagonal p)
  · simpa [Broadcasts] using diagonalChannel_marginals (Matrix.diagonal q)

def basisProjector {d : ℕ} (i : Fin d) : Q d :=
  Matrix.diagonal (fun a => if a = i then 1 else 0)

theorem basisProjector_trace {d : ℕ} (i : Fin d) : (basisProjector i).trace = 1 := by
  simp [basisProjector]

theorem diagonal_decomposition {d : ℕ} (p : Fin d → ℂ) :
    ∑ i, p i • basisProjector i = Matrix.diagonal p := by
  ext a b
  simp [basisProjector, Matrix.sum_apply, Matrix.diagonal, mul_ite]

theorem diagonalChannel_decomposition {d : ℕ} (p : Fin d → ℂ) :
    (diagonalChannel d).toLinearMap (Matrix.diagonal p) =
      ∑ i, p i • (basisProjector i ⊗ₖ basisProjector i) := by
  ext a b
  simp [diagonalChannel_apply, basisProjector, Matrix.sum_apply, Matrix.diagonal,
    Matrix.kroneckerMap_apply, ite_and, mul_ite]
  split_ifs <;> simp_all

theorem partial_trace_B_sum {d : ℕ} {ι : Type*} (s : Finset ι) (X : ι → Joint d) :
    partial_trace_B (∑ i ∈ s, X i) = ∑ i ∈ s, partial_trace_B (X i) := by
  ext a b
  simp only [partial_trace_B, QuantumPOVMNaimarkDilation.partialTrace, Matrix.sum_apply]
  exact Finset.sum_comm

theorem partial_trace_A_sum {d : ℕ} {ι : Type*} (s : Finset ι) (X : ι → Joint d) :
    partial_trace_A (∑ i ∈ s, X i) = ∑ i ∈ s, partial_trace_A (X i) := by
  ext a b
  simp only [partial_trace_A, Matrix.sum_apply]
  exact Finset.sum_comm

theorem partial_trace_B_smul {d : ℕ} (z : ℂ) (X : Joint d) :
    partial_trace_B (z • X) = z • partial_trace_B X := by
  ext a b
  simp [partial_trace_B, QuantumPOVMNaimarkDilation.partialTrace, Finset.mul_sum]

theorem partial_trace_A_smul {d : ℕ} (z : ℂ) (X : Joint d) :
    partial_trace_A (z • X) = z • partial_trace_A X := by
  ext a b
  simp [partial_trace_A, Finset.mul_sum]

def tensorUnitary {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.unitaryGroup (Fin d × Fin d) ℂ :=
  ⟨(U : Q d) ⊗ₖ (U : Q d), Matrix.kronecker_mem_unitary U.property U.property⟩

def conjugate {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (X : Q d) : Q d :=
  (U : Q d) * X * (U : Q d).conjTranspose

def basisChannel {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) : CPTPMap d :=
  (unitaryChannel (tensorUnitary U)).comp ((diagonalChannel d).comp (unitaryChannel (star U)))

theorem conjugate_trace {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (X : Q d) :
    (conjugate U X).trace = X.trace := by
  rw [conjugate, Matrix.trace_mul_cycle]
  change (star (U : Q d) * (U : Q d) * X).trace = X.trace
  rw [Unitary.coe_star_mul_self, Matrix.one_mul]

theorem conjugate_diagonal_decomposition {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) (p : Fin d → ℂ) :
    ∑ i, p i • conjugate U (basisProjector i) = conjugate U (Matrix.diagonal p) := by
  rw [← diagonal_decomposition p]
  simp [conjugate, Matrix.mul_sum, Matrix.sum_mul]

theorem basisChannel_on_diagonal {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (p : Fin d → ℂ) :
    (basisChannel U).toLinearMap (conjugate U (Matrix.diagonal p)) =
      ∑ i, p i • (conjugate U (basisProjector i) ⊗ₖ conjugate U (basisProjector i)) := by
  have hcancel : (unitaryChannel (star U)).toLinearMap
      (conjugate U (Matrix.diagonal p)) = Matrix.diagonal p := by
    rw [unitaryChannel_apply]
    simp [conjugate, ← Matrix.star_eq_conjTranspose, Matrix.mul_assoc,
      ← mul_assoc (star (U : Q d)) (U : Q d)]
  change (unitaryChannel (tensorUnitary U)).toLinearMap
    ((diagonalChannel d).toLinearMap ((unitaryChannel (star U)).toLinearMap _)) = _
  rw [hcancel, diagonalChannel_decomposition, unitaryChannel_apply]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [tensorUnitary, Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul,
    conjugate]

theorem basisChannel_broadcasts {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (p : Fin d → ℂ) : Broadcasts (basisChannel U) (conjugate U (Matrix.diagonal p)) := by
  constructor
  · rw [basisChannel_on_diagonal, partial_trace_B_sum]
    simp_rw [partial_trace_B_smul, partial_trace_B_tensor, conjugate_trace,
      basisProjector_trace, one_smul]
    exact conjugate_diagonal_decomposition U p
  · rw [basisChannel_on_diagonal, partial_trace_A_sum]
    simp_rw [partial_trace_A_smul, partial_trace_A_tensor, conjugate_trace,
      basisProjector_trace, one_smul]
    exact conjugate_diagonal_decomposition U p

theorem jointly_diagonalized_broadcasting {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (p q : Fin d → ℂ) :
    CanBroadcast (conjugate U (Matrix.diagonal p)) (conjugate U (Matrix.diagonal q)) :=
  ⟨basisChannel U, basisChannel_broadcasts U p, basisChannel_broadcasts U q⟩

theorem joint_eigenbasis {d : ℕ} (A B : Q d) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : A * B = B * A) :
    ∃ (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) (p q : Fin d → ℂ),
      ∀ i, A.toEuclideanLin (b i) = p i • b i ∧ B.toEuclideanLin (b i) = q i • b i := by
  classical
  have hAs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hBs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hc : Commute A.toEuclideanLin B.toEuclideanLin := by
    change A.toEuclideanLin * B.toEuclideanLin = B.toEuclideanLin * A.toEuclideanLin
    change A.toEuclideanLin.comp B.toEuclideanLin = B.toEuclideanLin.comp A.toEuclideanLin
    simpa only [Matrix.toLpLin_mul_same] using congrArg Matrix.toEuclideanLin hAB
  let V (z : ℂ × ℂ) := Module.End.eigenspace A.toEuclideanLin z.2 ⊓
    Module.End.eigenspace B.toEuclideanLin z.1
  have ho₀ := hAs.orthogonalFamily_eigenspace_inf_eigenspace hBs
  let : Fintype {z : ℂ × ℂ // V z ≠ ⊥} := ho₀.independent.fintypeNeBotOfFiniteDimensional
  let ho := ho₀.comp (f := fun z : {z : ℂ × ℂ // V z ≠ ⊥} => z.val) Subtype.val_injective
  have hi : DirectSum.IsInternal (fun z : {z : ℂ × ℂ // V z ≠ ⊥} => V z.val) := by
    apply ho.isInternal_iff.mpr
    rw [iSup_ne_bot_subtype, show (⨆ z, V z) = ⊤ from ?_, Submodule.top_orthogonal_eq_bot]
    change (⨆ z : ℂ × ℂ, Module.End.eigenspace A.toEuclideanLin z.2 ⊓
      Module.End.eigenspace B.toEuclideanLin z.1) = ⊤
    rw [iSup_prod, iSup_comm]
    exact hAs.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hBs hc
  let hn : Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) = d := by simp
  refine ⟨hi.subordinateOrthonormalBasis hn ho,
    fun i => (hi.subordinateOrthonormalBasisIndex hn i ho).val.2,
    fun i => (hi.subordinateOrthonormalBasisIndex hn i ho).val.1, ?_⟩
  intro i
  have hm := hi.subordinateOrthonormalBasis_subordinate hn i ho
  exact ⟨Module.End.mem_eigenspace_iff.mp hm.1, Module.End.mem_eigenspace_iff.mp hm.2⟩

theorem joint_unitary_diagonalization {d : ℕ} (A B : Q d)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A * B = B * A) :
    ∃ (U : Matrix.unitaryGroup (Fin d) ℂ) (p q : Fin d → ℂ),
      A = conjugate U (Matrix.diagonal p) ∧ B = conjugate U (Matrix.diagonal q) := by
  classical
  obtain ⟨b, p, q, hb⟩ := joint_eigenbasis A B hA hB hAB
  let U : Matrix.unitaryGroup (Fin d) ℂ :=
    ⟨(EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix b.toBasis,
      (EuclideanSpace.basisFun (Fin d) ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
  have hu (i j : Fin d) : (U : Q d) i j = b j i := by
    simp [U, Module.Basis.toMatrix_apply]
  have aux (X : Q d) (v : Fin d → ℂ)
      (hv : ∀ i, X.toEuclideanLin (b i) = v i • b i) :
      X = conjugate U (Matrix.diagonal v) := by
    have he : X * (U : Q d) = (U : Q d) * Matrix.diagonal v := by
      ext i j
      have hh := congrArg (fun z : EuclideanSpace ℂ (Fin d) => z i) (hv j)
      simpa [Matrix.toLpLin_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        hu, Matrix.diagonal, mul_ite, mul_comm] using hh
    have hh := congrArg (fun Z : Q d => Z * (U : Q d).conjTranspose) he
    simpa [conjugate, Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose] using hh
  exact ⟨U, p, q, aux A p (fun i => (hb i).1), aux B q (fun i => (hb i).2)⟩

theorem quantum_broadcasting_constructive_sufficiency {d : ℕ} (ρ σ : Q d)
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) (hc : ρ * σ = σ * ρ) :
    CanBroadcast ρ σ := by
  obtain ⟨U, p, q, rfl, rfl⟩ := joint_unitary_diagonalization ρ σ hρ.1.isHermitian
    hσ.1.isHermitian hc
  exact jointly_diagonalized_broadcasting U p q

section Pure
open QuantumNoCloningUnitary

theorem pure_sandwich {d : ℕ} (ψ φ : Ket d) :
    rho ψ * rho φ * rho ψ = (overlapSq ψ φ : ℂ) • rho ψ := by
  have hm : (ψ.conjTranspose * φ) * (φ.conjTranspose * ψ) =
      (overlapSq ψ φ : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i; fin_cases j
    change (∑ k : Fin 1, (ψ.conjTranspose * φ) 0 k * (φ.conjTranspose * ψ) k 0) = _
    simp only [Fin.sum_univ_one]
    change overlap ψ φ * overlap φ ψ = (overlapSq ψ φ : ℂ) * 1
    rw [overlap_swap ψ φ, mul_one, mul_comm]
    exact (Complex.normSq_eq_conj_mul_self (z := overlap ψ φ)).symm
  calc
    _ = ψ * ((ψ.conjTranspose * φ) * (φ.conjTranspose * ψ)) * ψ.conjTranspose := by
      simp [rho, Matrix.mul_assoc]
    _ = _ := by rw [hm]; simp [rho]

theorem pure_projectors_commute_iff {d : ℕ} (ψ φ : Ket d)
    (hψ : Normalized ψ) (hφ : Normalized φ) :
    rho ψ * rho φ = rho φ * rho ψ ↔ ψ.conjTranspose * φ = 0 ∨ rho ψ = rho φ := by
  constructor
  · intro hc
    have hp : rho ψ * rho φ = (overlapSq ψ φ : ℂ) • rho ψ := by
      rw [← pure_sandwich]
      rw [hc, Matrix.mul_assoc, rho_idempotent ψ hψ]
    have hh := congrArg (fun Z : Q d => Z * rho φ) hp
    rw [Matrix.mul_assoc, rho_idempotent φ hφ, Matrix.smul_mul, hp, smul_smul] at hh
    have ht := congrArg Matrix.trace hh
    simp only [Matrix.trace_smul, rho_trace ψ hψ, smul_eq_mul, mul_one] at ht
    have hr : overlapSq ψ φ = overlapSq ψ φ ^ 2 := by
      exact_mod_cast ht.trans (pow_two _).symm
    rcases QuantumNoCloningTheorem.cloning_overlap_quadratic _ hr with h0 | h1
    · exact Or.inl ((overlap_zero_iff ψ φ).mp h0)
    · exact Or.inr ((overlap_one_iff ψ φ hψ hφ).mp h1)
  · rintro (h0 | he)
    · have h0' : φ.conjTranspose * ψ = 0 := by
        simpa using congrArg Matrix.conjTranspose h0
      simp [rho, Matrix.mul_assoc, ← Matrix.mul_assoc ψ.conjTranspose φ, h0,
        ← Matrix.mul_assoc φ.conjTranspose ψ, h0']
    · rw [he]

theorem phase_broadcasting_invariance {d : ℕ} (ψ φ : Ket d) (z : ℂ)
    (hz : Complex.normSq z = 1) :
    CanBroadcast (rho (z • ψ)) (rho φ) ↔ CanBroadcast (rho ψ) (rho φ) := by
  rw [phase_density ψ z hz]

theorem orthogonal_pure_broadcasting {d : ℕ} (ψ φ : Ket d)
    (hψ : Normalized ψ) (hφ : Normalized φ) (horth : ψ.conjTranspose * φ = 0) :
    CanBroadcast (rho ψ) (rho φ) :=
  quantum_broadcasting_constructive_sufficiency _ _ ⟨rho_positive ψ, rho_trace ψ hψ⟩
    ⟨rho_positive φ, rho_trace φ hφ⟩ ((pure_projectors_commute_iff ψ φ hψ hφ).mpr (.inl horth))

end Pure

/-- Algebraic final step of the BCFJS support argument. The support hypothesis
must still be derived from fidelity saturation; it is not a channel assumption. -/
theorem saturation_support_marginal_commutes {d : ℕ} (S : Joint d) (μ : Fin d → ℂ)
    (hsupport : ∀ i j, μ i ≠ μ j → ∀ a, S a (i, j) = 0) :
    Matrix.diagonal μ * partial_trace_B (S.conjTranspose * S) =
      partial_trace_B (S.conjTranspose * S) * Matrix.diagonal μ := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : μ i = μ j
  · rw [hij, mul_comm]
  · have hz : partial_trace_B (S.conjTranspose * S) i j = 0 := by
      change (∑ k, ∑ a, S.conjTranspose (i, k) a * S a (j, k)) = 0
      apply Finset.sum_eq_zero
      intro k _
      apply Finset.sum_eq_zero
      intro a _
      by_cases hik : μ i = μ k
      · have hjk : μ j ≠ μ k := fun h => hij (hik.trans h.symm)
        simp [hsupport j k hjk a]
      · simp [Matrix.conjTranspose_apply, hsupport i k hik a]
    rw [hz, mul_zero, zero_mul]

/-- A positive real eigenvalue of a unitary is one unless its eigenvector is zero.
This applies to rectangular matrices of vectors as well. -/
theorem unitary_positive_eigenvalue {ι κ : Type*} [Fintype ι] [Finite κ]
    [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) (V : Matrix ι κ ℂ)
    (a : ℝ) (ha : 0 < a) (he : (U : Mat ι) * V = (a : ℂ) • V) :
    V = 0 ∨ a = 1 := by
  let : Fintype κ := Fintype.ofFinite κ
  by_cases hv : V = 0
  · exact Or.inl hv
  right
  have hn : (V.conjTranspose * V).trace ≠ 0 := by
    exact fun hz => hv (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hz)
  have ht : (((U : Mat ι) * V).conjTranspose * ((U : Mat ι) * V)).trace =
      (V.conjTranspose * V).trace := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (U : Mat ι).conjTranspose (U : Mat ι) V]
    change (V.conjTranspose * ((star (U : Mat ι) * (U : Mat ι)) * V)).trace = _
    rw [Unitary.coe_star_mul_self, Matrix.one_mul]
  rw [he] at ht
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal] at ht
  have hc : (a : ℂ) * a = 1 := by
    apply mul_right_cancel₀ hn
    simpa [mul_assoc] using ht
  have hr : a * a = 1 := by exact_mod_cast hc
  nlinarith

/-- The unitary intertwining relation in the BCFJS equality argument forces
zero cross-eigenspace columns; the joint output need not be invertible. -/
theorem saturation_intertwiner_support {d : ℕ}
    (W : Matrix.unitaryGroup (Fin d × Fin d) ℂ) (S : Joint d)
    (μ : Fin d → ℝ) (hμ : ∀ i, 0 < μ i)
    (he : (W : Joint d) * S =
      S * Matrix.diagonal (fun a : Fin d × Fin d => ((μ a.2 / μ a.1 : ℝ) : ℂ))) :
    ∀ i j, μ i ≠ μ j → ∀ a, S a (i, j) = 0 := by
  intro i j hij
  let V : Matrix (Fin d × Fin d) (Fin 1) ℂ := fun a _ => S a (i, j)
  have hv : (W : Joint d) * V = ((μ j / μ i : ℝ) : ℂ) • V := by
    ext a b
    have h := congrArg (fun Z : Joint d => Z a (i, j)) he
    change (∑ x, (W : Joint d) a x * S x (i, j)) = ((μ j / μ i : ℝ) : ℂ) * S a (i, j)
    simpa [Matrix.mul_apply, Matrix.diagonal, mul_ite, mul_comm] using h
  have hz : V = 0 := by
    rcases unitary_positive_eigenvalue W V (μ j / μ i) (div_pos (hμ j) (hμ i)) hv with h0 | h1
    · exact h0
    · exact False.elim (hij ((div_eq_one_iff_eq (ne_of_gt (hμ i))).mp h1).symm)
  intro a
  exact congrArg (fun Z : Matrix (Fin d × Fin d) (Fin 1) ℂ => Z a 0) hz

theorem dimension_one_broadcasting (ρ σ : Q 1) : CanBroadcast ρ σ := by
  have hρ : ρ = Matrix.diagonal (fun i => ρ i i) := by
    ext i j; fin_cases i; fin_cases j; simp
  have hσ : σ = Matrix.diagonal (fun i => σ i i) := by
    ext i j; fin_cases i; fin_cases j; simp
  rw [hρ, hσ]
  exact diagonal_pair_broadcasting _ _

/-- A mixed diagonal state is broadcast to a correlated, non-product output. -/
theorem correlated_mixed_output :
    let ρ : Q 2 := Matrix.diagonal (fun _ => (1 / 2 : ℂ))
    Broadcasts (diagonalChannel 2) ρ ∧
      (diagonalChannel 2).toLinearMap ρ ≠ ρ ⊗ₖ ρ := by
  dsimp
  constructor
  · simpa [Broadcasts] using
      diagonalChannel_marginals (Matrix.diagonal (fun _ : Fin 2 => (1/2 : ℂ)))
  · intro he
    have h := congrArg (fun X : Joint 2 => X (0, 1) (0, 1)) he
    norm_num [diagonalChannel_apply, Matrix.kroneckerMap_apply] at h

theorem zero_plus_projectors_noncommuting :
    let P := QuantumNoCloningUnitary.rho QuantumNoCloningUnitary.zeroKet
    let Q := QuantumNoCloningUnitary.rho QuantumNoCloningUnitary.plusQubit
    P * Q ≠ Q * P := by
  dsimp
  intro he
  have ho := (pure_projectors_commute_iff _ _
    (QuantumBB84ProtocolQBER.ket_normalized 0 0)
    (QuantumBB84ProtocolQBER.ket_normalized 1 0)).mp he
  rcases ho with h0 | h1
  · have h := (QuantumNoCloningUnitary.overlap_zero_iff _ _).mpr h0
    rw [QuantumNoCloningUnitary.bb84_zero_plus_overlap] at h
    norm_num at h
  · have h := (QuantumNoCloningUnitary.overlap_one_iff _ _
      (QuantumBB84ProtocolQBER.ket_normalized 0 0)
      (QuantumBB84ProtocolQBER.ket_normalized 1 0)).mpr h1
    rw [QuantumNoCloningUnitary.bb84_zero_plus_overlap] at h
    norm_num at h

/-- The support and commutation conclusions follow from the unitary relation.
Obtaining that relation from broadcasting remains a separate open obligation. -/
theorem saturation_intertwiner_marginal_commutes {d : ℕ}
    (W : Matrix.unitaryGroup (Fin d × Fin d) ℂ) (S : Joint d)
    (μ : Fin d → ℝ) (hμ : ∀ i, 0 < μ i)
    (he : (W : Joint d) * S =
      S * Matrix.diagonal (fun a : Fin d × Fin d => ((μ a.2 / μ a.1 : ℝ) : ℂ))) :
    Matrix.diagonal (fun i => (μ i : ℂ)) * partial_trace_B (S.conjTranspose * S) =
      partial_trace_B (S.conjTranspose * S) * Matrix.diagonal (fun i => (μ i : ℂ)) := by
  apply saturation_support_marginal_commutes
  intro i j hij
  exact saturation_intertwiner_support W S μ hμ he i j
    (fun h => hij (congrArg (fun x : ℝ => (x : ℂ)) h))

/-- The unitary-plus-blank model of module 141 is an actual CPTP channel here. -/
def unitaryBlankChannel {d : ℕ} (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (b : QuantumNoCloningUnitary.Ket d) (hb : QuantumNoCloningUnitary.Normalized b) : CPTPMap d :=
  (unitaryChannel U).comp (appendStateChannel (QuantumNoCloningUnitary.rho b)
    ⟨QuantumNoCloningUnitary.rho_positive b, QuantumNoCloningUnitary.rho_trace b hb⟩)

theorem unitary_density_cloning_implies_broadcasting {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (b ψ : QuantumNoCloningUnitary.Ket d) (hb : QuantumNoCloningUnitary.Normalized b)
    (hψ : QuantumNoCloningUnitary.Normalized ψ)
    (hc : QuantumNoCloningUnitary.DensityClones (U : Joint d) b ψ) :
    Broadcasts (unitaryBlankChannel U b hb) (QuantumNoCloningUnitary.rho ψ) := by
  have he : (unitaryBlankChannel U b hb).toLinearMap (QuantumNoCloningUnitary.rho ψ) =
      QuantumNoCloningUnitary.rho ψ ⊗ₖ QuantumNoCloningUnitary.rho ψ := by
    change (unitaryChannel U).toLinearMap _ = _
    rw [unitaryChannel_apply]
    exact hc
  constructor
  · rw [he, partial_trace_B_tensor, QuantumNoCloningUnitary.rho_trace ψ hψ, one_smul]
  · rw [he, partial_trace_A_tensor, QuantumNoCloningUnitary.rho_trace ψ hψ, one_smul]

theorem unitary_cloned_pair_canBroadcast {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (b ψ φ : QuantumNoCloningUnitary.Ket d) (hb : QuantumNoCloningUnitary.Normalized b)
    (hψ : QuantumNoCloningUnitary.Normalized ψ) (hφ : QuantumNoCloningUnitary.Normalized φ)
    (hcψ : QuantumNoCloningUnitary.DensityClones (U : Joint d) b ψ)
    (hcφ : QuantumNoCloningUnitary.DensityClones (U : Joint d) b φ) :
    CanBroadcast (QuantumNoCloningUnitary.rho ψ) (QuantumNoCloningUnitary.rho φ) :=
  ⟨unitaryBlankChannel U b hb,
    unitary_density_cloning_implies_broadcasting U b ψ hb hψ hcψ,
    unitary_density_cloning_implies_broadcasting U b φ hb hφ hcφ⟩

/-- Final algebraic step after obtaining a positive invertible geometric-mean
operator. Neither premise is assumed by the definition of a channel. -/
theorem commutation_from_invertible_sandwich {d : ℕ} (A B M : Q d)
    (hM : IsUnit M) (hA : A = M * B * M) (hc : M * A = A * M) : A * B = B * A := by
  have hMB : M * B = B * M := by
    apply hM.mul_right_cancel
    apply hM.mul_left_cancel
    simpa [hA, Matrix.mul_assoc] using hc
  have hBM : Commute B M := hMB.symm
  have hh := (hBM.mul_right (Commute.refl B)).mul_right hBM
  rw [hA]
  exact hh.eq.symm

/-! ## Necessity by symmetric logarithmic derivatives

For τ = ρ + σ, spectral division constructs a Hermitian A satisfying
Aτ + τA = 2ρ, including on the kernel of τ. Complete positivity supplies
Kraus operators. Preservation of both marginals makes the sum of the
squared Kraus intertwiner defects vanish. Thus (A ⊗ 1) E(τ) = (1 ⊗ A) E(τ).
Taking partial traces yields Aτ = τA and hence ρσ = σρ.
-/
open Matrix
open scoped MatrixOrder

/-- A Kraus representation is derived from block complete positivity. -/
theorem Channel.exists_kraus {d : ℕ} {κ : Type*} [Fintype κ]
    (E : Channel (Fin d) κ) :
    ∃ K : (Fin d × κ) → Matrix κ (Fin d) ℂ, E.toLinearMap = krausMap K := by
  classical
  let v : Fin d × Fin d → ℂ := fun a => if a.1 = a.2 then 1 else 0
  let C := amplify E.toLinearMap d (vecMulVec v (star v))
  have hC : C.PosSemidef := E.completely_positive _ _ (posSemidef_vecMulVec_self_star v)
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hC.nonneg
  let K : (Fin d × κ) → Matrix κ (Fin d) ℂ := fun a u i => star (S a (i, u))
  refine ⟨K, ?_⟩
  have hc (i j : Fin d) (u w : κ) :
      E.toLinearMap (single i j 1) u w = ∑ a, K a u i * star (K a w j) := by
    have hh := congrFun (congrFun hS (i, u)) (j, w)
    change C (i, u) (j, w) = _ at hh
    have hv (a b : Fin d) :
        (fun u w => vecMulVec v (star v) (a,u) (b,w)) = single a b 1 := by
      ext u w
      by_cases ha : a = u <;> by_cases hb : b = w <;>
        simp [vecMulVec, v, ha, hb]
    simpa [C, amplify, hv, K, Matrix.mul_apply] using hh
  apply LinearMap.ext
  intro X
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  have hs (i j : Fin d) : E.toLinearMap (single i j (X i j)) =
      krausMap K (single i j (X i j)) := by
    have hi : single i j (X i j) = (X i j) • single i j (1 : ℂ) := by
      simp
    rw [hi, map_smul, map_smul]
    congr 1
    ext u w
    simpa [krausMap, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.single_apply, Matrix.conjTranspose_apply, ite_and, eq_comm] using hc i j u w
  simp_rw [hs]
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]

theorem partial_trace_B_mul_left {d : ℕ} (A : Q d) (X : Joint d) :
    partial_trace_B ((A ⊗ₖ 1) * X) = A * partial_trace_B X := by
  ext i j
  simp only [partial_trace_B, QuantumPOVMNaimarkDilation.partialTrace, Matrix.mul_apply,
    kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Fintype.sum_prod_type, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.mul_sum]
  exact Finset.sum_comm

theorem partial_trace_B_mul_right {d : ℕ} (A : Q d) (X : Joint d) :
    partial_trace_B (X * (A ⊗ₖ 1)) = partial_trace_B X * A := by
  ext i j
  simp only [partial_trace_B, QuantumPOVMNaimarkDilation.partialTrace, Matrix.mul_apply,
    kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, Fintype.sum_prod_type,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_mul]
  exact Finset.sum_comm

theorem partial_trace_B_local_cyclic {d : ℕ} (A : Q d) (X : Joint d) :
    partial_trace_B ((1 ⊗ₖ A) * X) = partial_trace_B (X * (1 ⊗ₖ A)) := by
  ext i j
  simp only [partial_trace_B, QuantumPOVMNaimarkDilation.partialTrace, Matrix.mul_apply,
    kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul, Fintype.sum_prod_type,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, mul_ite, mul_zero, Finset.sum_ite_eq']
  rw [Finset.sum_comm]
  congr 1
  ext a
  congr 1
  ext b
  exact mul_comm _ _

theorem trace_local_left {d : ℕ} (A : Q d) (X : Joint d) :
    ((A ⊗ₖ 1) * X).trace = (A * partial_trace_B X).trace := by
  rw [← partial_trace_B_mul_left, partial_trace_B_trace]

theorem trace_local_right {d : ℕ} (A : Q d) (X : Joint d) :
    ((1 ⊗ₖ A) * X).trace = (A * partial_trace_A X).trace := by
  simp only [trace, diag_apply, Matrix.mul_apply, kroneckerMap_apply, Matrix.one_apply,
    ite_mul, one_mul, zero_mul, Fintype.sum_prod_type, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, partial_trace_A,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

/-- Equality of a quadratic channel bound gives a Kraus intertwiner on the
support of the input. No invertibility of that input is needed. -/
theorem kraus_quadratic_saturation {d : ℕ} {κ η : Type*} [Fintype κ] [Fintype η]
    (E : Channel (Fin d) κ) (K : η → Matrix κ (Fin d) ℂ)
    (hK : E.toLinearMap = krausMap K) (S A : Q d) (B : Mat κ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hquad : (B * B * E.toLinearMap (S * Sᴴ)).trace = (A * A * (S * Sᴴ)).trace)
    (hcross : (B * E.toLinearMap (A * (S * Sᴴ) + (S * Sᴴ) * A)).trace =
      2 * (A * A * (S * Sᴴ)).trace) :
    ∀ j, B * K j * S = K j * A * S := by
  classical
  let L (j : η) := B * K j * S - K j * A * S
  have hexp : ∑ j, L j * (L j)ᴴ =
      B * E.toLinearMap (S * Sᴴ) * B -
        B * E.toLinearMap ((S * Sᴴ) * A) -
        E.toLinearMap (A * (S * Sᴴ)) * B +
        E.toLinearMap (A * (S * Sᴴ) * A) := by
    rw [hK]
    simp only [krausMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum,
      Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [L, conjTranspose_sub, conjTranspose_mul, hA.eq, hB.eq,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  have hz : ∑ j, (L j * (L j)ᴴ).trace = 0 := by
    rw [← Matrix.trace_sum, hexp, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
      E.trace_preserving]
    have ht : (B * E.toLinearMap (S * Sᴴ) * B).trace =
        (B * B * E.toLinearMap (S * Sᴴ)).trace := by
      rw [Matrix.trace_mul_cycle]
    have ht' : (A * (S * Sᴴ) * A).trace = (A * A * (S * Sᴴ)).trace := by
      rw [Matrix.trace_mul_cycle]
    have ht'' : (E.toLinearMap (A * (S * Sᴴ)) * B).trace =
        (B * E.toLinearMap (A * (S * Sᴴ))).trace := Matrix.trace_mul_comm _ _
    rw [ht, ht', ht'', hquad]
    simp only [map_add, Matrix.mul_add, Matrix.trace_add] at hcross
    linear_combination -hcross
  have hzj (j : η) : (L j * (L j)ᴴ).trace = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      (Matrix.posSemidef_self_mul_conjTranspose (L i)).trace_nonneg)).mp hz j (Finset.mem_univ j)
  intro j
  exact sub_eq_zero.mp (Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp (hzj j))


theorem Broadcasts.add {d : ℕ} {E : CPTPMap d} {ρ σ : Q d}
    (hρ : Broadcasts E ρ) (hσ : Broadcasts E σ) : Broadcasts E (ρ + σ) := by
  constructor
  · rw [map_add]
    have ha : ∀ X Y : Joint d, partial_trace_B (X + Y) =
        partial_trace_B X + partial_trace_B Y := by
      intro X Y
      ext i j
      simp [partial_trace_B, QuantumPOVMNaimarkDilation.partialTrace,
        Matrix.add_apply, Finset.sum_add_distrib]
    rw [ha, hρ.1, hσ.1]
  · rw [map_add]
    have ha : ∀ X Y : Joint d, partial_trace_A (X + Y) =
        partial_trace_A X + partial_trace_A Y := by
      intro X Y
      ext i j
      simp [partial_trace_A, Matrix.add_apply, Finset.sum_add_distrib]
    rw [ha, hρ.2, hσ.2]

/-- A broadcast pair with a symmetric logarithmic derivative must commute.
The derivative is an auxiliary witness, constructed below for arbitrary densities. -/
theorem broadcasting_commutes_of_sld {d : ℕ} (E : CPTPMap d) (ρ τ A : Q d)
    (hτ : τ.PosSemidef) (hρb : Broadcasts E ρ) (hτb : Broadcasts E τ)
    (hA : A.IsHermitian) (hsld : A * τ + τ * A = (2 : ℂ) • ρ) :
    ρ * τ = τ * ρ := by
  classical
  obtain ⟨K, hK⟩ := E.exists_kraus
  obtain ⟨S₀, hS₀⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hτ.nonneg
  change τ = S₀ᴴ * S₀ at hS₀
  let S := S₀ᴴ
  have hS : S * Sᴴ = τ := by simpa [S] using hS₀.symm
  have hsldtrace : (A * ((2 : ℂ) • ρ)).trace = 2 * (A * A * τ).trace := by
    rw [← hsld, Matrix.mul_add, Matrix.trace_add, ← Matrix.mul_assoc]
    have ht : (A * (τ * A)).trace = (A * A * τ).trace := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    rw [ht]
    ring
  have hleft : ∀ j, (A ⊗ₖ 1) * K j * S = K j * A * S := by
    apply kraus_quadratic_saturation E K hK S A _ hA
      (by simp [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hA.eq])
    · rw [hS, ← Matrix.mul_kronecker_mul, Matrix.one_mul, trace_local_left, hτb.1]
    · rw [hS, hsld, map_smul, Matrix.mul_smul, Matrix.trace_smul,
        trace_local_left, hρb.1]
      simpa [Matrix.mul_smul, Matrix.trace_smul] using hsldtrace
  have hright : ∀ j, (1 ⊗ₖ A) * K j * S = K j * A * S := by
    apply kraus_quadratic_saturation E K hK S A _ hA
      (by simp [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hA.eq])
    · rw [hS, ← Matrix.mul_kronecker_mul, Matrix.one_mul, trace_local_right, hτb.2]
    · rw [hS, hsld, map_smul, Matrix.mul_smul, Matrix.trace_smul,
        trace_local_right, hρb.2]
      simpa [Matrix.mul_smul, Matrix.trace_smul] using hsldtrace
  have hlr : (A ⊗ₖ 1) * E.toLinearMap τ = (1 ⊗ₖ A) * E.toLinearMap τ := by
    rw [hK, ← hS]
    simp only [krausMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hj := (hleft j).trans (hright j).symm
    simpa only [Matrix.mul_assoc] using congrArg (fun X => X * (Sᴴ * (K j)ᴴ)) hj
  have hrl : E.toLinearMap τ * (A ⊗ₖ 1) = E.toLinearMap τ * (1 ⊗ₖ A) := by
    have hh := congrArg Matrix.conjTranspose hlr
    simpa only [Matrix.conjTranspose_mul, (E.positive τ hτ).isHermitian.eq,
      Matrix.conjTranspose_kronecker, hA.eq, Matrix.conjTranspose_one] using hh
  have hcomm : A * τ = τ * A := by
    have hh := congrArg partial_trace_B hlr
    rw [partial_trace_B_mul_left, partial_trace_B_local_cyclic, ← hrl,
      partial_trace_B_mul_right, hτb.1] at hh
    exact hh
  have hρ : (2 : ℂ) • (A * τ) = (2 : ℂ) • ρ := by
    simpa [← hcomm, two_smul ℂ] using hsld
  have hρ' : A * τ = ρ := (smul_right_injective _ (by norm_num : (2 : ℂ) ≠ 0)) hρ
  rw [← hρ', ← Matrix.mul_assoc, hcomm]


theorem psd_row_zero {d : ℕ} (R : Q d) (hR : R.PosSemidef) (i : Fin d)
    (hi : R i i = 0) : ∀ j, R i j = 0 := by
  have hv : star (Pi.single i (1 : ℂ)) ⬝ᵥ R *ᵥ (Pi.single i 1) = 0 := by
    simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using hi
  have hz := (hR.dotProduct_mulVec_zero_iff _).mp hv
  intro j
  have hj := congrFun hz j
  have hj' : R j i = 0 := by simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hj
  have hh := congrFun (congrFun hR.isHermitian.eq i) j
  simpa [Matrix.conjTranspose_apply, hj'] using hh.symm

theorem exists_symmetric_logarithmic_derivative {d : ℕ} (ρ σ : Q d)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    ∃ A : Q d, A.IsHermitian ∧ A * (ρ + σ) + (ρ + σ) * A = (2 : ℂ) • ρ := by
  classical
  let τ := ρ + σ
  have hτ : τ.PosSemidef := hρ.add hσ
  let U := hτ.isHermitian.eigenvectorUnitary
  have hu : (U : Q d)ᴴ * (U : Q d) = 1 := Unitary.coe_star_mul_self U
  have hv : (U : Q d) * (U : Q d)ᴴ = 1 := Unitary.coe_mul_star_self U
  let μ := hτ.isHermitian.eigenvalues
  let D : Q d := diagonal (fun i => (μ i : ℂ))
  have hτd : τ = (U : Q d) * D * (U : Q d)ᴴ := hτ.isHermitian.spectral_theorem
  let R := (U : Q d)ᴴ * ρ * (U : Q d)
  let V := (U : Q d)ᴴ * σ * (U : Q d)
  have hR : R.PosSemidef := hρ.conjTranspose_mul_mul_same _
  have hV : V.PosSemidef := hσ.conjTranspose_mul_mul_same _
  have hRV : R + V = D := by
    dsimp [R, V]
    rw [← Matrix.add_mul, ← Matrix.mul_add]
    change (U : Q d)ᴴ * τ * (U : Q d) = D
    rw [hτd]
    simp only [← Matrix.mul_assoc, hu, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hu, Matrix.mul_one]
  have hzero (i : Fin d) (hi : μ i = 0) : ∀ j, R i j = 0 := by
    apply psd_row_zero R hR i
    have hh := congrFun (congrFun hRV i) i
    have h1 := hR.diag_nonneg (i := i)
    have h2 := hV.diag_nonneg (i := i)
    have hsum : R i i + V i i = 0 := by simpa [D, hi] using hh
    exact le_antisymm (hsum ▸ le_add_of_nonneg_right h2) h1
  let B : Q d := fun i j => 2 * R i j / ((μ i + μ j : ℝ) : ℂ)
  have hB : B.IsHermitian := by
    ext i j
    change star (2 * R j i / ((μ j + μ i : ℝ) : ℂ)) =
      2 * R i j / ((μ i + μ j : ℝ) : ℂ)
    simp only [star_div₀, star_mul, star_ofNat, Complex.star_def, Complex.conj_ofReal]
    have hh := congrFun (congrFun hR.isHermitian.eq i) j
    simp only [Matrix.conjTranspose_apply] at hh
    change (starRingEnd ℂ) (R j i) = R i j at hh
    rw [hh, add_comm (μ j) (μ i), mul_comm (R i j) 2]
  have hBD : B * D + D * B = (2 : ℂ) • R := by
    ext i j
    change (B * diagonal (fun i => (μ i : ℂ))) i j +
      (diagonal (fun i => (μ i : ℂ)) * B) i j = 2 * R i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hz : μ i + μ j = 0
    · have hi : μ i = 0 := by
        have hp := hτ.eigenvalues_nonneg i
        have hq := hτ.eigenvalues_nonneg j
        change 0 ≤ μ i at hp
        change 0 ≤ μ j at hq
        linarith
      simp [B, hzero i hi j]
    · have hz' : ((μ i + μ j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hz
      dsimp [B]
      push_cast at hz' ⊢
      field_simp [hz']
      ring
  refine ⟨(U : Q d) * B * (U : Q d)ᴴ, ?_, ?_⟩
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_mul, hB.eq,
      Matrix.mul_assoc]
  · change (U : Q d) * B * (U : Q d)ᴴ * τ +
        τ * ((U : Q d) * B * (U : Q d)ᴴ) = (2 : ℂ) • ρ
    rw [hτd]
    have hu := Unitary.coe_star_mul_self U
    change (U : Q d)ᴴ * (U : Q d) = 1 at hu
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (U : Q d)ᴴ, hu,
      Matrix.one_mul]
    have hh := congrArg (fun X => (U : Q d) * X * (U : Q d)ᴴ) hBD
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc] at hh
    have hr : (U : Q d) * R * (U : Q d)ᴴ = ρ := by
      dsimp [R]
      simp only [← Matrix.mul_assoc, hv, Matrix.one_mul]
      simp only [Matrix.mul_assoc, hv, Matrix.mul_one]
    rw [← Matrix.mul_assoc (U : Q d) R, hr] at hh
    exact hh


/-- Necessity for all finite-dimensional density matrices, without a rank assumption. -/
theorem quantum_broadcasting_necessity {d : ℕ} (ρ σ : Q d)
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) (hb : CanBroadcast ρ σ) :
    ρ * σ = σ * ρ := by
  obtain ⟨E, heρ, heσ⟩ := hb
  obtain ⟨A, hA, hsld⟩ := exists_symmetric_logarithmic_derivative ρ σ hρ.1 hσ.1
  have hc := broadcasting_commutes_of_sld E ρ (ρ + σ) A (hρ.1.add hσ.1)
    heρ (heρ.add heσ) hA hsld
  simpa only [Matrix.mul_add, Matrix.add_mul, add_left_cancel_iff] using hc

/-- BCFJS no-broadcasting equivalence; outputs need not be product states. -/
theorem quantum_no_broadcasting_theorem {d : ℕ} (ρ σ : Q d)
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    CanBroadcast ρ σ ↔ ρ * σ = σ * ρ :=
  ⟨quantum_broadcasting_necessity ρ σ hρ hσ,
    quantum_broadcasting_constructive_sufficiency ρ σ hρ hσ⟩

open QuantumNoCloningUnitary in
/-- Pure projectors can be broadcast precisely when orthogonal or identical. -/
theorem quantum_pure_state_no_broadcasting {d : ℕ} (ψ φ : Ket d)
    (hψ : Normalized ψ) (hφ : Normalized φ) :
    CanBroadcast (rho ψ) (rho φ) ↔ ψᴴ * φ = 0 ∨ rho ψ = rho φ := by
  rw [quantum_no_broadcasting_theorem _ _
    ⟨rho_positive ψ, rho_trace ψ hψ⟩ ⟨rho_positive φ, rho_trace φ hφ⟩]
  exact pure_projectors_commute_iff ψ φ hψ hφ


open QuantumNoCloningUnitary in
theorem pure_projectors_equal_iff_phase {d : ℕ} (ψ φ : Ket d)
    (hψ : Normalized ψ) (hφ : Normalized φ) :
    rho ψ = rho φ ↔ ∃ z : ℂ, Complex.normSq z = 1 ∧ ψ = z • φ := by
  constructor
  · intro he
    refine ⟨overlap φ ψ, (overlap_one_iff φ ψ hφ hψ).mpr he.symm, ?_⟩
    have hp : rho ψ * ψ = ψ := by
      rw [rho, Matrix.mul_assoc, hψ, Matrix.mul_one]
    rw [he] at hp
    have hscalar : φᴴ * ψ = (overlap φ ψ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
      ext i j
      fin_cases i; fin_cases j
      simp [overlap]
    simpa [rho, Matrix.mul_assoc, hscalar, Matrix.mul_smul] using hp.symm
  · rintro ⟨z, hz, rfl⟩
    exact phase_density φ z hz

open QuantumNoCloningUnitary in
theorem quantum_pure_state_phase_criterion {d : ℕ} (ψ φ : Ket d)
    (hψ : Normalized ψ) (hφ : Normalized φ) :
    CanBroadcast (rho ψ) (rho φ) ↔
      ψᴴ * φ = 0 ∨ ∃ z : ℂ, Complex.normSq z = 1 ∧ ψ = z • φ := by
  rw [quantum_pure_state_no_broadcasting ψ φ hψ hφ,
    pure_projectors_equal_iff_phase ψ φ hψ hφ]

open QuantumNoCloningUnitary in
theorem zero_plus_not_broadcastable : ¬ CanBroadcast (rho zeroKet) (rho plusQubit) := by
  intro hb
  apply zero_plus_projectors_noncommuting
  exact quantum_broadcasting_necessity _ _
    ⟨rho_positive _, rho_trace _ (QuantumBB84ProtocolQBER.ket_normalized _ _)⟩
    ⟨rho_positive _, rho_trace _ (QuantumBB84ProtocolQBER.ket_normalized _ _)⟩ hb

open QuantumNoCloningUnitary in
/-- The general CPTP theorem specializes to a unitary channel with a fixed blank. -/
theorem bridge_to_quantum_no_cloning {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ) (b ψ φ : Ket d)
    (hb : Normalized b) (hψ : Normalized ψ) (hφ : Normalized φ)
    (hcψ : DensityClones (U : Joint d) b ψ) (hcφ : DensityClones (U : Joint d) b φ) :
    ψᴴ * φ = 0 ∨ rho ψ = rho φ :=
  (quantum_pure_state_no_broadcasting ψ φ hψ hφ).mp
    (unitary_cloned_pair_canBroadcast U b ψ φ hb hψ hφ hcψ hcφ)

structure QuantumNoBroadcastingMixedSuite : Prop where
  equivalence : ∀ {d} (ρ σ : Q d), IsDensityMatrix ρ → IsDensityMatrix σ →
    (CanBroadcast ρ σ ↔ ρ * σ = σ * ρ)
  constructive : ∀ {d} (ρ σ : Q d), IsDensityMatrix ρ → IsDensityMatrix σ →
    ρ * σ = σ * ρ → CanBroadcast ρ σ
  necessity : ∀ {d} (ρ σ : Q d), IsDensityMatrix ρ → IsDensityMatrix σ →
    CanBroadcast ρ σ → ρ * σ = σ * ρ
  pure_criterion : ∀ {d} (ψ φ : QuantumNoCloningUnitary.Ket d),
    QuantumNoCloningUnitary.Normalized ψ → QuantumNoCloningUnitary.Normalized φ →
    (CanBroadcast (QuantumNoCloningUnitary.rho ψ) (QuantumNoCloningUnitary.rho φ) ↔
      ψᴴ * φ = 0 ∨ ∃ z : ℂ, Complex.normSq z = 1 ∧ ψ = z • φ)
  identical : ∀ {d} (ρ : Q d), IsDensityMatrix ρ → CanBroadcast ρ ρ
  qubit_obstruction : ¬ CanBroadcast
    (QuantumNoCloningUnitary.rho QuantumNoCloningUnitary.zeroKet)
    (QuantumNoCloningUnitary.rho QuantumNoCloningUnitary.plusQubit)
  unitary_bridge : ∀ {d} (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (b ψ φ : QuantumNoCloningUnitary.Ket d),
    QuantumNoCloningUnitary.Normalized b → QuantumNoCloningUnitary.Normalized ψ →
    QuantumNoCloningUnitary.Normalized φ →
    QuantumNoCloningUnitary.DensityClones (U : Joint d) b ψ →
    QuantumNoCloningUnitary.DensityClones (U : Joint d) b φ →
    ψᴴ * φ = 0 ∨ QuantumNoCloningUnitary.rho ψ = QuantumNoCloningUnitary.rho φ

theorem verification_suite : QuantumNoBroadcastingMixedSuite where
  equivalence := quantum_no_broadcasting_theorem
  constructive := quantum_broadcasting_constructive_sufficiency
  necessity := quantum_broadcasting_necessity
  pure_criterion := quantum_pure_state_phase_criterion
  identical := quantum_identical_states_broadcasting
  qubit_obstruction := zero_plus_not_broadcastable
  unitary_bridge := bridge_to_quantum_no_cloning

end QuantumNoBroadcastingMixed
