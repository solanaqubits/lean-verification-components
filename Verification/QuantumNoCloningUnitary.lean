/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumNoCloningTheorem
import Verification.QuantumBB84ProtocolQBER
import Verification.QuantumPOVMNaimarkDilation
import Mathlib.Tactic.NoncommRing

/-! Exact pure-state cloning with a fixed blank and a common unitary.
Vector equality and equality of pure density matrices are deliberately distinct. -/
noncomputable section
open scoped BigOperators ComplexOrder Kronecker
namespace QuantumNoCloningUnitary
abbrev Ket (d : ℕ) := Matrix (Fin d) (Fin 1) ℂ
abbrev Q (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
abbrev Joint (d : ℕ) := Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ
variable {d : ℕ}
def Normalized (ψ : Ket d) : Prop := ψ.conjTranspose * ψ = 1
def Unitary (U : Joint d) : Prop := U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1
def rho (ψ : Ket d) : Q d := ψ * ψ.conjTranspose
def overlap (ψ φ : Ket d) : ℂ := (ψ.conjTranspose * φ) 0 0
def overlapSq (ψ φ : Ket d) : ℝ := Complex.normSq (overlap ψ φ)
def VectorClones (U : Joint d) (b ψ : Ket d) : Prop := U * (ψ ⊗ₖ b) = ψ ⊗ₖ ψ
def DensityClones (U : Joint d) (b ψ : Ket d) : Prop := 
  U * (rho ψ ⊗ₖ rho b) * U.conjTranspose = rho ψ ⊗ₖ rho ψ

@[simp] theorem rho_hermitian (ψ : Ket d) : (rho ψ).conjTranspose = rho ψ := by
  simp [rho]
theorem rho_positive (ψ : Ket d) : (rho ψ).PosSemidef := 
  Matrix.posSemidef_self_mul_conjTranspose ψ
theorem rho_idempotent (ψ : Ket d) (hψ : Normalized ψ) : rho ψ * rho ψ = rho ψ := by
  calc
    _ = ψ * (ψ.conjTranspose * ψ) * ψ.conjTranspose := by simp [rho, Matrix.mul_assoc]
    _ = rho ψ := by rw [hψ]; simp [rho]
theorem rho_trace (ψ : Ket d) (hψ : Normalized ψ) : (rho ψ).trace = 1 := by
  rw [rho, Matrix.trace_mul_comm, hψ]
  simp

theorem overlap_swap (ψ φ : Ket d) : overlap φ ψ = star (overlap ψ φ) := by
  have h := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0)
    (Matrix.conjTranspose_mul ψ.conjTranspose φ)
  simpa [overlap, Matrix.conjTranspose_apply] using h.symm

theorem trace_overlap (ψ φ : Ket d) : (rho ψ * rho φ).trace = (overlapSq ψ φ : ℂ) := by
  have h : (rho ψ * rho φ).trace = overlap φ ψ * overlap ψ φ := by
    calc
      _ = (ψ * (ψ.conjTranspose * φ) * φ.conjTranspose).trace := by
        simp [rho, Matrix.mul_assoc]
      _ = ((φ.conjTranspose * ψ) * (ψ.conjTranspose * φ)).trace := 
        Matrix.trace_mul_cycle _ _ _
      _ = _ := by
        simp only [Matrix.trace, Fin.sum_univ_one, Matrix.diag_apply]
        rw [Matrix.mul_apply]
        simp only [Fin.sum_univ_one]
        rfl
  rw [h, overlap_swap]
  simpa [overlapSq] using (Complex.normSq_eq_conj_mul_self (z := overlap ψ φ)).symm

theorem tensor_inner (ψ φ b c : Ket d) :
    (ψ ⊗ₖ b).conjTranspose * (φ ⊗ₖ c) = 
      (ψ.conjTranspose * φ) ⊗ₖ (b.conjTranspose * c) := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]

theorem unitary_inner (U : Joint d) (hU : Unitary U)
    {ι : Type*} (v w : Matrix (Fin d × Fin d) ι ℂ) :
    (U * v).conjTranspose * (U * w) = v.conjTranspose * w := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U.conjTranspose, hU.1, Matrix.one_mul]

theorem vector_cloning_overlap_square (U : Joint d) (hU : Unitary U)
    (b ψ φ : Ket d) (hb : Normalized b)
    (hψ : VectorClones U b ψ) (hφ : VectorClones U b φ) :
    overlap ψ φ = overlap ψ φ ^ 2 := by
  have h := unitary_inner U hU (ψ ⊗ₖ b) (φ ⊗ₖ b)
  rw [hψ, hφ, tensor_inner, tensor_inner, hb] at h
  have hh := congrArg (fun M => M (0,0) (0,0)) h
  simpa [Matrix.kroneckerMap_apply, overlap, pow_two] using hh.symm

theorem complex_square_cases (c : ℂ) (h : c = c ^ 2) : c = 0 ∨ c = 1 := by
  have hmul : c * (c-1) = 0 := by
    calc c * (c-1) = c ^ 2-c := by ring
         _ = 0 := by rw [← h]; ring
  rcases mul_eq_zero.mp hmul with hz | ho
  · exact Or.inl hz
  · exact Or.inr (sub_eq_zero.mp ho)

theorem conjugation_trace (U : Joint d) (hU : Unitary U) (M : Joint d) :
    (U * M * U.conjTranspose).trace = M.trace := by
  rw [Matrix.trace_mul_comm]
  simp [← Matrix.mul_assoc, hU.1]

theorem conjugation_product_trace (U : Joint d) (hU : Unitary U) (A B : Joint d) :
    ((U * A * U.conjTranspose) * (U * B * U.conjTranspose)).trace = (A * B).trace := by
  have h : (U * A * U.conjTranspose) * (U * B * U.conjTranspose) =
      U * (A * B) * U.conjTranspose := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U.conjTranspose, hU.1, Matrix.one_mul]
  rw [h, conjugation_trace U hU]

theorem density_cloning_overlap_square (U : Joint d) (hU : Unitary U)
    (b ψ φ : Ket d) (hb : Normalized b)
    (hψ : DensityClones U b ψ) (hφ : DensityClones U b φ) :
    (rho ψ * rho φ).trace = (rho ψ * rho φ).trace ^ 2 := by
  have h := conjugation_product_trace U hU (rho ψ ⊗ₖ rho b) (rho φ ⊗ₖ rho b)
  rw [hψ, hφ, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.trace_kronecker, Matrix.trace_kronecker, rho_idempotent b hb, rho_trace b hb] at h
  simpa [pow_two] using h.symm

/-- Squared Hilbert-Schmidt distance supplies the upper overlap bound and equality case. -/
theorem density_distance_trace (ψ φ : Ket d) (hψ : Normalized ψ) (hφ : Normalized φ) :
    ((rho ψ-rho φ).conjTranspose * (rho ψ-rho φ)).trace = 
      2 - 2 * (overlapSq ψ φ : ℂ) := by
  rw [Matrix.conjTranspose_sub, rho_hermitian, rho_hermitian, sub_mul, mul_sub, mul_sub]
  simp only [Matrix.trace_sub, rho_idempotent ψ hψ, rho_idempotent φ hφ,
    rho_trace ψ hψ, rho_trace φ hφ]
  rw [Matrix.trace_mul_comm (rho φ), trace_overlap]
  ring

theorem overlap_bounds (ψ φ : Ket d) (hψ : Normalized ψ) (hφ : Normalized φ) :
    0 ≤ overlapSq ψ φ ∧ overlapSq ψ φ ≤ 1 := by
  refine ⟨Complex.normSq_nonneg _, ?_⟩
  have h := (Matrix.posSemidef_conjTranspose_mul_self (rho ψ-rho φ)).trace_nonneg
  rw [density_distance_trace ψ φ hψ hφ] at h
  have hr := (Complex.nonneg_iff.mp h).1
  norm_num [Complex.sub_re, Complex.mul_re] at hr
  linarith

theorem overlap_zero_iff (ψ φ : Ket d) : overlapSq ψ φ = 0 ↔ ψ.conjTranspose * φ = 0 := by
  rw [overlapSq, Complex.normSq_eq_zero]
  constructor
  · intro h
    ext i j
    fin_cases i; fin_cases j
    exact h
  · intro h
    simp [overlap, h]

theorem overlap_one_iff (ψ φ : Ket d) (hψ : Normalized ψ) (hφ : Normalized φ) :
    overlapSq ψ φ = 1 ↔ rho ψ = rho φ := by
  constructor
  · intro h
    apply sub_eq_zero.mp
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    rw [density_distance_trace ψ φ hψ hφ, h]
    norm_num
  · intro h
    have ht := trace_overlap ψ φ
    rw [h, rho_idempotent φ hφ, rho_trace φ hφ] at ht
    exact_mod_cast ht.symm

theorem density_cloning_real_overlap_square (U : Joint d) (hU : Unitary U)
    (b ψ φ : Ket d) (hb : Normalized b)
    (hψ : DensityClones U b ψ) (hφ : DensityClones U b φ) :
    overlapSq ψ φ = overlapSq ψ φ ^ 2 := by
  have h := density_cloning_overlap_square U hU b ψ φ hb hψ hφ
  rw [trace_overlap] at h
  exact_mod_cast h

theorem density_cloning_ortho_or_identical (U : Joint d) (hU : Unitary U)
    (b ψ φ : Ket d) (hb : Normalized b) (hnψ : Normalized ψ) (hnφ : Normalized φ)
    (hψ : DensityClones U b ψ) (hφ : DensityClones U b φ) :
    (overlapSq ψ φ = 0 ∧ ψ.conjTranspose * φ = 0) ∨
      (overlapSq ψ φ = 1 ∧ rho ψ = rho φ) := by
  have h := density_cloning_real_overlap_square U hU b ψ φ hb hψ hφ
  rcases QuantumNoCloningTheorem.cloning_overlap_quadratic _ h with hz | ho
  · exact Or.inl ⟨hz, (overlap_zero_iff ψ φ).mp hz⟩
  · exact Or.inr ⟨ho, (overlap_one_iff ψ φ hnψ hnφ).mp ho⟩

theorem phase_density (ψ : Ket d) (z : ℂ) (hz : Complex.normSq z = 1) : rho (z • ψ) = rho ψ := by
  simp only [rho, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hz' : star z * z = 1 := by
    simpa [hz] using (Complex.normSq_eq_conj_mul_self (z := z)).symm
  rw [hz', one_smul]

theorem phase_invariance (ψ : Ket d) (hψ : Normalized ψ) (z : ℂ)
    (hz : Complex.normSq z = 1) : rho (z • ψ) = rho ψ ∧ overlapSq ψ (z • ψ) = 1 := by
  refine ⟨phase_density ψ z hz, ?_⟩
  have h := trace_overlap ψ (z • ψ)
  rw [phase_density ψ z hz, rho_idempotent ψ hψ, rho_trace ψ hψ] at h
  exact_mod_cast h.symm

theorem vector_clones_density (U : Joint d) (b ψ : Ket d) (h : VectorClones U b ψ) :
    DensityClones U b ψ := by
  have heq := congrArg (fun M => M * M.conjTranspose) h
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker] at heq
  have hi : U * (rho ψ ⊗ₖ rho b) * U.conjTranspose = 
      (U * (ψ ⊗ₖ b)) * ((ψ.conjTranspose ⊗ₖ b.conjTranspose) * U.conjTranspose) := by
    rw [rho, rho, Matrix.mul_kronecker_mul]
    simp [Matrix.mul_assoc]
  unfold DensityClones
  rw [hi, heq, ← Matrix.mul_kronecker_mul]
  rfl

/-- A prescribed state can always be copied; this is not a common cloner for unknown inputs. -/
theorem single_state_cloner (b ψ : Ket d) (hb : Normalized b) (hψ : Normalized ψ) :
    ∃ U : Joint d, Unitary U ∧ VectorClones U b ψ := by
  have hi : (ψ ⊗ₖ b).conjTranspose * (ψ ⊗ₖ b) = 1 := by
    rw [tensor_inner, hψ, hb, Matrix.one_kronecker_one]
  have ho : (ψ ⊗ₖ ψ).conjTranspose * (ψ ⊗ₖ ψ) = 1 := by
    rw [tensor_inner, hψ, Matrix.one_kronecker_one]
  obtain ⟨U, hl, hr, hv⟩ := QuantumPOVMNaimarkDilation.unitary_between_isometries
    (ψ ⊗ₖ b) (ψ ⊗ₖ ψ) hi ho
  exact ⟨U, ⟨hl,hr⟩, hv⟩

def basisKet (i : Fin d) : Ket d := fun j _ => if j = i then 1 else 0

theorem basis_inner (i j : Fin d) :
    (basisKet i).conjTranspose * basisKet j = if i = j then 1 else 0 := by
  ext a b
  fin_cases a; fin_cases b
  by_cases h : i = j <;> simp [basisKet, Matrix.mul_apply, Matrix.conjTranspose_apply, h, eq_comm]

theorem basis_normalized (i : Fin d) : Normalized (basisKet i) := by
  simp [Normalized, basis_inner]

/-- The superposition is embedded in any two distinct coordinate directions. -/
def plusKet (i j : Fin d) : Ket d := 
  (QuantumBB84ProtocolQBER.rootTwo/2) • (basisKet i + basisKet j)

theorem plus_normalized (i j : Fin d) (hij : i ≠ j) : Normalized (plusKet i j) := by
  unfold Normalized plusKet
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, basis_inner,
    if_neg hij, if_neg hij.symm, add_zero, zero_add, star_div₀,
    RCLike.star_def, QuantumBB84ProtocolQBER.rootTwo_star, star_ofNat]
  ext a b
  fin_cases a; fin_cases b
  norm_num [Matrix.ofNat_apply]
  ring_nf
  norm_num

theorem basis_plus_overlap (i j : Fin d) (hij : i ≠ j) :
    overlapSq (basisKet i) (plusKet i j) = 1/2 := by
  have h : overlap (basisKet i) (plusKet i j) = QuantumBB84ProtocolQBER.rootTwo/2 := by
    simp [overlap, plusKet, Matrix.mul_smul, Matrix.mul_add, basis_inner, hij]
  rw [overlapSq, h]
  simp [QuantumBB84ProtocolQBER.rootTwo, Complex.normSq_ofReal]

theorem phase_invariance_exp (ψ : Ket d) (hψ : Normalized ψ) (θ : ℝ) :
    rho (Complex.exp ((θ:ℂ) * Complex.I) • ψ) = rho ψ ∧
      overlapSq ψ (Complex.exp ((θ:ℂ) * Complex.I) • ψ) = 1 := by
  apply phase_invariance ψ hψ
  rw [← Complex.sq_norm, Complex.norm_exp]
  simp

theorem pair_zero_plus_unclonable (i j : Fin d) (hij : i ≠ j)
    (U : Joint d) (hU : Unitary U) (b : Ket d) (hb : Normalized b) :
    ¬ (DensityClones U b (basisKet i) ∧ DensityClones U b (plusKet i j)) := by
  rintro ⟨h0,hp⟩
  have h := density_cloning_real_overlap_square U hU b _ _ hb h0 hp
  rw [basis_plus_overlap i j hij] at h
  norm_num at h

theorem no_universal_unitary_cloning (hd : 2 ≤ d) :
    ¬ ∃ (U : Joint d) (b : Ket d), Unitary U ∧ Normalized b ∧
      ∀ ψ : Ket d, Normalized ψ → DensityClones U b ψ := by
  rintro ⟨U,b,hU,hb,h⟩
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i,j]
  exact pair_zero_plus_unclonable i j hij U hU b hb
    ⟨h _ (basis_normalized i),h _ (plus_normalized i j hij)⟩

theorem no_universal_vector_cloning (hd : 2 ≤ d) :
    ¬ ∃ (U : Joint d) (b : Ket d), Unitary U ∧ Normalized b ∧
      ∀ ψ : Ket d, Normalized ψ → VectorClones U b ψ := by
  rintro ⟨U,b,hU,hb,h⟩
  exact no_universal_unitary_cloning hd
    ⟨U,b,hU,hb,fun ψ hn => vector_clones_density U b ψ (h ψ hn)⟩

theorem bridge_to_quantum_no_cloning_theorem (U : Joint d) (hU : Unitary U)
    (b ψ φ : Ket d) (hb : Normalized b)
    (hψ : DensityClones U b ψ) (hφ : DensityClones U b φ) :
    overlapSq ψ φ = overlapSq ψ φ ^ 2 ∧ (overlapSq ψ φ = 0 ∨ overlapSq ψ φ = 1) := by
  have h := density_cloning_real_overlap_square U hU b ψ φ hb hψ hφ
  exact ⟨h,QuantumNoCloningTheorem.cloning_overlap_quadratic _ h⟩

abbrev zeroKet : Ket 2 := QuantumBB84ProtocolQBER.ket 0 0
abbrev oneKet : Ket 2 := QuantumBB84ProtocolQBER.ket 0 1
abbrev plusQubit : Ket 2 := QuantumBB84ProtocolQBER.ket 1 0

def CNOT : Joint 2 := fun i j => if i.1 = j.1 ∧ i.2 = j.1 + j.2 then 1 else 0

theorem cnot_unitary : Unitary CNOT := by
  constructor <;> ext ⟨i,j⟩ ⟨k,l⟩ <;>
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [CNOT, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, Prod.ext_iff,
      show (1:Fin 2) + 1 = 0 by decide]

theorem cnot_clones_computational_basis : VectorClones CNOT zeroKet zeroKet ∧
    VectorClones CNOT zeroKet oneKet := by
  constructor <;> ext ⟨i,j⟩ ⟨a,b⟩ <;>
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [CNOT, QuantumBB84ProtocolQBER.ket, Matrix.mul_apply,
      Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

def bell : Matrix (Fin 2 × Fin 2) (Fin 1 × Fin 1) ℂ := 
  (QuantumBB84ProtocolQBER.rootTwo/2) • (zeroKet ⊗ₖ zeroKet + oneKet ⊗ₖ oneKet)

theorem cnot_plus_output : CNOT * (plusQubit ⊗ₖ zeroKet) = bell := by
  ext ⟨i,j⟩ ⟨a,b⟩
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [CNOT, bell, QuantumBB84ProtocolQBER.ket, Matrix.mul_apply,
      Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- No product of two vectors equals this Bell vector, even without normalization assumptions. -/
theorem bell_not_product (v w : Ket 2) : bell ≠ v ⊗ₖ w := by
  intro h
  have h00 := congrArg (fun M => M (0,0) (0,0)) h
  have h01 := congrArg (fun M => M (0,1) (0,0)) h
  have h10 := congrArg (fun M => M (1,0) (0,0)) h
  have h11 := congrArg (fun M => M (1,1) (0,0)) h
  norm_num [bell, QuantumBB84ProtocolQBER.ket, Matrix.kroneckerMap_apply] at h00 h01 h10 h11
  have hm : (v 0 0 * w 0 0) * (v 1 0 * w 1 0) = (v 0 0 * w 1 0) * (v 1 0 * w 0 0) := by ring
  rw [← h00,← h11, mul_eq_zero.mpr h01, mul_eq_zero.mpr h10] at hm
  have hs := QuantumBB84ProtocolQBER.rootTwo_sq
  have hh : (2:ℂ) = 0 := by linear_combination 4 * hm - hs
  norm_num at hh

theorem cnot_entangles_superposition : CNOT * (plusQubit ⊗ₖ zeroKet) = bell ∧
    CNOT * (plusQubit ⊗ₖ zeroKet) ≠ plusQubit ⊗ₖ plusQubit := by
  exact ⟨cnot_plus_output, by rw [cnot_plus_output]; exact bell_not_product _ _⟩

theorem bb84_zero_plus_overlap : overlapSq zeroKet plusQubit = 1/2 := by
  have h : (rho zeroKet * rho plusQubit).trace = (1/2:ℂ) := by
    change (QuantumBB84ProtocolQBER.P 0 0 * QuantumBB84ProtocolQBER.P 1 0).trace = 1/2
    norm_num [QuantumBB84ProtocolQBER.projector_exact, QuantumBB84ProtocolQBER.projectorTable,
      Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two]
  rw [trace_overlap] at h
  have hr := congrArg Complex.re h
  norm_num at hr
  exact hr

theorem bridge_to_bb84_unclonability (U : Joint 2) (hU : Unitary U) (b : Ket 2)
    (hb : Normalized b) :
    ¬ ∀ (basis bit : Fin 2), DensityClones U b (QuantumBB84ProtocolQBER.ket basis bit) := by
  intro h
  have ht := density_cloning_real_overlap_square U hU b zeroKet plusQubit hb (h 0 0) (h 1 0)
  rw [bb84_zero_plus_overlap] at ht
  norm_num at ht

theorem basis_overlap_orthogonal (i j : Fin d) (hij : i ≠ j) :
    overlapSq (basisKet i) (basisKet j) = 0 := by
  apply (overlap_zero_iff _ _).mpr
  simp [basis_inner, hij]

theorem minus_phase_regression (ψ : Ket d) (hψ : Normalized ψ) :
    rho (-ψ) = rho ψ ∧ overlapSq ψ (-ψ) = 1 := by
  simpa using phase_invariance ψ hψ (-1) (by norm_num)

/-- Literal vector equality detects a phase that the density formulation forgets. -/
theorem opposite_vectors_not_both_cloned (U : Joint d) (hU : Unitary U)
    (b ψ : Ket d) (hb : Normalized b) (hψ : Normalized ψ) :
    ¬ (VectorClones U b ψ ∧ VectorClones U b (-ψ)) := by
  rintro ⟨ha,hb'⟩
  have h := vector_cloning_overlap_square U hU b ψ (-ψ) hb ha hb'
  have hc : overlap ψ (-ψ) = -1 := by
    unfold overlap
    rw [Matrix.mul_neg, hψ]
    simp
  rw [hc] at h
  norm_num at h

theorem vector_cloning_cases (U : Joint d) (hU : Unitary U)
    (b ψ φ : Ket d) (hb : Normalized b)
    (hψ : VectorClones U b ψ) (hφ : VectorClones U b φ) :
    overlap ψ φ = 0 ∨ overlap ψ φ = 1 := 
  complex_square_cases _ (vector_cloning_overlap_square U hU b ψ φ hb hψ hφ)

theorem trace_overlap_real (ψ φ : Ket d) :
    (rho ψ * rho φ).trace.im = 0 ∧ (rho ψ * rho φ).trace.re = overlapSq ψ φ := by
  simp [trace_overlap]

theorem cnot_trace_preserving (M : Joint 2) : (CNOT * M * CNOT.conjTranspose).trace = M.trace := 
  conjugation_trace CNOT cnot_unitary M

structure QuantumNoCloningUnitarySuite : Prop where
  vector_restriction : ∀ {d} (U : Joint d), Unitary U → ∀ b ψ φ,
    Normalized b → VectorClones U b ψ → VectorClones U b φ → overlap ψ φ = overlap ψ φ ^ 2
  density_restriction : ∀ {d} (U : Joint d), Unitary U → ∀ b ψ φ,
    Normalized b → DensityClones U b ψ → DensityClones U b φ →
      (rho ψ * rho φ).trace = (rho ψ * rho φ).trace ^ 2
  probability_bounds : ∀ {d} (ψ φ : Ket d), Normalized ψ → Normalized φ →
    0 ≤ overlapSq ψ φ ∧ overlapSq ψ φ ≤ 1
  physical_criterion : ∀ {d} (U : Joint d), Unitary U → ∀ b ψ φ,
    Normalized b → Normalized ψ → Normalized φ → DensityClones U b ψ → DensityClones U b φ →
      (overlapSq ψ φ = 0 ∧ ψ.conjTranspose * φ = 0) ∨ (overlapSq ψ φ = 1 ∧ rho ψ = rho φ)
  phase_independence : ∀ {d} (ψ : Ket d), Normalized ψ → ∀ θ : ℝ,
    rho (Complex.exp ((θ:ℂ) * Complex.I) • ψ) = rho ψ ∧
      overlapSq ψ (Complex.exp ((θ:ℂ) * Complex.I) • ψ) = 1
  prescribed_state : ∀ {d} (b ψ : Ket d), Normalized b → Normalized ψ →
    ∃ U : Joint d, Unitary U ∧ VectorClones U b ψ
  no_universal : ∀ d, 2 ≤ d → ¬ ∃ (U : Joint d) (b : Ket d),
    Unitary U ∧ Normalized b ∧ ∀ ψ, Normalized ψ → DensityClones U b ψ
  cnot_valid : Unitary CNOT
  cnot_basis : VectorClones CNOT zeroKet zeroKet ∧ VectorClones CNOT zeroKet oneKet
  bell_output : CNOT * (plusQubit ⊗ₖ zeroKet) = bell
  bell_entangled : ∀ v w : Ket 2, bell ≠ v ⊗ₖ w
  bb84 : ∀ U : Joint 2, Unitary U → ∀ b, Normalized b →
    ¬ ∀ basis bit, DensityClones U b (QuantumBB84ProtocolQBER.ket basis bit)
  scalar_bridge : ∀ {d} (U : Joint d), Unitary U → ∀ b ψ φ,
    Normalized b → DensityClones U b ψ → DensityClones U b φ →
    overlapSq ψ φ = overlapSq ψ φ ^ 2 ∧ (overlapSq ψ φ = 0 ∨ overlapSq ψ φ = 1)

theorem quantum_no_cloning_unitary_master_suite : QuantumNoCloningUnitarySuite := {
  vector_restriction := vector_cloning_overlap_square
  density_restriction := density_cloning_overlap_square
  probability_bounds := overlap_bounds
  physical_criterion := density_cloning_ortho_or_identical
  phase_independence := phase_invariance_exp
  prescribed_state := single_state_cloner
  no_universal := fun _ => no_universal_unitary_cloning
  cnot_valid := cnot_unitary
  cnot_basis := cnot_clones_computational_basis
  bell_output := cnot_plus_output
  bell_entangled := bell_not_product
  bb84 := bridge_to_bb84_unclonability
  scalar_bridge := bridge_to_quantum_no_cloning_theorem
}

end QuantumNoCloningUnitary
