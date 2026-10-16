/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumQutritTwoOfThreeSecretSharingContract

/-! An explicit permutation decoder for the fixed three-qutrit code.
The recovery operators are given by finite formulas, without choosing a recovery
from an existence proof. This does not implement a numerical simulator. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder Kronecker
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract
open QuantumKnillLaflammeEnvironmentCriterion QuantumKnillLaflammeRecoveryNecessity
open QuantumReferencePreservingRecoveryContract QuantumErasureCorrectabilityContract
open QuantumQutritTwoOfThreeSecretSharingContract QuantumHelstromStateDiscrimination
namespace QuantumQutritSecretSharingExplicitDecoder

/-- Forward and inverse basis-coordinate maps, with arithmetic in Fin 3. -/
def decodeCoordinates (uv : Fin 3 × Fin 3) : Fin 3 × Fin 3 :=
  (uv.2 - uv.1, 2 * uv.2 - uv.1)
def encodeCoordinates (st : Fin 3 × Fin 3) : Fin 3 × Fin 3 :=
  (st.2 - 2 * st.1, st.2 - st.1)

theorem coordinates_left_inverse : Function.LeftInverse encodeCoordinates decodeCoordinates := by
  decide

theorem coordinates_right_inverse : Function.RightInverse encodeCoordinates decodeCoordinates := by
  decide

def decoderEquiv : Fin 9 ≃ Fin 9 :=
  finProdFinEquiv.symm.trans
    ((Equiv.mk decodeCoordinates encodeCoordinates coordinates_left_inverse
      coordinates_right_inverse).trans finProdFinEquiv)

/-- Column x is the basis vector indexed by decoderEquiv x. -/
def decoder : Q 9 := fun y x => if y = decoderEquiv x then 1 else 0

theorem decoder_basis (u v s t : Fin 3) :
    decoder (pair s t) (pair u v) = if s = v-u ∧ t = 2*v-u then 1 else 0 := by
  simp [decoder, decoderEquiv, decodeCoordinates, pair]

theorem decoder_unitary_left : decoder.conjTranspose * decoder = 1 := by
  ext x y
  simp [decoder, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    mul_ite, eq_comm]

theorem decoder_unitary_right : decoder * decoder.conjTranspose = 1 := by
  ext x y
  obtain ⟨u,rfl⟩ := decoderEquiv.surjective x
  obtain ⟨v,rfl⟩ := decoderEquiv.surjective y
  simp [decoder, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    mul_ite]

/-- D tensor I_3 in the flat ((logical,auxiliary),lost) ordering. -/
def liftedDecoder : Q 27 := fromProduct 9 3 (decoder ⊗ₖ (1 : Q 3))

/-- Columns |s> tensor |Omega_3>, expressed in the same flat ordering. -/
def separatedCode : Matrix (Fin 27) (Fin 3) ℂ := fun x s =>
  let uv := (finProdFinEquiv : Fin 9 × Fin 3 ≃ Fin 27).symm x
  let st := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm uv.1
  if st.1 = s ∧ st.2 = uv.2 then amplitude else 0

theorem separated_entry (s t w i : Fin 3) :
    separatedCode (triple s t w) i = if s = i ∧ t = w then amplitude else 0 := by
  simp [separatedCode, triple, pair]

theorem lifted_row (u : Fin 9) (w : Fin 3) (y : Fin 27) :
    liftedDecoder (pair u w) y = if y = pair (decoderEquiv.symm u) w then 1 else 0 := by
  obtain ⟨⟨v,z⟩,rfl⟩ := (finProdFinEquiv : Fin 9 × Fin 3 ≃ Fin 27).surjective y
  simp [liftedDecoder, fromProduct, decoder, pair, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Equiv.eq_symm_apply, mul_ite, ite_and, eq_comm]
  split_ifs <;> rfl

theorem lifted_mul_entry (M : Matrix (Fin 27) (Fin 3) ℂ)
    (u : Fin 9) (w s : Fin 3) :
    (liftedDecoder * M) (pair u w) s = M (pair (decoderEquiv.symm u) w) s := by
  simp [Matrix.mul_apply, lifted_row]

/-- Support equality is a finite arithmetic statement, checked by the kernel. -/
theorem decoded_support : ∀ (u : Fin 9) (w s : Fin 3),
    let uv := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm (decoderEquiv.symm u)
    let st := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm u
    (uv.2 = uv.1 + s ∧ w = uv.1 + 2*s) ↔ (st.1 = s ∧ st.2 = w) := by
  decide

theorem decoder_code (q : Fin 3) : liftedDecoder * groupedCode q = separatedCode := by
  rw [cyclic_code]
  ext x s
  obtain ⟨⟨u,w⟩,rfl⟩ := (finProdFinEquiv : Fin 9 × Fin 3 ≃ Fin 27).surjective x
  change (liftedDecoder * code) (pair u w) s = separatedCode (pair u w) s
  rw [lifted_mul_entry]
  simp only [code, separatedCode, pair, Equiv.symm_apply_apply]
  have h := decoded_support u w s
  dsimp only at h
  simp only [h]

/-- X tensor |Omega><Omega|, with explicit associative tensor indexing. -/
def factorized (X : Q 3) : Q 27 := fun x y =>
  let uv := (finProdFinEquiv : Fin 9 × Fin 3 ≃ Fin 27).symm x
  let wz := (finProdFinEquiv : Fin 9 × Fin 3 ≃ Fin 27).symm y
  let st := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm uv.1
  let ab := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm wz.1
  X st.1 ab.1 * maximallyEntangled 3 (st.2,uv.2) (ab.2,wz.2)

theorem separated_factorization (X : Q 3) : encode separatedCode X = factorized X := by
  ext x y
  obtain ⟨⟨st,w⟩,rfl⟩ := (finProdFinEquiv : Fin 9 × Fin 3 ≃ Fin 27).surjective x
  obtain ⟨⟨ab,z⟩,rfl⟩ := (finProdFinEquiv : Fin 9 × Fin 3 ≃ Fin 27).surjective y
  obtain ⟨⟨s,t⟩,rfl⟩ := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).surjective st
  obtain ⟨⟨a,b⟩,rfl⟩ := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).surjective ab
  by_cases ht : t = w <;> by_cases hb : b = z <;>
    simp [encode, separatedCode, factorized, Matrix.mul_apply, Matrix.conjTranspose_apply,
      maximallyEntangled, mul_ite, ite_mul, apply_ite (starRingEnd ℂ), ht, hb]
  ring_nf
  norm_num
  ring

theorem decoding_factorization (q : Fin 3) (X : Q 3) :
    liftedDecoder * encode (groupedCode q) X * liftedDecoder.conjTranspose =
      factorized X := by
  have h : liftedDecoder * encode (groupedCode q) X * liftedDecoder.conjTranspose =
      encode (liftedDecoder * groupedCode q) X := by
    simp only [encode, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [h, decoder_code, separated_factorization]

/-- Three concrete operators (I tensor <t|) D, with no chosen recovery. -/
def recoveryOperator (t : Fin 3) : Matrix (Fin 3) (Fin 9) ℂ :=
  erasureOperator 3 3 t * decoder

theorem recovery_complete :
    ∑ t, (recoveryOperator t).conjTranspose * recoveryOperator t = 1 := by
  simp only [recoveryOperator, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_sum]
  simp_rw [← Matrix.mul_assoc (erasureOperator 3 3 _).conjTranspose]
  rw [← Matrix.sum_mul, erasure_complete, Matrix.one_mul, decoder_unitary_left]

def explicitRecovery : KrausChannel 9 3 3 where
  operators := recoveryOperator
  complete := recovery_complete

/-- Finite recovery formula on arbitrary pair matrices. -/
theorem explicit_apply (Y : Q 9) :
    apply_channel explicitRecovery Y = ∑ t : Fin 3,
      recoveryOperator t * Y * (recoveryOperator t).conjTranspose :=
  apply_channel_eq _ _

theorem erasure_mul_entry {a b k : ℕ} (t : Fin b)
    (M : Matrix (Fin (a * b)) (Fin k) ℂ) (i : Fin a) (j : Fin k) :
    (erasureOperator a b t * M) i j = M (pair i t) j := by
  simp [erasureOperator, Matrix.mul_apply]

theorem recovery_entry (t s : Fin 3) (x : Fin 9) :
    recoveryOperator t s x = decoder (pair s t) x := erasure_mul_entry t decoder s x

set_option maxHeartbeats 2000000 in
-- The finite branch calculation checks all syndrome and logical indices.
theorem recovery_branch (q t w : Fin 3) :
    recoveryOperator t * erasureOperator 9 3 w * groupedCode q =
      (if t = w then amplitude else 0) • (1 : Q 3) := by
  rw [cyclic_code, Matrix.mul_assoc]
  ext i j
  simp only [Matrix.mul_apply, recovery_entry]
  change (∑ x : Fin 9, decoder (pair i t) x *
    (erasureOperator 9 3 w * code) x j) = _
  simp_rw [erasure_mul_entry]
  fin_cases t <;> fin_cases w <;> fin_cases i <;> fin_cases j <;>
    norm_num [decoder, decoderEquiv, decodeCoordinates, code, pair, Matrix.smul_apply,
      Matrix.one_apply, Fin.sum_univ_succ, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Fin.add_def, Fin.mul_def, Fin.sub_def, Fin.neg_def, Fin.ext_iff]

theorem explicit_recovery (q : Fin 3) (X : Q 3) :
    apply_channel explicitRecovery (retainedPair q (encode code X)) = X := by
  change apply_channel explicitRecovery (traceB (encode (groupedCode q) X)) = X
  rw [← erasure_apply, ← composite_action]
  simp only [compositeOperator, explicitRecovery, erasureChannel, recovery_branch,
    Fintype.sum_prod_type]
  simp only [ite_smul, zero_smul, ite_mul, Algebra.smul_mul_assoc, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Matrix.conjTranspose_smul,
    amplitude_star, Matrix.conjTranspose_one, Algebra.mul_smul_comm, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  ext i j
  simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.ofNat_apply]
  ring_nf
  simp
  ring

theorem explicit_reference_recovery (q : Fin 3) (m : ℕ) (X : Joint m 3) :
    liftedRecovery (erasureChannel 9 3) (groupedCode q) explicitRecovery m X = X :=
  erasure_reference_recovery _ _ (explicit_recovery q) m X

theorem agrees_with_pairRecovery (q : Fin 3) (X : Q 3) :
    apply_channel explicitRecovery (retainedPair q (encode code X)) =
      apply_channel (pairRecovery q) (retainedPair q (encode code X)) := by
  rw [explicit_recovery, pair_recovery]

structure QuantumQutritSecretSharingExplicitDecoderSuite : Prop where
  left_inverse : Function.LeftInverse encodeCoordinates decodeCoordinates
  right_inverse : Function.RightInverse encodeCoordinates decodeCoordinates
  unitary_left : decoder.conjTranspose * decoder = 1
  unitary_right : decoder * decoder.conjTranspose = 1
  basis_action : ∀ (u v s t : Fin 3), decoder (pair s t) (pair u v) =
    if s = v-u ∧ t = 2*v-u then 1 else 0
  code_action : ∀ q, liftedDecoder * groupedCode q = separatedCode
  factorization : ∀ q (X : Q 3),
    liftedDecoder * encode (groupedCode q) X * liftedDecoder.conjTranspose = factorized X
  completeness : ∑ t, (recoveryOperator t).conjTranspose * recoveryOperator t = 1
  recovery : ∀ q (X : Q 3),
    apply_channel explicitRecovery (retainedPair q (encode code X)) = X
  reference : ∀ q m (X : Joint m 3),
    liftedRecovery (erasureChannel 9 3) (groupedCode q) explicitRecovery m X = X
  agreement : ∀ q (X : Q 3),
    apply_channel explicitRecovery (retainedPair q (encode code X)) =
      apply_channel (pairRecovery q) (retainedPair q (encode code X))

theorem verification_suite : QuantumQutritSecretSharingExplicitDecoderSuite where
  left_inverse := coordinates_left_inverse
  right_inverse := coordinates_right_inverse
  unitary_left := decoder_unitary_left
  unitary_right := decoder_unitary_right
  basis_action := decoder_basis
  code_action := decoder_code
  factorization := decoding_factorization
  completeness := recovery_complete
  recovery := explicit_recovery
  reference := explicit_reference_recovery
  agreement := agrees_with_pairRecovery

end QuantumQutritSecretSharingExplicitDecoder
