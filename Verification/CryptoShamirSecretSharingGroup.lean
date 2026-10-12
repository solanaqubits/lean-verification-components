import Verification.CryptoShamirSecretSharing
import Verification.CryptoSchnorrMultiSignaturesMuSigGroup
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Probability.Distributions.Uniform

set_option linter.style.header false
noncomputable section
open scoped BigOperators
open Polynomial

namespace CryptoShamirSecretSharingGroup

/-- Degree strictly below the threshold, including the zero polynomial for positive thresholds. -/
def ShamirPoly (K : Type*) [Field K] (t : ℕ) (s : K) :=
  {p : K[X] // p.natDegree < t ∧ p.eval 0 = s}

section Field
variable {K : Type*} [Field K] {ι : Type*}

def lagrange_coeff [DecidableEq ι] (ξ : ι → K) (I : Finset ι) (i : ι) : K :=
  ∏ j ∈ I.erase i, (-ξ j) * (ξ i - ξ j)⁻¹

theorem lagrange_denom_nonzero (ξ : ι → K) (hξ : Function.Injective ξ)
    {i j : ι} (h : i ≠ j) : ξ i - ξ j ≠ 0 := sub_ne_zero.mpr (hξ.ne h)

/-- The same interpolation identity applies independently over real and finite fields. -/
theorem field_lagrange_bridge [DecidableEq ι] (ξ : ι → K) (hξ : Function.Injective ξ)
    (I : Finset ι) (p : K[X]) (hp : p.natDegree < I.card) :
    ∑ i ∈ I, lagrange_coeff ξ I i * p.eval (ξ i) = p.eval 0 := by
  have hd : p.degree < (I.card : WithBot ℕ) :=
    lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hp)
  have he := congrArg (Polynomial.eval (0 : K)) (Lagrange.eq_interpolate (hξ.injOn (s := ↑I)) hd)
  simpa [Lagrange.interpolate_apply, Lagrange.basis, Lagrange.basisDivisor,
    lagrange_coeff, eval_finsetSum, eval_prod, mul_comm] using he.symm

theorem shamir_threshold_reconstruction [DecidableEq ι] {t : ℕ} {s : K} (ξ : ι → K)
    (hξ : Function.Injective ξ) (I : Finset ι) (hI : I.card = t)
    (p : ShamirPoly K t s) :
    ∑ i ∈ I, lagrange_coeff ξ I i * p.val.eval (ξ i) = s := by
  rw [field_lagrange_bridge ξ hξ I p.val (hI ▸ p.property.1), p.property.2]

/-- Normalized vanishing polynomial; nonzero coordinates ensure its value at zero is one. -/
def coalitionPoly (ξ : ι → K) (A : Finset ι) : K[X] :=
  ∏ i ∈ A, Lagrange.basisDivisor 0 (ξ i)

theorem coalitionPoly_eval_zero (ξ : ι → K) (hξ : ∀ i, ξ i ≠ 0) (A : Finset ι) :
    (coalitionPoly ξ A).eval 0 = 1 := by
  simp [coalitionPoly, eval_prod, Lagrange.eval_basisDivisor_left_of_ne (Ne.symm (hξ _))]

theorem coalitionPoly_eval_member (ξ : ι → K) (A : Finset ι) {i : ι} (hi : i ∈ A) :
    (coalitionPoly ξ A).eval (ξ i) = 0 := by
  rw [coalitionPoly, eval_prod]
  exact Finset.prod_eq_zero hi (Lagrange.eval_basisDivisor_right)

theorem coalitionPoly_degree (ξ : ι → K) (hξ : ∀ i, ξ i ≠ 0) (A : Finset ι) :
    (coalitionPoly ξ A).natDegree = A.card := by
  unfold coalitionPoly
  rw [natDegree_prod _ _ (fun i _ => Lagrange.basisDivisor_ne_zero_iff.mpr (Ne.symm (hξ i)))]
  simp [Lagrange.natDegree_basisDivisor_of_ne (Ne.symm (hξ _))]

theorem coalition_annihilator_poly (ξ : ι → K) (hξ : ∀ i, ξ i ≠ 0)
    (A : Finset ι) {t : ℕ} (hA : A.card < t) :
    ∃ L : K[X], L.natDegree < t ∧ L.eval 0 = 1 ∧ ∀ i ∈ A, L.eval (ξ i) = 0 :=
  ⟨coalitionPoly ξ A, by rw [coalitionPoly_degree ξ hξ]; exact hA,
    coalitionPoly_eval_zero ξ hξ A, fun _ hi => coalitionPoly_eval_member ξ A hi⟩

def shiftPoly {t : ℕ} {s s' : K} (L : K[X]) (hL : L.natDegree < t)
    (h0 : L.eval 0 = 1) (p : ShamirPoly K t s) : ShamirPoly K t s' :=
  ⟨p.val + (s' - s) • L,
    lt_of_le_of_lt (natDegree_add_le _ _) (max_lt p.property.1
      (lt_of_le_of_lt (natDegree_smul_le _ _) hL)), by simp [eval_add, eval_smul, h0, p.property.2]⟩

def shamir_poly_shift_equiv {t : ℕ} (s s' : K) (L : K[X])
    (hL : L.natDegree < t) (h0 : L.eval 0 = 1) :
    ShamirPoly K t s ≃ ShamirPoly K t s' where
  toFun := shiftPoly L hL h0
  invFun := shiftPoly L hL h0
  left_inv p := by
    apply Subtype.ext
    change p.val + (s' - s) • L + (s - s') • L = p.val
    rw [add_assoc, ← add_smul]
    simp
  right_inv p := by
    apply Subtype.ext
    change p.val + (s - s') • L + (s' - s) • L = p.val
    rw [add_assoc, ← add_smul]
    simp

def observe {t : ℕ} {s : K} (ξ : ι → K) (A : Finset ι)
    (p : ShamirPoly K t s) : (i : A) → K := fun i => p.val.eval (ξ i)

theorem shift_preserves_observations {t : ℕ} (s s' : K) (ξ : ι → K)
    (hξ : ∀ i, ξ i ≠ 0) (A : Finset ι) (hA : A.card < t)
    (p : ShamirPoly K t s) :
    observe ξ A (shamir_poly_shift_equiv s s' (coalitionPoly ξ A)
      (by rw [coalitionPoly_degree ξ hξ]; exact hA)
      (coalitionPoly_eval_zero ξ hξ A) p) = observe ξ A p := by
  funext i
  change (p.val + (s' - s) • coalitionPoly ξ A).eval (ξ i) = p.val.eval (ξ i)
  simp [eval_add, eval_smul, coalitionPoly_eval_member ξ A i.property]

instance polyNonempty {t : ℕ} [Fact (0 < t)] (s : K) : Nonempty (ShamirPoly K t s) :=
  ⟨⟨C s, by simpa using (Fact.out : 0 < t), by simp⟩⟩

instance polyFintype [Fintype K] (t : ℕ) (s : K) : Fintype (ShamirPoly K t s) := by
  classical
  apply Fintype.ofInjective (fun p : ShamirPoly K t s => fun i : Fin t => p.val.coeff i)
  intro p p' he
  apply Subtype.ext
  apply Polynomial.ext
  intro j
  by_cases hj : j < t
  · exact congrFun he ⟨j, hj⟩
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le p.property.1 (Nat.le_of_not_gt hj)),
      coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le p'.property.1 (Nat.le_of_not_gt hj))]

def observationLaw [Fintype K] {t : ℕ} [Fact (0 < t)]
    (ξ : ι → K) (A : Finset ι) (s : K) : PMF ((i : A) → K) :=
  (PMF.uniformOfFintype (ShamirPoly K t s)).map (observe ξ A)

/-- Uniform measure is preserved by a bijection, including between different secret fibers. -/
theorem map_uniform_equiv {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  classical
  ext b
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply]
  simp_rw [← e.symm_apply_eq]
  simp [Fintype.card_congr e]

theorem shamir_pmf_perfect_secrecy [Fintype K] {t : ℕ} [Fact (0 < t)]
    (ξ : ι → K) (hξ : ∀ i, ξ i ≠ 0) (A : Finset ι) (hA : A.card < t) (s s' : K) :
    observationLaw (t := t) ξ A s = observationLaw (t := t) ξ A s' := by
  let e := shamir_poly_shift_equiv s s' (coalitionPoly ξ A)
    (by rw [coalitionPoly_degree ξ hξ]; exact hA) (coalitionPoly_eval_zero ξ hξ A)
  have he : observe ξ A ∘ e = observe (s := s) ξ A := by
    funext p
    exact shift_preserves_observations s s' ξ hξ A hA p
  unfold observationLaw
  rw [← map_uniform_equiv e, PMF.map_comp, he]

/-- Evaluation commutes with every finite weighted sum. -/
theorem weighted_share_eval (J : Finset ι) (w : ι → K) (p : ι → K[X]) (z : K) :
    (∑ j ∈ J, w j • p j).eval z = ∑ j ∈ J, w j * (p j).eval z := by
  simp [eval_finsetSum, eval_smul, smul_eq_mul]

theorem shamir_homomorphism_weighted_sum {t : ℕ} (ht : 0 < t)
    (J : Finset ι) (w s : ι → K) (p : ∀ j, ShamirPoly K t (s j)) :
    (∑ j ∈ J, w j • (p j).val).natDegree < t ∧
    (∑ j ∈ J, w j • (p j).val).eval 0 = ∑ j ∈ J, w j * s j := by
  constructor
  · classical
    induction J using Finset.induction_on with
    | empty => simpa using ht
    | @insert a J ha ih =>
      rw [Finset.sum_insert ha]
      exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt
        (lt_of_le_of_lt (natDegree_smul_le _ _) (p a).property.1) ih)
  · simp [weighted_share_eval, fun j => (p j).property.2]

theorem shamir_group_reconstruction [DecidableEq ι] {B : Type*} [AddCommGroup B]
    [Module K B] {t : ℕ} {s : K} (G : B) (ξ : ι → K) (hξ : Function.Injective ξ)
    (I : Finset ι) (hI : I.card = t) (p : ShamirPoly K t s) :
    ∑ i ∈ I, lagrange_coeff ξ I i • (p.val.eval (ξ i) • G) = s • G := by
  simp_rw [smul_smul]
  rw [← Finset.sum_smul, shamir_threshold_reconstruction ξ hξ I hI p]

theorem weighted_group_shares {B : Type*} [AddCommGroup B] [Module K B]
    (G : B) (J : Finset ι) (w : ι → K) (p : ι → K[X]) (z : K) :
    ∑ j ∈ J, w j • ((p j).eval z • G) = (∑ j ∈ J, w j • p j).eval z • G := by
  simp_rw [smul_smul]
  rw [← Finset.sum_smul, weighted_share_eval]

theorem shamir_zero_coord_leakage {t : ℕ} {s : K} (p : ShamirPoly K t s)
    (ξ : ι → K) (i : ι) (hi : ξ i = 0) : p.val.eval (ξ i) = s := by
  rw [hi, p.property.2]

theorem threshold_one {s : K} (p : ShamirPoly K 1 s) (z : K) : p.val.eval z = s := by
  have hp := Polynomial.eq_C_of_natDegree_eq_zero
    (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ p.property.1))
  rw [hp, eval_C]
  have h0 := p.property.2
  rw [hp, eval_C] at h0
  exact h0

theorem two_share_field (s a x y : K) (hxy : x ≠ y) :
    y / (y - x) * (s + a * x) + (-x) / (y - x) * (s + a * y) = s := by
  field_simp [sub_ne_zero.mpr (Ne.symm hxy)]
  ring

theorem threshold_two_coefficients [DecidableEq ι] (ξ : ι → K) {i j : ι} (hij : i ≠ j) :
    lagrange_coeff ξ {i, j} i = (-ξ j) * (ξ i - ξ j)⁻¹ ∧
    lagrange_coeff ξ {i, j} j = (-ξ i) * (ξ j - ξ i)⁻¹ := by
  constructor
  · simp [lagrange_coeff, hij]
  · rw [Finset.pair_comm]
    simp [lagrange_coeff, Ne.symm hij]

theorem threshold_all {n : ℕ} {s : K} (ξ : Fin n → K) (hξ : Function.Injective ξ)
    (p : ShamirPoly K n s) :
    ∑ i, lagrange_coeff ξ Finset.univ i * p.val.eval (ξ i) = s :=
  shamir_threshold_reconstruction ξ hξ Finset.univ (by simp) p

/-- Relabelling the selected participants preserves the reconstructed secret. -/
theorem reconstruction_permutation {n t : ℕ} {s : K} (ξ : Fin n → K)
    (hξ : Function.Injective ξ) (e : Equiv.Perm (Fin n)) (I : Finset (Fin n))
    (hI : I.card = t) (p : ShamirPoly K t s) :
    (∑ i ∈ I.map e.toEmbedding, lagrange_coeff (ξ ∘ e.symm) (I.map e.toEmbedding) i *
      p.val.eval (ξ (e.symm i))) = ∑ i ∈ I, lagrange_coeff ξ I i * p.val.eval (ξ i) := by
  rw [shamir_threshold_reconstruction ξ hξ I hI p]
  exact shamir_threshold_reconstruction (ξ ∘ e.symm) (hξ.comp e.symm.injective)
    (I.map e.toEmbedding) (by simpa using hI) p

end Field

/-- Bridge to the actual real model; the finite-field identity is specialized independently. -/
theorem bridge_to_scalar_shamir (p : CryptoShamirSecretSharing.Shamir2Polynomial)
    (x y : ℝ) (hxy : x ≠ y) :
    CryptoShamirSecretSharing.reconstructSecret x (CryptoShamirSecretSharing.share p x)
      y (CryptoShamirSecretSharing.share p y) = p.secret := by
  exact two_share_field p.secret p.slope x y hxy

/-- Valid static threshold parameters and the cyclic group witness. -/
structure Setup (q t n : ℕ) [Fact (Nat.Prime q)] (B : Type*)
    [AddCommGroup B] [Module (ZMod q) B] where
  threshold_pos : 0 < t
  threshold_le : t ≤ n
  enough_coordinates : n < q
  coordinates : Fin n → ZMod q
  coordinates_injective : Function.Injective coordinates
  coordinates_nonzero : ∀ i, coordinates i ≠ 0
  generator : B
  generator_bijective : Function.Bijective (fun x : ZMod q => x • generator)

/-- Canonical coordinates 1,...,n and generator 1 witness all setup conditions. -/
def ConsistencyModel (q t n : ℕ) [Fact (Nat.Prime q)] (ht : 0 < t)
    (htn : t ≤ n) (hnq : n < q) : Setup q t n (ZMod q) where
  threshold_pos := ht
  threshold_le := htn
  enough_coordinates := hnq
  coordinates := fun i => ((i.val + 1 : ℕ) : ZMod q)
  coordinates_injective := by
    intro i j h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (lt_of_le_of_lt (Nat.succ_le_of_lt i.isLt) hnq),
      ZMod.val_natCast_of_lt (lt_of_le_of_lt (Nat.succ_le_of_lt j.isLt) hnq)] at hv
    exact Fin.ext (Nat.succ.inj hv)
  coordinates_nonzero := by
    intro i h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (lt_of_le_of_lt (Nat.succ_le_of_lt i.isLt) hnq), ZMod.val_zero] at hv
    exact Nat.noConfusion hv
  generator := 1
  generator_bijective := by simp [smul_eq_mul]

structure GroupProperties {q t n : ℕ} [Fact (Nat.Prime q)] {B : Type*}
    [AddCommGroup B] [Module (ZMod q) B] (S : Setup q t n B) : Prop where
  recovery : ∀ (s : ZMod q) (p : ShamirPoly (ZMod q) t s) (I : Finset (Fin n)), I.card = t →
    ∑ i ∈ I, lagrange_coeff S.coordinates I i * p.val.eval (S.coordinates i) = s
  secrecy : ∀ (A : Finset (Fin n)), A.card < t → ∀ (s s' : ZMod q),
    letI : Fact (0 < t) := ⟨S.threshold_pos⟩
    observationLaw (t := t) S.coordinates A s = observationLaw (t := t) S.coordinates A s'
  group_recovery : ∀ (s : ZMod q) (p : ShamirPoly (ZMod q) t s) (I : Finset (Fin n)), I.card = t →
    ∑ i ∈ I, lagrange_coeff S.coordinates I i • (p.val.eval (S.coordinates i) • S.generator) =
      s • S.generator
  weighted : ∀ (ι : Type) (J : Finset ι) (w s : ι → ZMod q)
    (p : ∀ j, ShamirPoly (ZMod q) t (s j)),
    (∑ j ∈ J, w j • (p j).val).natDegree < t ∧
    (∑ j ∈ J, w j • (p j).val).eval 0 = ∑ j ∈ J, w j * s j
  unique_scalar : ∀ a b : ZMod q, a • S.generator = b • S.generator → a = b

theorem group_properties {q t n : ℕ} [Fact (Nat.Prime q)] {B : Type*}
    [AddCommGroup B] [Module (ZMod q) B] (S : Setup q t n B) : GroupProperties S where
  recovery := fun _ p I hI =>
    shamir_threshold_reconstruction S.coordinates S.coordinates_injective I hI p
  secrecy := by
    intro A hA s s'
    let : Fact (0 < t) := ⟨S.threshold_pos⟩
    exact shamir_pmf_perfect_secrecy S.coordinates S.coordinates_nonzero A hA s s'
  group_recovery := fun _ p I hI =>
    shamir_group_reconstruction S.generator S.coordinates S.coordinates_injective I hI p
  weighted := fun _ J w s p => shamir_homomorphism_weighted_sum S.threshold_pos J w s p
  unique_scalar := fun _ _ h => S.generator_bijective.1 h

structure CryptoShamirSecretSharingGroupSuite : Prop where
  groups : ∀ (q t n : ℕ) [Fact (Nat.Prime q)] (B : Type) [AddCommGroup B]
    [Module (ZMod q) B] (S : Setup q t n B), GroupProperties S
  model : ∀ (q t n : ℕ) [Fact (Nat.Prime q)], 0 < t → t ≤ n → n < q →
    Nonempty (Setup q t n (ZMod q))
  scalar_bridge : ∀ (p : CryptoShamirSecretSharing.Shamir2Polynomial) (x y : ℝ), x ≠ y →
    CryptoShamirSecretSharing.reconstructSecret x (CryptoShamirSecretSharing.share p x)
      y (CryptoShamirSecretSharing.share p y) = p.secret

theorem crypto_shamir_group_master_suite : CryptoShamirSecretSharingGroupSuite where
  groups := fun _ _ _ _ _ _ _ => group_properties
  model := fun q t n _ ht htn hnq => ⟨ConsistencyModel q t n ht htn hnq⟩
  scalar_bridge := bridge_to_scalar_shamir

end CryptoShamirSecretSharingGroup
