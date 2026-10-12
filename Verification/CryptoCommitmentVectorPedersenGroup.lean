/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoPedersenHomomorphicSum
import Verification.CryptoSchnorrMultiSignaturesMuSigGroup

/-!
# Vector Pedersen commitments

Indexed generators are not a linearly independent basis. Collision extraction is
an algebraic relation; no adversarial security or parameter-generation model is
asserted. Uniform blinding is modeled explicitly using PMF.
-/
namespace CryptoCommitmentVectorPedersenGroup

open scoped BigOperators

abbrev MsgVector (q k : ℕ) := Fin k → ZMod q

variable {q k : ℕ} [Fact (Nat.Prime q)]
variable {A : Type} [AddCommGroup A] [Module (ZMod q) A]

structure Setup (q k : ℕ) (A : Type) [Fact (Nat.Prime q)] [AddCommGroup A]
    [Module (ZMod q) A] where
  blinder : A
  blinder_bijective : Function.Bijective (fun r : ZMod q => r • blinder)
  bases : Fin k → A
  bases_nonzero : ∀ i, bases i ≠ 0

def commit_vec (G : Fin k → A) (H : A) (m : MsgVector q k) (r : ZMod q) : A :=
  (∑ i, m i • G i) + r • H

@[simp] theorem commit_vec_zero (G : Fin k → A) (H : A) :
    commit_vec G H (0 : MsgVector q k) 0 = 0 := by simp [commit_vec]

theorem commit_vec_add_homomorphism (G : Fin k → A) (H : A)
    (m m' : MsgVector q k) (r r' : ZMod q) :
    commit_vec G H (m + m') (r + r') = commit_vec G H m r + commit_vec G H m' r' := by
  simp only [commit_vec, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

theorem commit_vec_smul_homomorphism (G : Fin k → A) (H : A)
    (a : ZMod q) (m : MsgVector q k) (r : ZMod q) :
    commit_vec G H (a • m) (a * r) = a • commit_vec G H m r := by
  simp [commit_vec, smul_add, Finset.smul_sum, smul_smul]

theorem commit_vec_weighted_sum_homomorphism {ι : Type} (s : Finset ι)
    (G : Fin k → A) (H : A) (w r : ι → ZMod q) (m : ι → MsgVector q k) :
    (∑ j ∈ s, w j • commit_vec G H (m j) (r j)) =
      commit_vec G H (∑ j ∈ s, w j • m j) (∑ j ∈ s, w j * r j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [ih, commit_vec_add_homomorphism, commit_vec_smul_homomorphism]

theorem commit_vec_hiding_equiv (G : Fin k → A) (H : A)
    (hH : Function.Bijective (fun r : ZMod q => r • H)) (m : MsgVector q k) :
    Function.Bijective (commit_vec G H m) := by
  constructor
  · intro r t h
    exact hH.1 (add_left_cancel h)
  · intro y
    obtain ⟨r, hr⟩ := hH.2 (y - ∑ i, m i • G i)
    exact ⟨r, by simp [commit_vec, hr]⟩

/-- Finiteness is supplied by the generator bijection, not a hardness assumption. -/
noncomputable abbrev setupFintype (S : Setup q k A) : Fintype A :=
  Fintype.ofEquiv (ZMod q) (Equiv.ofBijective _ S.blinder_bijective)

noncomputable def commitmentLaw (G : Fin k → A) (H : A) (m : MsgVector q k) : PMF A :=
  (PMF.uniformOfFintype (ZMod q)).map (commit_vec G H m)

theorem commit_vec_perfect_hiding [Fintype A] (G : Fin k → A) (H : A)
    (hH : Function.Bijective (fun r : ZMod q => r • H)) (m : MsgVector q k) :
    commitmentLaw G H m = PMF.uniformOfFintype A :=
  CryptoPedersenHomomorphicSum.map_uniform_equiv
    (Equiv.ofBijective _ (commit_vec_hiding_equiv G H hH m))

theorem message_independent_law (G : Fin k → A) (H : A)
    (hH : Function.Bijective (fun r : ZMod q => r • H)) (m m' : MsgVector q k) :
    commitmentLaw G H m = commitmentLaw G H m' := by
  let : Fintype A := Fintype.ofEquiv (ZMod q) (Equiv.ofBijective _ hH)
  rw [commit_vec_perfect_hiding G H hH, commit_vec_perfect_hiding G H hH]

theorem commit_vec_collision_iff (G : Fin k → A) (H : A)
    (m m' : MsgVector q k) (r r' : ZMod q) :
    commit_vec G H m r = commit_vec G H m' r' ↔
      (∑ i, (m i - m' i) • G i) + (r - r') • H = 0 := by
  have he : (∑ i, (m i - m' i) • G i) + (r - r') • H =
      commit_vec G H m r - commit_vec G H m' r' := by
    simp only [commit_vec, sub_smul, Finset.sum_sub_distrib]
    abel
  rw [he, sub_eq_zero]

theorem commit_vec_collision_linear_relation (G : Fin k → A) (H : A)
    (m m' : MsgVector q k) (r r' : ZMod q)
    (hc : commit_vec G H m r = commit_vec G H m' r') :
    (∑ i, (m i - m' i) • G i) + (r - r') • H = 0 :=
  (commit_vec_collision_iff G H m m' r r').mp hc

theorem commit_vec_collision_nontrivial_coeff (m m' : MsgVector q k) (hm : m ≠ m') :
    ∃ i, m i - m' i ≠ 0 := by
  classical
  by_contra h
  push Not at h
  exact hm (funext fun i => sub_eq_zero.mp (h i))

/-- Known coordinates exclude j: its logarithm is the output of this extraction. -/
theorem commit_vec_dlog_extraction_conditional (G : Fin k → A) (H : A)
    (m m' : MsgVector q k) (r r' : ZMod q) (j : Fin k) (α : Fin k → ZMod q)
    (known : ∀ i, i ≠ j → G i = α i • H)
    (hc : commit_vec G H m r = commit_vec G H m' r') (hj : m j ≠ m' j) :
    G j = (-((m j - m' j)⁻¹ *
      ((∑ i ∈ Finset.univ.erase j, (m i - m' i) * α i) + (r - r')))) • H := by
  classical
  have rel := commit_vec_collision_linear_relation G H m m' r r' hc
  rw [← Finset.add_sum_erase Finset.univ (fun i => (m i - m' i) • G i)
    (Finset.mem_univ j)] at rel
  have he : (∑ i ∈ Finset.univ.erase j, (m i - m' i) • G i) =
      (∑ i ∈ Finset.univ.erase j, (m i - m' i) * α i) • H := by
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [known i (Finset.ne_of_mem_erase hi), smul_smul]
  rw [he, add_assoc, ← add_smul] at rel
  have eqn := eq_neg_of_add_eq_zero_left rel
  have h := congrArg (fun P : A => (m j - m' j)⁻¹ • P) eqn
  simpa [smul_neg, smul_smul, sub_ne_zero.mpr hj] using h

theorem commit_vec_permutation (G : Fin k → A) (H : A)
    (m : MsgVector q k) (r : ZMod q) (p : Equiv.Perm (Fin k)) :
    commit_vec (G ∘ p) H (m ∘ p) r = commit_vec G H m r := by
  unfold commit_vec
  rw [show (∑ i, (m ∘ p) i • (G ∘ p) i) = ∑ i, m i • G i from
    Equiv.sum_comp p (fun i => m i • G i)]

theorem commit_vec_identical_generators_collision (G : Fin k → A) (H : A)
    (m : MsgVector q k) (r : ZMod q) (i j : Fin k) (hg : G i = G j) :
    commit_vec G H (m ∘ Equiv.swap i j) r = commit_vec G H m r := by
  classical
  have fixed : G ∘ Equiv.swap i j = G := by
    funext a
    by_cases hi : a = i
    · subst a; simp [hg]
    by_cases hj : a = j
    · subst a; simp [hg]
    simp [Equiv.swap_apply_of_ne_of_ne hi hj]
  simpa [fixed] using commit_vec_permutation G H m r (Equiv.swap i j)

/-- A known nonzero kernel vector produces a distinct opening by translation. -/
theorem commit_vec_known_relation_alternate_open (G : Fin k → A) (H : A)
    (m d : MsgVector q k) (r t : ZMod q)
    (rel : (∑ i, d i • G i) + t • H = 0) (hn : d ≠ 0 ∨ t ≠ 0) :
    (m + d, r + t) ≠ (m, r) ∧
      commit_vec G H (m + d) (r + t) = commit_vec G H m r := by
  constructor
  · intro he
    have hd : d = 0 := add_left_cancel ((congrArg Prod.fst he).trans (add_zero m).symm)
    have ht : t = 0 := add_left_cancel ((congrArg Prod.snd he).trans (add_zero r).symm)
    exact hn.elim (fun h => h hd) (fun h => h ht)
  · rw [commit_vec_add_homomorphism]
    exact add_eq_left.mpr rel

theorem bridge_to_scalar_pedersen [Fintype A] (S : CryptoPedersenHomomorphicSum.Setup q A)
    (m r : ZMod q) :
    commit_vec (fun _ : Fin 1 => S.g) S.h (fun _ => m) r =
      CryptoPedersenHomomorphicSum.commit S m r := by
  simp [commit_vec, CryptoPedersenHomomorphicSum.commit]

theorem empty_vector (H : A) (m : MsgVector q 0) (r : ZMod q) :
    commit_vec (fun i : Fin 0 => Fin.elim0 i) H m r = r • H := by simp [commit_vec]

def ConsistencyModel (q k : ℕ) [Fact (Nat.Prime q)] : Setup q k (ZMod q) where
  blinder := 1
  blinder_bijective := by simp [smul_eq_mul]
  bases := fun _ => 1
  bases_nonzero := fun _ => one_ne_zero

structure GroupProperties (S : Setup q k A) : Prop where
  additive : ∀ (m m' : MsgVector q k) (r r' : ZMod q),
    commit_vec S.bases S.blinder (m + m') (r + r') =
    commit_vec S.bases S.blinder m r + commit_vec S.bases S.blinder m' r'
  scaling : ∀ (a : ZMod q) (m : MsgVector q k) (r : ZMod q),
    commit_vec S.bases S.blinder (a • m) (a * r) =
    a • commit_vec S.bases S.blinder m r
  weighted : ∀ (ι : Type) (s : Finset ι) (w r : ι → ZMod q) (m : ι → MsgVector q k),
    (∑ j ∈ s, w j • commit_vec S.bases S.blinder (m j) (r j)) =
      commit_vec S.bases S.blinder (∑ j ∈ s, w j • m j) (∑ j ∈ s, w j * r j)
  hidden : ∀ (m m' : MsgVector q k),
    commitmentLaw S.bases S.blinder m = commitmentLaw S.bases S.blinder m'
  uniform : ∀ [Fintype A] (m : MsgVector q k),
    commitmentLaw S.bases S.blinder m = PMF.uniformOfFintype A
  collision : ∀ (m m' : MsgVector q k) (r r' : ZMod q),
    commit_vec S.bases S.blinder m r = commit_vec S.bases S.blinder m' r' →
    (∑ i, (m i - m' i) • S.bases i) + (r - r') • S.blinder = 0
  nontrivial : ∀ (m m' : MsgVector q k), m ≠ m' → ∃ i, m i - m' i ≠ 0
  extraction : ∀ (m m' : MsgVector q k) (r r' : ZMod q) (j : Fin k) (α : Fin k → ZMod q),
    (∀ i, i ≠ j → S.bases i = α i • S.blinder) →
    commit_vec S.bases S.blinder m r = commit_vec S.bases S.blinder m' r' → m j ≠ m' j →
    S.bases j = (-((m j - m' j)⁻¹ *
      ((∑ i ∈ Finset.univ.erase j, (m i - m' i) * α i) + (r - r')))) • S.blinder
  alternate : ∀ (m d : MsgVector q k) (r t : ZMod q), (∑ i, d i • S.bases i) + t • S.blinder = 0 →
    d ≠ 0 ∨ t ≠ 0 → (m + d, r + t) ≠ (m, r) ∧
      commit_vec S.bases S.blinder (m + d) (r + t) = commit_vec S.bases S.blinder m r

theorem group_properties (S : Setup q k A) : GroupProperties S where
  additive := commit_vec_add_homomorphism S.bases S.blinder
  scaling := commit_vec_smul_homomorphism S.bases S.blinder
  weighted := fun _ s => commit_vec_weighted_sum_homomorphism s S.bases S.blinder
  hidden := message_independent_law S.bases S.blinder S.blinder_bijective
  uniform := by
    intro inst m
    exact commit_vec_perfect_hiding S.bases S.blinder S.blinder_bijective m
  collision := commit_vec_collision_linear_relation S.bases S.blinder
  nontrivial := commit_vec_collision_nontrivial_coeff
  extraction := commit_vec_dlog_extraction_conditional S.bases S.blinder
  alternate := commit_vec_known_relation_alternate_open S.bases S.blinder

structure CryptoCommitmentVectorPedersenGroupSuite : Prop where
  groups : ∀ (q k : ℕ) [Fact (Nat.Prime q)] (A : Type) [AddCommGroup A]
    [Module (ZMod q) A] (S : Setup q k A), GroupProperties S
  model : ∀ (q k : ℕ) [Fact (Nat.Prime q)], Nonempty (Setup q k (ZMod q))
  scalar_bridge : ∀ (q : ℕ) [Fact (Nat.Prime q)] (A : Type) [Fintype A]
    [AddCommGroup A] [Module (ZMod q) A] (S : CryptoPedersenHomomorphicSum.Setup q A) m r,
    commit_vec (fun _ : Fin 1 => S.g) S.h (fun _ => m) r = CryptoPedersenHomomorphicSum.commit S m r

theorem crypto_vector_pedersen_master_suite : CryptoCommitmentVectorPedersenGroupSuite where
  groups := fun _ _ _ _ _ _ => group_properties
  model := fun q k _ => ⟨ConsistencyModel q k⟩
  scalar_bridge := fun _ _ _ _ _ _ => bridge_to_scalar_pedersen

end CryptoCommitmentVectorPedersenGroup
