/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoShamirSecretSharingGroup
import Verification.CryptoSchnorrMultiSignaturesMuSigGroup
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Abel

/-!
# Algebraic FROST completeness

Abstract deterministic binding/challenge functions model their typed inputs, not
hash security or byte encodings. One signing session uses shares of one Shamir
polynomial. Nonce generation, reuse prevention, DKG, VSS and unforgeability are
outside this module. Tampering results keep the public transcript fixed.
-/

noncomputable section
open scoped BigOperators
open CryptoShamirSecretSharingGroup

namespace CryptoThresholdSchnorrFrostGroup

section Algebra
variable {K B ι : Type*} [Field K] [AddCommGroup B] [Module K B] [DecidableEq ι]

def nonceShare (G : B) (d e ρ : K) : B := d • G + ρ • (e • G)
def response (d e ρ c lam share : K) : K := d + ρ * e + c * lam * share

theorem frost_share_verification (G : B) (d e ρ c lam share : K) :
    response d e ρ c lam share • G = nonceShare G d e ρ + (c * lam) • (share • G) := by
  unfold response
  rw [CryptoSchnorrMultiSignaturesMuSigGroup.partial_module_identity]
  simp only [nonceShare, add_smul, mul_smul]

/-- Reuse Shamir's group theorem at the selected set's cardinality. -/
theorem frost_group_interpolation (G : B) (ξ : ι → K) (hξ : Function.Injective ξ)
    {t : ℕ} (f : Polynomial K) (hf : f.natDegree < t) (I : Finset ι) (hI : t ≤ I.card) :
    ∑ i ∈ I, lagrange_coeff ξ I i • (f.eval (ξ i) • G) = f.eval 0 • G := by
  exact shamir_group_reconstruction G ξ hξ I rfl
    ⟨f, lt_of_lt_of_le hf hI, rfl⟩

omit [DecidableEq ι] in
/-- Composition accepts arbitrary valid partial equations under one transcript. -/
theorem frost_composition (G : B) (I : Finset ι) (N Y : ι → B) (lam z : ι → K)
    (c : K) (h : ∀ i ∈ I, z i • G = N i + (c * lam i) • Y i) :
    (∑ i ∈ I, z i) • G = (∑ i ∈ I, N i) + c • (∑ i ∈ I, lam i • Y i) := by
  rw [Finset.sum_smul, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simpa [mul_smul] using h i hi

theorem frost_aggregate_verification (G : B) (ξ : ι → K) (hξ : Function.Injective ξ)
    {t : ℕ} (f : Polynomial K) (hf : f.natDegree < t) (I : Finset ι) (hI : t ≤ I.card)
    (d e ρ : ι → K) (c : K) :
    (∑ i ∈ I, response (d i) (e i) (ρ i) c (lagrange_coeff ξ I i) (f.eval (ξ i))) • G =
      (∑ i ∈ I, nonceShare G (d i) (e i) (ρ i)) + c • (f.eval 0 • G) := by
  rw [frost_composition G I _ (fun i => f.eval (ξ i) • G) (lagrange_coeff ξ I) _ c
    (fun i _ => frost_share_verification G _ _ _ _ _ _)]
  rw [frost_group_interpolation G ξ hξ f hf I hI]

/-- A single changed scalar cannot verify against the unchanged right-hand side. -/
theorem shifted_response_rejected (G : B) (hG : Function.Injective (fun x : K => x • G))
    (z δ : K) (hδ : δ ≠ 0) : (z + δ) • G ≠ z • G := by
  intro h
  have h' := hG h
  exact hδ (add_left_cancel (show z + δ = z + 0 by simpa using h'))

def shiftAt (z : ι → K) (i : ι) (δ : K) : ι → K :=
  fun k => z k + if k = i then δ else 0

theorem sum_shiftAt (I : Finset ι) (z : ι → K) {i : ι} (hi : i ∈ I) (δ : K) :
    ∑ k ∈ I, shiftAt z i δ k = (∑ k ∈ I, z k) + δ := by
  simp [shiftAt, Finset.sum_add_distrib, hi]

def cancelErrors (z : ι → K) (i j : ι) (δ : K) : ι → K :=
  shiftAt (shiftAt z i δ) j (-δ)

theorem frost_error_cancellation_counterexample (G : B)
    (hG : Function.Injective (fun x : K => x • G)) (I : Finset ι) (z : ι → K)
    {i j : ι} (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) (δ : K) (hδ : δ ≠ 0) :
    (∑ k ∈ I, cancelErrors z i j δ k) = ∑ k ∈ I, z k ∧
    cancelErrors z i j δ i • G ≠ z i • G ∧
    cancelErrors z i j δ j • G ≠ z j • G := by
  refine ⟨?_, ?_, ?_⟩
  · simp [cancelErrors, sum_shiftAt I _ hj, sum_shiftAt I _ hi]
  · simpa [cancelErrors, shiftAt, hij] using shifted_response_rejected G hG (z i) δ hδ
  · simpa [cancelErrors, shiftAt, hij.symm] using
      shifted_response_rejected G hG (z j) (-δ) (neg_ne_zero.mpr hδ)

end Algebra

section Sessions
variable {q t n : ℕ} [Fact (Nat.Prime q)]
variable {B Msg : Type} [AddCommGroup B] [Module (ZMod q) B]

/-- The sorted list contains actual scalar identifiers and both public commitments. -/
abbrev CommitmentList (q : ℕ) (B : Type) := List (ZMod q × B × B)

structure HashContext (q : ℕ) (B Msg : Type) where
  binding : B → Msg → CommitmentList q B → ZMod q → ZMod q
  challenge : B → B → Msg → ZMod q

def identifierLE (S : Setup q t n B) (i j : Fin n) : Prop :=
  (S.coordinates i).val ≤ (S.coordinates j).val

instance (S : Setup q t n B) : DecidableRel (identifierLE S) :=
  fun _ _ => inferInstanceAs (Decidable (_ ≤ _))
instance (S : Setup q t n B) : IsTrans (Fin n) (identifierLE S) :=
  ⟨fun _ _ _ h h' => le_trans h h'⟩
instance (S : Setup q t n B) : Std.Total (identifierLE S) :=
  ⟨fun _ _ => le_total _ _⟩
instance (S : Setup q t n B) : Std.Antisymm (identifierLE S) :=
  ⟨fun _ _ h h' => S.coordinates_injective (ZMod.val_injective _ (le_antisymm h h'))⟩

def canonicalOrder (S : Setup q t n B) (I : Finset (Fin n)) : List (Fin n) :=
  I.sort (identifierLE S)

theorem canonicalOrder_nodup (S : Setup q t n B) (I : Finset (Fin n)) :
    (canonicalOrder S I).Nodup := Finset.sort_nodup _ _

theorem canonicalOrder_sorted (S : Setup q t n B) (I : Finset (Fin n)) :
    (canonicalOrder S I).Pairwise (fun i j => (S.coordinates i).val ≤ (S.coordinates j).val) :=
  Finset.pairwise_sort I (identifierLE S)

def commitmentList (S : Setup q t n B) (I : Finset (Fin n))
    (d e : Fin n → ZMod q) : CommitmentList q B :=
  (canonicalOrder S I).map (fun i => (S.coordinates i, d i • S.generator, e i • S.generator))

/-- Reject duplicates before converting a wire-level enumeration to a set. -/
def validEnumeration (xs : List (Fin n)) : Prop := xs.Nodup

theorem duplicate_enumeration_rejected (i : Fin n) (xs : List (Fin n)) :
    ¬validEnumeration (i :: i :: xs) := by simp [validEnumeration]

structure Session (S : Setup q t n B) (Msg : Type) where
  signers : Finset (Fin n)
  enough : t ≤ signers.card
  message : Msg
  hidingNonce : Fin n → ZMod q
  bindingNonce : Fin n → ZMod q

variable (S : Setup q t n B) (H : HashContext q B Msg)
variable (f : Polynomial (ZMod q))

def publicKey : B := f.eval 0 • S.generator

def sharePublic (i : Fin n) : B := f.eval (S.coordinates i) • S.generator

def bindingFactor (a : Session S Msg) (i : Fin n) : ZMod q :=
  H.binding (publicKey S f) a.message
    (commitmentList S a.signers a.hidingNonce a.bindingNonce) (S.coordinates i)

def R_share (a : Session S Msg) (i : Fin n) : B :=
  nonceShare S.generator (a.hidingNonce i) (a.bindingNonce i) (bindingFactor S H f a i)

def R_agg (a : Session S Msg) : B := ∑ i ∈ a.signers, R_share S H f a i

def challenge (a : Session S Msg) : ZMod q :=
  H.challenge (R_agg S H f a) (publicKey S f) a.message

def z_share (a : Session S Msg) (i : Fin n) : ZMod q :=
  response (a.hidingNonce i) (a.bindingNonce i) (bindingFactor S H f a i)
    (challenge S H f a) (lagrange_coeff S.coordinates a.signers i) (f.eval (S.coordinates i))

def z_agg (a : Session S Msg) : ZMod q := ∑ i ∈ a.signers, z_share S H f a i

theorem session_share_verification (a : Session S Msg) (i : Fin n) :
    z_share S H f a i • S.generator = R_share S H f a i +
      (challenge S H f a * lagrange_coeff S.coordinates a.signers i) • sharePublic S f i :=
  frost_share_verification _ _ _ _ _ _ _

theorem session_aggregate_verification (hf : f.natDegree < t) (a : Session S Msg) :
    z_agg S H f a • S.generator = R_agg S H f a + challenge S H f a • publicKey S f :=
  frost_aggregate_verification S.generator S.coordinates S.coordinates_injective f hf
    a.signers a.enough a.hidingNonce a.bindingNonce (bindingFactor S H f a) (challenge S H f a)

/-- Different sets and nonce pairs recompute every transcript-dependent quantity. -/
theorem frost_alternate_coalition_correctness (hf : f.natDegree < t)
    (a b : Session S Msg) :
    (z_agg S H f a • S.generator = R_agg S H f a + challenge S H f a • publicKey S f) ∧
    (z_agg S H f b • S.generator = R_agg S H f b + challenge S H f b • publicKey S f) :=
  ⟨session_aggregate_verification S H f hf a, session_aggregate_verification S H f hf b⟩

/-- Canonicalization erases enumeration order, not participant identity. -/
theorem frost_canonical_order_invariance (xs ys : List (Fin n)) (hp : xs.Perm ys)
    (d e : Fin n → ZMod q) :
    canonicalOrder S xs.toFinset = canonicalOrder S ys.toFinset ∧
    commitmentList S xs.toFinset d e = commitmentList S ys.toFinset d e := by
  have he : xs.toFinset = ys.toFinset := List.toFinset_eq_of_perm _ _ hp
  rw [he]
  exact ⟨rfl, rfl⟩

def sessionFromList (xs : List (Fin n)) (_ : validEnumeration xs)
    (h : t ≤ xs.toFinset.card) (m : Msg) (d e : Fin n → ZMod q) : Session S Msg :=
  ⟨xs.toFinset, h, m, d, e⟩

theorem canonical_session_invariance (xs ys : List (Fin n)) (hp : xs.Perm ys)
    (hx : validEnumeration xs) (hy : validEnumeration ys)
    (hxs : t ≤ xs.toFinset.card) (hys : t ≤ ys.toFinset.card)
    (m : Msg) (d e : Fin n → ZMod q) :
    let a := sessionFromList S xs hx hxs m d e
    let b := sessionFromList S ys hy hys m d e
    bindingFactor S H f a = bindingFactor S H f b ∧
    challenge S H f a = challenge S H f b ∧
    R_agg S H f a = R_agg S H f b ∧ z_agg S H f a = z_agg S H f b := by
  have he : xs.toFinset = ys.toFinset := List.toFinset_eq_of_perm _ _ hp
  simp only [sessionFromList, he, and_self, eq_self]

theorem frost_single_share_tamper_rejected (hf : f.natDegree < t)
    (a : Session S Msg) (i : Fin n) (δ : ZMod q) (hδ : δ ≠ 0) :
    (z_share S H f a i + δ) • S.generator ≠ R_share S H f a i +
      (challenge S H f a * lagrange_coeff S.coordinates a.signers i) • sharePublic S f i ∧
    (z_agg S H f a + δ) • S.generator ≠ R_agg S H f a + challenge S H f a • publicKey S f := by
  rw [← session_share_verification S H f a i, ← session_aggregate_verification S H f hf a]
  exact ⟨shifted_response_rejected _ S.generator_bijective.1 _ δ hδ,
    shifted_response_rejected _ S.generator_bijective.1 _ δ hδ⟩

theorem session_error_cancellation (hf : f.natDegree < t) (a : Session S Msg)
    {i j : Fin n} (hi : i ∈ a.signers) (hj : j ∈ a.signers) (hij : i ≠ j)
    (δ : ZMod q) (hδ : δ ≠ 0) :
    (∑ k ∈ a.signers, cancelErrors (z_share S H f a) i j δ k) • S.generator =
      R_agg S H f a + challenge S H f a • publicKey S f ∧
    cancelErrors (z_share S H f a) i j δ i • S.generator ≠ R_share S H f a i +
      (challenge S H f a * lagrange_coeff S.coordinates a.signers i) • sharePublic S f i ∧
    cancelErrors (z_share S H f a) i j δ j • S.generator ≠ R_share S H f a j +
      (challenge S H f a * lagrange_coeff S.coordinates a.signers j) • sharePublic S f j := by
  obtain ⟨hs, hi', hj'⟩ := frost_error_cancellation_counterexample S.generator
    S.generator_bijective.1 a.signers (z_share S H f a) hi hj hij δ hδ
  rw [hs, ← session_share_verification S H f a i, ← session_share_verification S H f a j]
  exact ⟨session_aggregate_verification S H f hf a, hi', hj'⟩

end Sessions

/-- Every valid parameter choice has a concrete scalar group model. -/
def ConsistencyModel (q t n : ℕ) [Fact (Nat.Prime q)] (ht : 0 < t)
    (htn : t ≤ n) (hnq : n < q) : Setup q t n (ZMod q) :=
  CryptoShamirSecretSharingGroup.ConsistencyModel q t n ht htn hnq

section Boundaries
variable {K B ι : Type*} [Field K] [AddCommGroup B] [Module K B] [DecidableEq ι]

theorem frost_reduction_to_schnorr_t1 (ξ : ι → K) (f : Polynomial K)
    (hf : f.natDegree < 1) (i : ι) (d e ρ c : K) :
    response d e ρ c (lagrange_coeff ξ {i} i) (f.eval (ξ i)) =
      (d + ρ * e) + c * f.eval 0 := by
  have hs := threshold_one (⟨f, hf, rfl⟩ : ShamirPoly K 1 (f.eval 0)) (ξ i)
  simp [response, lagrange_coeff, hs]

theorem frost_threshold_two (G : B) (ξ : ι → K) (hξ : Function.Injective ξ)
    (f : Polynomial K) (hf : f.natDegree < 2) {i j : ι} (hij : i ≠ j)
    (d e ρ : ι → K) (c : K) :
    (∑ k ∈ ({i, j} : Finset ι), response (d k) (e k) (ρ k) c
      (lagrange_coeff ξ {i, j} k) (f.eval (ξ k))) • G =
      (∑ k ∈ ({i, j} : Finset ι), nonceShare G (d k) (e k) (ρ k)) + c • (f.eval 0 • G) :=
  frost_aggregate_verification G ξ hξ f hf _ (by simp [hij]) d e ρ c

omit [DecidableEq ι] in
/-- Full participation at threshold n. -/
theorem frost_threshold_all {n : ℕ} (G : B) (ξ : Fin n → K) (hξ : Function.Injective ξ)
    (f : Polynomial K) (hf : f.natDegree < n) (d e ρ : Fin n → K) (c : K) :
    (∑ i, response (d i) (e i) (ρ i) c (lagrange_coeff ξ Finset.univ i)
      (f.eval (ξ i))) • G =
      (∑ i, nonceShare G (d i) (e i) (ρ i)) + c • (f.eval 0 • G) :=
  frost_aggregate_verification G ξ hξ f hf Finset.univ (by simp) d e ρ c

end Boundaries

section Suite
variable {q t n : ℕ} [Fact (Nat.Prime q)]
variable {B Msg : Type} [AddCommGroup B] [Module (ZMod q) B]

structure SessionProperties (S : Setup q t n B) (H : HashContext q B Msg) : Prop where
  partials : ∀ (f : Polynomial (ZMod q)) (a : Session S Msg) (i : Fin n),
    z_share S H f a i • S.generator = R_share S H f a i +
      (challenge S H f a * lagrange_coeff S.coordinates a.signers i) • sharePublic S f i
  aggregate : ∀ (f : Polynomial (ZMod q)), f.natDegree < t → ∀ a : Session S Msg,
    z_agg S H f a • S.generator = R_agg S H f a + challenge S H f a • publicKey S f
  canonical : ∀ (xs ys : List (Fin n)), xs.Perm ys → ∀ (d e : Fin n → ZMod q),
    canonicalOrder S xs.toFinset = canonicalOrder S ys.toFinset ∧
    commitmentList S xs.toFinset d e = commitmentList S ys.toFinset d e
  ordered : ∀ I, (canonicalOrder S I).Pairwise
    (fun i j => (S.coordinates i).val ≤ (S.coordinates j).val)
  tamper : ∀ (f : Polynomial (ZMod q)), f.natDegree < t → ∀ (a : Session S Msg)
    (i : Fin n) (δ : ZMod q), δ ≠ 0 →
    (z_share S H f a i + δ) • S.generator ≠ R_share S H f a i +
      (challenge S H f a * lagrange_coeff S.coordinates a.signers i) • sharePublic S f i ∧
    (z_agg S H f a + δ) • S.generator ≠ R_agg S H f a + challenge S H f a • publicKey S f
  cancellation : ∀ (f : Polynomial (ZMod q)), f.natDegree < t → ∀ (a : Session S Msg)
    (i j : Fin n), i ∈ a.signers → j ∈ a.signers → i ≠ j → ∀ δ : ZMod q, δ ≠ 0 →
    (∑ k ∈ a.signers, cancelErrors (z_share S H f a) i j δ k) • S.generator =
      R_agg S H f a + challenge S H f a • publicKey S f ∧
    cancelErrors (z_share S H f a) i j δ i • S.generator ≠ R_share S H f a i +
      (challenge S H f a * lagrange_coeff S.coordinates a.signers i) • sharePublic S f i ∧
    cancelErrors (z_share S H f a) i j δ j • S.generator ≠ R_share S H f a j +
      (challenge S H f a * lagrange_coeff S.coordinates a.signers j) • sharePublic S f j

theorem session_properties (S : Setup q t n B) (H : HashContext q B Msg) :
    SessionProperties S H where
  partials := session_share_verification S H
  aggregate := session_aggregate_verification S H
  canonical := frost_canonical_order_invariance S
  ordered := canonicalOrder_sorted S
  tamper := frost_single_share_tamper_rejected S H
  cancellation := fun f hf a _ _ hi hj hij δ hδ =>
    session_error_cancellation S H f hf a hi hj hij δ hδ

end Suite

structure CryptoThresholdSchnorrFrostGroupSuite : Prop where
  sessions : ∀ (q t n : ℕ) [Fact (Nat.Prime q)] (B Msg : Type) [AddCommGroup B]
    [Module (ZMod q) B] (S : Setup q t n B) (H : HashContext q B Msg), SessionProperties S H
  model : ∀ (q t n : ℕ) [Fact (Nat.Prime q)], 0 < t → t ≤ n → n < q →
    Nonempty (Setup q t n (ZMod q))
  schnorr : ∀ (q : ℕ) [Fact (Nat.Prime q)] (ξ : Fin 1 → ZMod q)
    (f : Polynomial (ZMod q)), f.natDegree < 1 → ∀ (d e ρ c : ZMod q),
    response d e ρ c (lagrange_coeff ξ {0} 0) (f.eval (ξ 0)) = (d + ρ * e) + c * f.eval 0

theorem crypto_threshold_schnorr_frost_group_master_suite :
    CryptoThresholdSchnorrFrostGroupSuite where
  sessions := fun _ _ _ _ _ _ _ _ => session_properties
  model := fun q t n _ ht htn hnq => ⟨ConsistencyModel q t n ht htn hnq⟩
  schnorr := fun _ _ ξ f hf d e ρ c => frost_reduction_to_schnorr_t1 ξ f hf 0 d e ρ c

end CryptoThresholdSchnorrFrostGroup
