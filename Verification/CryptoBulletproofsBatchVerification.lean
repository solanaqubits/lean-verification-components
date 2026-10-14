/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsInnerProduct
import Verification.CryptoBulletproofsRangeReduction
import Mathlib.Probability.Distributions.Uniform

/-! Random linear batching of fixed public verification residuals. The probability
bound concerns independent uniform field weights, not witness extraction or ROM. -/
namespace CryptoBulletproofsBatchVerification
open scoped BigOperators ENNReal
open CryptoBulletproofsInnerProduct CryptoBulletproofsRangeReduction

section Residuals
variable {q n : ℕ} [Fact q.Prime] {A : Type} [AddCommGroup A] [Module (ZMod q) A]

def batch_residual_sum (D : Fin n → A) (r : Fin n → ZMod q) : A := ∑ i, r i • D i

theorem batch_completeness (D : Fin n → A) (h : ∀ i, D i = 0) (r : Fin n → ZMod q) :
    batch_residual_sum D r = 0 := by simp [batch_residual_sum, h]

theorem joint_permutation_invariance (D : Fin n → A) (r : Fin n → ZMod q)
    (e : Equiv.Perm (Fin n)) :
    batch_residual_sum (D ∘ e) (r ∘ e) = batch_residual_sum D r := by
  exact Equiv.sum_comp e (fun i => r i • D i)

theorem cancellation_counterexample (D : A) (r : ZMod q) :
    r • D + r • (-D) = 0 := by simp

/-- Fixing all other coordinates leaves at most one accepting pivot coefficient. -/
theorem accepting_pivot_unique (D : Fin n → A) (j : Fin n) (hj : D j ≠ 0)
    (r s : Fin n → ZMod q) (hr : batch_residual_sum D r = 0)
    (hs : batch_residual_sum D s = 0) (he : ∀ i, i ≠ j → r i = s i) : r = s := by
  classical
  have ht : (∑ i ∈ Finset.univ.erase j, r i • D i) =
      ∑ i ∈ Finset.univ.erase j, s i • D i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i (Finset.mem_erase.mp hi).1]
  have hh : r j • D j = s j • D j := by
    unfold batch_residual_sum at hr hs
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at hr hs
    rw [ht] at hr
    exact add_left_cancel (hr.trans hs.symm)
  have hp : r j = s j := (smul_left_injective (ZMod q) hj) hh
  funext i
  by_cases hi : i = j
  · simpa [hi] using hp
  · exact he i hi

theorem accepting_card_bound (D : Fin n → A) (hd : ∃ j, D j ≠ 0) :
    Nat.card {r : Fin n → ZMod q // batch_residual_sum D r = 0} ≤ q ^ (n - 1) := by
  classical
  obtain ⟨j, hj⟩ := hd
  let restrict : {r : Fin n → ZMod q // batch_residual_sum D r = 0} →
      ({i : Fin n // i ≠ j} → ZMod q) := fun r i => r.val i.val
  have hinj : Function.Injective restrict := by
    intro r s h
    apply Subtype.ext
    exact accepting_pivot_unique D j hj r.val s.val r.property s.property
      (fun i hi => congrFun h ⟨i, hi⟩)
  have hc := Fintype.card_le_of_injective restrict hinj
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin] using hc

/-- Uniform on the full product includes zero weights and samples every coordinate
independently; D is an external fixed parameter of this experiment. -/
noncomputable def acceptance_probability (D : Fin n → A) : ℝ≥0∞ :=
  (PMF.uniformOfFintype (Fin n → ZMod q)).toOuterMeasure
    {r | batch_residual_sum D r = 0}

theorem batch_soundness_error_bound (D : Fin n → A) (hd : ∃ j, D j ≠ 0) :
    acceptance_probability (q := q) D ≤ 1 / (q : ℝ≥0∞) := by
  classical
  unfold acceptance_probability
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  have hc := accepting_card_bound (q := q) D hd
  rw [Nat.card_eq_fintype_card] at hc
  have hn : n ≠ 0 := by obtain ⟨j, _⟩ := hd; have := j.isLt; omega
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hexp : q ^ n = q ^ (n - 1) * q := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
  calc
    _ ≤ (q ^ (n - 1) : ℕ) / (Fintype.card (Fin n → ZMod q) : ℝ≥0∞) :=
      ENNReal.div_le_div_right (by exact_mod_cast hc) _
    _ = 1 / (q : ℝ≥0∞) := by
      simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, hexp, Nat.cast_mul]
      simpa only [mul_one] using ENNReal.mul_div_mul_left 1 (q : ℝ≥0∞)
        (show (q ^ (n - 1) : ℕ) ≠ (0 : ℝ≥0∞) by exact_mod_cast pow_ne_zero (n - 1) hq)
        (ENNReal.natCast_ne_top _)
end Residuals

section Protocol
variable {q k m : ℕ} [Fact q.Prime] {A : Type} [AddCommGroup A] [Module (ZMod q) A]

/-- Public data of a single fixed proof. IPA challenges are units by construction. -/
structure ProofInstance (q : ℕ) (A : Type) (k : ℕ) where
  V : A
  y : ZMod q
  z : ZMod q
  x : ZMod q
  xs : Fin k → (ZMod q)ˣ
  transcript : RangeReductionTranscript q A k

structure ProofResiduals (A : Type) where
  poly_residual : A
  ipa_residual : A
  scalars_valid : Prop

def polynomial_residual (p : Generators q A k) (t : ProofInstance q A k) : A :=
  value_commit p t.transcript.tx t.transcript.taux -
    (t.z ^ 2 • t.V + delta_fn t.y t.z (2 ^ k) • p.B +
      t.x • t.transcript.T1 + t.x ^ 2 • t.transcript.T2)

def inner_product_residual (p : Generators q A k) (t : ProofInstance q A k) : A :=
  range_target p t.transcript.Ac t.transcript.Sc t.y t.z t.x t.transcript.mu t.transcript.tx +
    round_correction t.xs t.transcript.ipa -
    (multiscalar_mul (fun i => t.transcript.ipa.a_final * weights_G k t.xs i) p.G +
      multiscalar_mul (fun i => t.transcript.ipa.b_final * weights_H k t.xs i) (scaled_H p.H t.y) +
      (t.transcript.ipa.a_final * t.transcript.ipa.b_final) • p.U)

def proof_residuals (p : Generators q A k) (t : ProofInstance q A k) : ProofResiduals A :=
  ⟨polynomial_residual p t, inner_product_residual p t, t.y ≠ 0 ∧ t.x ≠ 0⟩

/-- The additional x guard is explicit; module 159 itself permits x=0. -/
def individual_verify [DecidableEq A] (p : Generators q A k) (t : ProofInstance q A k) : Bool :=
  decide (t.x ≠ 0) && verify_range_reduction p t.V t.y t.z t.x t.xs t.transcript

theorem individual_iff_residuals_zero [DecidableEq A] (p : Generators q A k)
    (t : ProofInstance q A k) :
    individual_verify p t = true ↔ (proof_residuals p t).scalars_valid ∧
      (proof_residuals p t).poly_residual = 0 ∧ (proof_residuals p t).ipa_residual = 0 := by
  simp only [individual_verify, verify_range_reduction, ipa_batch_verification_equivalence,
    batch_verifier, Bool.and_eq_true, decide_eq_true_eq, proof_residuals,
    polynomial_residual, inner_product_residual, sub_eq_zero]
  tauto

/-- First m coordinates are polynomial residuals, the next m are IPA residuals. -/
def residual_vector (proofs : Fin m → ProofResiduals A) : Fin (2 * m) → A :=
  fun i => Fin.append (fun j => (proofs j).poly_residual) (fun j => (proofs j).ipa_residual)
    (Fin.cast (two_mul m) i)

theorem residual_vector_zero_iff (proofs : Fin m → ProofResiduals A) :
    (∀ i, residual_vector proofs i = 0) ↔
      ∀ j, (proofs j).poly_residual = 0 ∧ (proofs j).ipa_residual = 0 := by
  constructor
  · intro h j
    constructor
    · simpa only [residual_vector, Fin.cast_cast, Fin.cast_refl, id_eq,
        Fin.append_left, Fin.append_right] using h (Fin.cast (two_mul m).symm (Fin.castAdd m j))
    · simpa only [residual_vector, Fin.cast_cast, Fin.cast_refl, id_eq,
        Fin.append_left, Fin.append_right] using h (Fin.cast (two_mul m).symm (Fin.natAdd m j))
  · intro h i
    simp only [residual_vector]
    generalize Fin.cast (two_mul m) i = a
    exact Fin.addCases (fun j => by simpa using (h j).1)
      (fun j => by simpa only [Fin.append_right] using (h j).2) a

def verify_batch [DecidableEq A] (p : Generators q A k) (ts : Fin m → ProofInstance q A k)
    (r : Fin (2 * m) → ZMod q) : Bool :=
  decide (∀ j, (ts j).y ≠ 0 ∧ (ts j).x ≠ 0) &&
    decide (batch_residual_sum (residual_vector (fun j => proof_residuals p (ts j))) r = 0)

theorem batch_protocol_completeness [DecidableEq A] (p : Generators q A k)
    (ts : Fin m → ProofInstance q A k) (h : ∀ j, individual_verify p (ts j) = true)
    (r : Fin (2 * m) → ZMod q) : verify_batch p ts r = true := by
  have hz := fun j => (individual_iff_residuals_zero p (ts j)).mp (h j)
  have hv : ∀ i, residual_vector (fun j => proof_residuals p (ts j)) i = 0 :=
    (residual_vector_zero_iff _).mpr (fun j => (hz j).2)
  simp only [verify_batch, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun j => (hz j).1, batch_completeness _ hv r⟩

theorem batch_zero_y_rejected [DecidableEq A] (p : Generators q A k)
    (ts : Fin m → ProofInstance q A k) (j : Fin m) (hj : (ts j).y = 0)
    (r : Fin (2 * m) → ZMod q) : verify_batch p ts r = false := by
  have h : ¬ ∀ j, (ts j).y ≠ 0 ∧ (ts j).x ≠ 0 := fun h => (h j).1 hj
  simp [verify_batch, h]

theorem batch_zero_x_rejected [DecidableEq A] (p : Generators q A k)
    (ts : Fin m → ProofInstance q A k) (j : Fin m) (hj : (ts j).x = 0)
    (r : Fin (2 * m) → ZMod q) : verify_batch p ts r = false := by
  have h : ¬ ∀ j, (ts j).y ≠ 0 ∧ (ts j).x ≠ 0 := fun h => (h j).2 hj
  simp [verify_batch, h]

/-- Includes invalid guards: these reject with probability one. -/
theorem batch_protocol_soundness [DecidableEq A] (p : Generators q A k)
    (ts : Fin m → ProofInstance q A k) (hbad : ∃ j, individual_verify p (ts j) ≠ true) :
    (PMF.uniformOfFintype (Fin (2 * m) → ZMod q)).toOuterMeasure
      {r | verify_batch p ts r = true} ≤ 1 / (q : ℝ≥0∞) := by
  classical
  by_cases hg : ∀ j, (ts j).y ≠ 0 ∧ (ts j).x ≠ 0
  · have hd : ∃ i, residual_vector (fun j => proof_residuals p (ts j)) i ≠ 0 := by
      by_contra! hz
      have hh := (residual_vector_zero_iff _).mp hz
      obtain ⟨j, hj⟩ := hbad
      exact hj ((individual_iff_residuals_zero p (ts j)).mpr ⟨hg j, hh j⟩)
    simpa [verify_batch, hg, acceptance_probability] using
      batch_soundness_error_bound (q := q) _ hd
  · simp [verify_batch, hg]

/-- Coefficients on the common bases B, Hblind, U, G_i, H_i. -/
abbrev SharedIndex (k : ℕ) := Fin 3 ⊕ (Fin (2 ^ k) ⊕ Fin (2 ^ k))
abbrev LocalIndex (k : ℕ) := Fin 5 ⊕ (Fin k ⊕ Fin k)

def shared_bases (p : Generators q A k) : SharedIndex k → A :=
  Sum.elim ![p.B, p.Hblind, p.U] (Sum.elim p.G p.H)

def shared_coefficients (t : ProofInstance q A k) (u v : ZMod q) : SharedIndex k → ZMod q :=
  Sum.elim ![u * (t.transcript.tx - delta_fn t.y t.z (2 ^ k)),
    u * t.transcript.taux - v * t.transcript.mu,
    v * (t.transcript.tx - t.transcript.ipa.a_final * t.transcript.ipa.b_final)]
    (Sum.elim
      (fun i => v * (-t.z - t.transcript.ipa.a_final * weights_G k t.xs i))
      (fun i => (v * (t.z * t.y ^ i.val + t.z ^ 2 * 2 ^ i.val -
        t.transcript.ipa.b_final * weights_H k t.xs i)) * (t.y⁻¹) ^ i.val))

def local_bases (t : ProofInstance q A k) : LocalIndex k → A :=
  Sum.elim ![t.V, t.transcript.Ac, t.transcript.Sc, t.transcript.T1, t.transcript.T2]
    (Sum.elim (fun i => (t.transcript.ipa.rounds i).L) (fun i => (t.transcript.ipa.rounds i).R))

def local_coefficients (t : ProofInstance q A k) (u v : ZMod q) : LocalIndex k → ZMod q :=
  Sum.elim ![-(u * t.z ^ 2), v, v * t.x, -(u * t.x), -(u * t.x ^ 2)]
    (Sum.elim (fun i => v * (t.xs i : ZMod q)^2)
      (fun i => v * (↑(t.xs i)⁻¹ : ZMod q)^2))

theorem weighted_residual_expansion (p : Generators q A k) (t : ProofInstance q A k)
    (u v : ZMod q) :
    u • polynomial_residual p t + v • inner_product_residual p t =
      (∑ i, shared_coefficients t u v i • shared_bases p i) +
      ∑ i, local_coefficients t u v i • local_bases t i := by
  simp only [polynomial_residual, inner_product_residual, value_commit, range_target,
    round_correction, multiscalar_mul, scaled_H, shared_coefficients, shared_bases,
    local_coefficients, local_bases, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    add_zero]
  simp only [smul_add, smul_sub, smul_neg, Finset.smul_sum, mul_smul, sub_smul, add_smul,
    neg_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  abel

def poly_weight (r : Fin (2 * m) → ZMod q) (j : Fin m) : ZMod q :=
  r (Fin.cast (two_mul m).symm (Fin.castAdd m j))
def ipa_weight (r : Fin (2 * m) → ZMod q) (j : Fin m) : ZMod q :=
  r (Fin.cast (two_mul m).symm (Fin.natAdd m j))

theorem residual_sum_split (p : Generators q A k) (ts : Fin m → ProofInstance q A k)
    (r : Fin (2 * m) → ZMod q) :
    batch_residual_sum (residual_vector (fun j => proof_residuals p (ts j))) r =
      ∑ j, (poly_weight r j • polynomial_residual p (ts j) +
        ipa_weight r j • inner_product_residual p (ts j)) := by
  unfold batch_residual_sum
  rw [← (finCongr (two_mul m).symm).sum_comp, Fin.sum_univ_add]
  simp only [residual_vector, finCongr_apply, Fin.cast_cast, Fin.cast_refl, id_eq,
    Fin.append_left, Fin.append_right, proof_residuals, poly_weight, ipa_weight,
    Finset.sum_add_distrib]

/-- A single MSM index: common bases occur once; proof-specific points retain their index. -/
abbrev MSMIndex (k m : ℕ) := SharedIndex k ⊕ (Fin m × LocalIndex k)

def msm_bases (p : Generators q A k) (ts : Fin m → ProofInstance q A k) : MSMIndex k m → A :=
  Sum.elim (shared_bases p) (fun ji => local_bases (ts ji.1) ji.2)

def msm_coefficients (ts : Fin m → ProofInstance q A k) (r : Fin (2 * m) → ZMod q) :
    MSMIndex k m → ZMod q :=
  Sum.elim (fun i => ∑ j, shared_coefficients (ts j) (poly_weight r j) (ipa_weight r j) i)
    (fun ji => local_coefficients (ts ji.1) (poly_weight r ji.1) (ipa_weight r ji.1) ji.2)

def combined_msm (p : Generators q A k) (ts : Fin m → ProofInstance q A k)
    (r : Fin (2 * m) → ZMod q) : A := ∑ i, msm_coefficients ts r i • msm_bases p ts i

theorem msm_rearrangement_equiv (p : Generators q A k) (ts : Fin m → ProofInstance q A k)
    (r : Fin (2 * m) → ZMod q) :
    batch_residual_sum (residual_vector (fun j => proof_residuals p (ts j))) r =
      combined_msm p ts r := by
  rw [residual_sum_split]
  simp_rw [weighted_residual_expansion]
  unfold combined_msm msm_coefficients msm_bases
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_smul]
  rw [Fintype.sum_prod_type, Finset.sum_add_distrib, Finset.sum_comm]

def verify_batch_msm [DecidableEq A] (p : Generators q A k) (ts : Fin m → ProofInstance q A k)
    (r : Fin (2 * m) → ZMod q) : Bool :=
  decide (∀ j, (ts j).y ≠ 0 ∧ (ts j).x ≠ 0) && decide (combined_msm p ts r = 0)

theorem verify_batch_msm_equiv [DecidableEq A] (p : Generators q A k)
    (ts : Fin m → ProofInstance q A k) (r : Fin (2 * m) → ZMod q) :
    verify_batch p ts r = verify_batch_msm p ts r := by
  simp only [verify_batch, verify_batch_msm, msm_rearrangement_equiv]

/-- The challenge x is additionally required to be nonzero by this module's wrapper. -/
theorem honest_individual_completeness [DecidableEq A] (p : Generators q A k)
    (a s t : Vec k (ZMod q)) (v gamma alpha rho tau1 tau2 y z x : ZMod q)
    (xs : Fin k → (ZMod q)ˣ) (hy : y ≠ 0) (hx : x ≠ 0)
    (hbit : ∀ i, a i * (a i - 1) = 0) (hv : ∑ i, (2 : ZMod q) ^ i.val * a i = v) :
    individual_verify p ⟨value_commit p v gamma, y, z, x, xs,
      range_prover p a s t gamma alpha rho tau1 tau2 y z x xs⟩ = true := by
  simp only [individual_verify]
  rw [range_proof_composition_completeness p a s t v gamma alpha rho tau1 tau2 y z x xs hy hbit hv]
  simp [hx]

/-- Reindexing proofs pairs each polynomial and IPA coefficient with its proof. -/
def permute_weights (e : Equiv.Perm (Fin m)) (r : Fin (2 * m) → ZMod q) : Fin (2 * m) → ZMod q :=
  fun i => Fin.append (poly_weight r ∘ e) (ipa_weight r ∘ e) (Fin.cast (two_mul m) i)

theorem batch_joint_permutation_invariance [DecidableEq A] (p : Generators q A k)
    (ts : Fin m → ProofInstance q A k) (r : Fin (2 * m) → ZMod q) (e : Equiv.Perm (Fin m)) :
    verify_batch p (ts ∘ e) (permute_weights e r) = verify_batch p ts r := by
  have hg : (∀ j, (ts (e j)).y ≠ 0 ∧ (ts (e j)).x ≠ 0) ↔
      ∀ j, (ts j).y ≠ 0 ∧ (ts j).x ≠ 0 := by
    constructor
    · intro h j
      simpa using h (e.symm j)
    · intro h j
      exact h (e j)
  have hs : (∑ j, (poly_weight (permute_weights e r) j • polynomial_residual p (ts (e j)) +
      ipa_weight (permute_weights e r) j • inner_product_residual p (ts (e j)))) =
      ∑ j, (poly_weight r j • polynomial_residual p (ts j) +
        ipa_weight r j • inner_product_residual p (ts j)) := by
    simp only [poly_weight, ipa_weight, permute_weights, Fin.cast_cast, Fin.cast_refl,
      id_eq, Fin.append_left, Fin.append_right, Function.comp_apply]
    simpa only [poly_weight, ipa_weight] using Equiv.sum_comp e
      (fun j => poly_weight r j • polynomial_residual p (ts j) +
        ipa_weight r j • inner_product_residual p (ts j))
  simp only [verify_batch, residual_sum_split, Function.comp_apply, hg, hs]

/-- A concrete corruption family with a proved nonzero residual, not an assumption
that every syntactic transcript alteration must change its verification equation. -/
def alter_T1 (t : ProofInstance q A k) (D : A) : ProofInstance q A k :=
  { t with transcript := { t.transcript with T1 := t.transcript.T1 + D } }

theorem altered_T1_residual (p : Generators q A k) (t : ProofInstance q A k) (D : A) :
    polynomial_residual p (alter_T1 t D) = polynomial_residual p t - t.x • D := by
  simp only [polynomial_residual, alter_T1, smul_add]
  abel

theorem altered_T1_detectable (p : Generators q A k) (t : ProofInstance q A k)
    (D : A) (hD : D ≠ 0) (hx : t.x ≠ 0) (ht : polynomial_residual p t = 0) :
    polynomial_residual p (alter_T1 t D) ≠ 0 := by
  rw [altered_T1_residual, ht, zero_sub, neg_ne_zero]
  exact smul_ne_zero hx hD

theorem altered_T1_batch_error_bound [DecidableEq A] (p : Generators q A k)
    (ts : Fin m → ProofInstance q A k) (j : Fin m) (D : A) (hD : D ≠ 0)
    (hx : (ts j).x ≠ 0) (ht : polynomial_residual p (ts j) = 0) :
    (PMF.uniformOfFintype (Fin (2 * m) → ZMod q)).toOuterMeasure
      {r | verify_batch p (Function.update ts j (alter_T1 (ts j) D)) r = true} ≤
        1 / (q : ℝ≥0∞) := by
  apply batch_protocol_soundness
  refine ⟨j, ?_⟩
  simp only [Function.update_self]
  intro h
  exact altered_T1_detectable p (ts j) D hD hx ht
    ((individual_iff_residuals_zero p _).mp h).2.1

structure VerifiedProperties (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A] : Prop where
  individual_equivalence : ∀ k (p : Generators q A k) t,
    individual_verify p t = true ↔ (proof_residuals p t).scalars_valid ∧
      (proof_residuals p t).poly_residual = 0 ∧ (proof_residuals p t).ipa_residual = 0
  completeness : ∀ k m (p : Generators q A k) (ts : Fin m → ProofInstance q A k),
    (∀ j, individual_verify p (ts j) = true) → ∀ r, verify_batch p ts r = true
  probability_bound : ∀ n (D : Fin n → A), (∃ j, D j ≠ 0) →
    acceptance_probability (q := q) D ≤ 1 / (q : ℝ≥0∞)
  protocol_probability : ∀ k m (p : Generators q A k) (ts : Fin m → ProofInstance q A k),
    (∃ j, individual_verify p (ts j) ≠ true) →
    (PMF.uniformOfFintype (Fin (2 * m) → ZMod q)).toOuterMeasure
      {r | verify_batch p ts r = true} ≤ 1 / (q : ℝ≥0∞)
  msm_equivalence : ∀ k m (p : Generators q A k) (ts : Fin m → ProofInstance q A k) r,
    batch_residual_sum (residual_vector (fun j => proof_residuals p (ts j))) r = combined_msm p ts r
  permutation : ∀ k m (p : Generators q A k) (ts : Fin m → ProofInstance q A k)
    r (e : Equiv.Perm (Fin m)),
    verify_batch p (ts ∘ e) (permute_weights e r) = verify_batch p ts r
  cancellation : ∀ (D : A) (r : ZMod q), r • D + r • (-D) = 0
  zero_y : ∀ k m (p : Generators q A k) (ts : Fin m → ProofInstance q A k) j,
    (ts j).y = 0 → ∀ r, verify_batch p ts r = false
  zero_x : ∀ k m (p : Generators q A k) (ts : Fin m → ProofInstance q A k) j,
    (ts j).x = 0 → ∀ r, verify_batch p ts r = false

theorem verified_properties [DecidableEq A] : VerifiedProperties q A where
  individual_equivalence := fun _ => individual_iff_residuals_zero
  completeness := fun _ _ => batch_protocol_completeness
  probability_bound := fun _ => batch_soundness_error_bound
  protocol_probability := fun _ _ => batch_protocol_soundness
  msm_equivalence := fun _ _ => msm_rearrangement_equiv
  permutation := fun _ _ => batch_joint_permutation_invariance
  cancellation := cancellation_counterexample
  zero_y := fun _ _ => batch_zero_y_rejected
  zero_x := fun _ _ => batch_zero_x_rejected
end Protocol

structure CryptoBulletproofsBatchVerificationSuite : Prop where
  all_models : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A], VerifiedProperties q A
  cyclic_model : ∀ (q : ℕ) [Fact q.Prime],
    Nonempty (CryptoPedersenHomomorphicSum.Setup q (ZMod q))

theorem verification_suite : CryptoBulletproofsBatchVerificationSuite where
  all_models := fun _ _ _ _ _ _ => verified_properties
  cyclic_model := CryptoPedersenHomomorphicSum.setup_satisfiable

end CryptoBulletproofsBatchVerification
