/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsInnerProduct
import Verification.CryptoBulletproofsRangeReduction
import Verification.CryptoBulletproofsBatchVerification

/-! Algebraic aggregation of range witnesses. Challenges are external inputs.
Formal coefficient recovery is not extraction from accepted transcripts.
Knowledge soundness, binding security, HVZK and Fiat - Shamir remain outside scope. -/
namespace CryptoBulletproofsAggregation
open scoped BigOperators
open CryptoBulletproofsInnerProduct
open CryptoBulletproofsRangeReduction

abbrev Block (m n : ℕ) := Fin m × Fin n

def agg_index {m n : ℕ} (j : Fin m) (i : Fin n) : Fin (m * n) := finProdFinEquiv (j, i)
def global_index {m n : ℕ} (r : Block m n) : ℕ := (agg_index r.1 r.2).val

theorem global_index_eq {m n : ℕ} (j : Fin m) (i : Fin n) :
    global_index (j, i) = j.val * n + i.val := by
  simp [global_index, agg_index, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

@[simp] theorem global_index_inj {m n : ℕ} (r s : Block m n) :
    global_index r = global_index s ↔ r = s := by
  exact Fin.val_inj.trans finProdFinEquiv.injective.eq_iff

theorem agg_dimension (a b : ℕ) : 2 ^ b * 2 ^ a = 2 ^ (a + b) := by
  rw [pow_add, Nat.mul_comm]

def block_equiv (a b : ℕ) : Block (2 ^ b) (2 ^ a) ≃ Fin (2 ^ (a + b)) :=
  finProdFinEquiv.trans (finCongr (agg_dimension a b))

def flatten {a b : ℕ} {F : Type} (v : Block (2 ^ b) (2 ^ a) → F) : Vec (a + b) F :=
  fun i => v ((block_equiv a b).symm i)

theorem sum_flatten {a b : ℕ} {F : Type} [AddCommMonoid F]
    (v : Block (2 ^ b) (2 ^ a) → F) : ∑ i, flatten v i = ∑ r, v r :=
  (block_equiv a b).symm.sum_comp v

section Ring
variable {F : Type} [CommRing F] {m n : ℕ}
def block_weight (z : F) (r : Block m n) : F := z ^ (r.1.val + 2) * 2 ^ r.2.val
def agg_delta (m n : ℕ) (y z : F) : F :=
  (z - z ^ 2) * (∑ r : Block m n, y ^ global_index r) -
    ∑ j : Fin m, z ^ (j.val + 3) * (∑ i : Fin n, (2 : F) ^ i.val)
def block_value (u : Block m n → F) (j : Fin m) : F :=
  ∑ i : Fin n, (2 : F) ^ i.val * u (j, i)
def agg_l_poly (u s : Block m n → F) (z x : F) : Block m n → F :=
  fun r => u r - z + x * s r
def agg_r_poly (v t : Block m n → F) (y z x : F) : Block m n → F :=
  fun r => y ^ global_index r * (v r + z + x * t r) + block_weight z r
def block_dot (u v : Block m n → F) : F := ∑ r, u r * v r

def agg_t0 (u v : Block m n → F) (y z : F) : F :=
  block_dot (agg_l_poly u 0 z 0) (agg_r_poly v 0 y z 0)
def agg_t1 (u v s t : Block m n → F) (y z : F) : F :=
  ∑ r, ((u r - z) * (y ^ global_index r * t r) +
    s r * (y ^ global_index r * (v r + z) + block_weight z r))
def agg_t2 (s t : Block m n → F) (y : F) : F :=
  ∑ r, s r * (y ^ global_index r * t r)

theorem global_power_sum (y : F) :
    (∑ r : Block m n, y ^ global_index r) = ∑ i : Fin (m * n), y ^ i.val :=
  finProdFinEquiv.sum_comp (fun i => y ^ i.val)

theorem agg_delta_m1_spec (y z : F) : agg_delta 1 n y z = delta_fn y z n := by
  simp [agg_delta, delta_fn, Fintype.sum_prod_type, global_index_eq]

theorem agg_inner_product_expansion (u v s t : Block m n → F) (y z x : F) :
    block_dot (agg_l_poly u s z x) (agg_r_poly v t y z x) =
      agg_t0 u v y z + agg_t1 u v s t y z * x + agg_t2 s t y * x ^ 2 := by
  simp only [block_dot, agg_l_poly, agg_r_poly, agg_t0, agg_t1, agg_t2,
    Pi.zero_apply, mul_zero, add_zero, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem agg_t0_residual (u v : Block m n → F) (values : Fin m → F) (y z : F) :
    agg_t0 u v y z - ((∑ j, z ^ (j.val + 2) * values j) + agg_delta m n y z) =
      (∑ r, (u r * v r) * y ^ global_index r) +
      z * (∑ r, (u r - v r - 1) * y ^ global_index r) +
      ∑ j, z ^ (j.val + 2) * (block_value u j - values j) := by
  have hc : ∀ r : Block m n,
      (u r - z) * (y ^ global_index r * (v r + z) + block_weight z r) =
      (u r * v r) * y ^ global_index r + z * ((u r - v r - 1) * y ^ global_index r) +
      (z - z ^ 2) * y ^ global_index r +
      z ^ (r.1.val + 2) * ((2 : F)^r.2.val * u r) - z ^ (r.1.val + 3) * 2 ^ r.2.val := by
    intro r
    simp only [block_weight, show r.1.val + 3 = (r.1.val + 2) + 1 from rfl, pow_succ]
    ring
  simp only [agg_t0, block_dot, agg_l_poly, agg_r_poly, Pi.zero_apply, mul_zero,
    add_zero, hc, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [agg_delta, block_value, Fintype.sum_prod_type, mul_sub, Finset.mul_sum,
    Finset.sum_sub_distrib]
  ring

theorem agg_t0_spec (u v : Block m n → F) (values : Fin m → F) (y z : F)
    (hb : ∀ r, v r = u r - 1) (hbit : ∀ r, u r * v r = 0)
    (hv : ∀ j, block_value u j = values j) :
    agg_t0 u v y z = (∑ j, z ^ (j.val + 2) * values j) + agg_delta m n y z := by
  apply sub_eq_zero.mp
  rw [agg_t0_residual]
  simp only [hbit, zero_mul, Finset.sum_const_zero, zero_add, hv, sub_self, mul_zero, add_zero]
  simp [hb]
end Ring

section Formal
variable {F : Type} [Field F] {m n : ℕ}
open Polynomial
noncomputable def agg_formal_t0 (u v : Block m n → F) : YZ F :=
  agg_t0 (fun r => liftYZ (u r)) (fun r => liftYZ (v r)) (C X) X
noncomputable def agg_formal_rhs (values : Fin m → F) (n : ℕ) : YZ F :=
  (∑ j, X ^ (j.val + 2) * liftYZ (values j)) + agg_delta m n (C (X : Polynomial F)) X

theorem agg_formal_residual (u v : Block m n → F) (values : Fin m → F) :
    agg_formal_t0 u v - agg_formal_rhs values n =
      C (∑ r, C (u r * v r) * X ^ global_index r) +
      C (∑ r, C (u r - v r - 1) * X ^ global_index r) * X +
      ∑ j, C (C (block_value u j - values j)) * X ^ (j.val + 2) := by
  rw [agg_formal_t0, agg_formal_rhs, agg_t0_residual]
  simp only [liftYZ, block_value, map_sum, map_sub, map_mul, map_pow, map_ofNat, map_one]
  simp only [mul_comm]

theorem agg_poly_identity_implies_bits (u v : Block m n → F) (values : Fin m → F)
    (h : agg_formal_t0 u v = agg_formal_rhs values n) :
    (∀ r, v r = u r - 1) ∧ (∀ r, u r = 0 ∨ u r = 1) ∧
      (∀ j, block_value u j = values j) := by
  have hr := agg_formal_residual u v values
  rw [h, sub_self] at hr
  have h0 := congrArg (fun p : YZ F => p.coeff 0) hr
  have h1 := congrArg (fun p : YZ F => p.coeff 1) hr
  have hn0 : ∀ j : Fin m, 0 ≠ j.val + 2 := by intro j; omega
  have hn1 : ∀ j : Fin m, 1 ≠ j.val + 2 := by intro j; omega
  norm_num only [coeff_zero, coeff_add, coeff_C, coeff_C_mul_X, finsetSum_coeff,
    coeff_C_mul_X_pow, hn0, hn1, if_false, if_true, Finset.sum_const_zero,
    zero_add, add_zero] at h0 h1
  have hb : ∀ r, v r = u r - 1 := by
    intro r
    have hi := congrArg (fun p : Polynomial F => p.coeff (global_index r)) h1
    simp only [coeff_zero, finsetSum_coeff, coeff_C_mul_X_pow, global_index_inj,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at hi
    linear_combination hi
  have hab : ∀ r, u r * v r = 0 := by
    intro r
    have hi := congrArg (fun p : Polynomial F => p.coeff (global_index r)) h0
    simpa only [coeff_zero, finsetSum_coeff, coeff_C_mul_X_pow, global_index_inj,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] using hi.symm
  refine ⟨hb, fun r => ?_, fun j => ?_⟩
  · have hi := hab r
    rw [hb r, mul_eq_zero, sub_eq_zero] at hi
    exact hi
  · simp only [hab, map_zero, zero_mul, Finset.sum_const_zero, zero_add] at hr
    simp only [hb, sub_sub_cancel, sub_self, map_zero, zero_mul, Finset.sum_const_zero,
      map_zero, zero_mul, zero_add] at hr
    have hi := congrArg (fun p : YZ F => (p.coeff (j.val + 2)).coeff 0) hr
    simp only [coeff_zero, finsetSum_coeff, coeff_C_mul_X_pow,
      Nat.add_right_cancel_iff, Fin.val_inj, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, coeff_C_zero] at hi
    exact sub_eq_zero.mp hi.symm

theorem agg_formal_identity_iff (u v : Block m n → F) (values : Fin m → F) :
    agg_formal_t0 u v = agg_formal_rhs values n ↔
      (∀ r, v r = u r - 1) ∧ (∀ r, u r = 0 ∨ u r = 1) ∧
        (∀ j, block_value u j = values j) := by
  constructor
  · exact agg_poly_identity_implies_bits u v values
  · rintro ⟨hb, hbit, hv⟩
    apply sub_eq_zero.mp
    rw [agg_formal_residual]
    have hab : ∀ r, u r * v r = 0 := by
      intro r
      rw [hb r]
      rcases hbit r with hi | hi <;> simp [hi]
    simp only [hab, map_zero, zero_mul, Finset.sum_const_zero, zero_add]
    simp [hb, hv]
end Formal

section Protocol
variable {q : ℕ} [Fact q.Prime] {a b : ℕ}
variable {A : Type} [AddCommGroup A] [Module (ZMod q) A]
abbrev Bits (a b : ℕ) (F : Type) := Block (2 ^ b) (2 ^ a) → F

structure AggGenerators (A : Type) (a b : ℕ) where
  B : A
  Hblind : A
  U : A
  G : Bits a b A
  H : Bits a b A

def block_msm {m n : ℕ} (u : Block m n → ZMod q) (G : Block m n → A) : A :=
  ∑ r, u r • G r

theorem msm_flatten (u : Bits a b (ZMod q)) (G : Bits a b A) :
    multiscalar_mul (flatten u) (flatten G) = block_msm u G :=
  sum_flatten (fun r => u r • G r)

theorem dot_flatten (u v : Bits a b (ZMod q)) :
    dot_product (flatten u) (flatten v) = block_dot u v :=
  sum_flatten (fun r => u r * v r)

def agg_scaled_H (H : Bits a b A) (y : ZMod q) : Bits a b A :=
  fun r => (y⁻¹) ^ global_index r • H r

theorem agg_scaled_generators_valid (H : Bits a b A) (y : ZMod q) (hy : y ≠ 0)
    (r : Block (2 ^ b) (2 ^ a)) : y ^ global_index r • agg_scaled_H H y r = H r := by
  simp [agg_scaled_H, smul_smul, hy]

def agg_vector_commit (p : AggGenerators A a b) (u v : Bits a b (ZMod q)) (s : ZMod q) : A :=
  block_msm u p.G + block_msm v p.H + s • p.Hblind

def agg_value_commit (p : AggGenerators A a b) (v gamma : ZMod q) : A :=
  v • p.B + gamma • p.Hblind

def agg_target (p : AggGenerators A a b) (Ac Sc : A) (y z x mu tx : ZMod q) : A :=
  Ac + x • Sc + block_msm (fun _ => - z) p.G +
    block_msm (fun r => z * y ^ global_index r + block_weight z r) (agg_scaled_H p.H y) -
    mu • p.Hblind + tx • p.U

private theorem agg_scaled_coordinate (u v s t y z x w : ZMod q) (j : ℕ)
    (G H : A) (hy : y ≠ 0) :
    u • G + v • H + x • (s • G + t • H) + ( - z) • G +
      (z * y ^ j + w) • ((y⁻¹) ^ j • H) =
    (u - z + x * s) • G + (y ^ j * (v + z + x * t) + w) • ((y⁻¹) ^ j • H) := by
  have hj : y ^ j ≠ 0 := pow_ne_zero _ hy
  simp only [inv_pow]
  match_scalars <;> field_simp <;> ring

theorem agg_target_invariant (p : AggGenerators A a b) (u v s t : Bits a b (ZMod q))
    (alpha rho y z x : ZMod q) (hy : y ≠ 0) :
    agg_target p (agg_vector_commit p u v alpha) (agg_vector_commit p s t rho)
      y z x (alpha + x * rho) (block_dot (agg_l_poly u s z x) (agg_r_poly v t y z x)) =
    ipa_target p.U (flatten p.G) (flatten (agg_scaled_H p.H y))
      (flatten (agg_l_poly u s z x)) (flatten (agg_r_poly v t y z x)) := by
  have he : block_msm u p.G + block_msm v p.H +
      x • (block_msm s p.G + block_msm t p.H) + block_msm (fun _ => - z) p.G +
      block_msm (fun r => z * y ^ global_index r + block_weight z r) (agg_scaled_H p.H y) =
      block_msm (agg_l_poly u s z x) p.G +
        block_msm (agg_r_poly v t y z x) (agg_scaled_H p.H y) := by
    simp only [block_msm, smul_add, Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    simpa only [smul_add, agg_scaled_H, agg_l_poly, agg_r_poly] using
      agg_scaled_coordinate (u r) (v r) (s r) (t r) y z x (block_weight z r)
        (global_index r) (p.G r) (p.H r) hy
  unfold ipa_target
  rw [msm_flatten, msm_flatten, dot_flatten, ← he]
  unfold agg_target agg_vector_commit
  simp only [smul_add, add_smul, mul_smul]
  abel

/-- Proof body: public value commitments and verifier challenges are separate. -/
abbrev AggregatedRangeProof (q : ℕ) (A : Type) (a b : ℕ) :=
  RangeReductionTranscript q A (a + b)

structure AggregatedEnvelope (q : ℕ) (A : Type) (a b : ℕ) where
  values : Fin (2 ^ b) → A
  proof : AggregatedRangeProof q A a b

def verify_aggregation [DecidableEq A] (p : AggGenerators A a b) (V : Fin (2 ^ b) → A)
    (y z x : ZMod q) (xs : Fin (a + b) → (ZMod q)ˣ) (tr : AggregatedRangeProof q A a b) : Bool :=
  decide (y ≠ 0) &&
  decide (agg_value_commit p tr.tx tr.taux =
    (∑ j, z ^ (j.val + 2) • V j) + agg_delta (2 ^ b) (2 ^ a) y z • p.B +
    x • tr.T1 + x ^ 2 • tr.T2) &&
  verifier p.U (flatten p.G) (flatten (agg_scaled_H p.H y))
    (agg_target p tr.Ac tr.Sc y z x tr.mu tr.tx) xs tr.ipa

def agg_prover (p : AggGenerators A a b) (u s t : Bits a b (ZMod q))
    (gamma : Fin (2 ^ b) → ZMod q) (alpha rho tau1 tau2 y z x : ZMod q)
    (xs : Fin (a + b) → (ZMod q)ˣ) : AggregatedRangeProof q A a b :=
  let v := fun r => u r - 1
  let l := agg_l_poly u s z x
  let rr := agg_r_poly v t y z x
  ⟨agg_vector_commit p u v alpha, agg_vector_commit p s t rho,
    agg_value_commit p (agg_t1 u v s t y z) tau1, agg_value_commit p (agg_t2 s t y) tau2,
    block_dot l rr, (∑ j, z ^ (j.val + 2) * gamma j) + x * tau1 + x ^ 2 * tau2, alpha + x * rho,
    prover p.U (flatten p.G) (flatten (agg_scaled_H p.H y)) (flatten l) (flatten rr) xs⟩

theorem agg_polynomial_commitment_equation (p : AggGenerators A a b)
    (u s t : Bits a b (ZMod q)) (values gamma : Fin (2 ^ b) → ZMod q)
    (tau1 tau2 y z x : ZMod q) (hbit : ∀ r, u r * (u r - 1) = 0)
    (hv : ∀ j, block_value u j = values j) :
    agg_value_commit p (block_dot (agg_l_poly u s z x)
      (agg_r_poly (fun r => u r - 1) t y z x))
      ((∑ j, z ^ (j.val + 2) * gamma j) + x * tau1 + x ^ 2 * tau2) =
    (∑ j, z ^ (j.val + 2) • agg_value_commit p (values j) (gamma j)) +
      agg_delta (2 ^ b) (2 ^ a) y z • p.B +
      x • agg_value_commit p (agg_t1 u (fun r => u r - 1) s t y z) tau1 +
      x ^ 2 • agg_value_commit p (agg_t2 s t y) tau2 := by
  rw [agg_inner_product_expansion,
    agg_t0_spec u (fun r => u r - 1) values y z (fun _ => rfl) hbit hv]
  simp only [agg_value_commit, smul_add, smul_smul, Finset.sum_add_distrib,
    ← Finset.sum_smul]
  match_scalars <;> ring

theorem agg_completeness [DecidableEq A] (p : AggGenerators A a b)
    (u s t : Bits a b (ZMod q)) (values gamma : Fin (2 ^ b) → ZMod q)
    (alpha rho tau1 tau2 y z x : ZMod q) (xs : Fin (a + b) → (ZMod q)ˣ)
    (hy : y ≠ 0) (hbit : ∀ r, u r * (u r - 1) = 0) (hv : ∀ j, block_value u j = values j) :
    verify_aggregation p (fun j => agg_value_commit p (values j) (gamma j)) y z x xs
      (agg_prover p u s t gamma alpha rho tau1 tau2 y z x xs) = true := by
  simp only [verify_aggregation, agg_prover]
  rw [agg_target_invariant p u (fun r => u r - 1) s t alpha rho y z x hy, ipa_completeness]
  simp [hy, agg_polynomial_commitment_equation p u s t values gamma tau1 tau2 y z x hbit hv]

theorem agg_zero_y_rejected [DecidableEq A] (p : AggGenerators A a b)
    (V : Fin (2 ^ b) → A) (z x : ZMod q) xs tr :
    verify_aggregation p V 0 z x xs tr = false := by simp [verify_aggregation]

def agg_group_payload (tr : AggregatedRangeProof q A a b) : List A :=
  [tr.Ac, tr.Sc, tr.T1, tr.T2] ++ group_payload tr.ipa

def agg_scalar_payload (tr : AggregatedRangeProof q A a b) : List (ZMod q) :=
  [tr.tx, tr.taux, tr.mu] ++ scalar_payload tr.ipa

def envelope_group_payload (tr : AggregatedEnvelope q A a b) : List A :=
  List.ofFn tr.values ++ agg_group_payload tr.proof

omit [Fact q.Prime] [AddCommGroup A] [Module (ZMod q) A] in
theorem agg_ipa_transcript_size (tr : AggregatedRangeProof q A a b) :
    (group_payload tr.ipa).length = 2 * (a + b) ∧ (scalar_payload tr.ipa).length = 2 :=
  (ipa_proof_elements_count tr.ipa).2

omit [Fact q.Prime] [AddCommGroup A] [Module (ZMod q) A] in
theorem agg_full_proof_size (tr : AggregatedRangeProof q A a b) :
    (agg_group_payload tr).length = 4 + 2 * (a + b) ∧ (agg_scalar_payload tr).length = 5 := by
  simp [agg_group_payload, agg_scalar_payload, (agg_ipa_transcript_size tr).1,
    (agg_ipa_transcript_size tr).2]
  omega

omit [Fact q.Prime] [AddCommGroup A] [Module (ZMod q) A] in
theorem agg_envelope_size (tr : AggregatedEnvelope q A a b) :
    (envelope_group_payload tr).length = 2 ^ b + 4 + 2 * (a + b) := by
  simp [envelope_group_payload, (agg_full_proof_size tr.proof).1, Nat.add_assoc]
end Protocol

section Natural
variable {q : ℕ} [Fact q.Prime] {m n a b : ℕ}

theorem agg_formal_natural_range (u v : Block m n → ZMod q) (values : Fin m → ℕ)
    (hv : ∀ j, values j < q) (hq : 2 ^ n < q)
    (h : agg_formal_t0 u v = agg_formal_rhs (fun j => (values j : ZMod q)) n) :
    ∀ j, values j < 2 ^ n := by
  obtain ⟨_, hb, he⟩ := agg_poly_identity_implies_bits u v _ h
  intro j
  let bits : Fin n → ℕ := fun i => if u (j,i) = 0 then 0 else 1
  have hbits : ∀ i, bits i ≤ 1 := by intro i; simp only [bits]; split <;> omega
  have hc : ∀ i, (bits i : ZMod q) = u (j,i) := by
    intro i
    rcases hb (j,i) with hi | hi <;> simp [bits, hi]
  have hlt := CryptoPedersenRangeProofLinear.bitValue_lt bits hbits
  have hvcast : (CryptoPedersenRangeProofLinear.bitValue bits : ZMod q) = (values j : ZMod q) := by
    rw [CryptoPedersenRangeProofLinear.bitValue_cast]
    simpa only [CryptoPedersenRangeProofLinear.weight, hc, block_value] using he j
  have hvnat := congrArg ZMod.val hvcast
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans hlt hq), Nat.mod_eq_of_lt (hv j)] at hvnat
  exact hvnat ▸ hlt

variable {A : Type} [AddCommGroup A] [Module (ZMod q) A] [DecidableEq A]

theorem agg_natural_completeness (p : AggGenerators A a b)
    (values : Fin (2 ^ b) → ℕ) (hv : ∀ j, values j < 2 ^ (2 ^ a))
    (s t : Bits a b (ZMod q)) (gamma : Fin (2 ^ b) → ZMod q)
    (alpha rho tau1 tau2 y z x : ZMod q) (xs : Fin (a + b) → (ZMod q)ˣ) (hy : y ≠ 0) :
    ∃ bits : Bits a b ℕ, (∀ r, bits r ≤ 1) ∧
      (∀ j, CryptoPedersenRangeProofLinear.bitValue (fun i => bits (j,i)) = values j) ∧
      verify_aggregation p (fun j => agg_value_commit p (values j : ZMod q) (gamma j)) y z x xs
        (agg_prover p (fun r => (bits r : ZMod q)) s t
          gamma alpha rho tau1 tau2 y z x xs) = true := by
  have h := fun j => natural_bits (values j) (hv j)
  choose bits hb he using h
  refine ⟨fun r => bits r.1 r.2, fun r => hb r.1 r.2, he, ?_⟩
  apply agg_completeness p _ s t _ gamma alpha rho tau1 tau2 y z x xs hy
  · intro r
    have hi := hb r.1 r.2
    have hh : bits r.1 r.2 = 0 ∨ bits r.1 r.2 = 1 := by omega
    rcases hh with hh | hh <;> simp [hh]
  · intro j
    rw [← he j, CryptoPedersenRangeProofLinear.bitValue_cast]
    rfl
end Natural

section Single
variable {F : Type} [CommRing F] {n : ℕ}

theorem agg_l_m1_spec (u s : Fin n → F) (z x : F) (i : Fin n) :
    agg_l_poly (fun r : Block 1 n => u r.2) (fun r => s r.2) z x (0,i) = l_poly u s z x i := rfl

theorem agg_r_m1_spec (v t : Fin n → F) (y z x : F) (i : Fin n) :
    agg_r_poly (fun r : Block 1 n => v r.2) (fun r => t r.2) y z x (0,i) =
      r_poly v t y z x i := by simp [agg_r_poly, r_poly, block_weight, global_index_eq]

theorem agg_t0_m1_spec (u v : Fin n → F) (y z : F) :
    agg_t0 (fun r : Block 1 n => u r.2) (fun r => v r.2) y z = t0 u v y z := by
  simp [agg_t0, block_dot, Fintype.sum_prod_type, agg_l_poly, agg_r_poly,
    block_weight, global_index_eq, t0, dot, l_poly, r_poly]
end Single

section FormalCurve
variable {F : Type} [Field F] {m n : ℕ}
open Polynomial
noncomputable def agg_formal_curve (u v s t : Block m n → F) : Polynomial (YZ F) :=
  block_dot (agg_l_poly (fun r => C (liftYZ (u r))) (fun r => C (liftYZ (s r))) (C X) X)
    (agg_r_poly (fun r => C (liftYZ (v r))) (fun r => C (liftYZ (t r))) (C (C X)) (C X) X)
noncomputable def agg_formal_curve_rhs (u v s t : Block m n → F) (values : Fin m → F) :
    Polynomial (YZ F) :=
  C (agg_formal_rhs values n) +
    C (agg_t1 (fun r => liftYZ (u r)) (fun r => liftYZ (v r))
      (fun r => liftYZ (s r)) (fun r => liftYZ (t r)) (C X) X) * X +
    C (agg_t2 (fun r => liftYZ (s r)) (fun r => liftYZ (t r)) (C X)) * X ^ 2

theorem agg_formal_curve_expansion (u v s t : Block m n → F) :
    agg_formal_curve u v s t = C (agg_formal_t0 u v) +
      C (agg_t1 (fun r => liftYZ (u r)) (fun r => liftYZ (v r))
        (fun r => liftYZ (s r)) (fun r => liftYZ (t r)) (C X) X) * X +
      C (agg_t2 (fun r => liftYZ (s r)) (fun r => liftYZ (t r)) (C X)) * X ^ 2 := by
  rw [agg_formal_curve, agg_inner_product_expansion]
  simp only [agg_formal_t0, agg_t0, agg_t1, agg_t2, block_dot, agg_l_poly, agg_r_poly,
    block_weight, Pi.zero_apply, mul_zero, add_zero, map_sum, map_add, map_mul,
    map_sub, map_pow, map_ofNat]

theorem agg_three_variable_iff (u v s t : Block m n → F) (values : Fin m → F) :
    agg_formal_curve u v s t = agg_formal_curve_rhs u v s t values ↔
      (∀ r, v r = u r - 1) ∧ (∀ r, u r = 0 ∨ u r = 1) ∧
        (∀ j, block_value u j = values j) := by
  constructor
  · intro h
    rw [agg_formal_curve_expansion, agg_formal_curve_rhs] at h
    have hc := congrArg (fun p : Polynomial (YZ F) => p.coeff 0) h
    norm_num only [coeff_add, coeff_C_zero, coeff_C_mul_X_pow, coeff_C_mul_X,
      if_false, add_zero] at hc
    exact (agg_formal_identity_iff u v values).mp hc
  · intro h
    rw [agg_formal_curve_expansion, agg_formal_curve_rhs,
      (agg_formal_identity_iff u v values).mpr h]
end FormalCurve

section MessageOrder
variable {q : ℕ} [Fact q.Prime] {a b : ℕ}
variable {A : Type} [AddCommGroup A] [Module (ZMod q) A]
theorem agg_first_messages (p : AggGenerators A a b) (u s t : Bits a b (ZMod q))
    (gamma : Fin (2 ^ b) → ZMod q) (alpha rho tau1 tau2 y z x : ZMod q) xs :
    (agg_prover p u s t gamma alpha rho tau1 tau2 y z x xs).Ac =
      agg_vector_commit p u (fun r => u r - 1) alpha ∧
    (agg_prover p u s t gamma alpha rho tau1 tau2 y z x xs).Sc =
      agg_vector_commit p s t rho := ⟨rfl, rfl⟩

theorem agg_polynomial_messages (p : AggGenerators A a b) (u s t : Bits a b (ZMod q))
    (gamma : Fin (2 ^ b) → ZMod q) (alpha rho tau1 tau2 y z x : ZMod q) xs :
    (agg_prover p u s t gamma alpha rho tau1 tau2 y z x xs).T1 =
      agg_value_commit p (agg_t1 u (fun r => u r - 1) s t y z) tau1 ∧
    (agg_prover p u s t gamma alpha rho tau1 tau2 y z x xs).T2 =
      agg_value_commit p (agg_t2 s t y) tau2 := ⟨rfl, rfl⟩
end MessageOrder

section SingleProtocol
variable {q : ℕ} [Fact q.Prime] {a : ℕ}
variable {A : Type} [AddCommGroup A] [Module (ZMod q) A]

def single_generators (p : Generators q A a) : AggGenerators A a 0 :=
  ⟨p.B, p.Hblind, p.U, fun r => p.G r.2, fun r => p.H r.2⟩

omit [Fact q.Prime] [AddCommGroup A] [Module (ZMod q) A] in
 theorem flatten_single {F : Type} (u : Fin (2 ^ a) → F) :
    flatten (a := a) (b := 0) (fun r => u r.2) = u := by
  funext i
  apply congrArg u
  apply Fin.ext
  change i.val % 2 ^ a = i.val
  exact Nat.mod_eq_of_lt i.isLt

theorem agg_target_m1_spec (p : Generators q A a) (Ac Sc : A) (y z x mu tx : ZMod q) :
    agg_target (single_generators p) Ac Sc y z x mu tx = range_target p Ac Sc y z x mu tx := by
  simp [agg_target, range_target, block_msm, multiscalar_mul, single_generators,
    Fintype.sum_prod_type, agg_scaled_H, scaled_H, block_weight, global_index_eq]

theorem agg_verifier_m1_spec [DecidableEq A] (p : Generators q A a) (V : A)
    (y z x : ZMod q) (xs : Fin a → (ZMod q)ˣ) (tr : RangeReductionTranscript q A a) :
    verify_aggregation (single_generators p) (fun _ => V) y z x xs tr =
      verify_range_reduction p V y z x xs tr := by
  have hs : agg_scaled_H (single_generators p).H y =
      (fun r : Block (2 ^ 0) (2 ^ a) => scaled_H p.H y r.2) := by
    funext r
    rcases r with ⟨j,i⟩
    have hj : j = 0 := Fin.ext (by have h := j.isLt; norm_num at h; omega)
    subst j
    simp [agg_scaled_H, single_generators, scaled_H, global_index_eq]
  unfold verify_aggregation verify_range_reduction
  rw [agg_target_m1_spec, hs]
  rw [show flatten (single_generators p).G = p.G from flatten_single p.G, flatten_single]
  simp only [agg_value_commit, value_commit, agg_delta_m1_spec, single_generators,
    Nat.pow_zero, Fintype.sum_unique, Fin.default_eq_zero, Fin.val_zero, zero_add]
  rfl
end SingleProtocol

section Suite
variable (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A] [DecidableEq A]
structure VerifiedProperties : Prop where
  scalar_expansion : ∀ m n (u v s t : Block m n → ZMod q) y z x,
    block_dot (agg_l_poly u s z x) (agg_r_poly v t y z x) =
      agg_t0 u v y z + agg_t1 u v s t y z * x + agg_t2 s t y * x ^ 2
  constant_term : ∀ m n (u v : Block m n → ZMod q) (values : Fin m → ZMod q) y z,
    (∀ r, v r = u r - 1) → (∀ r, u r * v r = 0) → (∀ j, block_value u j = values j) →
    agg_t0 u v y z = (∑ j, z ^ (j.val + 2) * values j) + agg_delta m n y z
  formal_equivalence : ∀ m n (u v s t : Block m n → ZMod q) values,
    agg_formal_curve u v s t = agg_formal_curve_rhs u v s t values ↔
      (∀ r, v r = u r - 1) ∧ (∀ r, u r = 0 ∨ u r = 1) ∧ (∀ j, block_value u j = values j)
  natural_recovery : ∀ m n (u v : Block m n → ZMod q) (values : Fin m → ℕ),
    (∀ j, values j<q) → 2 ^ n<q →
    agg_formal_t0 u v = agg_formal_rhs (fun j => (values j : ZMod q)) n →
    ∀ j, values j<2 ^ n
  target : ∀ a b (p : AggGenerators A a b) (u v s t : Bits a b (ZMod q)) alpha rho y z x,
    y ≠ 0 → agg_target p (agg_vector_commit p u v alpha) (agg_vector_commit p s t rho)
      y z x (alpha + x * rho) (block_dot (agg_l_poly u s z x) (agg_r_poly v t y z x)) =
      ipa_target p.U (flatten p.G) (flatten (agg_scaled_H p.H y))
        (flatten (agg_l_poly u s z x)) (flatten (agg_r_poly v t y z x))
  completeness : ∀ a b (p : AggGenerators A a b) (u s t : Bits a b (ZMod q))
    (values gamma : Fin (2 ^ b) → ZMod q) alpha rho tau1 tau2 y z x xs,
    y ≠ 0 → (∀ r, u r * (u r - 1) = 0) →
    (∀ j, block_value u j = values j) →
    verify_aggregation p (fun j => agg_value_commit p (values j) (gamma j)) y z x xs
      (agg_prover p u s t gamma alpha rho tau1 tau2 y z x xs) = true
  single_verifier : ∀ a (p : Generators q A a) V y z x xs tr,
    verify_aggregation (single_generators p) (fun _ => V) y z x xs tr =
      verify_range_reduction p V y z x xs tr
  zero_rejection : ∀ a b (p : AggGenerators A a b) V z x xs tr,
    verify_aggregation (q := q) p V 0 z x xs tr = false
  ipa_size : ∀ a b (tr : AggregatedRangeProof q A a b),
    (group_payload tr.ipa).length = 2 * (a + b) ∧ (scalar_payload tr.ipa).length = 2
  full_size : ∀ a b (tr : AggregatedRangeProof q A a b),
    (agg_group_payload tr).length = 4 + 2 * (a + b) ∧ (agg_scalar_payload tr).length = 5
  envelope_size : ∀ a b (tr : AggregatedEnvelope q A a b),
    (envelope_group_payload tr).length = 2 ^ b + 4 + 2 * (a + b)

theorem verified_properties : VerifiedProperties q A where
  scalar_expansion := fun _ _ => agg_inner_product_expansion
  constant_term := fun _ _ => agg_t0_spec
  formal_equivalence := fun _ _ => agg_three_variable_iff
  natural_recovery := fun _ _ => agg_formal_natural_range
  target := fun _ _ => agg_target_invariant
  completeness := fun _ _ => agg_completeness
  single_verifier := fun _ => agg_verifier_m1_spec
  zero_rejection := fun _ _ => agg_zero_y_rejected
  ipa_size := fun _ _ => agg_ipa_transcript_size
  full_size := fun _ _ => agg_full_proof_size
  envelope_size := fun _ _ => agg_envelope_size
end Suite

structure CryptoBulletproofsAggregationSuite : Prop where
  all_models : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A], VerifiedProperties q A
  cyclic_model : ∀ (q : ℕ) [Fact q.Prime],
    Nonempty (CryptoPedersenHomomorphicSum.Setup q (ZMod q))

theorem verification_suite : CryptoBulletproofsAggregationSuite where
  all_models := fun _ _ _ _ _ _ => verified_properties _ _
  cyclic_model := CryptoPedersenHomomorphicSum.setup_satisfiable

end CryptoBulletproofsAggregation
