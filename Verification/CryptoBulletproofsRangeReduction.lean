/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoCommitmentVectorPedersenGroup
import Verification.CryptoPedersenRangeProofLinear
import Verification.CryptoBulletproofsInnerProduct
import Mathlib.Algebra.Polynomial.Coeff

/-! Algebraic range reduction and honest composition with IPA. Formal polynomial
identities, unlike a single challenge evaluation, certify the bit constraints.
Knowledge extraction, binding security, HVZK and Fiat-Shamir are not asserted. -/
namespace CryptoBulletproofsRangeReduction
open scoped BigOperators
open CryptoBulletproofsInnerProduct

section Ring
variable {F : Type} [CommRing F] {n : ℕ}
def y_powers (y : F) (n : ℕ) : Fin n → F := fun i => y ^ i.val
def two_powers (n : ℕ) : Fin n → F := fun i => 2 ^ i.val
def dot (a b : Fin n → F) : F := ∑ i, a i * b i
def delta_fn (y z : F) (n : ℕ) : F :=
  (z - z ^ 2) * (∑ i : Fin n, y ^ i.val) - z ^ 3 * (∑ i : Fin n, (2 : F) ^ i.val)
def l_poly (a s : Fin n → F) (z x : F) : Fin n → F := fun i => a i - z + x * s i
def r_poly (b s : Fin n → F) (y z x : F) : Fin n → F :=
  fun i => y ^ i.val * (b i + z + x * s i) + z ^ 2 * 2 ^ i.val

def t0 (a b : Fin n → F) (y z : F) : F := dot (l_poly a 0 z 0) (r_poly b 0 y z 0)
def t1 (a b s t : Fin n → F) (y z : F) : F :=
  ∑ i, ((a i - z) * (y ^ i.val * t i) + s i * (y ^ i.val * (b i + z) + z ^ 2 * 2 ^ i.val))
def t2 (s t : Fin n → F) (y : F) : F := ∑ i, s i * (y ^ i.val * t i)

theorem poly_inner_product_eq (a b s t : Fin n → F) (y z x : F) :
    dot (l_poly a s z x) (r_poly b t y z x) =
      t0 a b y z + t1 a b s t y z * x + t2 s t y * x ^ 2 := by
  simp only [dot, l_poly, r_poly, t0, t1, t2, Pi.zero_apply, mul_zero, add_zero,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- This residual keeps the independent Y- and Z-coefficients visible. -/
theorem t0_residual (a b : Fin n → F) (v y z : F) :
    t0 a b y z - (z ^ 2 * v + delta_fn y z n) =
      (∑ i, (a i * b i) * y ^ i.val) +
      z * (∑ i, (a i - b i - 1) * y ^ i.val) +
      z ^ 2 * ((∑ i, (2 : F) ^ i.val * a i) - v) := by
  simp only [t0, dot, l_poly, r_poly, delta_fn, Pi.zero_apply, mul_zero, add_zero,
    mul_sub, Finset.mul_sum]
  have h : (∑ i : Fin n, (a i - z) * (y ^ i.val * (b i + z) + z ^ 2 * 2 ^ i.val)) =
      ∑ i : Fin n, ((a i * b i) * y ^ i.val + z * ((a i-b i-1) * y ^ i.val) +
        z ^ 2 * (2 ^ i.val * a i) + (z-z ^ 2) * y ^ i.val - z ^ 3 * 2 ^ i.val) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem t0_spec (a b : Fin n → F) (v y z : F)
    (hb : ∀ i, b i = a i - 1) (hbit : ∀ i, a i * b i = 0)
    (hv : ∑ i, (2 : F) ^ i.val * a i = v) :
    t0 a b y z = z ^ 2 * v + delta_fn y z n := by
  apply sub_eq_zero.mp
  rw [t0_residual]
  simp only [hbit, zero_mul, Finset.sum_const_zero, hv, sub_self, mul_zero, zero_add]
  simp [hb]
end Ring

section Formal
variable {F : Type} [Field F] {n : ℕ}
open Polynomial
/-- Y is the inner indeterminate, Z the outer indeterminate. -/
abbrev YZ (F : Type) [Semiring F] := Polynomial (Polynomial F)
noncomputable def liftYZ (a : F) : YZ F := C (C a)
noncomputable def formal_t0 (a b : Fin n → F) : YZ F :=
  t0 (fun i => liftYZ (a i)) (fun i => liftYZ (b i)) (C X) X
noncomputable def formal_rhs (v : F) (n : ℕ) : YZ F :=
  X ^ 2 * liftYZ v + delta_fn (C (X : Polynomial F)) X n

theorem formal_residual (a b : Fin n → F) (v : F) :
    formal_t0 a b - formal_rhs v n =
      C (∑ i, C (a i * b i) * X ^ i.val) +
      C (∑ i, C (a i - b i - 1) * X ^ i.val) * X +
      C (C ((∑ i, (2 : F) ^ i.val * a i) - v)) * X ^ 2 := by
  rw [formal_t0, formal_rhs, t0_residual]
  simp only [liftYZ, map_sum, map_sub, map_mul, map_pow, map_ofNat, map_one]
  ring

/-- Coefficient extraction, not evaluation on finitely many field elements. -/
theorem formal_coefficients_imply_range (a b : Fin n → F) (v : F)
    (h : formal_t0 a b = formal_rhs v n) :
    (∀ i, b i = a i - 1) ∧ (∀ i, a i = 0 ∨ a i = 1) ∧
      (∑ i, (2 : F) ^ i.val * a i) = v := by
  have hr := formal_residual a b v
  rw [h, sub_self] at hr
  have h0 := congrArg (fun p : YZ F => p.coeff 0) hr
  have h1 := congrArg (fun p : YZ F => p.coeff 1) hr
  have h2 := congrArg (fun p : YZ F => (p.coeff 2).coeff 0) hr
  norm_num only [coeff_zero, coeff_add, coeff_C, coeff_C_mul_X_pow, coeff_C_mul_X,
    if_false, if_true, zero_add, add_zero] at h0 h1 h2
  have hb : ∀ i, b i = a i - 1 := by
    intro i
    have hi := congrArg (fun p : Polynomial F => p.coeff i.val) h1
    simp only [coeff_zero, finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at hi
    linear_combination hi
  have hab : ∀ i, a i * b i = 0 := by
    intro i
    have hi := congrArg (fun p : Polynomial F => p.coeff i.val) h0
    simpa only [coeff_zero, finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] using hi.symm
  refine ⟨hb, fun i => ?_, ?_⟩
  · have hi := hab i
    rw [hb i, mul_eq_zero, sub_eq_zero] at hi
    exact hi
  · exact sub_eq_zero.mp h2.symm
theorem formal_identity_iff (a b : Fin n → F) (v : F) :
    formal_t0 a b = formal_rhs v n ↔
      (∀ i, b i = a i - 1) ∧ (∀ i, a i = 0 ∨ a i = 1) ∧
        (∑ i, (2 : F) ^ i.val * a i) = v := by
  constructor
  · exact formal_coefficients_imply_range a b v
  · rintro ⟨hb, hbit, hv⟩
    apply sub_eq_zero.mp
    rw [formal_residual]
    have hab : ∀ i, a i * b i = 0 := by
      intro i
      rw [hb i]
      rcases hbit i with hi | hi <;> simp [hi]
    simp only [hab, map_zero, zero_mul, Finset.sum_const_zero, zero_add]
    simp [hb, hv]

/-- Three independent formal indeterminates: outer X, then Z, then Y. -/
noncomputable def formal_curve (a b s t : Fin n → F) : Polynomial (YZ F) :=
  dot (l_poly (fun i => C (liftYZ (a i))) (fun i => C (liftYZ (s i))) (C X) X)
    (r_poly (fun i => C (liftYZ (b i))) (fun i => C (liftYZ (t i))) (C (C X)) (C X) X)

noncomputable def formal_curve_rhs (a b s t : Fin n → F) (v : F) : Polynomial (YZ F) :=
  C (formal_rhs v n) +
    C (t1 (fun i => liftYZ (a i)) (fun i => liftYZ (b i))
      (fun i => liftYZ (s i)) (fun i => liftYZ (t i)) (C X) X) * X +
    C (t2 (fun i => liftYZ (s i)) (fun i => liftYZ (t i)) (C X)) * X ^ 2

theorem formal_curve_expansion (a b s t : Fin n → F) :
    formal_curve a b s t = C (formal_t0 a b) +
      C (t1 (fun i => liftYZ (a i)) (fun i => liftYZ (b i))
        (fun i => liftYZ (s i)) (fun i => liftYZ (t i)) (C X) X) * X +
      C (t2 (fun i => liftYZ (s i)) (fun i => liftYZ (t i)) (C X)) * X ^ 2 := by
  rw [formal_curve, poly_inner_product_eq]
  simp only [formal_t0, t0, t1, t2, dot, l_poly, r_poly, Pi.zero_apply,
    mul_zero, add_zero, map_sum, map_add, map_mul, map_sub, map_pow, map_ofNat]

theorem formal_three_variable_iff (a b s t : Fin n → F) (v : F) :
    formal_curve a b s t = formal_curve_rhs a b s t v ↔
      (∀ i, b i = a i - 1) ∧ (∀ i, a i = 0 ∨ a i = 1) ∧
        (∑ i, (2 : F) ^ i.val * a i) = v := by
  constructor
  · intro h
    rw [formal_curve_expansion, formal_curve_rhs] at h
    have hc := congrArg (fun p : Polynomial (YZ F) => p.coeff 0) h
    norm_num only [coeff_add, coeff_C_zero, coeff_C_mul_X_pow, coeff_C_mul_X,
      if_false, add_zero] at hc
    exact (formal_identity_iff a b v).mp hc
  · intro h
    rw [formal_curve_expansion, formal_curve_rhs, (formal_identity_iff a b v).mpr h]
end Formal

section Protocol
variable {q : ℕ} [Fact q.Prime] {n k : ℕ}
variable {A : Type} [AddCommGroup A] [Module (ZMod q) A]

theorem boolean_iff_product_zero (a : ZMod q) :
    (a = 0 ∨ a = 1) ↔ a * (a - 1) = 0 := by rw [mul_eq_zero, sub_eq_zero]

theorem natural_bits (v : ℕ) (hv : v < 2 ^ n) :
    ∃ b : Fin n → ℕ, (∀ i, b i ≤ 1) ∧
      CryptoPedersenRangeProofLinear.bitValue b = v :=
  (CryptoPedersenRangeProofLinear.nat_bit_decomp_iff n v).mp hv

/-- The canonical representative hypothesis prevents claiming a range for v+q. -/
theorem formal_identity_natural_range (a b : Fin n → ZMod q) (v : ℕ)
    (hv : v < q) (hq : 2 ^ n < q)
    (h : formal_t0 a b = formal_rhs (v : ZMod q) n) : v < 2 ^ n := by
  obtain ⟨_, hb, he⟩ := formal_coefficients_imply_range a b (v : ZMod q) h
  let bits : Fin n → ℕ := fun i => if a i = 0 then 0 else 1
  have hbits : ∀ i, bits i ≤ 1 := by intro i; simp only [bits]; split <;> omega
  have hc : ∀ i, (bits i : ZMod q) = a i := by
    intro i
    rcases hb i with hi | hi <;> simp [bits, hi]
  have hlt := CryptoPedersenRangeProofLinear.bitValue_lt bits hbits
  have hvcast : (CryptoPedersenRangeProofLinear.bitValue bits : ZMod q) = (v : ZMod q) := by
    rw [CryptoPedersenRangeProofLinear.bitValue_cast]
    simpa only [CryptoPedersenRangeProofLinear.weight, hc] using he
  have hvnat := congrArg ZMod.val hvcast
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans hlt hq), Nat.mod_eq_of_lt hv] at hvnat
  exact hvnat ▸ hlt

structure Generators (q : ℕ) (A : Type) (k : ℕ) where
  B : A
  Hblind : A
  U : A
  G : Vec k A
  H : Vec k A

def scaled_H (H : Fin n → A) (y : ZMod q) : Fin n → A := fun i => (y⁻¹) ^ i.val • H i

theorem scaled_generators_valid (H : Fin n → A) (y : ZMod q) (hy : y ≠ 0) (i : Fin n) :
    y ^ i.val • scaled_H H y i = H i := by
  simp [scaled_H, smul_smul, hy]

def vector_commit (p : Generators q A k) (a b : Vec k (ZMod q)) (r : ZMod q) : A :=
  multiscalar_mul a p.G + multiscalar_mul b p.H + r • p.Hblind

def value_commit (p : Generators q A k) (v r : ZMod q) : A := v • p.B + r • p.Hblind

def range_target (p : Generators q A k) (Ac Sc : A) (y z x mu tx : ZMod q) : A :=
  Ac + x • Sc + multiscalar_mul (fun _ => -z) p.G +
    multiscalar_mul (fun i => z * y ^ i.val + z ^ 2 * 2 ^ i.val) (scaled_H p.H y) -
    mu • p.Hblind + tx • p.U

private theorem scaled_coordinate (a b s t y z x : ZMod q) (j : ℕ)
    (G H : A) (hy : y ≠ 0) :
    a • G + b • H + x • (s • G + t • H) + (-z) • G +
      (z * y ^ j + z ^ 2 * 2 ^ j) • ((y⁻¹) ^ j • H) =
    (a-z+x * s) • G + (y ^ j * (b+z+x * t)+z ^ 2 * 2 ^ j) • ((y⁻¹) ^ j • H) := by
  have hj : y ^ j ≠ 0 := pow_ne_zero _ hy
  simp only [inv_pow]
  match_scalars <;> field_simp <;> ring

theorem range_ipa_target_invariant (p : Generators q A k)
    (a b s t : Vec k (ZMod q)) (alpha rho y z x : ZMod q) (hy : y ≠ 0) :
    range_target p (vector_commit p a b alpha) (vector_commit p s t rho)
      y z x (alpha + x * rho) (dot (l_poly a s z x) (r_poly b t y z x)) =
    ipa_target p.U p.G (scaled_H p.H y) (l_poly a s z x) (r_poly b t y z x) := by
  have he : multiscalar_mul a p.G + multiscalar_mul b p.H +
      x • (multiscalar_mul s p.G + multiscalar_mul t p.H) +
      multiscalar_mul (fun _ => -z) p.G +
      multiscalar_mul (fun i => z * y ^ i.val + z ^ 2 * 2 ^ i.val) (scaled_H p.H y) =
      multiscalar_mul (l_poly a s z x) p.G +
      multiscalar_mul (r_poly b t y z x) (scaled_H p.H y) := by
    simp only [multiscalar_mul, smul_add, Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [smul_add, scaled_H, l_poly, r_poly] using
      scaled_coordinate (a i) (b i) (s i) (t i) y z x i.val (p.G i) (p.H i) hy
  unfold range_target vector_commit ipa_target
  rw [show dot (l_poly a s z x) (r_poly b t y z x) =
    dot_product (l_poly a s z x) (r_poly b t y z x) from rfl]
  rw [← he]
  simp only [smul_add, add_smul, mul_smul]
  abel

structure RangeReductionTranscript (q : ℕ) (A : Type) (k : ℕ) where
  Ac : A
  Sc : A
  T1 : A
  T2 : A
  tx : ZMod q
  taux : ZMod q
  mu : ZMod q
  ipa : IPATranscript q A k

/-- Verifier challenges are external inputs, never chosen inside the transcript. -/
def verify_range_reduction [DecidableEq A] (p : Generators q A k) (V : A)
    (y z x : ZMod q) (xs : Fin k → (ZMod q)ˣ) (tr : RangeReductionTranscript q A k) : Bool :=
  decide (y ≠ 0) &&
  decide (value_commit p tr.tx tr.taux = z ^ 2 • V + delta_fn y z (2 ^ k) • p.B +
    x • tr.T1 + x ^ 2 • tr.T2) &&
  verifier p.U p.G (scaled_H p.H y) (range_target p tr.Ac tr.Sc y z x tr.mu tr.tx) xs tr.ipa

def range_prover (p : Generators q A k) (a s t : Vec k (ZMod q))
    (gamma alpha rho tau1 tau2 y z x : ZMod q) (xs : Fin k → (ZMod q)ˣ) :
    RangeReductionTranscript q A k :=
  let b := fun i => a i - 1
  let l := l_poly a s z x
  let r := r_poly b t y z x
  ⟨vector_commit p a b alpha, vector_commit p s t rho,
    value_commit p (t1 a b s t y z) tau1, value_commit p (t2 s t y) tau2,
    dot l r, z ^ 2 * gamma + x * tau1 + x ^ 2 * tau2, alpha+x * rho,
    prover p.U p.G (scaled_H p.H y) l r xs⟩

theorem polynomial_commitment_equation (p : Generators q A k) (a s t : Vec k (ZMod q))
    (v gamma tau1 tau2 y z x : ZMod q) (hbit : ∀ i, a i * (a i - 1) = 0)
    (hv : ∑ i, (2 : ZMod q) ^ i.val * a i = v) :
    value_commit p (dot (l_poly a s z x) (r_poly (fun i => a i - 1) t y z x))
      (z ^ 2 * gamma+x * tau1+x ^ 2 * tau2) =
      z ^ 2 • value_commit p v gamma + delta_fn y z (2 ^ k) • p.B +
      x • value_commit p (t1 a (fun i => a i - 1) s t y z) tau1 +
      x ^ 2 • value_commit p (t2 s t y) tau2 := by
  rw [poly_inner_product_eq, t0_spec a (fun i => a i - 1) v y z (fun _ => rfl) hbit hv]
  unfold value_commit
  match_scalars <;> ring

theorem range_proof_composition_completeness [DecidableEq A] (p : Generators q A k)
    (a s t : Vec k (ZMod q)) (v gamma alpha rho tau1 tau2 y z x : ZMod q)
    (xs : Fin k → (ZMod q)ˣ) (hy : y ≠ 0) (hbit : ∀ i, a i * (a i - 1) = 0)
    (hv : ∑ i, (2 : ZMod q) ^ i.val * a i = v) :
    verify_range_reduction p (value_commit p v gamma) y z x xs
      (range_prover p a s t gamma alpha rho tau1 tau2 y z x xs) = true := by
  simp only [verify_range_reduction, range_prover]
  rw [range_ipa_target_invariant p a (fun i => a i - 1) s t alpha rho y z x hy,
    ipa_completeness]
  simp [hy, polynomial_commitment_equation p a s t v gamma tau1 tau2 y z x hbit hv]

theorem zero_y_rejected [DecidableEq A] (p : Generators q A k) (V : A)
    (z x : ZMod q) (xs : Fin k → (ZMod q)ˣ) (tr : RangeReductionTranscript q A k) :
    verify_range_reduction p V 0 z x xs tr = false := by simp [verify_range_reduction]
theorem natural_range_completeness [DecidableEq A] (p : Generators q A k)
    (v : ℕ) (hv : v < 2 ^ (2 ^ k)) (s t : Vec k (ZMod q))
    (gamma alpha rho tau1 tau2 y z x : ZMod q) (xs : Fin k → (ZMod q)ˣ) (hy : y ≠ 0) :
    ∃ bits : Vec k ℕ, (∀ i, bits i ≤ 1) ∧
      CryptoPedersenRangeProofLinear.bitValue bits = v ∧
      verify_range_reduction p (value_commit p (v : ZMod q) gamma) y z x xs
        (range_prover p (fun i => (bits i : ZMod q)) s t
          gamma alpha rho tau1 tau2 y z x xs) = true := by
  obtain ⟨bits, hb, he⟩ := natural_bits v hv
  refine ⟨bits, hb, he, range_proof_composition_completeness p _ s t _
    gamma alpha rho tau1 tau2 y z x xs hy ?_ ?_⟩
  · intro i
    have hi := hb i
    have hh : bits i = 0 ∨ bits i = 1 := by omega
    rcases hh with hh | hh <;> simp [hh]
  · rw [← he, CryptoPedersenRangeProofLinear.bitValue_cast]
    rfl
/-- First commitments cannot depend on later verifier challenges. -/
theorem first_messages_independent (p : Generators q A k) (a s t : Vec k (ZMod q))
    (gamma alpha rho tau1 tau2 y z x : ZMod q) (xs : Fin k → (ZMod q)ˣ) :
    (range_prover p a s t gamma alpha rho tau1 tau2 y z x xs).Ac =
      vector_commit p a (fun i => a i - 1) alpha ∧
    (range_prover p a s t gamma alpha rho tau1 tau2 y z x xs).Sc = vector_commit p s t rho :=
  ⟨rfl, rfl⟩

theorem polynomial_messages_independent (p : Generators q A k) (a s t : Vec k (ZMod q))
    (gamma alpha rho tau1 tau2 y z x : ZMod q) (xs : Fin k → (ZMod q)ˣ) :
    (range_prover p a s t gamma alpha rho tau1 tau2 y z x xs).T1 =
      value_commit p (t1 a (fun i => a i - 1) s t y z) tau1 ∧
    (range_prover p a s t gamma alpha rho tau1 tau2 y z x xs).T2 =
      value_commit p (t2 s t y) tau2 := ⟨rfl, rfl⟩

structure VerifiedProperties (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A] : Prop where
  scalar_expansion : ∀ n (a b s t : Fin n → ZMod q) y z x,
    dot (l_poly a s z x) (r_poly b t y z x) =
      t0 a b y z + t1 a b s t y z * x + t2 s t y * x ^ 2
  formal_equivalence : ∀ n (a b s t : Fin n → ZMod q) v,
    formal_curve a b s t = formal_curve_rhs a b s t v ↔
      (∀ i, b i = a i - 1) ∧ (∀ i, a i = 0 ∨ a i = 1) ∧
        (∑ i, (2 : ZMod q) ^ i.val * a i) = v
  natural_range : ∀ n (a b : Fin n → ZMod q) (v : ℕ), v < q → 2 ^ n < q →
    formal_t0 a b = formal_rhs (v : ZMod q) n → v < 2 ^ n
  completeness : ∀ k (p : Generators q A k) (a s t : Vec k (ZMod q))
    (v gamma alpha rho tau1 tau2 y z x : ZMod q) (xs : Fin k → (ZMod q)ˣ),
    y ≠ 0 → (∀ i, a i * (a i - 1) = 0) → (∑ i, (2 : ZMod q) ^ i.val * a i) = v →
    verify_range_reduction p (value_commit p v gamma) y z x xs
      (range_prover p a s t gamma alpha rho tau1 tau2 y z x xs) = true
  zero_rejection : ∀ k (p : Generators q A k) (V : A) z x xs tr,
    verify_range_reduction p V 0 z x xs tr = false

theorem verified_properties [DecidableEq A] : VerifiedProperties q A where
  scalar_expansion := fun _ => poly_inner_product_eq
  formal_equivalence := fun _ => formal_three_variable_iff
  natural_range := fun _ => formal_identity_natural_range
  completeness := fun _ => range_proof_composition_completeness
  zero_rejection := fun _ => zero_y_rejected
end Protocol

structure CryptoBulletproofsRangeReductionSuite : Prop where
  all_models : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A], VerifiedProperties q A
  cyclic_model : ∀ (q : ℕ) [Fact q.Prime],
    Nonempty (CryptoPedersenHomomorphicSum.Setup q (ZMod q))

theorem verification_suite : CryptoBulletproofsRangeReductionSuite where
  all_models := fun _ _ _ _ _ _ => verified_properties
  cyclic_model := CryptoPedersenHomomorphicSum.setup_satisfiable

end CryptoBulletproofsRangeReduction
