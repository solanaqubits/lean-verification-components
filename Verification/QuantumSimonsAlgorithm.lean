/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumDeutschJozsaGeneral
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases

/-! Exact Simon sampling with a nonzero period. Recovery is conditional on rank;
independent sampling, running time and physical measurement are not modeled. -/
noncomputable section
open scoped BigOperators ComplexConjugate
namespace QuantumSimonsAlgorithm
open QuantumDeutschJozsaGeneral (Bits character signOfBool rho zeroBits)

abbrev Register (n : ℕ) := Bits n
abbrev JointState (n m : ℕ) := Register n → Register m → ℂ

def xorVec {n : ℕ} (x y : Register n) : Register n := fun i => x i ^^ y i

@[simp] theorem xor_self_right {n : ℕ} (x s : Register n) :
    xorVec (xorVec x s) s = x := by funext i; simp [xorVec]

@[simp] theorem xor_zero_iff {n : ℕ} (x y : Register n) :
    xorVec x y = zeroBits n ↔ x = y := by
  constructor
  · intro h; funext i; have := congrFun h i; simpa [xorVec, zeroBits] using this
  · rintro rfl; funext i; simp [xorVec, zeroBits]

theorem xor_ne_self {n : ℕ} (x s : Register n) (hs : s ≠ zeroBits n) :
    xorVec x s ≠ x := by
  intro h; apply hs; funext i
  have hi := congrFun h i
  cases hx : x i <;> cases hsi : s i <;> simp_all [xorVec, zeroBits]

def xorEquiv {n : ℕ} (s : Register n) : Register n ≃ Register n where
  toFun x := xorVec x s
  invFun x := xorVec x s
  left_inv x := xor_self_right x s
  right_inv x := xor_self_right x s

theorem character_xor {n : ℕ} (x s y : Register n) :
    character (xorVec x s) y = character x y * character s y := by
  unfold character
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [xorVec]
  cases x i <;> cases s i <;> cases y i <;> norm_num [signOfBool]

def SimonPromise {n m : ℕ} (f : Register n → Register m) (s : Register n) : Prop :=
  s ≠ zeroBits n ∧ ∀ x x', f x = f x' ↔ x = x' ∨ x = xorVec x' s

theorem promise_periodic {n m : ℕ} {f : Register n → Register m} {s : Register n}
    (h : SimonPromise f s) (x : Register n) : f (xorVec x s) = f x :=
  (h.2 _ _).2 (Or.inr rfl)

def hermitian {n m : ℕ} (u v : JointState n m) : ℂ :=
  ∑ x, ∑ z, conj (u x z) * v x z

def normSquared {n m : ℕ} (v : JointState n m) : ℝ :=
  ∑ x, ∑ z, Complex.normSq (v x z)

def xorOracle {n m : ℕ} (f : Register n → Register m) (v : JointState n m) : JointState n m :=
  fun x z => v x (xorVec z (f x))

theorem oracle_linear {n m : ℕ} (f : Register n → Register m) (a b : ℂ)
    (u v : JointState n m) :
    xorOracle f (fun x z => a * u x z + b * v x z) =
      fun x z => a * xorOracle f u x z + b * xorOracle f v x z := rfl

@[simp] theorem oracle_involution {n m : ℕ} (f : Register n → Register m)
    (v : JointState n m) : xorOracle f (xorOracle f v) = v := by
  funext x z; simp [xorOracle]

theorem oracle_inner {n m : ℕ} (f : Register n → Register m) (u v : JointState n m) :
    hermitian (xorOracle f u) (xorOracle f v) = hermitian u v := by
  unfold hermitian xorOracle
  apply Finset.sum_congr rfl
  intro x _
  exact Equiv.sum_comp (xorEquiv (f x)) (fun z => conj (u x z) * v x z)

theorem oracle_norm {n m : ℕ} (f : Register n → Register m) (v : JointState n m) :
    normSquared (xorOracle f v) = normSquared v := by
  unfold normSquared xorOracle
  apply Finset.sum_congr rfl
  intro x _
  exact Equiv.sum_comp (xorEquiv (f x)) (fun z => Complex.normSq (v x z))

theorem oracle_self_adjoint {n m : ℕ} (f : Register n → Register m) (u v : JointState n m) :
    hermitian (xorOracle f u) v = hermitian u (xorOracle f v) := by
  simpa using oracle_inner f u (xorOracle f v)

theorem simon_oracle_unitarity {n m : ℕ} (f : Register n → Register m) :
    (∀ v, xorOracle f (xorOracle f v) = v) ∧
    (∀ u v, hermitian (xorOracle f u) (xorOracle f v) = hermitian u v) :=
  ⟨oracle_involution f, oracle_inner f⟩

def inputHadamard {n m : ℕ} (v : JointState n m) : JointState n m :=
  fun y z => (rho n : ℂ) * ∑ x, (character x y : ℂ) * v x z

theorem hadamard_re {n m : ℕ} (v : JointState n m) (y : Register n) (z : Register m) :
    (inputHadamard v y z).re = QuantumDeutschJozsaGeneral.hadamard (fun x => (v x z).re) y := by
  simp [inputHadamard, QuantumDeutschJozsaGeneral.hadamard, Complex.mul_re]

theorem hadamard_im {n m : ℕ} (v : JointState n m) (y : Register n) (z : Register m) :
    (inputHadamard v y z).im = QuantumDeutschJozsaGeneral.hadamard (fun x => (v x z).im) y := by
  simp [inputHadamard, QuantumDeutschJozsaGeneral.hadamard, Complex.mul_im]

@[simp] theorem hadamard_involution {n m : ℕ} (v : JointState n m) :
    inputHadamard (inputHadamard v) = v := by
  funext y z
  apply Complex.ext <;> simp only [hadamard_re, hadamard_im]
  · exact congrFun (QuantumDeutschJozsaGeneral.hadamard_involution (fun x => (v x z).re)) y
  · exact congrFun (QuantumDeutschJozsaGeneral.hadamard_involution (fun x => (v x z).im)) y

theorem hadamard_norm {n m : ℕ} (v : JointState n m) :
    normSquared (inputHadamard v) = normSquared v := by
  unfold normSquared
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp only [Complex.normSq_apply, hadamard_re, hadamard_im, Finset.sum_add_distrib]
  have hr := QuantumDeutschJozsaGeneral.hadamard_norm (fun x => (v x z).re)
  have hi := QuantumDeutschJozsaGeneral.hadamard_norm (fun x => (v x z).im)
  exact congrArg₂ (· + ·) hr hi

def initial (n m : ℕ) : JointState n m :=
  fun x z => if x = zeroBits n ∧ z = zeroBits m then 1 else 0

def runSimon {n m : ℕ} (f : Register n → Register m) : JointState n m :=
  inputHadamard (xorOracle f (inputHadamard (initial n m)))

def fiberSum {n m : ℕ} (f : Register n → Register m) (y : Register n) (z : Register m) : ℝ :=
  ∑ x, if f x = z then character x y else 0

def probability {n m : ℕ} (f : Register n → Register m) (y : Register n) : ℝ :=
  ∑ z, Complex.normSq (runSimon f y z)

theorem first_hadamard (n m : ℕ) (x : Register n) (z : Register m) :
    inputHadamard (initial n m) x z = if z = zeroBits m then (rho n : ℂ) else 0 := by
  classical
  by_cases hz : z = zeroBits m
  · simp [inputHadamard, initial, hz, QuantumDeutschJozsaGeneral.character_symm]
  · simp [inputHadamard, initial, hz]

theorem after_oracle {n m : ℕ} (f : Register n → Register m) (x : Register n) (z : Register m) :
    xorOracle f (inputHadamard (initial n m)) x z = if f x = z then (rho n : ℂ) else 0 := by
  simp only [xorOracle, first_hadamard, xor_zero_iff]
  simp only [eq_comm]

theorem simon_circuit_amplitude {n m : ℕ} (f : Register n → Register m)
    (y : Register n) (z : Register m) :
    runSimon f y z = ((fiberSum f y z / (2 ^ n : ℝ) : ℝ) : ℂ) := by
  classical
  have hr : rho n * rho n = 1 / (2 ^ n : ℝ) := by
    have h := QuantumDeutschJozsaGeneral.rho_square n
    have hn : (2 ^ n : ℝ) ≠ 0 := by positivity
    apply (eq_div_iff hn).2; exact h
  simp only [runSimon, inputHadamard, after_oracle]
  simp_rw [mul_ite, mul_zero]
  have he : (∑ x, if f x = z then (character x y : ℂ) * (rho n : ℂ) else 0) =
      (fiberSum f y z : ℂ) * (rho n : ℂ) := by
    simp only [fiberSum, Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _; split_ifs <;> simp
  rw [he]
  push_cast
  have hc := congrArg (fun a : ℝ => (a : ℂ)) hr
  push_cast at hc
  calc
    _ = ((rho n : ℂ) * (rho n : ℂ)) * (fiberSum f y z : ℂ) := by ring
    _ = _ := by rw [hc]; ring

theorem run_normalized {n m : ℕ} (f : Register n → Register m) : normSquared (runSimon f) = 1 := by
  classical
  simp only [runSimon, hadamard_norm, oracle_norm]
  have he : initial n m = fun x z =>
      if x = zeroBits n then (if z = zeroBits m then 1 else 0) else 0 := by
    funext x z; simp [initial, ite_and]
  rw [he]
  simp only [normSquared, apply_ite Complex.normSq, Complex.normSq_one, Complex.normSq_zero]
  simp

theorem simon_distribution_normalized {n m : ℕ} (f : Register n → Register m) :
    (∑ y, probability f y) = 1 := run_normalized f


def bit (b : Bool) : ZMod 2 := if b then 1 else 0
def encode {n : ℕ} (x : Register n) : Fin n → ZMod 2 := fun i => bit (x i)
def dot {n : ℕ} (x y : Register n) : ZMod 2 := ∑ i, encode x i * encode y i

def paritySign (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> (first | exact Or.inl rfl | exact Or.inr rfl)

theorem paritySign_add (a b : ZMod 2) : paritySign (a+b) = paritySign a * paritySign b := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
    (norm_num [paritySign]; try rfl)

theorem paritySign_sum {α : Type*} (s : Finset α) (v : α → ZMod 2) :
    paritySign (∑ i ∈ s, v i) = ∏ i ∈ s, paritySign (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [paritySign]
  | @insert a s ha ih => simp [ha, paritySign_add, ih]

theorem character_dot {n : ℕ} (x y : Register n) : character x y = paritySign (dot x y) := by
  rw [dot, paritySign_sum]
  apply Finset.prod_congr rfl
  intro i _
  simp only [encode, bit]
  cases x i <;> cases y i <;> norm_num [signOfBool, paritySign]

theorem dot_comm {n : ℕ} (x y : Register n) : dot x y = dot y x := by
  simp only [dot, mul_comm]

theorem encode_xor {n : ℕ} (x y : Register n) : encode (xorVec x y) = encode x + encode y := by
  funext i
  simp only [encode, xorVec, Pi.add_apply]
  cases x i <;> cases y i <;> (norm_num [bit]; try rfl)

theorem encode_injective {n : ℕ} : Function.Injective (@encode n) := by
  intro x y h
  funext i
  have hi := congrFun h i
  cases hx : x i <;> cases hy : y i <;> simp_all [encode, bit]

@[simp] theorem encode_zero (n : ℕ) : encode (zeroBits n) = 0 := by
  funext i; simp [encode, bit, zeroBits]

theorem fiber_shift {n m : ℕ} {f : Register n → Register m} {s : Register n}
    (h : SimonPromise f s) (y : Register n) (z : Register m) :
    fiberSum f y z = fiberSum f y z * character s y := by
  classical
  calc
    fiberSum f y z = ∑ x, if f (xorVec x s) = z then character (xorVec x s) y else 0 :=
      (Equiv.sum_comp (xorEquiv s) (fun x => if f x = z then character x y else 0)).symm
    _ = _ := by
      simp_rw [promise_periodic h, character_xor]
      simp_rw [show ∀ (p : Prop) [Decidable p] (a b : ℝ),
        (if p then a*b else 0) = (if p then a else 0)*b by intros; split_ifs <;> simp]
      exact (Finset.sum_mul _ _ _).symm

theorem simon_amplitude_zero_when_odd_dot {n m : ℕ} {f : Register n → Register m}
    {s : Register n} (h : SimonPromise f s) (y : Register n) (hy : dot y s = 1)
    (z : Register m) : runSimon f y z = 0 := by
  have hc : character s y = -1 := by rw [character_dot, dot_comm, hy]; norm_num [paritySign]
  have hf := fiber_shift h y z
  rw [hc] at hf
  have hz : fiberSum f y z = 0 := by linarith
  simp [simon_circuit_amplitude, hz]

theorem fiber_pair_sum {n m : ℕ} (f : Register n → Register m) (y x x' : Register n) :
    (∑ z, (if f x = z then character x y else 0) *
      (if f x' = z then character x' y else 0)) =
      if f x' = f x then character x y * character x' y else 0 := by
  classical
  simp_rw [ite_mul, zero_mul]
  simp [mul_ite]

theorem matching_row_sum {n m : ℕ} {f : Register n → Register m} {s : Register n}
    (h : SimonPromise f s) (y x : Register n) :
    (∑ x', if f x' = f x then character x y * character x' y else 0) = 1 + character s y := by
  classical
  have hx := xor_ne_self x s h.1
  have he : ∀ x', (if f x' = f x then character x y * character x' y else 0) =
      (if x' = x then character x y * character x' y else 0) +
      (if x' = xorVec x s then character x y * character x' y else 0) := by
    intro x'
    simp only [h.2]
    by_cases ha : x' = x <;> by_cases hb : x' = xorVec x s <;> simp_all
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [character_xor]
  have hc := QuantumDeutschJozsaGeneral.character_sq x y
  calc
    _ = character x y ^ 2 * (1 + character s y) := by ring
    _ = _ := by rw [hc]; ring

theorem fiber_square_sum {n m : ℕ} {f : Register n → Register m} {s : Register n}
    (h : SimonPromise f s) (y : Register n) :
    (∑ z, fiberSum f y z ^ 2) = (2 ^ n : ℝ) * (1 + character s y) := by
  classical
  simp only [fiberSum, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Register m)))]
  simp_rw [fiber_pair_sum]
  calc
    _ = ∑ _x : Register n, (1 + character s y) := by
      apply Finset.sum_congr rfl
      intro x _
      simpa only [eq_comm, mul_comm] using matching_row_sum h y x
    _ = _ := by simp [Register, Bits]; ring

theorem probability_character {n m : ℕ} {f : Register n → Register m} {s : Register n}
    (h : SimonPromise f s) (y : Register n) :
    probability f y = (1 + character s y) / (2 ^ n : ℝ) := by
  have hn : (2 ^ n : ℝ) ≠ 0 := by positivity
  simp only [probability, simon_circuit_amplitude, Complex.normSq_ofReal, ← pow_two, div_pow]
  rw [← Finset.sum_div, fiber_square_sum h]
  field_simp

theorem simon_exact_probability_distribution {n m : ℕ} {f : Register n → Register m}
    {s : Register n} (h : SimonPromise f s) (y : Register n) :
    probability f y = if dot y s = 0 then 2 / (2 ^ n : ℝ) else 0 := by
  rw [probability_character h, character_dot, dot_comm]
  by_cases hy : dot y s = 0 <;> norm_num [paritySign, hy]


abbrev BinarySpace (n : ℕ) := Fin n → ZMod 2

def dotForm (n : ℕ) : LinearMap.BilinForm (ZMod 2) (BinarySpace n) :=
  dotProductBilin (ZMod 2) (ZMod 2)

@[simp] theorem dotForm_apply (n : ℕ) (x y : BinarySpace n) :
    dotForm n x y = ∑ i, x i * y i := rfl

theorem dotForm_nondegenerate (n : ℕ) : (dotForm n).Nondegenerate := by
  constructor
  · intro x hx
    funext i
    have hi := hx (Pi.single i 1)
    change x ⬝ᵥ Pi.single i 1 = 0 at hi
    change x i = 0
    simpa only [dotProduct_single, mul_one] using hi
  · intro y hy
    funext i
    have hi := hy (Pi.single i 1)
    change Pi.single i 1 ⬝ᵥ y = 0 at hi
    change y i = 0
    simpa only [single_dotProduct, one_mul] using hi

def rowSpan {n : ℕ} (Y : Finset (Register n)) : Submodule (ZMod 2) (BinarySpace n) :=
  Submodule.span (ZMod 2) (encode '' (Y : Set (Register n)))

def solutionSpace {n : ℕ} (Y : Finset (Register n)) : Submodule (ZMod 2) (BinarySpace n) :=
  (dotForm n).orthogonal (rowSpan Y)

theorem solutionSpace_mem {n : ℕ} (Y : Finset (Register n)) (v : Register n) :
    encode v ∈ solutionSpace Y ↔ ∀ y ∈ Y, dot y v = 0 := by
  change rowSpan Y ≤ LinearMap.ker ((dotForm n).flip (encode v)) ↔ _
  rw [rowSpan, Submodule.span_le]
  constructor
  · intro h y hy
    exact h ⟨y, hy, rfl⟩
  · intro h w hw
    obtain ⟨y, hy, rfl⟩ := hw
    exact h y hy

theorem nonzero_period_dimension {n : ℕ} {s : Register n} (hs : s ≠ zeroBits n) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := by omega
  subst n
  apply hs; funext i; exact Fin.elim0 i

theorem simon_linear_system_recovery {n : ℕ} (s : Register n) (Y : Finset (Register n))
    (hs : s ≠ zeroBits n) (hY : ∀ y ∈ Y, dot y s = 0)
    (hrank : Module.finrank (ZMod 2) (rowSpan Y) = n - 1) (v : Register n) :
    (∀ y ∈ Y, dot y v = 0) ↔ v = zeroBits n ∨ v = s := by
  have hn := nonzero_period_dimension hs
  have he : encode s ≠ 0 := by
    intro h; apply hs; apply encode_injective; simpa using h
  have hdim : Module.finrank (ZMod 2) (solutionSpace Y) = 1 := by
    rw [solutionSpace, LinearMap.BilinForm.finrank_orthogonal (dotForm_nondegenerate n), hrank]
    simp only [BinarySpace, Module.finrank_pi, Fintype.card_fin]
    omega
  have hspan : solutionSpace Y = Submodule.span (ZMod 2) {encode s} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim ((solutionSpace_mem Y s).2 hY) he
  rw [← solutionSpace_mem, hspan, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    rcases zmod_two_cases a with rfl | rfl
    · left; apply encode_injective; simpa using ha.symm
    · right; apply encode_injective; simpa using ha.symm
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩


theorem hadamard_linear {n m : ℕ} (a b : ℂ) (u v : JointState n m) :
    inputHadamard (fun x z => a * u x z + b * v x z) =
      fun x z => a * inputHadamard u x z + b * inputHadamard v x z := by
  funext y z
  simp only [inputHadamard, mul_add, Finset.sum_add_distrib]
  simp_rw [mul_left_comm (character _ y : ℂ), ← Finset.mul_sum]
  ring

theorem hadamard_inner {n m : ℕ} (u v : JointState n m) :
    hermitian (inputHadamard u) (inputHadamard v) = hermitian u v := by
  unfold hermitian
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Complex.ext
  · simp only [Complex.re_sum, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      sub_neg_eq_add, Finset.sum_add_distrib, hadamard_re, hadamard_im, neg_mul]
    exact congrArg₂ (· + ·)
      (QuantumDeutschJozsaGeneral.hadamard_inner (fun x => (u x z).re) (fun x => (v x z).re))
      (QuantumDeutschJozsaGeneral.hadamard_inner (fun x => (u x z).im) (fun x => (v x z).im))
  · simp only [Complex.im_sum, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      neg_mul, ← sub_eq_add_neg, Finset.sum_sub_distrib, hadamard_re, hadamard_im]
    exact congrArg₂ (· - ·)
      (QuantumDeutschJozsaGeneral.hadamard_inner (fun x => (u x z).re) (fun x => (v x z).im))
      (QuantumDeutschJozsaGeneral.hadamard_inner (fun x => (u x z).im) (fun x => (v x z).re))

theorem hadamard_real_compat {n m : ℕ} (v : Register n → Register m → ℝ)
    (y : Register n) (z : Register m) :
    inputHadamard (fun x z => (v x z : ℂ)) y z =
      (QuantumDeutschJozsaGeneral.hadamard (fun x => v x z) y : ℂ) := by
  simp [inputHadamard, QuantumDeutschJozsaGeneral.hadamard]

theorem no_nonzero_period_n0 (s : Register 0) : s = zeroBits 0 := by
  funext i; exact Fin.elim0 i

/-- The probability model is a finite Born-weight model, not a hardware measurement theorem. -/
structure QuantumSimonsSuite : Prop where
  oracle_unitary : ∀ (n m : ℕ) (f : Register n → Register m),
    (∀ v, xorOracle f (xorOracle f v) = v) ∧
    (∀ u v, hermitian (xorOracle f u) (xorOracle f v) = hermitian u v)
  hadamard_unitary : ∀ (n m : ℕ) (u v : JointState n m),
    inputHadamard (inputHadamard u) = u ∧
      hermitian (inputHadamard u) (inputHadamard v) = hermitian u v
  circuit_amplitude : ∀ (n m : ℕ) (f : Register n → Register m) y z,
    runSimon f y z = ((fiberSum f y z / (2 ^ n : ℝ) : ℝ) : ℂ)
  odd_amplitude : ∀ (n m : ℕ) (f : Register n → Register m) s,
    SimonPromise f s → ∀ y, dot y s = 1 → ∀ z, runSimon f y z = 0
  exact_distribution : ∀ (n m : ℕ) (f : Register n → Register m) s,
    SimonPromise f s → ∀ y,
      probability f y = if dot y s = 0 then 2 / (2 ^ n : ℝ) else 0
  normalized : ∀ (n m : ℕ) (f : Register n → Register m), (∑ y, probability f y) = 1
  recovery : ∀ (n : ℕ) (s : Register n) (Y : Finset (Register n)),
    s ≠ zeroBits n → (∀ y ∈ Y, dot y s = 0) →
    Module.finrank (ZMod 2) (rowSpan Y) = n - 1 → ∀ v,
      (∀ y ∈ Y, dot y v = 0) ↔ v = zeroBits n ∨ v = s

theorem quantum_simons_master_suite : QuantumSimonsSuite where
  oracle_unitary _ _ := simon_oracle_unitarity
  hadamard_unitary _ _ u v := ⟨hadamard_involution u, hadamard_inner u v⟩
  circuit_amplitude _ _ := simon_circuit_amplitude
  odd_amplitude _ _ _ _ := simon_amplitude_zero_when_odd_dot
  exact_distribution _ _ _ _ := simon_exact_probability_distribution
  normalized _ _ := simon_distribution_normalized
  recovery _ := simon_linear_system_recovery

end QuantumSimonsAlgorithm
