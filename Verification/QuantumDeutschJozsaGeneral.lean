/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumDeutschJozsa
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Exact real Walsh operators, an XOR ancilla circuit and Deutsch–Jozsa promise separation.
Physical measurement and oracle construction cost are outside this model. -/

noncomputable section
open scoped BigOperators
namespace QuantumDeutschJozsaGeneral

abbrev Bits (n : ℕ) := Fin n → Bool
abbrev State (n : ℕ) := Bits n → ℝ

def signOfBool (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem sign_sq (b : Bool) : signOfBool b ^ 2 = 1 := by
  cases b <;> norm_num [signOfBool]

theorem sign_xor (a b : Bool) : signOfBool (a ^^ b) = signOfBool a * signOfBool b := by
  cases a <;> cases b <;> norm_num [signOfBool]

def character {n : ℕ} (x y : Bits n) : ℝ := ∏ i, signOfBool (x i && y i)
def zeroBits (n : ℕ) : Bits n := fun _ => false
def basis {n : ℕ} (x : Bits n) : State n := fun y => if y = x then 1 else 0
def rho (n : ℕ) : ℝ := 1 / Real.sqrt (2 ^ n : ℝ)
def inner {n : ℕ} (v w : State n) : ℝ := ∑ x, v x * w x
def normSquared {n : ℕ} (v : State n) : ℝ := inner v v
def hadamard {n : ℕ} (v : State n) : State n := fun y => rho n * ∑ x, character x y * v x
def phaseOracle {n : ℕ} (f : Bits n → Bool) (v : State n) : State n :=
  fun x => signOfBool (f x) * v x

theorem card_bits (n : ℕ) : Fintype.card (Bits n) = 2 ^ n := by simp [Bits]
theorem rho_square (n : ℕ) : rho n * rho n * (2 ^ n : ℝ) = 1 := by
  have h : (0 : ℝ) < 2 ^ n := by positivity
  have hs := Real.sq_sqrt (le_of_lt h)
  have hn : Real.sqrt (2 ^ n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h)
  unfold rho
  field_simp
  nlinarith

theorem character_symm {n : ℕ} (x y : Bits n) : character x y = character y x := by
  simp only [character, Bool.and_comm]

@[simp] theorem character_zero {n : ℕ} (x : Bits n) : character x (zeroBits n) = 1 := by
  simp [character, zeroBits, signOfBool]

@[simp] theorem character_sq {n : ℕ} (x y : Bits n) : character x y ^ 2 = 1 := by
  simp [character, ← Finset.prod_pow]

theorem bit_orthogonal (a b : Bool) :
    (∑ x : Bool, signOfBool (x && a) * signOfBool (x && b)) = if a = b then 2 else 0 := by
  cases a <;> cases b <;> norm_num [signOfBool, Fintype.sum_bool]

theorem character_orthogonal {n : ℕ} (y z : Bits n) :
    (∑ x, character x y * character x z) = if y = z then (2 ^ n : ℝ) else 0 := by
  classical
  simp only [character, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) =>
    signOfBool (b && y i) * signOfBool (b && z i))]
  simp_rw [bit_orthogonal]
  by_cases h : y = z
  · simp [h]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ z i := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem hadamard_self_adjoint {n : ℕ} (v w : State n) :
    inner (hadamard v) w = inner v (hadamard w) := by
  unfold inner hadamard
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [character_symm y x]
  ring

theorem hadamard_involution {n : ℕ} (v : State n) : hadamard (hadamard v) = v := by
  classical
  funext y
  unfold hadamard
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [show ∀ x z, character x y * (rho n * (character z x * v z)) =
    (rho n * v z) * (character x y * character x z) by
      intro x z; rw [character_symm z x]; ring]
  simp_rw [← Finset.mul_sum, character_orthogonal]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  calc
    _ = (rho n * rho n * 2 ^ n) * v y := by ring
    _ = v y := by rw [rho_square, one_mul]

theorem hadamard_inner {n : ℕ} (v w : State n) :
    inner (hadamard v) (hadamard w) = inner v w := by
  rw [hadamard_self_adjoint, hadamard_involution]

theorem hadamard_norm {n : ℕ} (v : State n) :
    normSquared (hadamard v) = normSquared v := hadamard_inner v v

theorem phase_involution {n : ℕ} (f : Bits n → Bool) (v : State n) :
    phaseOracle f (phaseOracle f v) = v := by
  funext x
  simp [phaseOracle, ← mul_assoc, ← pow_two]

theorem phase_inner {n : ℕ} (f : Bits n → Bool) (v w : State n) :
    inner (phaseOracle f v) (phaseOracle f w) = inner v w := by
  unfold inner phaseOracle
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = signOfBool (f x) ^ 2 * (v x * w x) := by ring
    _ = _ := by rw [sign_sq, one_mul]

theorem hadamard_basis {n : ℕ} (z : Bits n) :
    hadamard (basis z) = fun y => rho n * character z y := by
  classical
  funext y
  simp [hadamard, basis]

theorem hadamard_uniform (n : ℕ) :
    hadamard (basis (zeroBits n)) = fun _ => rho n := by
  rw [hadamard_basis]
  funext y
  rw [character_symm, character_zero, mul_one]

def runDJ {n : ℕ} (f : Bits n → Bool) : State n :=
  hadamard (phaseOracle f (hadamard (basis (zeroBits n))))

theorem run_normalized {n : ℕ} (f : Bits n → Bool) : normSquared (runDJ f) = 1 := by
  classical
  unfold runDJ
  rw [hadamard_norm]
  unfold normSquared
  rw [phase_inner, hadamard_inner]
  simp [inner, basis]

theorem output_amplitude {n : ℕ} (f : Bits n → Bool) (y : Bits n) :
    runDJ f y = (∑ x, signOfBool (f x) * character x y) / (2 ^ n : ℝ) := by
  have hn : (2 ^ n : ℝ) ≠ 0 := by positivity
  have hr := rho_square n
  unfold runDJ
  rw [hadamard_uniform]
  simp only [hadamard, phaseOracle]
  have he : ∀ x, character x y * (signOfBool (f x) * rho n) =
      rho n * (signOfBool (f x) * character x y) := by intro x; ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  apply (eq_div_iff hn).2
  calc
    _ = (rho n * rho n * 2 ^ n) * (∑ x, signOfBool (f x) * character x y) := by ring
    _ = _ := by rw [hr, one_mul]


section FiniteMean
variable {α : Type*} [Fintype α]

def IsConstant (f : α → Bool) : Prop := ∀ x y, f x = f y
def trueCount (f : α → Bool) : ℕ := (Finset.univ.filter (fun x => f x = true)).card
def falseCount (f : α → Bool) : ℕ := (Finset.univ.filter (fun x => f x = false)).card
def IsBalanced (f : α → Bool) : Prop := 2 * trueCount f = Fintype.card α
def DJPromise (f : α → Bool) : Prop := IsConstant f ∨ IsBalanced f
def zeroStateAmplitude (f : α → Bool) : ℝ :=
  (∑ x, signOfBool (f x)) / (Fintype.card α : ℝ)
def zeroStateProb (f : α → Bool) : ℝ := zeroStateAmplitude f ^ 2

theorem counts_partition (f : α → Bool) : trueCount f + falseCount f = Fintype.card α := by
  classical
  unfold trueCount falseCount
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    cases h : f x <;> simp [h]
  · simp [Finset.disjoint_left]

theorem balanced_counts (f : α → Bool) : IsBalanced f ↔ trueCount f = falseCount f := by
  have h := counts_partition f
  unfold IsBalanced
  omega

theorem sum_sign (f : α → Bool) :
    (∑ x, signOfBool (f x)) = (Fintype.card α : ℝ) - 2 * (trueCount f : ℝ) := by
  classical
  have h : ∀ b, signOfBool b = 1 - 2 * (if b = true then (1 : ℝ) else 0) := by
    intro b; cases b <;> norm_num [signOfBool]
  simp_rw [h]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [trueCount]

omit [Fintype α] in
theorem constant_value (f : α → Bool) (hc : IsConstant f) (x : α) :
    ∀ y, f y = f x := fun y => hc y x

theorem constant_mean (f : α → Bool) (hc : IsConstant f) (hn : 0 < Fintype.card α)
    (x : α) : zeroStateAmplitude f = signOfBool (f x) := by
  have hz : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold zeroStateAmplitude
  simp_rw [constant_value f hc x]
  simp [hz]

theorem dj_constant_amplitude (f : α → Bool) (hc : IsConstant f)
    (hn : 0 < Fintype.card α) : zeroStateProb f = 1 := by
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hn
  rw [zeroStateProb, constant_mean f hc hn x, sign_sq]

theorem dj_balanced_amplitude (f : α → Bool) (hb : IsBalanced f) :
    zeroStateAmplitude f = 0 ∧ zeroStateProb f = 0 := by
  have h : 2 * (trueCount f : ℝ) = (Fintype.card α : ℝ) := by exact_mod_cast hb
  have hm : zeroStateAmplitude f = 0 := by
    rw [zeroStateAmplitude, sum_sign, ← h, sub_self, zero_div]
  exact ⟨hm, by simp [zeroStateProb, hm]⟩

theorem constant_not_balanced (f : α → Bool) (hn : 0 < Fintype.card α) :
    ¬ (IsConstant f ∧ IsBalanced f) := by
  rintro ⟨hc, hb⟩
  have h1 := dj_constant_amplitude f hc hn
  have h0 := (dj_balanced_amplitude f hb).2
  linarith

theorem dj_promise_zero_error_separation (f : α → Bool) (hp : DJPromise f)
    (hn : 0 < Fintype.card α) : zeroStateProb f = 1 ↔ IsConstant f := by
  constructor
  · intro h
    rcases hp with hc | hb
    · exact hc
    · have := (dj_balanced_amplitude f hb).2; linarith
  · intro hc; exact dj_constant_amplitude f hc hn

theorem dj_promise_balanced (f : α → Bool) (hp : DJPromise f)
    (hn : 0 < Fintype.card α) : zeroStateProb f = 0 ↔ IsBalanced f := by
  constructor
  · intro h
    rcases hp with hc | hb
    · have := dj_constant_amplitude f hc hn; linarith
    · exact hb
  · intro hb; exact (dj_balanced_amplitude f hb).2

theorem dj_edge_case_n0 (f : α → Bool) (hn : Fintype.card α = 1) :
    IsConstant f ∧ ¬ IsBalanced f ∧ zeroStateProb f = 1 := by
  have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have hc : IsConstant f := fun x y => congrArg f (Subsingleton.elim x y)
  have hp : 0 < Fintype.card α := by omega
  exact ⟨hc, fun hb => constant_not_balanced f hp ⟨hc, hb⟩,
    dj_constant_amplitude f hc hp⟩
end FiniteMean

theorem zero_amplitude {n : ℕ} (f : Bits n → Bool) :
    runDJ f (zeroBits n) = zeroStateAmplitude f := by
  rw [output_amplitude]
  simp [zeroStateAmplitude]

theorem balanced_half {n : ℕ} (f : Bits n → Bool) (hb : IsBalanced f) :
    trueCount f = 2 ^ n / 2 ∧ falseCount f = 2 ^ n / 2 := by
  have hc := counts_partition f
  have hd := (balanced_counts f).mp hb
  have hk := card_bits n
  unfold IsBalanced at hb
  omega

theorem run_constant {n : ℕ} (f : Bits n → Bool) (c : Bool) (hc : ∀ x, f x = c) :
    runDJ f = fun y => signOfBool c * basis (zeroBits n) y := by
  funext y
  rw [output_amplitude]
  simp_rw [hc]
  rw [← Finset.mul_sum]
  have h := character_orthogonal (zeroBits n) y
  simp only [character_zero, one_mul] at h
  rw [h]
  by_cases he : y = zeroBits n
  · simp [he, basis]
  · simp [he, Ne.symm he, basis]

def outcomeWeight {n : ℕ} (f : Bits n → Bool) (y : Bits n) : ℝ := runDJ f y ^ 2

theorem total_weight {n : ℕ} (f : Bits n → Bool) : (∑ y, outcomeWeight f y) = 1 := by
  simpa [normSquared, inner, outcomeWeight, pow_two] using run_normalized f

theorem nonzero_weight {n : ℕ} (f : Bits n → Bool) (hb : IsBalanced f) :
    (∑ y ∈ Finset.univ.erase (zeroBits n), outcomeWeight f y) = 1 := by
  classical
  have hz : outcomeWeight f (zeroBits n) = 0 := by
    rw [outcomeWeight, zero_amplitude, (dj_balanced_amplitude f hb).1]; norm_num
  have h := Finset.sum_erase_add Finset.univ (fun y => outcomeWeight f y)
    (Finset.mem_univ (zeroBits n))
  rw [hz, add_zero, total_weight] at h
  exact h

theorem promised_outcome_correct {n : ℕ} (f : Bits n → Bool) (hp : DJPromise f)
    (y : Bits n) (hy : 0 < outcomeWeight f y) :
    (y = zeroBits n ↔ IsConstant f) ∧ (y ≠ zeroBits n ↔ IsBalanced f) := by
  have hn : 0 < Fintype.card (Bits n) := by rw [card_bits]; positivity
  rcases hp with hc | hb
  · have hr := run_constant f (f (zeroBits n)) (constant_value f hc (zeroBits n))
    have he : y = zeroBits n := by
      by_contra h
      simp [outcomeWeight, hr, basis, h] at hy
    have hb : ¬ IsBalanced f := fun h => constant_not_balanced f hn ⟨hc, h⟩
    exact ⟨by simp [he, hc], by simp [he, hb]⟩
  · have he : y ≠ zeroBits n := by
      intro h; subst y
      rw [outcomeWeight, zero_amplitude, (dj_balanced_amplitude f hb).1] at hy
      norm_num at hy
    have hc : ¬ IsConstant f := fun h => constant_not_balanced f hn ⟨h, hb⟩
    exact ⟨by simp [he, hc], by simp [he, hb]⟩


theorem hadamard_add {n : ℕ} (v w : State n) :
    hadamard (fun x => v x + w x) = fun y => hadamard v y + hadamard w y := by
  funext y
  simp [hadamard, mul_add, Finset.sum_add_distrib]

theorem hadamard_smul {n : ℕ} (a : ℝ) (v : State n) :
    hadamard (fun x => a * v x) = fun y => a * hadamard v y := by
  funext y
  simp only [hadamard]
  simp_rw [mul_left_comm (character _ y) a, ← Finset.mul_sum]
  ring

theorem phase_linear {n : ℕ} (f : Bits n → Bool) (a b : ℝ) (v w : State n) :
    phaseOracle f (fun x => a * v x + b * w x) =
      fun x => a * phaseOracle f v x + b * phaseOracle f w x := by
  funext x; simp only [phaseOracle]; ring

theorem rho_succ (n : ℕ) : rho (n + 1) = (1 / Real.sqrt 2) * rho n := by
  simp [rho, pow_succ, mul_comm]

def kernel {n : ℕ} (x y : Bits n) : ℝ := rho n * character x y

theorem kernel_tensor (n : ℕ) (a b : Bool) (x y : Bits n) :
    kernel (Fin.cons a x) (Fin.cons b y) =
      (signOfBool (a && b) / Real.sqrt 2) * kernel x y := by
  simp only [kernel, character, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, rho_succ]
  ring

abbrev JointState (n : ℕ) := Bits n → Bool → ℝ

def minus (b : Bool) : ℝ := signOfBool b / Real.sqrt 2
def productState {n : ℕ} (v : State n) (u : Bool → ℝ) : JointState n :=
  fun x b => v x * u b
def xorOracle {n : ℕ} (f : Bits n → Bool) (ψ : JointState n) : JointState n :=
  fun x b => ψ x (b ^^ f x)
def jointNorm {n : ℕ} (ψ : JointState n) : ℝ := ∑ x, ∑ b, ψ x b ^ 2
def inputHadamard {n : ℕ} (ψ : JointState n) : JointState n :=
  fun y b => hadamard (fun x => ψ x b) y

theorem minus_normalized : (∑ b : Bool, minus b ^ 2) = 1 := by
  norm_num [minus, signOfBool, Fintype.sum_bool, div_pow]

def ancillaHadamard (u : Bool → ℝ) (b : Bool) : ℝ :=
  (u false + signOfBool b * u true) / Real.sqrt 2

theorem minus_prepared : ancillaHadamard (fun b => if b then 1 else 0) = minus := by
  funext b; simp [ancillaHadamard, minus]

theorem xor_involution {n : ℕ} (f : Bits n → Bool) (ψ : JointState n) :
    xorOracle f (xorOracle f ψ) = ψ := by
  funext x b
  simp [xorOracle]

theorem xor_linear {n : ℕ} (f : Bits n → Bool) (a b : ℝ) (v w : JointState n) :
    xorOracle f (fun x c => a * v x c + b * w x c) =
      fun x c => a * xorOracle f v x c + b * xorOracle f w x c := rfl

theorem xor_norm {n : ℕ} (f : Bits n → Bool) (ψ : JointState n) :
    jointNorm (xorOracle f ψ) = jointNorm ψ := by
  unfold jointNorm xorOracle
  apply Finset.sum_congr rfl
  intro x _
  cases f x <;> simp [add_comm]

theorem dj_phase_kickback {n : ℕ} (f : Bits n → Bool) (v : State n) :
    xorOracle f (productState v minus) = productState (phaseOracle f v) minus := by
  funext x b
  simp only [xorOracle, productState, minus, sign_xor, phaseOracle]
  ring

theorem inputHadamard_product {n : ℕ} (v : State n) (u : Bool → ℝ) :
    inputHadamard (productState v u) = productState (hadamard v) u := by
  funext y b
  simp only [inputHadamard, productState, hadamard]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  ring

theorem product_minus_norm {n : ℕ} (v : State n) :
    jointNorm (productState v minus) = normSquared v := by
  simp only [jointNorm, productState, mul_pow, ← Finset.mul_sum, minus_normalized, mul_one]
  simp only [normSquared, inner, pow_two]

theorem inputHadamard_norm {n : ℕ} (ψ : JointState n) :
    jointNorm (inputHadamard ψ) = jointNorm ψ := by
  unfold jointNorm inputHadamard
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simpa [normSquared, inner, pow_two] using hadamard_norm (fun x => ψ x b)

def jointRun {n : ℕ} (f : Bits n → Bool) : JointState n :=
  inputHadamard (xorOracle f (inputHadamard (productState (basis (zeroBits n)) minus)))

theorem joint_run_eq {n : ℕ} (f : Bits n → Bool) :
    jointRun f = productState (runDJ f) minus := by
  simp only [jointRun, inputHadamard_product, dj_phase_kickback, runDJ]

theorem joint_run_normalized {n : ℕ} (f : Bits n → Bool) : jointNorm (jointRun f) = 1 := by
  rw [joint_run_eq, product_minus_norm, run_normalized]

theorem marginal_weight {n : ℕ} (f : Bits n → Bool) (y : Bits n) :
    (∑ b, jointRun f y b ^ 2) = outcomeWeight f y := by
  rw [joint_run_eq]
  simp only [productState, mul_pow, ← Finset.mul_sum, minus_normalized, mul_one, outcomeWeight]


def liftOne (f : Bool → Bool) : Bits 1 → Bool := fun x => f (x 0)

def oneBitEquiv : Bool ≃ Bits 1 where
  toFun b := fun _ => b
  invFun x := x 0
  left_inv _ := rfl
  right_inv x := by funext i; exact congrArg x (Subsingleton.elim 0 i)

theorem sum_bits_one (g : Bits 1 → ℝ) :
    (∑ x, g x) = g (fun _ => false) + g (fun _ => true) := by
  rw [← Equiv.sum_comp oneBitEquiv]
  simp [oneBitEquiv, add_comm]

theorem dj_compat_one_qubit (f : Bool → Bool) :
    runDJ (liftOne f) (fun _ => false) = QuantumDeutschJozsa.amp0 f ∧
    runDJ (liftOne f) (fun _ => true) = QuantumDeutschJozsa.amp1 f := by
  constructor <;> rw [output_amplitude, sum_bits_one] <;>
    cases h0 : f false <;> cases h1 : f true <;>
    norm_num [liftOne, character, QuantumDeutschJozsa.amp0, QuantumDeutschJozsa.amp1,
      QuantumDeutschJozsa.phaseSign, signOfBool, h0, h1]

theorem constant_compat (f : Bool → Bool) :
    IsConstant (liftOne f) ↔ QuantumDeutschJozsa.IsConstant f := by
  constructor
  · intro h
    exact h (fun _ => false) (fun _ => true)
  · intro h x y
    unfold liftOne
    cases hx : x 0 <;> cases hy : y 0 <;> simp_all [QuantumDeutschJozsa.IsConstant]

theorem balanced_compat (f : Bool → Bool) :
    IsBalanced (liftOne f) ↔ QuantumDeutschJozsa.IsBalanced f := by
  have hs : zeroStateAmplitude (liftOne f) = QuantumDeutschJozsa.amp0 f := by
    rw [← zero_amplitude]; exact (dj_compat_one_qubit f).1
  constructor
  · intro hb hc
    have h := (constant_compat f).mpr hc
    exact constant_not_balanced (liftOne f) (by simp [Bits]) ⟨h, hb⟩
  · intro hb
    have hz := (QuantumDeutschJozsa.balanced_function_yields_one f hb).1
    have hmean : zeroStateAmplitude (liftOne f) = 0 := by
      rw [hs]
      nlinarith [sq_nonneg (QuantumDeutschJozsa.amp0 f)]
    have hn : (Fintype.card (Bits 1) : ℝ) ≠ 0 := by simp [Bits]
    have he := (div_eq_zero_iff).mp (show (∑ x, signOfBool (liftOne f x)) /
      (Fintype.card (Bits 1) : ℝ) = 0 from hmean)
    have hzsum := he.resolve_right hn
    rw [sum_sign] at hzsum
    unfold IsBalanced
    exact_mod_cast (show 2 * (trueCount (liftOne f) : ℝ) = Fintype.card (Bits 1) by linarith)

theorem bits_zero_result (f : Bits 0 → Bool) :
    IsConstant f ∧ ¬ IsBalanced f ∧ zeroStateProb f = 1 :=
  dj_edge_case_n0 f (by simp [Bits])

theorem hadamard_zero (v : State 0) : hadamard v = v := by
  funext y
  simp only [hadamard, rho, pow_zero, Real.sqrt_one, div_one, character,
    Fin.prod_univ_zero, one_mul, Fintype.sum_unique]
  exact congrArg v (Subsingleton.elim _ _)

theorem zero_weight {n : ℕ} (f : Bits n → Bool) :
    outcomeWeight f (zeroBits n) = zeroStateProb f := by
  rw [outcomeWeight, zero_amplitude, zeroStateProb]


def splitBits (n : ℕ) : Bits (n + 1) ≃ Bool × Bits n where
  toFun x := (x 0, fun i => x i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv x := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv p := by cases p; rfl

theorem sum_bits_succ {n : ℕ} (g : Bits (n + 1) → ℝ) :
    (∑ x, g x) = (∑ x : Bits n, g (Fin.cons false x)) +
      ∑ x : Bits n, g (Fin.cons true x) := by
  rw [← Equiv.sum_comp (splitBits n).symm]
  simp [Fintype.sum_prod_type, splitBits, add_comm]

theorem hadamard_one (u : Bool → ℝ) (b : Bool) :
    hadamard (fun x : Bits 1 => u (x 0)) (fun _ => b) = ancillaHadamard u b := by
  unfold hadamard
  rw [sum_bits_one]
  cases b <;> simp [character, rho, ancillaHadamard, signOfBool, div_eq_mul_inv, mul_comm]

theorem absent_promise_counterexample :
    ¬ DJPromise (fun x : Bits 2 => x 0 && x 1) ∧
    outcomeWeight (fun x : Bits 2 => x 0 && x 1) (zeroBits 2) = 1 / 4 := by
  constructor
  · intro h
    rcases h with hc | hb
    · have he := hc (fun _ => false) (fun _ => true)
      simp at he
    · have hn : ¬ IsBalanced (fun x : Bits 2 => x 0 && x 1) := by
        unfold IsBalanced trueCount
        decide
      exact hn hb
  · rw [outcomeWeight, output_amplitude]
    norm_num [sum_bits_succ, character, zeroBits, signOfBool]

def nonlinearBalanced (x : Bits 3) : Bool := x 0 ^^ (x 1 && x 2)

theorem nonlinear_balanced : IsBalanced nonlinearBalanced := by
  unfold IsBalanced trueCount nonlinearBalanced
  decide

theorem nonlinear_output (a b : Bool) :
    runDJ nonlinearBalanced ![true, a, b] = signOfBool (a && b) / 2 := by
  have hc : ∀ (c : Bool) (x : Bits 2), (Fin.cons c x : Bits 3) 2 = x 1 := fun _ _ => rfl
  rw [output_amplitude]
  cases a <;> cases b <;>
    norm_num [sum_bits_succ, character, nonlinearBalanced, signOfBool,
      Fin.prod_univ_succ, Matrix.cons_val_two, hc]

theorem balanced_not_single_output :
    outcomeWeight nonlinearBalanced ![true, false, false] = 1/4 ∧
    outcomeWeight nonlinearBalanced ![true, true, true] = 1/4 ∧
    (![true, false, false] : Bits 3) ≠ ![true, true, true] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [outcomeWeight, nonlinear_output]; norm_num [signOfBool]
  · rw [outcomeWeight, nonlinear_output]; norm_num [signOfBool]
  · intro h
    have := congrFun h 1
    simp at this

theorem plus_does_not_kickback :
    xorOracle (liftOne id) (productState (fun _ => 1) (fun _ => 1)) ≠
      productState (phaseOracle (liftOne id) (fun _ => 1)) (fun _ => 1) := by
  intro h
  have he := congrFun (congrFun h (fun _ => true)) false
  norm_num [xorOracle, productState, phaseOracle, liftOne, signOfBool] at he

structure QuantumDeutschJozsaGeneralSuite : Prop where
  hadamard_inverse : ∀ n (v : State n), hadamard (hadamard v) = v
  hadamard_isometry : ∀ n (v w : State n), inner (hadamard v) (hadamard w) = inner v w
  tensor_kernel : ∀ n a b (x y : Bits n),
    kernel (Fin.cons a x) (Fin.cons b y) =
      (signOfBool (a && b) / Real.sqrt 2) * kernel x y
  kickback : ∀ n (f : Bits n → Bool) (v : State n),
    xorOracle f (productState v minus) = productState (phaseOracle f v) minus
  circuit_output : ∀ n (f : Bits n → Bool), jointRun f = productState (runDJ f) minus
  circuit_norm : ∀ n (f : Bits n → Bool), jointNorm (jointRun f) = 1
  amplitude : ∀ n (f : Bits n → Bool) y,
    runDJ f y = (∑ x, signOfBool (f x) * character x y) / (2 ^ n : ℝ)
  promised_classification : ∀ n (f : Bits n → Bool), DJPromise f →
    ∀ y, 0 < outcomeWeight f y →
      (y = zeroBits n ↔ IsConstant f) ∧ (y ≠ zeroBits n ↔ IsBalanced f)
  balanced_total : ∀ n (f : Bits n → Bool), IsBalanced f →
    (∑ y ∈ Finset.univ.erase (zeroBits n), outcomeWeight f y) = 1
  edge_zero : ∀ f : Bits 0 → Bool, IsConstant f ∧ ¬ IsBalanced f ∧ zeroStateProb f = 1
  legacy : ∀ f : Bool → Bool,
    runDJ (liftOne f) (fun _ => false) = QuantumDeutschJozsa.amp0 f ∧
    runDJ (liftOne f) (fun _ => true) = QuantumDeutschJozsa.amp1 f

theorem quantum_deutsch_jozsa_general_master_suite : QuantumDeutschJozsaGeneralSuite := {
  hadamard_inverse := fun _ => hadamard_involution
  hadamard_isometry := fun _ => hadamard_inner
  tensor_kernel := kernel_tensor
  kickback := fun _ => dj_phase_kickback
  circuit_output := fun _ => joint_run_eq
  circuit_norm := fun _ => joint_run_normalized
  amplitude := fun _ => output_amplitude
  promised_classification := fun _ => promised_outcome_correct
  balanced_total := fun _ => nonzero_weight
  edge_zero := bits_zero_result
  legacy := dj_compat_one_qubit
}

end QuantumDeutschJozsaGeneral
