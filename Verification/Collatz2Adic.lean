import Mathlib.Data.Int.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false

namespace Collatz2Adic

/-- The parity-dependent accelerated Collatz step on integers. -/
def syracuseStep (x : ℤ) : ℤ :=
  if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

def syracuseIter : ℕ → ℤ → ℤ
  | 0, x => x
  | n + 1, x => syracuseStep (syracuseIter n x)

@[simp] theorem syracuseIter_zero (x : ℤ) : syracuseIter 0 x = x := rfl
@[simp] theorem syracuseIter_succ (n : ℕ) (x : ℤ) :
    syracuseIter (n + 1) x = syracuseStep (syracuseIter n x) := rfl

lemma two_pow_pred (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
  have he : k = (k - 1) + 1 := by omega
  calc
    (2 : ℤ) ^ k = (2 : ℤ) ^ ((k - 1) + 1) := congrArg _ he
    _ = 2 * (2 : ℤ) ^ (k - 1) := by rw [pow_succ]; ring

theorem mod2_eq_of_dvd_two_pow (k : ℕ) (hk : 1 ≤ k) (x y : ℤ)
    (h_div : (2 : ℤ) ^ k ∣ (x - y)) : x % 2 = y % 2 := by
  rcases h_div with ⟨m, hm⟩
  have he : x - y = 2 * ((2 : ℤ) ^ (k - 1) * m) := by
    rw [hm, two_pow_pred k hk]
    ring
  omega

theorem syracuse_diff_even (x y : ℤ) (hx : x % 2 = 0) (hy : y % 2 = 0) :
    syracuseStep x - syracuseStep y = (x - y) / 2 := by
  simp only [syracuseStep, if_pos hx, if_pos hy]
  omega

theorem syracuse_diff_odd (x y : ℤ) (hx : x % 2 ≠ 0) (hy : y % 2 ≠ 0) :
    syracuseStep x - syracuseStep y = 3 * ((x - y) / 2) := by
  simp only [syracuseStep, if_neg hx, if_neg hy]
  omega

/-- One step loses at most one binary digit of congruence precision. -/
theorem syracuse_2adic_continuous (k : ℕ) (hk : 1 ≤ k) (x y : ℤ)
    (h_div : (2 : ℤ) ^ k ∣ (x - y)) :
    (2 : ℤ) ^ (k - 1) ∣ (syracuseStep x - syracuseStep y) := by
  have hp := mod2_eq_of_dvd_two_pow k hk x y h_div
  rcases h_div with ⟨m, hm⟩
  have hf : x - y = 2 * ((2 : ℤ) ^ (k - 1) * m) := by
    rw [hm, two_pow_pred k hk]
    ring
  have hh : (x - y) / 2 = (2 : ℤ) ^ (k - 1) * m := by omega
  by_cases hx : x % 2 = 0
  · have hy : y % 2 = 0 := by omega
    rw [syracuse_diff_even x y hx hy, hh]
    exact dvd_mul_right _ _
  · have hy : y % 2 ≠ 0 := by omega
    rw [syracuse_diff_odd x y hx hy, hh]
    use 3 * m
    ring

/-- Integer congruence estimate for iterates, without constructing a map on Z_2. -/
theorem syracuse_iter_2adic_continuous (n k : ℕ) (x y : ℤ)
    (h_div : (2 : ℤ) ^ (k + n) ∣ (x - y)) :
    (2 : ℤ) ^ k ∣ (syracuseIter n x - syracuseIter n y) := by
  induction n generalizing k with
  | zero => simpa using h_div
  | succ n ih =>
      have he : k + (n + 1) = (k + 1) + n := by omega
      rw [he] at h_div
      have hi := ih (k + 1) h_div
      simpa using syracuse_2adic_continuous (k + 1) (by omega)
        (syracuseIter n x) (syracuseIter n y) hi

/-- Preserving the same modulus is false even for the pair 0 and 2. -/
theorem same_modulus_not_preserved :
    (2 : ℤ) ∣ (0 - 2) ∧ ¬ (2 : ℤ) ∣ (syracuseStep 0 - syracuseStep 2) := by
  norm_num [syracuseStep]

structure Collatz2AdicFormalSuite : Prop where
  h_parity_match : ∀ (k : ℕ), 1 ≤ k → ∀ (x y : ℤ),
    (2 : ℤ) ^ k ∣ (x - y) → x % 2 = y % 2
  h_step_cont : ∀ (k : ℕ), 1 ≤ k → ∀ (x y : ℤ),
    (2 : ℤ) ^ k ∣ (x - y) → (2 : ℤ) ^ (k - 1) ∣ (syracuseStep x - syracuseStep y)
  h_iter_cont : ∀ (n k : ℕ) (x y : ℤ),
    (2 : ℤ) ^ (k + n) ∣ (x - y) → (2 : ℤ) ^ k ∣ (syracuseIter n x - syracuseIter n y)

theorem collatz_2adic_master_verification_suite : Collatz2AdicFormalSuite := {
  h_parity_match := mod2_eq_of_dvd_two_pow
  h_step_cont := syracuse_2adic_continuous
  h_iter_cont := syracuse_iter_2adic_continuous
}

#print axioms collatz_2adic_master_verification_suite

end Collatz2Adic
