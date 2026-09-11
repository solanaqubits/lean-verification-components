import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false

namespace CryptoZKFRILowDegree

/-- Fold adjacent coefficient pairs; an unpaired last coefficient is retained. -/
def friFoldStep {R : Type*} [Add R] [Mul R] (alpha : R) : List R → List R
  | [] => []
  | [x] => [x]
  | x :: y :: rest => (x + alpha * y) :: friFoldStep alpha rest

theorem friFoldStep_length {R : Type*} [Add R] [Mul R] (alpha : R) (p : List R) :
    (friFoldStep alpha p).length = (p.length + 1) / 2 := by
  induction p using friFoldStep.induct with
  | case1 => simp [friFoldStep]
  | case2 x => simp [friFoldStep]
  | case3 x y rest ih =>
      simp only [friFoldStep, List.length_cons] at *
      omega

/-- An arithmetic degree bound, not the degree of a Polynomial object. -/
def friDegreeStep (d : ℕ) : ℕ := d / 2

def friRoundsDeg (d : ℕ) : ℕ → ℕ
  | 0 => d
  | k + 1 => friDegreeStep (friRoundsDeg d k)

theorem friDegreeStep_strict_lt (d : ℕ) (h : 1 ≤ d) : friDegreeStep d < d := by
  dsimp [friDegreeStep]
  omega

theorem friRoundsDeg_eq (d k : ℕ) : friRoundsDeg d k = d / (2 ^ k) := by
  induction k with
  | zero => simp [friRoundsDeg]
  | succ k ih =>
      dsimp [friRoundsDeg, friDegreeStep]
      rw [ih, pow_succ, Nat.div_div_eq_div_mul]

/-- The numerical bound reaches zero once 2^k exceeds d. -/
theorem fri_terminates_at_constant (d k : ℕ) (h : d < 2 ^ k) : friRoundsDeg d k = 0 := by
  rw [friRoundsDeg_eq]
  exact Nat.div_eq_of_lt h

noncomputable section

def evalPolyDeg3 (c0 c1 c2 c3 x : ℝ) : ℝ :=
  c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3

def evalPolyDeg1 (a0 a1 y : ℝ) : ℝ := a0 + a1 * y

theorem fri_fold_eval_degree3 (c0 c1 c2 c3 alpha x : ℝ) (hx : x ≠ 0) :
    ((evalPolyDeg3 c0 c1 c2 c3 x + evalPolyDeg3 c0 c1 c2 c3 (-x)) / 2) +
    alpha * ((evalPolyDeg3 c0 c1 c2 c3 x - evalPolyDeg3 c0 c1 c2 c3 (-x)) / (2 * x)) =
    evalPolyDeg1 (c0 + alpha * c1) (c2 + alpha * c3) (x ^ 2) := by
  dsimp [evalPolyDeg3, evalPolyDeg1]
  field_simp
  ring

structure CryptoZKFRISuite : Prop where
  h_fold_length : ∀ {R : Type*} [Add R] [Mul R] (alpha : R) (p : List R),
    (friFoldStep alpha p).length = (p.length + 1) / 2
  h_deg_step_lt : ∀ d, 1 ≤ d → friDegreeStep d < d
  h_rounds_eq : ∀ d k, friRoundsDeg d k = d / (2 ^ k)
  h_termination : ∀ d k, d < 2 ^ k → friRoundsDeg d k = 0
  h_eval_identity : ∀ (c0 c1 c2 c3 alpha x : ℝ), x ≠ 0 →
    ((evalPolyDeg3 c0 c1 c2 c3 x + evalPolyDeg3 c0 c1 c2 c3 (-x)) / 2) +
    alpha * ((evalPolyDeg3 c0 c1 c2 c3 x - evalPolyDeg3 c0 c1 c2 c3 (-x)) / (2 * x)) =
    evalPolyDeg1 (c0 + alpha * c1) (c2 + alpha * c3) (x ^ 2)

theorem crypto_zk_fri_master_verification_suite : CryptoZKFRISuite := {
  h_fold_length := friFoldStep_length
  h_deg_step_lt := friDegreeStep_strict_lt
  h_rounds_eq := friRoundsDeg_eq
  h_termination := fri_terminates_at_constant
  h_eval_identity := fri_fold_eval_degree3
}

#print axioms crypto_zk_fri_master_verification_suite

end
end CryptoZKFRILowDegree
