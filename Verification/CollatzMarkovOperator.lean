import Verification.CollatzEffectiveDrift

set_option linter.style.header false

noncomputable section

namespace CollatzMarkovOperator

open CollatzBase CollatzRemainderBound CollatzEffectiveDrift

/-- Candidate branchwise logarithmic bound; its relation to actual jumps is not proved here. -/
def branch_drift_bound (a b : ℕ) (r : ℚ) (n : ℕ) : ℝ :=
  (a : ℝ) * Real.log 3 - (b : ℝ) * Real.log 2 + (r : ℝ) * (1 / (n : ℝ))

/-- Weighted sum of the six candidate bounds.
The name is retained for compatibility; no Markov transition kernel is defined here.
-/
def tree32_markov_drift (n : ℕ) : ℝ :=
  (1 / 4 : ℝ) * branch_drift_bound 1 2 rem_b1 n +
  (1 / 4 : ℝ) * branch_drift_bound 1 3 rem_b5 n +
  (1 / 4 : ℝ) * branch_drift_bound 2 3 rem_b3 n +
  (1 / 8 : ℝ) * branch_drift_bound 3 4 rem_b7 n +
  (1 / 16 : ℝ) * branch_drift_bound 4 5 rem_b15 n +
  (1 / 16 : ℝ) * branch_drift_bound 4 4 rem_b31 n

/-- The weighted sum equals the previously bounded scalar expression. -/
theorem tree32_markov_drift_eq (n : ℕ) :
    tree32_markov_drift n =
    ((15 / 8 : ℝ) * Real.log 3 - (49 / 16 : ℝ) * Real.log 2) +
    ((expected_remainder : ℝ) * (1 / (n : ℝ))) := by
  norm_num [tree32_markov_drift, branch_drift_bound,
    expected_remainder, rem_b1, rem_b5, rem_b3, rem_b7, rem_b15, rem_b31]
  ring

/-- Negativity of the specified weighted expression above the sufficient threshold. -/
theorem tree32_markov_drift_strictly_negative (n : ℕ) (hn : 13 ≤ n) :
    tree32_markov_drift n < 0 := by
  rw [tree32_markov_drift_eq]
  exact effective_drift_strictly_negative n hn

/-- Every positive input reaches one or lies above the threshold with negative weighted expression.
The alternatives need not be disjoint; this does not prove global reachability of one.
-/
theorem collatz_positive_global_dichotomy (n : ℕ) (hn : 0 < n) :
    (∃ m : ℕ, collatzIter m n = 1) ∨
    (13 ≤ n ∧ tree32_markov_drift n < 0) := by
  by_cases h : n ≤ 12
  · left
    exact collatz_finite_prefix_to_one n hn h
  · right
    have hn13 : 13 ≤ n := by omega
    exact ⟨hn13, tree32_markov_drift_strictly_negative n hn13⟩

#print axioms tree32_markov_drift_eq
#print axioms tree32_markov_drift_strictly_negative
#print axioms collatz_positive_global_dichotomy

end CollatzMarkovOperator
