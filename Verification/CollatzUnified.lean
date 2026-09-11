import Verification.CollatzBase
import Verification.CollatzAttractor
import Verification.CollatzCycles
import Verification.CollatzParity
import Verification.CollatzDyadicContract
import Verification.CollatzAverageDrift
import Verification.CollatzBranchSeven
import Verification.CollatzBranchFifteen
import Verification.CollatzDyadicTree32
import Verification.CollatzGeometricDrift
import Verification.CollatzLogPotential
import Verification.CollatzRemainderBound
import Verification.CollatzEffectiveDrift
import Verification.CollatzMarkovOperator

set_option linter.style.header false

namespace CollatzUnified

open CollatzBase CollatzCycles CollatzDyadicTree32 CollatzGeometricDrift
open CollatzRemainderBound CollatzEffectiveDrift CollatzMarkovOperator

/-- A proposition collecting selected verified guarantees from the fourteen-stage development.
The weighted expression is not yet identified with a transition kernel's conditional drift.
-/
structure CollatzFormalSuite : Prop where
  /-- No positive one-step returns. -/
  h_no_p1 : ∀ n > 0, ¬ IsPeriodic 1 n
  /-- No positive two-step returns. -/
  h_no_p2 : ∀ n > 0, ¬ IsPeriodic 2 n
  /-- Every input in the finite positive prefix reaches one. -/
  h_prefix : ∀ n, 1 ≤ n → n ≤ 12 → ∃ m : ℕ, collatzIter m n = 1
  /-- Coverage of odd inputs by the six residue branches. -/
  h_partition : ∀ n, n % 2 = 1 →
    n % 8 = 1 ∨ n % 8 = 5 ∨ n % 8 = 3 ∨ n % 16 = 7 ∨ n % 32 = 15 ∨ n % 32 = 31
  /-- The exact integer inequality underlying the geometric coefficient bound. -/
  h_geom_int : (3 : ℕ) ^ 30 < (2 : ℕ) ^ 49
  /-- The exact weighted remainder sum. -/
  h_rem_sum : expected_remainder = 40 / 81
  /-- Negativity of the specified weighted scalar expression above the threshold. -/
  h_drift_neg : ∀ n, 13 ≤ n → tree32_markov_drift n < 0
  /-- A nonexclusive disjunction, not a global reachability theorem. -/
  h_dichotomy : ∀ n > 0,
    (∃ m : ℕ, collatzIter m n = 1) ∨ (13 ≤ n ∧ tree32_markov_drift n < 0)

/-- Assemble the proved guarantees without additional assumptions or custom axioms.
This theorem does not assert the Collatz conjecture or almost-sure absorption of a Markov model.
-/
theorem collatz_master_verification_suite : CollatzFormalSuite := {
  h_no_p1 := no_period_one
  h_no_p2 := no_period_two
  h_prefix := collatz_finite_prefix_to_one
  h_partition := odd_dyadic_complete_partition_32
  h_geom_int := collatz_tree32_integer_drift_strict_contraction
  h_rem_sum := expected_remainder_eq
  h_drift_neg := tree32_markov_drift_strictly_negative
  h_dichotomy := collatz_positive_global_dichotomy
}

#print axioms collatz_master_verification_suite

end CollatzUnified
