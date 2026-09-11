import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option linter.style.header false
noncomputable section

namespace Collatz2AdicErgodic

/-- Numerical cylinder weight, without constructing a measure space. -/
def cylinderMeasure (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

theorem cylinder_measure_pos (k : ℕ) : 0 < cylinderMeasure k := by
  dsimp [cylinderMeasure]
  positivity

theorem cylinder_measure_halving (k : ℕ) :
    cylinderMeasure (k + 1) + cylinderMeasure (k + 1) = cylinderMeasure k := by
  dsimp [cylinderMeasure]
  rw [pow_succ]
  ring

def syracuse (x : ℤ) : ℤ := if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

theorem syracuse_even_branch (y : ℤ) : syracuse (2 * y) = y := by
  dsimp [syracuse]
  have hm : (2 * y) % 2 = 0 := by omega
  rw [if_pos hm]
  omega

/-- Branch evaluation, not surjectivity of the odd branch on integers. -/
theorem syracuse_odd_branch (y : ℤ) : syracuse (2 * y - 1) = 3 * y - 1 := by
  dsimp [syracuse]
  have hm : (2 * y - 1) % 2 ≠ 0 := by omega
  rw [if_neg hm]
  omega

def domainMod4 : Finset ℤ := {0, 1, 2, 3}
def domainMod8 : Finset ℤ := {0, 1, 2, 3, 4, 5, 6, 7}

theorem fiber_mod2_zero :
    (domainMod4.filter (fun x => syracuse x % 2 = 0)) = {0, 1} := by decide

theorem fiber_mod2_one :
    (domainMod4.filter (fun x => syracuse x % 2 = 1)) = {2, 3} := by decide

theorem fiber_mod4_zero :
    (domainMod8.filter (fun x => syracuse x % 4 = 0)) = {0, 5} := by decide

theorem fiber_mod4_one :
    (domainMod8.filter (fun x => syracuse x % 4 = 1)) = {2, 3} := by decide

theorem fiber_mod4_two :
    (domainMod8.filter (fun x => syracuse x % 4 = 2)) = {1, 4} := by decide

theorem fiber_mod4_three :
    (domainMod8.filter (fun x => syracuse x % 4 = 3)) = {6, 7} := by decide

theorem card_fiber_mod2_zero :
    (domainMod4.filter (fun x => syracuse x % 2 = 0)).card = 2 := by decide

theorem measure_preserving_rank1_zero :
    ((domainMod4.filter (fun x => syracuse x % 2 = 0)).card : ℝ) /
      (domainMod4.card : ℝ) = cylinderMeasure 1 := by
  rw [card_fiber_mod2_zero]
  have ht : domainMod4.card = 4 := by decide
  rw [ht]
  norm_num [cylinderMeasure]

theorem card_fiber_mod2_one :
    (domainMod4.filter (fun x => syracuse x % 2 = 1)).card = 2 := by decide

theorem measure_preserving_rank1_one :
    ((domainMod4.filter (fun x => syracuse x % 2 = 1)).card : ℝ) /
      (domainMod4.card : ℝ) = cylinderMeasure 1 := by
  rw [card_fiber_mod2_one]
  have ht : domainMod4.card = 4 := by decide
  rw [ht]
  norm_num [cylinderMeasure]

theorem card_fibers_mod4_all_two :
    (domainMod8.filter (fun x => syracuse x % 4 = 0)).card = 2 ∧
    (domainMod8.filter (fun x => syracuse x % 4 = 1)).card = 2 ∧
    (domainMod8.filter (fun x => syracuse x % 4 = 2)).card = 2 ∧
    (domainMod8.filter (fun x => syracuse x % 4 = 3)).card = 2 := by decide

theorem measure_preserving_rank2 (r : ℤ) (hr : r ∈ ({0, 1, 2, 3} : Finset ℤ)) :
    ((domainMod8.filter (fun x => syracuse x % 4 = r)).card : ℝ) /
      (domainMod8.card : ℝ) = cylinderMeasure 2 := by
  have ht : domainMod8.card = 8 := by decide
  have hc : (domainMod8.filter (fun x => syracuse x % 4 = r)).card = 2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  rw [hc, ht]
  norm_num [cylinderMeasure]

structure Collatz2AdicErgodicFormalSuite : Prop where
  h_meas_pos : ∀ k, 0 < cylinderMeasure k
  h_meas_halving : ∀ k, cylinderMeasure (k + 1) + cylinderMeasure (k + 1) = cylinderMeasure k
  h_even_branch : ∀ y, syracuse (2 * y) = y
  h_odd_branch : ∀ y, syracuse (2 * y - 1) = 3 * y - 1
  h_fiber_r1_zero : (domainMod4.filter (fun x => syracuse x % 2 = 0)).card = 2
  h_fiber_r1_one : (domainMod4.filter (fun x => syracuse x % 2 = 1)).card = 2
  h_meas_r1_zero : ((domainMod4.filter (fun x => syracuse x % 2 = 0)).card : ℝ) /
    (domainMod4.card : ℝ) = cylinderMeasure 1
  h_meas_r1_one : ((domainMod4.filter (fun x => syracuse x % 2 = 1)).card : ℝ) /
    (domainMod4.card : ℝ) = cylinderMeasure 1
  h_fibers_r2_card : (domainMod8.filter (fun x => syracuse x % 4 = 0)).card = 2 ∧
    (domainMod8.filter (fun x => syracuse x % 4 = 1)).card = 2 ∧
    (domainMod8.filter (fun x => syracuse x % 4 = 2)).card = 2 ∧
    (domainMod8.filter (fun x => syracuse x % 4 = 3)).card = 2
  h_meas_r2 : ∀ r, r ∈ ({0, 1, 2, 3} : Finset ℤ) →
    ((domainMod8.filter (fun x => syracuse x % 4 = r)).card : ℝ) /
      (domainMod8.card : ℝ) = cylinderMeasure 2

theorem collatz_2adic_ergodic_master_verification_suite : Collatz2AdicErgodicFormalSuite := {
  h_meas_pos := cylinder_measure_pos
  h_meas_halving := cylinder_measure_halving
  h_even_branch := syracuse_even_branch
  h_odd_branch := syracuse_odd_branch
  h_fiber_r1_zero := card_fiber_mod2_zero
  h_fiber_r1_one := card_fiber_mod2_one
  h_meas_r1_zero := measure_preserving_rank1_zero
  h_meas_r1_one := measure_preserving_rank1_one
  h_fibers_r2_card := card_fibers_mod4_all_two
  h_meas_r2 := measure_preserving_rank2
}

#print axioms collatz_2adic_ergodic_master_verification_suite

end Collatz2AdicErgodic
