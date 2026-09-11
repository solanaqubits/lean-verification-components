import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Verification.LamzouriMollifier

set_option linter.style.header false

noncomputable section

namespace LamzouriMeasure

open LamzouriMollifier

/-- The real polynomial trial family on the unit interval. -/
def trialPoly (c x : ℝ) : ℝ := (1 - x) + c * x * (1 - x)
def trialPolySq (c x : ℝ) : ℝ := (trialPoly c x) ^ 2

def f0 (x : ℝ) : ℝ := (1 - x) ^ 2
def f1 (x : ℝ) : ℝ := 2 * x * (1 - x) ^ 2
def f2 (x : ℝ) : ℝ := x ^ 2 * (1 - x) ^ 2

theorem trialPolySq_eq_decomp (c x : ℝ) :
    trialPolySq c x = f0 x + c * f1 x + c ^ 2 * f2 x := by
  dsimp [trialPolySq, trialPoly, f0, f1, f2]
  ring

def F0 (x : ℝ) : ℝ := x - x ^ 2 + x ^ 3 / 3
def F1 (x : ℝ) : ℝ := x ^ 2 - (4 / 3 : ℝ) * x ^ 3 + x ^ 4 / 2
def F2 (x : ℝ) : ℝ := x ^ 3 / 3 - x ^ 4 / 2 + x ^ 5 / 5

theorem hasDerivAt_F0 (x : ℝ) : HasDerivAt F0 (f0 x) x := by
  have h := ((hasDerivAt_id x).sub (hasDerivAt_pow 2 x)).add
    ((hasDerivAt_pow 3 x).div_const 3)
  convert h using 1 <;> first | rfl | (dsimp [f0]; ring)

theorem hasDerivAt_F1 (x : ℝ) : HasDerivAt F1 (f1 x) x := by
  have h := ((hasDerivAt_pow 2 x).sub
    (HasDerivAt.const_mul (4 / 3) (hasDerivAt_pow 3 x))).add
    ((hasDerivAt_pow 4 x).div_const 2)
  convert h using 1 <;> first | rfl | (dsimp [f1]; ring)

theorem hasDerivAt_F2 (x : ℝ) : HasDerivAt F2 (f2 x) x := by
  have h := (((hasDerivAt_pow 3 x).div_const 3).sub
    ((hasDerivAt_pow 4 x).div_const 2)).add ((hasDerivAt_pow 5 x).div_const 5)
  convert h using 1 <;> first | rfl | (dsimp [f2]; ring)

/-- An antiderivative of the squared trial polynomial. -/
def antiDeriv (c x : ℝ) : ℝ := F0 x + c * F1 x + c ^ 2 * F2 x

theorem hasDerivAt_antiDeriv (c x : ℝ) :
    HasDerivAt (antiDeriv c) (trialPolySq c x) x := by
  rw [trialPolySq_eq_decomp]
  exact ((hasDerivAt_F0 x).add (HasDerivAt.const_mul c (hasDerivAt_F1 x))).add
    (HasDerivAt.const_mul (c ^ 2) (hasDerivAt_F2 x))

theorem antiDeriv_boundary_diff (c : ℝ) :
    antiDeriv c 1 - antiDeriv c 0 = normFunctional c := by
  dsimp [antiDeriv, F0, F1, F2, normFunctional]
  ring

theorem trialPolySq_continuous (c : ℝ) : Continuous (trialPolySq c) := by
  unfold trialPolySq trialPoly
  fun_prop

/-- The Lebesgue interval integral of the square is the prescribed denominator. -/
theorem integral_trialPolySq (c : ℝ) :
    (∫ x in (0 : ℝ)..1, trialPolySq c x) = normFunctional c := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_antiDeriv c x)
    ((trialPolySq_continuous c).intervalIntegrable 0 1)]
  exact antiDeriv_boundary_diff c

/-- Uniform positive lower bound for this scalar quadratic family.
This does not assert coercivity of a Hilbert-space operator. -/
theorem norm_functional_coercive (c : ℝ) :
    (1 / 8 : ℝ) ≤ normFunctional c := by
  rw [norm_functional_eq_sos]
  nlinarith [sq_nonneg (c + (5 / 2 : ℝ))]

theorem norm_functional_at_min_point : normFunctional (-5 / 2) = 1 / 8 := by
  norm_num [normFunctional]

/-- The minimum value is attained at exactly one parameter. -/
theorem norm_functional_min_iff (c : ℝ) :
    normFunctional c = 1 / 8 ↔ c = -5 / 2 := by
  rw [norm_functional_eq_sos]
  constructor
  · intro h
    nlinarith [sq_nonneg (c + (5 / 2 : ℝ))]
  · intro h
    rw [h]
    norm_num

#print axioms integral_trialPolySq
#print axioms norm_functional_coercive
#print axioms norm_functional_min_iff

end LamzouriMeasure
