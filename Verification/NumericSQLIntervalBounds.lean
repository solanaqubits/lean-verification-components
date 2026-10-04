/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.NumericRealRounding
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Rational enclosures of a conditional SQL target

The target is sqrt(hbar / (mass * frequency)), not the optimization gap
A / I + B * I - 2 * sqrt(A * B). Input localization is an explicit hypothesis.
Rational square checks justify real root enclosures; no physical calibration,
Python implementation, JSON parser, or hash function is verified here.
-/

namespace NumericSQLIntervalBounds

structure RatInterval where
  lo : ℚ
  hi : ℚ
  h_le : lo ≤ hi
  deriving DecidableEq

def containsReal (I : RatInterval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/-- Positive intervals admit endpoint multiplication. -/
def mulInterval (I J : RatInterval) (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo) :
    RatInterval :=
  ⟨I.lo * J.lo, I.hi * J.hi,
    mul_le_mul I.h_le J.h_le hJ (hI.trans I.h_le)⟩

theorem rat_mul_interval_sound (I J : RatInterval) (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo)
    (x y : ℝ) (hx : containsReal I x) (hy : containsReal J y) :
    containsReal (mulInterval I J hI hJ) (x * y) := by
  have hi : (0 : ℝ) ≤ I.lo := by exact_mod_cast hI
  have hj : (0 : ℝ) ≤ J.lo := by exact_mod_cast hJ
  dsimp [containsReal, mulInterval] at *
  push_cast
  exact ⟨mul_le_mul hx.1 hy.1 hj (hi.trans hx.1),
    mul_le_mul hx.2 hy.2 (hj.trans hy.1) (hi.trans (hx.1.trans hx.2))⟩

/-- Numerator nonnegative and denominator bounded strictly away from zero. -/
def divInterval (I J : RatInterval) (hI : 0 ≤ I.lo) (hJ : 0 < J.lo) :
    RatInterval :=
  ⟨I.lo / J.hi, I.hi / J.lo,
    div_le_div₀ (hI.trans I.h_le) I.h_le hJ J.h_le⟩

theorem rat_div_interval_sound (I J : RatInterval) (hI : 0 ≤ I.lo) (hJ : 0 < J.lo)
    (x y : ℝ) (hx : containsReal I x) (hy : containsReal J y) :
    containsReal (divInterval I J hI hJ) (x / y) := by
  have hi : (0 : ℝ) ≤ I.lo := by exact_mod_cast hI
  have hj : (0 : ℝ) < J.lo := by exact_mod_cast hJ
  dsimp [containsReal, divInterval] at *
  push_cast
  exact ⟨div_le_div₀ (hi.trans hx.1) hx.1 (hj.trans_le hy.1) hy.2,
    div_le_div₀ (hi.trans (hx.1.trans hx.2)) hx.2 hj hy.1⟩

/-- This certificate requires nonnegative endpoints; squaring does not fix the upper sign. -/
theorem rat_sqrt_interval_sound (L U : ℚ) (y : ℝ)
    (hL : 0 ≤ L) (hU : 0 ≤ U)
    (hlo : (L : ℝ) ^ 2 ≤ y) (hhi : y ≤ (U : ℝ) ^ 2) :
    (L : ℝ) ≤ Real.sqrt y ∧ Real.sqrt y ≤ (U : ℝ) := by
  have hl : (0 : ℝ) ≤ L := by exact_mod_cast hL
  have hu : (0 : ℝ) ≤ U := by exact_mod_cast hU
  have hy : 0 ≤ y := (sq_nonneg _).trans hlo
  have hs := Real.sq_sqrt hy
  have hn := Real.sqrt_nonneg y
  constructor <;> nlinarith

/-- A fully rational certificate for the square-root image of an interval. -/
def SqrtWitness (I R : RatInterval) : Prop :=
  0 ≤ R.lo ∧ 0 ≤ R.hi ∧ R.lo ^ 2 ≤ I.lo ∧ I.hi ≤ R.hi ^ 2

instance (I R : RatInterval) : Decidable (SqrtWitness I R) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def checkSqrtWitness (I R : RatInterval) : Bool := decide (SqrtWitness I R)

theorem sqrt_witness_sound (I R : RatInterval) (y : ℝ)
    (hy : containsReal I y) (hw : SqrtWitness I R) : containsReal R (Real.sqrt y) := by
  have hlo : (R.lo : ℝ) ^ 2 ≤ (I.lo : ℝ) := by exact_mod_cast hw.2.2.1
  have hhi : (I.hi : ℝ) ≤ (R.hi : ℝ) ^ 2 := by exact_mod_cast hw.2.2.2
  exact rat_sqrt_interval_sound R.lo R.hi y hw.1 hw.2.1
    (hlo.trans hy.1) (hy.2.trans hhi)

theorem check_sqrt_witness_sound (I R : RatInterval) (y : ℝ)
    (hy : containsReal I y) (hw : checkSqrtWitness I R = true) :
    containsReal R (Real.sqrt y) :=
  sqrt_witness_sound I R y hy (of_decide_eq_true hw)

noncomputable def sqlRadicand (hbar m omega : ℝ) : ℝ := hbar / (m * omega)
noncomputable def sqlTarget (hbar m omega : ℝ) : ℝ :=
  Real.sqrt (sqlRadicand hbar m omega)

/-- Explicit extremal radicand bounds: hlo/(mhi*whi), hhi/(mlo*wlo). -/
def radicandInterval (H M W : RatInterval)
    (hh : 0 < H.lo) (hm : 0 < M.lo) (hw : 0 < W.lo) : RatInterval :=
  divInterval H (mulInterval M W hm.le hw.le) hh.le (mul_pos hm hw)

theorem sql_radicand_enclosure (H M W : RatInterval)
    (hh : 0 < H.lo) (hm : 0 < M.lo) (hw : 0 < W.lo)
    (hbar m omega : ℝ) (hH : containsReal H hbar)
    (hM : containsReal M m) (hW : containsReal W omega) :
    containsReal (radicandInterval H M W hh hm hw) (sqlRadicand hbar m omega) :=
  rat_div_interval_sound H (mulInterval M W hm.le hw.le) hh.le (mul_pos hm hw)
    hbar (m * omega) hH (rat_mul_interval_sound M W hm.le hw.le m omega hM hW)

/-- The output interval is supplied explicitly and checked by rational inequalities. -/
theorem sql_interval_enclosure (H M W R : RatInterval)
    (hh : 0 < H.lo) (hm : 0 < M.lo) (hw : 0 < W.lo)
    (hbar m omega : ℝ) (hH : containsReal H hbar)
    (hM : containsReal M m) (hW : containsReal W omega)
    (hcert : checkSqrtWitness (radicandInterval H M W hh hm hw) R = true) :
    containsReal R (sqlTarget hbar m omega) :=
  check_sqrt_witness_sound _ R _
    (sql_radicand_enclosure H M W hh hm hw hbar m omega hH hM hW) hcert

/-- A computable coarse enclosure exists without invoking density or choice. -/
def coarseRootInterval (I : RatInterval) (hI : 0 ≤ I.lo) : RatInterval :=
  ⟨0, I.hi + 1, by linarith [I.h_le]⟩

theorem coarse_root_witness (I : RatInterval) (hI : 0 ≤ I.lo) :
    SqrtWitness I (coarseRootInterval I hI) := by
  have hh := I.h_le
  dsimp [SqrtWitness, coarseRootInterval]
  refine ⟨le_refl _, by linarith, by simpa, ?_⟩
  nlinarith [sq_nonneg I.hi]

/-- Smaller radicand intervals retain any already checked root enclosure. -/
theorem sqrt_witness_restrict (I J R : RatInterval)
    (hlo : I.lo ≤ J.lo) (hhi : J.hi ≤ I.hi) (hw : SqrtWitness I R) :
    SqrtWitness J R :=
  ⟨hw.1, hw.2.1, hw.2.2.1.trans hlo, hhi.trans hw.2.2.2⟩

/-- End-to-end theorem for the prescribed real expression and rational certificates. -/
theorem sql_rounding_soundness (g : NumericRoundingCertificates.MagnitudeGrid)
    (H M W R : RatInterval) (hh : 0 < H.lo) (hm : 0 < M.lo) (hw : 0 < W.lo)
    (hbar m omega : ℝ) (hH : containsReal H hbar)
    (hM : containsReal M m) (hW : containsReal W omega)
    (hcert : checkSqrtWitness (radicandInterval H M W hh hm hw) R = true)
    (f : NumericRoundingCertificates.FloatRepresentation g)
    (hround : NumericRoundingCertificates.checkIntervalCertificate g R.lo R.hi f =
      .decided f) : NumericRealRounding.realRound g (sqlTarget hbar m omega) = f := by
  have he := sql_interval_enclosure H M W R hh hm hw hbar m omega hH hM hW hcert
  exact NumericRealRounding.interval_certificate_real_sound g R.lo R.hi _ f hround he.1 he.2

/-- Explicit coarse witness, useful as a total fallback but not necessarily decisive. -/
theorem sql_coarse_enclosure (H M W : RatInterval)
    (hh : 0 < H.lo) (hm : 0 < M.lo) (hw : 0 < W.lo)
    (hbar m omega : ℝ) (hH : containsReal H hbar)
    (hM : containsReal M m) (hW : containsReal W omega) :
    ∃ R : RatInterval, SqrtWitness (radicandInterval H M W hh hm hw) R ∧
      containsReal R (sqlTarget hbar m omega) := by
  let I := radicandInterval H M W hh hm hw
  have hp : 0 ≤ I.lo := by
    change 0 ≤ H.lo / (M.hi * W.hi)
    exact div_nonneg hh.le (mul_nonneg (hm.le.trans M.h_le) (hw.le.trans W.h_le))
  refine ⟨coarseRootInterval I hp, coarse_root_witness I hp, ?_⟩
  exact sqrt_witness_sound I _ _
    (sql_radicand_enclosure H M W hh hm hw hbar m omega hH hM hW)
    (coarse_root_witness I hp)

structure NumericSQLIntervalBoundsSuite : Prop where
  sqrt_bounds : ∀ L U : ℚ, ∀ y : ℝ, 0 ≤ L → 0 ≤ U →
    (L : ℝ) ^ 2 ≤ y → y ≤ (U : ℝ) ^ 2 →
    (L : ℝ) ≤ Real.sqrt y ∧ Real.sqrt y ≤ (U : ℝ)
  root_checker : ∀ I R : RatInterval, ∀ y : ℝ, containsReal I y →
    checkSqrtWitness I R = true → containsReal R (Real.sqrt y)
  enclosure : ∀ H M W R : RatInterval, ∀ hh : 0 < H.lo, ∀ hm : 0 < M.lo,
    ∀ hw : 0 < W.lo, ∀ hbar m omega : ℝ, containsReal H hbar → containsReal M m →
    containsReal W omega → checkSqrtWitness (radicandInterval H M W hh hm hw) R = true →
    containsReal R (sqlTarget hbar m omega)
  rounding : ∀ g : NumericRoundingCertificates.MagnitudeGrid, ∀ H M W R : RatInterval,
    ∀ hh : 0 < H.lo, ∀ hm : 0 < M.lo, ∀ hw : 0 < W.lo, ∀ hbar m omega : ℝ,
    containsReal H hbar → containsReal M m → containsReal W omega →
    checkSqrtWitness (radicandInterval H M W hh hm hw) R = true →
    ∀ f : NumericRoundingCertificates.FloatRepresentation g,
    NumericRoundingCertificates.checkIntervalCertificate g R.lo R.hi f = .decided f →
    NumericRealRounding.realRound g (sqlTarget hbar m omega) = f

theorem numeric_sql_interval_master_suite : NumericSQLIntervalBoundsSuite := {
  sqrt_bounds := rat_sqrt_interval_sound
  root_checker := check_sqrt_witness_sound
  enclosure := sql_interval_enclosure
  rounding := sql_rounding_soundness
}

end NumericSQLIntervalBounds
