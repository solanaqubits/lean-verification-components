import Verification.NumericSQLGapBounds

open NumericSQLGapBounds NumericSQLIntervalBounds NumericRoundingCertificates NumericRealRounding

set_option maxRecDepth 8192

def sqrtTwoGapBounds : RatInterval :=
  ⟨1709679290002018430137083 / 1208925819614629174706176,
   1709679290002018430137084 / 1208925819614629174706176, by decide +kernel⟩
def gapEncoding : FloatRepresentation binary64 :=
  ⟨false, ⟨4595349584587014967, by decide +kernel⟩⟩

-- Irrational G = 3 - 2*sqrt(2), with root and affine endpoints kernel checked.
example : realRound binary64 (sqlNoiseGap 2 1 1) = gapEncoding := by
  simpa using sql_gap_affine_rounding_soundness binary64 2 1 1 sqrtTwoGapBounds
    (by decide +kernel) gapEncoding (by decide +kernel)

-- The exact decimal value 0.1 is rational 1/10, not its binary64 approximation.
def decimalRootBounds : RatInterval := ⟨9 / 100, 11 / 100, by decide +kernel⟩
example : checkSqrtWitness (productInterval (1 / 10) (1 / 10)) decimalRootBounds = true := by
  decide +kernel
example : checkIntervalCertificate binary64
    (gapInterval (1 / 10) (1 / 10) 1 decimalRootBounds).lo
    (gapInterval (1 / 10) (1 / 10) 1 decimalRootBounds).hi positiveZero = .indeterminate := by
  decide +kernel
-- Separate exact-zero evidence leaves the preceding interval inconclusive.
example : realRound binary64 (sqlNoiseGap (1 / 10) (1 / 10) 1) = positiveZero := by
  apply sql_gap_exact_zero_rounding <;> norm_num

example (A B I : ℝ) (ha : 0 < A) (hb : 0 < B) (hi : 0 < I)
    (hne : A ≠ B * I ^ 2) : 0 < sqlNoiseGap A B I :=
  lt_of_le_of_ne (sql_gap_nonneg A B I ha hb hi)
    (fun h => hne ((sql_gap_zero_iff A B I ha hb hi).mp h.symm))

-- Ordinary exact positive gap.
def unitRoot : RatInterval := ⟨1, 1, by decide⟩
example : realRound binary64 (sqlNoiseGap 1 1 2) = halfEncoding := by
  simpa using sql_gap_affine_rounding_soundness binary64 1 1 2 unitRoot
    (by decide +kernel) halfEncoding (by decide +kernel)

-- Incorrect root witnesses cannot enter the composed theorem.
example : checkSqrtWitness (productInterval 2 1) unitRoot = false := by decide +kernel
example : checkSqrtWitness (productInterval 1 1) ⟨-1, -1, by decide⟩ = false := by
  decide +kernel
-- A claimed negative zero is rejected even for exact zero endpoints.
example : checkIntervalCertificate binary64 0 0 negativeZero = .indeterminate := by
  decide +kernel
-- Positivity is essential to the balance criterion, unlike the affine identity.
example : (1 : ℝ) = 1 * (-1) ^ 2 ∧ sqlNoiseGap 1 1 (-1) ≠ 0 := by
  norm_num [sqlNoiseGap]

-- Existing historical interval outcome is not superseded by new proofs.
example : checkInterval binary64 historicalLower historicalUpper = .indeterminate :=
  historical_interval_indeterminate

-- A strictly positive gap can round to +0 at the underflow midpoint.
-- This is a tie, distinct from the exact-zero theorem above.
def smallRoot : RatInterval := ⟨1 / 2 ^ 1074, 1 / 2 ^ 1074, le_refl _⟩
example : (gapInterval (1 / 2 ^ 1074) (1 / 2 ^ 1074) 2 smallRoot).lo = 1 / 2 ^ 1075 := by
  decide +kernel
example : (gapInterval (1 / 2 ^ 1074) (1 / 2 ^ 1074) 2 smallRoot).hi = 1 / 2 ^ 1075 := by
  decide +kernel
example : realRound binary64
    (sqlNoiseGap ((1 / 2 ^ 1074 : ℚ) : ℝ) ((1 / 2 ^ 1074 : ℚ) : ℝ) 2) = positiveZero := by
  simpa only [Rat.cast_ofNat] using sql_gap_affine_rounding_soundness binary64 (1 / 2 ^ 1074) (1 / 2 ^ 1074) 2
    smallRoot (by decide +kernel) positiveZero (by decide +kernel)
