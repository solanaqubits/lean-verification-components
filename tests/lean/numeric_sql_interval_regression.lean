import Verification.NumericSQLIntervalBounds

open NumericSQLIntervalBounds NumericRoundingCertificates NumericRealRounding

set_option maxRecDepth 8192

def pointInterval (x : ℚ) : RatInterval := ⟨x, x, le_refl _⟩
def sqrtTwoBounds : RatInterval :=
  ⟨1709679290002018430137083 / 1208925819614629174706176,
   1709679290002018430137084 / 1208925819614629174706176, by decide +kernel⟩
def sqrtTwoEncoding : FloatRepresentation binary64 :=
  ⟨false, ⟨4609047870845172685, by decide +kernel⟩⟩

-- Both the irrational enclosure and its final binary64 code are kernel checked.
example : checkSqrtWitness (pointInterval 2) sqrtTwoBounds = true := by decide +kernel
example : checkIntervalCertificate binary64 sqrtTwoBounds.lo sqrtTwoBounds.hi
    sqrtTwoEncoding = .decided sqrtTwoEncoding := by decide +kernel
example : realRound binary64 (sqlTarget 2 1 1) = sqrtTwoEncoding := by
  apply sql_rounding_soundness binary64 (pointInterval 2) (pointInterval 1) (pointInterval 1)
    sqrtTwoBounds (by decide) (by decide) (by decide) 2 1 1
    (by norm_num [containsReal, pointInterval]) (by norm_num [containsReal, pointInterval])
    (by norm_num [containsReal, pointInterval])
  · decide +kernel
  · decide +kernel

-- A positive interval of possible parameters, not only pointInterval inputs.
def hBounds : RatInterval := ⟨4, 9, by decide⟩
def mBounds : RatInterval := ⟨1, 2, by decide⟩
def wBounds : RatInterval := ⟨1, 2, by decide⟩
def rootBounds : RatInterval := ⟨1, 3, by decide⟩
example (h m w : ℝ) (hh : containsReal hBounds h)
    (hm : containsReal mBounds m) (hw : containsReal wBounds w) :
    containsReal rootBounds (sqlTarget h m w) := by
  exact sql_interval_enclosure hBounds mBounds wBounds rootBounds
    (by decide) (by decide) (by decide) h m w hh hm hw (by decide +kernel)

-- Square inequalities alone cannot justify a negative upper root bound.
example : checkSqrtWitness (pointInterval 1) (pointInterval (-1)) = false := by decide +kernel
example : checkSqrtWitness (pointInterval 2) (pointInterval 1) = false := by decide +kernel
example : checkSqrtWitness (pointInterval 2) (pointInterval 2) = false := by decide +kernel
example : checkSqrtWitness (pointInterval 0) (pointInterval 0) = true := by decide +kernel

-- A true broad enclosure need not determine one rounded result.
example : checkIntervalCertificate binary64 1 2 sqrtTwoEncoding = .indeterminate := by
  decide +kernel

-- Cast compatibility preserves existing signed-zero and midpoint behavior.
example : realRound binary64 ((-(1 / 2 ^ 1075) : ℚ) : ℝ) = negativeZero := by
  rw [realRound_ratCast]
  exact binary64_negative_underflow_tie
example : realRound binary64 ((1 / 2 : ℚ) : ℝ) = halfEncoding := by
  rw [realRound_ratCast]
  exact interval_certificate_sound binary64 (1 / 2) (1 / 2) (1 / 2) halfEncoding
    half_interval_certificate (le_refl _) (le_refl _)
example : checkInterval binary64 historicalLower historicalUpper = .indeterminate :=
  historical_interval_indeterminate
