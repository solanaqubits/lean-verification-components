/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.NumericRoundingCertificates

open NumericRoundingCertificates NumericBinaryGrid

set_option maxRecDepth 8192

-- Independent static fixtures from the SimLab provenance package.
example : checkExactMidpoint binary64 (3 / 2 ^ 1075) 1 =
    .decided ⟨false, ⟨2, by decide +kernel⟩⟩ := by decide +kernel

example : checkExactMidpoint binary64 (((2 : ℚ) ^ 53 - 1) / 2 ^ 1075) (2 ^ 52 - 1) =
    .decided ⟨false, ⟨2 ^ 52, by decide +kernel⟩⟩ := by decide +kernel

example : checkExactMidpoint binary64 (((2 : ℚ) ^ 53 + 1) / 2 ^ 1075) (2 ^ 52) =
    .decided ⟨false, ⟨2 ^ 52, by decide +kernel⟩⟩ := by decide +kernel

example : checkExactMidpoint binary64 (1 + 1 / 2 ^ 53) (1023 * 2 ^ 52) =
    .decided ⟨false, ⟨1023 * 2 ^ 52, by decide +kernel⟩⟩ := by decide +kernel

example : checkExactMidpoint binary64 (1 + 3 / 2 ^ 53) (1023 * 2 ^ 52 + 1) =
    .decided ⟨false, ⟨1023 * 2 ^ 52 + 2, by decide +kernel⟩⟩ := by decide +kernel

example : roundNearestEven binary64 (1 / 2 ^ 1075) = positiveZero := binary64_underflow_tie
example : roundNearestEven binary64 (2 ^ 1024 - 2 ^ 970) = positiveInfinity :=
  binary64_overflow_tie
example : (0 : ℚ) < 1 / 2 ^ 1075 := by decide +kernel
example : positiveZero.decode = .zero false := by decide +kernel
example : negativeZero.decode = .zero true := by decide +kernel
example : positiveInfinity.decode = .infinity false := by decide +kernel
example : positiveZero ≠ negativeZero := by decide +kernel

-- The sign transition is not lost by comparing both zeros as rational zero.
example : checkInterval binary64 (-(1 / 2 ^ 1075)) 0 = .indeterminate := by
  apply checkInterval_indeterminate_of_different
  rw [binary64_negative_underflow_tie, binary64_exact_zero]
  decide +kernel

-- Ordinary exact enclosure and the deliberately widened invalid claim.
example : checkIntervalCertificate binary64 (1 / 2) (1 / 2) halfEncoding =
    .decided halfEncoding := half_interval_certificate
example : checkIntervalCertificate binary64 0 1 halfEncoding = .indeterminate := by decide +kernel
example : checkIntervalCertificate binary64 1 0 halfEncoding = .indeterminate := by decide +kernel
example : checkIntervalCertificate binary64 0 0 negativeZero = .indeterminate := by decide +kernel

-- Near-ties, wrong adjacent-pair index, and the out-of-range infinity index are rejected.
example : checkExactMidpoint binary64 (1 / 2 ^ 1076) 0 = .indeterminate := by decide +kernel
example : checkExactMidpoint binary64 (3 / 2 ^ 1076) 0 = .indeterminate := by decide +kernel
example : checkExactMidpoint binary64 (1 / 2 ^ 1075) 1 = .indeterminate := by decide +kernel
example : checkExactMidpoint binary64 (2 ^ 1024 - 2 ^ 970) binary64Last =
    .indeterminate := by decide +kernel

-- Actual original 256-bit bounds, shared by two distinct source records.
example : historicalLower ≤ historicalUpper := historical_bounds_ordered
example : checkInterval binary64 historicalLower historicalUpper = .indeterminate :=
  historical_interval_indeterminate

-- Generic theorem interfaces retain the enclosure premise explicitly.
example (g : MagnitudeGrid) (L U x : ℚ) (f : FloatRepresentation g)
    (h : checkIntervalCertificate g L U f = .decided f) (hL : L ≤ x) (hU : x ≤ U) :
    roundNearestEven g x = f := interval_certificate_sound g L U x f h hL hU

-- The unclaimed widened interval itself is inconclusive, not merely a rejected half claim.
example : checkInterval binary64 0 1 = .indeterminate := by
  have hu : roundNearestEven binary64 1 =
      ⟨false, ⟨1023 * 2 ^ 52, by decide +kernel⟩⟩ :=
    inCell_sound binary64 1 _ (by decide +kernel)
  apply checkInterval_indeterminate_of_different
  rw [binary64_exact_zero, hu]
  decide +kernel

example : checkExactMidpoint binary64 (-(2 ^ 1024 - 2 ^ 970)) (binary64Last - 1) =
    .decided ⟨true, ⟨binary64Last, by decide +kernel⟩⟩ := by decide +kernel
