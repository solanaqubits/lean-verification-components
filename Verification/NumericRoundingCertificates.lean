/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.NumericBinaryGrid
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Tactic.Linarith

/-!
# Exact rational rounding certificates

A finite magnitude grid includes zero and a virtual overflow endpoint. Codes
preserve signed zero and infinity separately from rational values. Exact rational
zero is canonical positive zero. Theorems concern this specification, not Python,
JSON parsing, hashing, or the construction of SQL enclosures.
-/

namespace NumericRoundingCertificates

/-- Strictly increasing magnitudes; `last` is the virtual overflow endpoint. -/
structure MagnitudeGrid where
  last : ℕ
  last_pos : 0 < last
  value : ℕ → ℚ
  value_zero : value 0 = 0
  increasing : StrictMono value

/-- Exact rational midpoint. -/
def midpoint (a b : ℚ) : ℚ := (a + b) / 2

/-- Boundary between consecutive magnitude codes. -/
def boundary (g : MagnitudeGrid) (j : ℕ) : ℚ := midpoint (g.value j) (g.value (j + 1))

/-- At a boundary the upper code wins exactly when the lower code is odd. -/
def crossed (g : MagnitudeGrid) (x : ℚ) (j : ℕ) : Prop :=
  boundary g j < x ∨ boundary g j = x ∧ j % 2 = 1

instance (g : MagnitudeGrid) (x : ℚ) (j : ℕ) : Decidable (crossed g x j) :=
  inferInstanceAs (Decidable (_ ∨ _ ∧ _))

/-- Number of crossed boundaries, including the transition to infinity. -/
def magnitudeCode (g : MagnitudeGrid) (x : ℚ) : ℕ :=
  ((Finset.range g.last).filter (crossed g x)).card

theorem magnitudeCode_le (g : MagnitudeGrid) (x : ℚ) : magnitudeCode g x ≤ g.last := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

theorem magnitudeCode_monotone (g : MagnitudeGrid) : Monotone (magnitudeCode g) := by
  intro x y hxy
  apply Finset.card_le_card
  intro j hj
  obtain ⟨hj, hc⟩ := Finset.mem_filter.mp hj
  refine Finset.mem_filter.mpr ⟨hj, ?_⟩
  rcases hc with h | ⟨h, hp⟩
  · exact Or.inl (lt_of_lt_of_le h hxy)
  · rcases lt_or_eq_of_le hxy with hxy | hxy
    · exact Or.inl (h.trans_lt hxy)
    · exact Or.inr ⟨h.trans hxy, hp⟩

/-- Finite encoding: magnitude zero and last denote signed zero and infinity. -/
structure FloatRepresentation (g : MagnitudeGrid) where
  negative : Bool
  magnitude : Fin (g.last + 1)
  deriving DecidableEq

/-- Interpretation keeps zero signs and infinities outside the rational field. -/
inductive FloatValue where
  | zero (negative : Bool)
  | finite (value : ℚ)
  | infinity (negative : Bool)
  deriving DecidableEq, Repr

/-- Decode the tagged result; the last grid value is virtual, never finite infinity. -/
def FloatRepresentation.decode {g : MagnitudeGrid} (f : FloatRepresentation g) : FloatValue :=
  if f.magnitude.val = 0 then .zero f.negative
  else if f.magnitude.val = g.last then .infinity f.negative
  else .finite (if f.negative then -g.value f.magnitude.val else g.value f.magnitude.val)

/-- Nearest-even rounding, with exact rational zero mapped to positive zero. -/
def roundNearestEven (g : MagnitudeGrid) (x : ℚ) : FloatRepresentation g :=
  ⟨decide (x < 0), ⟨magnitudeCode g |x|, Nat.lt_succ_of_le (magnitudeCode_le g |x|)⟩⟩

/-- Convexity of rounding fibers, including signed zero and overflow encodings. -/
theorem interval_rounding_soundness (g : MagnitudeGrid) (L U x : ℚ)
    (f : FloatRepresentation g) (hL : L ≤ x) (hU : x ≤ U)
    (hfL : roundNearestEven g L = f) (hfU : roundNearestEven g U = f) :
    roundNearestEven g x = f := by
  have he := hfL.trans hfU.symm
  have hs : decide (L < 0) = decide (U < 0) := congrArg FloatRepresentation.negative he
  have hm : magnitudeCode g |L| = magnitudeCode g |U| :=
    congrArg (fun f => f.magnitude.val) he
  have hc : magnitudeCode g |x| = magnitudeCode g |L| := by
    by_cases hLn : L < 0
    · have hUn : U < 0 := of_decide_eq_true (by simpa [hLn] using hs.symm)
      have hxn : x < 0 := lt_of_le_of_lt hU hUn
      rw [abs_of_neg hLn, abs_of_neg hUn] at hm
      rw [abs_of_neg hxn, abs_of_neg hLn]
      apply le_antisymm
      · exact magnitudeCode_monotone g (neg_le_neg hL)
      · rw [hm]
        exact magnitudeCode_monotone g (neg_le_neg hU)
    · have hLp : 0 ≤ L := le_of_not_gt hLn
      have hxp : 0 ≤ x := hLp.trans hL
      have hUp : 0 ≤ U := hxp.trans hU
      rw [abs_of_nonneg hLp, abs_of_nonneg hUp] at hm
      rw [abs_of_nonneg hxp, abs_of_nonneg hLp]
      apply le_antisymm
      · rw [hm]
        exact magnitudeCode_monotone g hU
      · exact magnitudeCode_monotone g hL
  have hsign : decide (x < 0) = decide (L < 0) := by
    by_cases hLn : L < 0
    · have hUn : U < 0 := of_decide_eq_true (by simpa [hLn] using hs.symm)
      simp [hLn, lt_of_le_of_lt hU hUn]
    · simp [hLn, not_lt.mpr ((le_of_not_gt hLn).trans hL)]
  have hxL : roundNearestEven g x = roundNearestEven g L := by
    unfold roundNearestEven
    rw [hsign]
    congr 1
    exact Fin.ext hc
  exact hxL.trans hfL

/-- Inability to conclude is distinct from a rounded representation. -/
inductive CertificateVerdict (g : MagnitudeGrid) where
  | decided (result : FloatRepresentation g)
  | indeterminate
  deriving DecidableEq

/-- Reversed bounds are rejected conservatively. -/
def checkInterval (g : MagnitudeGrid) (L U : ℚ) : CertificateVerdict g :=
  if L ≤ U ∧ roundNearestEven g L = roundNearestEven g U then
    .decided (roundNearestEven g L)
  else .indeterminate

theorem checkInterval_sound (g : MagnitudeGrid) (L U x : ℚ) (f : FloatRepresentation g)
    (h : checkInterval g L U = .decided f) (hL : L ≤ x) (hU : x ≤ U) :
    roundNearestEven g x = f := by
  unfold checkInterval at h
  split_ifs at h with hc
  · have hf : roundNearestEven g L = f := CertificateVerdict.decided.inj h
    exact interval_rounding_soundness g L U x f hL hU hf (hc.2.symm.trans hf)

theorem checkInterval_indeterminate_of_different (g : MagnitudeGrid) (L U : ℚ)
    (h : roundNearestEven g L ≠ roundNearestEven g U) :
    checkInterval g L U = .indeterminate := by
  simp [checkInterval, h]

/-- Grid boundaries are strictly ordered; this follows from the decoded values. -/
theorem boundary_strictMono (g : MagnitudeGrid) : StrictMono (boundary g) := by
  intro i j hij
  have h₁ := g.increasing hij
  have h₂ := g.increasing (Nat.add_lt_add_right hij 1)
  dsimp [boundary, midpoint]
  linarith

theorem boundary_pos (g : MagnitudeGrid) (j : ℕ) : 0 < boundary g j := by
  have h₀ : 0 ≤ g.value j := by
    rw [← g.value_zero]
    exact g.increasing.monotone (Nat.zero_le j)
  have h₁ : 0 < g.value (j + 1) := by
    rw [← g.value_zero]
    exact g.increasing (Nat.zero_lt_succ j)
  dsimp [boundary, midpoint]
  linarith

/-- A local boundary witness determines the global count without enumerating the grid. -/
theorem magnitudeCode_eq_of_cut (g : MagnitudeGrid) (x : ℚ) (k : ℕ)
    (hk : k ≤ g.last) (hcut : ∀ j < g.last, crossed g x j ↔ j < k) :
    magnitudeCode g x = k := by
  have hset : (Finset.range g.last).filter (crossed g x) = Finset.range k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro ⟨hj, hc⟩
      exact (hcut j hj).mp hc
    · intro hj
      have hjg : j < g.last := lt_of_lt_of_le hj hk
      exact ⟨hjg, (hcut j hjg).mpr hj⟩
  simp [magnitudeCode, hset]

/-- Code chosen at a tie: even lower code, otherwise its even successor. -/
def tieCode (j : ℕ) : ℕ := if j % 2 = 0 then j else j + 1

theorem tieCode_le (g : MagnitudeGrid) (j : ℕ) (hj : j < g.last) :
    tieCode j ≤ g.last := by
  unfold tieCode
  split_ifs <;> omega

theorem tieCode_even (j : ℕ) : tieCode j % 2 = 0 := by
  unfold tieCode
  split_ifs <;> omega

/-- The midpoint rule is derived from all boundaries, not assumed by the checker. -/
theorem magnitudeCode_midpoint (g : MagnitudeGrid) (j : ℕ) (hj : j < g.last) :
    magnitudeCode g (boundary g j) = tieCode j := by
  apply magnitudeCode_eq_of_cut g _ _ (tieCode_le g j hj)
  intro i _
  have hlt := (boundary_strictMono g).lt_iff_lt (a := i) (b := j)
  have heq := (boundary_strictMono g).injective.eq_iff (a := i) (b := j)
  simp only [crossed, hlt, heq, tieCode]
  split_ifs <;> omega

/-- Expected signed encoding at an adjacent-magnitude midpoint. -/
def midpointResult (g : MagnitudeGrid) (negative : Bool) (j : Fin g.last) :
    FloatRepresentation g :=
  ⟨negative, ⟨tieCode j.val, Nat.lt_succ_of_le (tieCode_le g j.val j.isLt)⟩⟩

theorem round_at_midpoint (g : MagnitudeGrid) (x : ℚ) (j : Fin g.last)
    (h : |x| = boundary g j.val) :
    roundNearestEven g x = midpointResult g (decide (x < 0)) j := by
  unfold roundNearestEven midpointResult
  congr 1
  apply Fin.ext
  simp only [h, magnitudeCode_midpoint g j.val j.isLt]

/-- Exact subtraction certifies equality; adjacency comes from consecutive valid codes. -/
def checkExactMidpoint (g : MagnitudeGrid) (x : ℚ) (j : ℕ) : CertificateVerdict g :=
  if h : j < g.last ∧ |x| - boundary g j = 0 then
    .decided (midpointResult g (decide (x < 0)) ⟨j, h.1⟩)
  else .indeterminate

theorem exact_midpoint_soundness (g : MagnitudeGrid) (x : ℚ) (j : ℕ)
    (f : FloatRepresentation g) (h : checkExactMidpoint g x j = .decided f) :
    roundNearestEven g x = f := by
  unfold checkExactMidpoint at h
  split_ifs at h with hc
  have hf := CertificateVerdict.decided.inj h
  exact (round_at_midpoint g x ⟨j, hc.1⟩ (sub_eq_zero.mp hc.2)).trans hf

/-- Crossing a later boundary entails crossing every earlier boundary. -/
theorem crossed_downward (g : MagnitudeGrid) (x : ℚ) {i j : ℕ} (hij : i ≤ j)
    (hj : crossed g x j) : crossed g x i := by
  rcases lt_or_eq_of_le hij with hij | hij
  · have hb := boundary_strictMono g hij
    have hx : boundary g j ≤ x := by
      rcases hj with hj | ⟨hj, _⟩
      · exact le_of_lt hj
      · exact le_of_eq hj
    exact Or.inl (hb.trans_le hx)
  · simpa [hij] using hj

/-- Constant-size local cell witness, including asymmetric tie endpoints. -/
def inMagnitudeCell (g : MagnitudeGrid) (x : ℚ) (k : ℕ) : Prop :=
  k ≤ g.last ∧ (k = 0 ∨ crossed g x (k - 1)) ∧
    (k = g.last ∨ ¬ crossed g x k)

instance (g : MagnitudeGrid) (x : ℚ) (k : ℕ) : Decidable (inMagnitudeCell g x k) :=
  inferInstanceAs (Decidable (_ ∧ (_ ∨ _) ∧ (_ ∨ _)))

theorem magnitudeCode_of_cell (g : MagnitudeGrid) (x : ℚ) (k : ℕ)
    (h : inMagnitudeCell g x k) : magnitudeCode g x = k := by
  apply magnitudeCode_eq_of_cut g x k h.1
  intro j hj
  constructor
  · intro hc
    by_contra hnot
    have hkj : k ≤ j := by omega
    rcases h.2.2 with heq | hu
    · omega
    · exact hu (crossed_downward g x hkj hc)
  · intro hjk
    rcases h.2.1 with heq | hl
    · omega
    · exact crossed_downward g x (by omega) hl

/-- Local cells select a nearest rational grid value, including the virtual endpoint. -/
theorem cell_nearest (g : MagnitudeGrid) (x : ℚ) (k : ℕ)
    (h : inMagnitudeCell g x k) (j : ℕ) (_hj : j ≤ g.last) :
    |x - g.value k| ≤ |x - g.value j| := by
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · have hk : k ≠ 0 := by omega
    have hl : crossed g x (k - 1) := h.2.1.resolve_left hk
    have hb : boundary g (k - 1) ≤ x := by
      rcases hl with hl | ⟨hl, _⟩
      · exact le_of_lt hl
      · exact le_of_eq hl
    have hv := g.increasing.monotone (show j ≤ k - 1 by omega)
    have hstrict := g.increasing hjk
    have hsucc : k - 1 + 1 = k := by omega
    simp only [boundary, midpoint, hsucc] at hb
    have hxj : 0 ≤ x - g.value j := by linarith
    rw [abs_of_nonneg hxj]
    apply abs_le.mpr
    constructor <;> linarith
  · exact le_rfl
  · have hk : k ≠ g.last := by omega
    have hu : ¬ crossed g x k := h.2.2.resolve_left hk
    have hb : x ≤ boundary g k := le_of_not_gt (fun hx => hu (Or.inl hx))
    have hv := g.increasing.monotone (show k + 1 ≤ j by omega)
    have hstrict := g.increasing hkj
    dsimp [boundary, midpoint] at hb
    have hxj : x - g.value j ≤ 0 := by linarith
    rw [abs_of_nonpos hxj]
    apply abs_le.mpr
    constructor <;> linarith

/-- The counted boundaries form an initial segment, with no missing interior boundary. -/
theorem crossed_iff_lt_code (g : MagnitudeGrid) (x : ℚ) (j : ℕ) (hj : j < g.last) :
    crossed g x j ↔ j < magnitudeCode g x := by
  constructor
  · intro hc
    have hsub : Finset.range (j + 1) ⊆ (Finset.range g.last).filter (crossed g x) := by
      intro i hi
      have hi' : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hi'.trans_lt hj),
        crossed_downward g x hi' hc⟩
    have hcard := Finset.card_le_card hsub
    have : j + 1 ≤ magnitudeCode g x := by simpa [magnitudeCode] using hcard
    omega
  · intro hcode
    by_contra hnot
    have hsub : (Finset.range g.last).filter (crossed g x) ⊆ Finset.range j := by
      intro i hi
      obtain ⟨_, hc⟩ := Finset.mem_filter.mp hi
      apply Finset.mem_range.mpr
      by_contra hji
      exact hnot (crossed_downward g x (by omega) hc)
    have hcard := Finset.card_le_card hsub
    have : magnitudeCode g x ≤ j := by simpa [magnitudeCode] using hcard
    omega

/-- Every rounded magnitude belongs to its local cell. -/
theorem magnitudeCode_in_cell (g : MagnitudeGrid) (x : ℚ) :
    inMagnitudeCell g x (magnitudeCode g x) := by
  have hk := magnitudeCode_le g x
  refine ⟨hk, ?_, ?_⟩
  · by_cases hz : magnitudeCode g x = 0
    · exact Or.inl hz
    · exact Or.inr ((crossed_iff_lt_code g x _ (by omega)).mpr (by omega))
  · by_cases he : magnitudeCode g x = g.last
    · exact Or.inl he
    · exact Or.inr (fun hc => (Nat.lt_irrefl _)
        ((crossed_iff_lt_code g x _ (by omega)).mp hc))

/-- Nearest-value meaning of the rounding specification, before overflow interpretation. -/
theorem round_magnitude_nearest (g : MagnitudeGrid) (x : ℚ) (j : ℕ) (hj : j ≤ g.last) :
    abs (abs x - g.value (roundNearestEven g x).magnitude.val) ≤
      abs (abs x - g.value j) := by
  exact cell_nearest g |x| _ (magnitudeCode_in_cell g |x|) j hj

/-- Local signed cell membership; exact zero has only the positive encoding. -/
def inCell (g : MagnitudeGrid) (x : ℚ) (f : FloatRepresentation g) : Prop :=
  f.negative = decide (x < 0) ∧ inMagnitudeCell g |x| f.magnitude.val

instance (g : MagnitudeGrid) (x : ℚ) (f : FloatRepresentation g) :
    Decidable (inCell g x f) := inferInstanceAs (Decidable (_ ∧ _))

theorem inCell_sound (g : MagnitudeGrid) (x : ℚ) (f : FloatRepresentation g)
    (h : inCell g x f) : roundNearestEven g x = f := by
  obtain ⟨sign, code⟩ := f
  have hc := magnitudeCode_of_cell g |x| code.val h.2
  unfold roundNearestEven
  rw [← h.1]
  congr 1
  exact Fin.ext hc

/-- The rounding specification always supplies a valid local cell. -/
theorem inCell_round (g : MagnitudeGrid) (x : ℚ) : inCell g x (roundNearestEven g x) := by
  exact ⟨rfl, magnitudeCode_in_cell g |x|⟩

/-- Local checks are both sound and complete for the specified rounding result. -/
theorem inCell_iff_round (g : MagnitudeGrid) (x : ℚ) (f : FloatRepresentation g) :
    inCell g x f ↔ roundNearestEven g x = f := by
  constructor
  · exact inCell_sound g x f
  · intro h
    rw [← h]
    exact inCell_round g x

/-- Executable witness checker: only the claimed cell's adjacent boundaries are decoded. -/
def checkIntervalCertificate (g : MagnitudeGrid) (L U : ℚ) (f : FloatRepresentation g) :
    CertificateVerdict g :=
  if L ≤ U ∧ inCell g L f ∧ inCell g U f then .decided f else .indeterminate

theorem interval_certificate_sound (g : MagnitudeGrid) (L U x : ℚ)
    (f : FloatRepresentation g) (h : checkIntervalCertificate g L U f = .decided f)
    (hL : L ≤ x) (hU : x ≤ U) : roundNearestEven g x = f := by
  unfold checkIntervalCertificate at h
  split_ifs at h with hc
  exact interval_rounding_soundness g L U x f hL hU
    (inCell_sound g L f hc.2.1) (inCell_sound g U f hc.2.2)

/-- The efficient checker agrees with endpoint rounding when the claimed encoding is supplied. -/
theorem interval_certificate_decided_iff (g : MagnitudeGrid) (L U : ℚ)
    (f : FloatRepresentation g) :
    checkIntervalCertificate g L U f = .decided f ↔
      L ≤ U ∧ roundNearestEven g L = f ∧ roundNearestEven g U = f := by
  simp [checkIntervalCertificate, inCell_iff_round]

/-- Interval contraction preserves any established rounded value. -/
theorem rounding_on_subinterval (g : MagnitudeGrid) (L U L' U' : ℚ)
    (f : FloatRepresentation g) (hL : L ≤ L') (hLU : L' ≤ U') (hU : U' ≤ U)
    (hfL : roundNearestEven g L = f) (hfU : roundNearestEven g U = f) :
    roundNearestEven g L' = f ∧ roundNearestEven g U' = f := by
  exact ⟨interval_rounding_soundness g L U L' f hL (hLU.trans hU) hfL hfU,
    interval_rounding_soundness g L U U' f (hL.trans hLU) hU hfL hfU⟩

/-- Concrete binary64 grid, including its virtual next-binade overflow endpoint. -/
def binary64 : MagnitudeGrid where
  last := NumericBinaryGrid.binary64Last
  last_pos := by norm_num [NumericBinaryGrid.binary64Last, NumericBinaryGrid.binary64Base]
  value := NumericBinaryGrid.binary64Value
  value_zero := NumericBinaryGrid.binary64Value_zero
  increasing := NumericBinaryGrid.binary64Value_strictMono

/-- Positive zero, distinct from negative underflow zero. -/
def positiveZero : FloatRepresentation binary64 := ⟨false, ⟨0, by decide +kernel⟩⟩

/-- Negative underflow zero. Exact rational zero itself is canonical positive zero. -/
def negativeZero : FloatRepresentation binary64 := ⟨true, ⟨0, by decide +kernel⟩⟩

/-- Positive least subnormal encoding. -/
def leastSubnormal : FloatRepresentation binary64 := ⟨false, ⟨1, by decide +kernel⟩⟩

/-- Positive infinity's encoding, not a rational infinity value. -/
def positiveInfinity : FloatRepresentation binary64 :=
  ⟨false, ⟨NumericBinaryGrid.binary64Last, by
    change NumericBinaryGrid.binary64Last < NumericBinaryGrid.binary64Last + 1
    omega⟩⟩

set_option maxRecDepth 8192 in
/-- SimLab exact underflow tie: a positive rational rounds to positive zero. -/
theorem binary64_underflow_tie : roundNearestEven binary64 (1 / 2 ^ 1075) = positiveZero := by
  exact exact_midpoint_soundness binary64 _ 0 positiveZero (by decide +kernel)

set_option maxRecDepth 8192 in
theorem binary64_negative_underflow_tie :
    roundNearestEven binary64 (-(1 / 2 ^ 1075)) = negativeZero := by
  exact exact_midpoint_soundness binary64 _ 0 negativeZero (by decide +kernel)

set_option maxRecDepth 8192 in
theorem binary64_exact_zero : roundNearestEven binary64 0 = positiveZero := by
  exact inCell_sound binary64 0 positiveZero (by decide +kernel)

set_option maxRecDepth 8192 in
theorem binary64_overflow_tie :
    roundNearestEven binary64 (2 ^ 1024 - 2 ^ 970) = positiveInfinity := by
  exact exact_midpoint_soundness binary64 _ (NumericBinaryGrid.binary64Last - 1)
    positiveInfinity (by decide +kernel)

/-- Encoding of the ordinary exact value one half. -/
def halfEncoding : FloatRepresentation binary64 :=
  ⟨false, ⟨1022 * 2 ^ 52, by decide +kernel⟩⟩

set_option maxRecDepth 8192 in
/-- Retained SimLab singleton interval from A=B=1, I=2; SQL derivation is separate. -/
theorem half_interval_certificate :
    checkIntervalCertificate binary64 (1 / 2) (1 / 2) halfEncoding =
      .decided halfEncoding := by decide +kernel

/-- Shared lower bound of the two retained original decimal 256-bit records. -/
def historicalLower : ℚ := ((2 : ℚ) ^ 256 - 6) / 2 ^ 1331

/-- Shared upper bound of the two retained original decimal 256-bit records. -/
def historicalUpper : ℚ := ((2 : ℚ) ^ 255 + 1) / 2 ^ 1330

set_option maxRecDepth 8192 in
theorem historical_bounds_ordered : historicalLower ≤ historicalUpper := by decide +kernel

set_option maxRecDepth 8192 in
theorem historical_lower_rounds_zero :
    roundNearestEven binary64 historicalLower = positiveZero := by
  exact inCell_sound binary64 _ positiveZero (by decide +kernel)

set_option maxRecDepth 8192 in
theorem historical_upper_rounds_subnormal :
    roundNearestEven binary64 historicalUpper = leastSubnormal := by
  exact inCell_sound binary64 _ leastSubnormal (by decide +kernel)

/-- The original interval evidence remains inconclusive, regardless of later exact evidence. -/
theorem historical_interval_indeterminate :
    checkInterval binary64 historicalLower historicalUpper = .indeterminate := by
  apply checkInterval_indeterminate_of_different
  rw [historical_lower_rounds_zero, historical_upper_rounds_subnormal]
  decide

/-- Selected universal guarantees, with no SQL enclosure or parsing assumption hidden inside. -/
structure NumericRoundingCertificatesSuite : Prop where
  interval_sound : ∀ (g : MagnitudeGrid) (L U x : ℚ) (f : FloatRepresentation g),
    L ≤ x → x ≤ U → roundNearestEven g L = f → roundNearestEven g U = f →
    roundNearestEven g x = f
  witness_sound : ∀ (g : MagnitudeGrid) (L U x : ℚ) (f : FloatRepresentation g),
    checkIntervalCertificate g L U f = .decided f → L ≤ x → x ≤ U →
    roundNearestEven g x = f
  midpoint_sound : ∀ (g : MagnitudeGrid) (x : ℚ) (j : ℕ) (f : FloatRepresentation g),
    checkExactMidpoint g x j = .decided f → roundNearestEven g x = f
  local_nearest : ∀ (g : MagnitudeGrid) (x : ℚ) (k j : ℕ),
    inMagnitudeCell g x k → j ≤ g.last → |x - g.value k| ≤ |x - g.value j|
  global_nearest : ∀ (g : MagnitudeGrid) (x : ℚ) (j : ℕ), j ≤ g.last →
    abs (abs x - g.value (roundNearestEven g x).magnitude.val) ≤ abs (abs x - g.value j)
  ordinary_interval : checkIntervalCertificate binary64 (1 / 2) (1 / 2) halfEncoding =
    .decided halfEncoding
  underflow_tie : roundNearestEven binary64 (1 / 2 ^ 1075) = positiveZero
  retained_indeterminate : checkInterval binary64 historicalLower historicalUpper = .indeterminate

/-- Assemble proved rounding guarantees and exact binary64 regressions. -/
theorem numeric_rounding_certificates_master_suite : NumericRoundingCertificatesSuite where
  interval_sound := interval_rounding_soundness
  witness_sound := interval_certificate_sound
  midpoint_sound := exact_midpoint_soundness
  local_nearest := fun g x k j h hj => cell_nearest g x k h j hj
  global_nearest := round_magnitude_nearest
  ordinary_interval := half_interval_certificate
  underflow_tie := binary64_underflow_tie
  retained_indeterminate := historical_interval_indeterminate

end NumericRoundingCertificates
