/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumShorOrderFindingCore
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.RingTheory.Fintype
import Mathlib.Data.Nat.Log

/-! Computable rational continued fractions and conditional Shor postprocessing.
No unknown spectral numerator or period is an input to the candidate algorithm. -/
namespace QuantumShorContinuedFractions

private theorem tail_den_lt (x : ℚ) (h : Int.fract x ≠ 0) :
    ((Int.fract x)⁻¹).den < x.den := by
  rw [Rat.den_inv_of_ne_zero h, ← Rat.den_intFract x]
  have hn : 0 ≤ (Int.fract x).num := Rat.num_nonneg.mpr (Int.fract_nonneg x)
  have hl := Int.fract_lt_one x
  rw [← Rat.num_div_den (Int.fract x), div_lt_one (by positivity)] at hl
  have hi : (Int.fract x).num < ((Int.fract x).den : ℤ) := by exact_mod_cast hl
  exact_mod_cast (show ((Int.fract x).num.natAbs : ℤ) < ((Int.fract x).den : ℤ) by
    simpa [Int.natCast_natAbs, abs_of_nonneg hn] using hi)

/-- Euclidean continued fractions: floor is integer division, and the reciprocal
fractional part is the next complete quotient. Stops at an integer. -/
def convergents (x : ℚ) : List ℚ :=
  if h : Int.fract x = 0 then [⌊x⌋]
  else (⌊x⌋ : ℚ) :: (convergents (Int.fract x)⁻¹).map (fun z => (⌊x⌋ : ℚ) + z⁻¹)
termination_by x.den
decreasing_by exact tail_den_lt x h

/-- Every real convergent of a rational input is in the finite executable list,
including the repeated terminal convergents of Mathlib's totalized definition. -/
theorem real_convergent_mem (x : ℚ) (k : ℕ) :
    Real.convergent (x : ℝ) k ∈ convergents x := by
  induction x using convergents.induct generalizing k with
  | case1 x h =>
    have hx : x = (⌊x⌋ : ℚ) := by
      have := Int.fract_add_floor x
      rw [h, zero_add] at this
      exact this.symm
    rw [convergents, dif_pos h]
    have hc : (x : ℝ) = (⌊x⌋ : ℝ) := by exact_mod_cast hx
    simp [hc]
  | case2 x h ih =>
    rw [convergents, dif_neg h]
    cases k with
    | zero => simp
    | succ k =>
      apply List.mem_cons_of_mem
      apply List.mem_map.mpr
      refine ⟨Real.convergent (((Int.fract x)⁻¹ : ℚ) : ℝ) k, ih k, ?_⟩
      simp

/-- The executable list has no entries other than actual convergents. -/
theorem mem_convergents_iff (x z : ℚ) :
    z ∈ convergents x ↔ ∃ k, Real.convergent (x : ℝ) k = z := by
  constructor
  · induction x using convergents.induct generalizing z with
    | case1 x h =>
      rw [convergents, dif_pos h, List.mem_singleton]
      intro hz
      exact ⟨0, by simp [hz]⟩
    | case2 x h ih =>
      rw [convergents, dif_neg h]
      intro hz
      rcases List.mem_cons.mp hz with hz | hz
      · exact ⟨0, by simp [hz]⟩
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
        obtain ⟨k, hk⟩ := ih u hu
        refine ⟨k + 1, ?_⟩
        simpa using congrArg (fun z : ℚ => (⌊x⌋ : ℚ) + z⁻¹) hk
  · rintro ⟨k, rfl⟩; exact real_convergent_mem x k

/-- Observable inputs only: measured integer, register size, modulus bound. -/
def candidates (y Q N : ℕ) : List ℚ :=
  (convergents ((y : ℚ) / Q)).filter (fun z => z.den < N)

/-- Reduction uses the canonical numerator and positive denominator of a rational. -/
def reduced (s r : ℕ) : ℚ := (s : ℚ) / r

theorem reduced_den (s r : ℕ) (hr : 0 < r) :
    (reduced s r).den = r / Nat.gcd s r := by
  simp [reduced, Rat.natCast_div_eq_divInt, Rat.den_mkRat, hr.ne', Nat.gcd_comm]

theorem reduced_num (s r : ℕ) (hr : 0 < r) :
    (reduced s r).num = (s / Nat.gcd s r : ℕ) := by
  simp [reduced, Rat.natCast_div_eq_divInt, Rat.num_mkRat, hr.ne',
    Nat.gcd_comm]

theorem reduced_coprime (s r : ℕ) (hr : 0 < r) :
    Nat.Coprime (s / Nat.gcd s r) (r / Nat.gcd s r) := by
  have h := (reduced s r).reduced
  rw [reduced_num s r hr, reduced_den s r hr] at h
  simpa only [Int.natAbs_natCast] using h

theorem candidate_divisor_property (s r : ℕ) (hr : 0 < r) :
    (reduced s r).den = r / Nat.gcd s r ∧ (reduced s r).den ∣ r := by
  rw [reduced_den s r hr]
  exact ⟨rfl, Nat.div_dvd_of_dvd (Nat.gcd_dvd_right s r)⟩

theorem reduced_den_le (s r : ℕ) (hr : 0 < r) : (reduced s r).den ≤ r := by
  rw [reduced_den s r hr]; exact Nat.div_le_self _ _

theorem legendre_approximation_condition {N Q r s y : ℕ}
    (hr : 0 < r) (hrN : r < N) (hQ : N ^ 2 ≤ Q)
    (hnear : |(y : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * (Q : ℝ))) :
    |(y : ℝ) / Q - (reduced s r : ℝ)| <
      1 / (2 * ((reduced s r).den : ℝ) ^ 2) := by
  have hd := (reduced s r).pos
  have hle := reduced_den_le s r hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hnR : (r : ℝ) < N := by exact_mod_cast hrN
  have hqR : (N : ℝ) ^ 2 ≤ Q := by exact_mod_cast hQ
  have hdR : (0 : ℝ) < (reduced s r).den := by exact_mod_cast hd
  have hlR : ((reduced s r).den : ℝ) ≤ r := by exact_mod_cast hle
  have hsquare : ((reduced s r).den : ℝ) ^ 2 < Q := by nlinarith
  have hb : 1 / (2 * (Q : ℝ)) < 1 / (2 * ((reduced s r).den : ℝ) ^ 2) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith
  have heq : (reduced s r : ℝ) = (s : ℝ) / r := by simp [reduced]
  rw [heq]
  exact hnear.trans_lt hb

theorem convergent_recovery_soundness {N Q r s y : ℕ}
    (hr : 0 < r) (hrN : r < N) (hQ : N ^ 2 ≤ Q)
    (hnear : |(y : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * (Q : ℝ))) :
    reduced s r ∈ candidates y Q N := by
  have h := legendre_approximation_condition hr hrN hQ hnear
  have hc : |(((y : ℚ) / Q : ℚ) : ℝ) - (reduced s r : ℝ)| <
      1 / (2 * ((reduced s r).den : ℝ) ^ 2) := by simpa using h
  obtain ⟨k, hk⟩ := Real.exists_rat_eq_convergent hc
  apply List.mem_filter.mpr
  exact ⟨hk ▸ real_convergent_mem ((y : ℚ) / Q) k, by
    simpa using (lt_of_le_of_lt (reduced_den_le s r hr) hrN)⟩

theorem exact_order_recovery_when_coprime (s r : ℕ) (hr : 0 < r)
    (hcop : Nat.Coprime s r) : (reduced s r).den = r := by
  simp [reduced_den s r hr, hcop.gcd_eq_one]

theorem modular_check_soundness (a N q : ℕ) :
    (a : ZMod N) ^ q = 1 ↔ orderOf (a : ZMod N) ∣ q :=
  orderOf_dvd_iff_pow_eq_one.symm

theorem checked_divisor_is_order (a N q : ℕ)
    (hcheck : (a : ZMod N) ^ q = 1) (hdiv : q ∣ orderOf (a : ZMod N)) :
    q = orderOf (a : ZMod N) :=
  Nat.dvd_antisymm hdiv ((modular_check_soundness a N q).mp hcheck)

/-- In the sufficiently resolved order-finding setting a modular nearest sample
has no wrap-around ambiguity, even for s=0 or either rounding tie. -/
theorem nearest_has_no_wrap {N Q r s y : ℕ}
    (hr : 0 < r) (hs : s < r) (hrN : r < N) (hQ : N ^ 2 ≤ Q) (hy : y < Q)
    (hnear : ∃ z : ℤ, |(s : ℝ) / r - (y : ℝ) / Q - z| ≤ 1 / (2 * (Q : ℝ))) :
    |(y : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * (Q : ℝ)) := by
  have hN : 0 < N := by omega
  have hQp : 0 < Q := lt_of_lt_of_le (pow_pos hN 2) hQ
  have hrQ : r < Q := by nlinarith
  have rpos : (0 : ℝ) < r := by exact_mod_cast hr
  have Qpos : (0 : ℝ) < Q := by exact_mod_cast hQp
  have sr : (s : ℝ) + 1 ≤ r := by exact_mod_cast (show s + 1 ≤ r by omega)
  have yQ : (y : ℝ) + 1 ≤ Q := by exact_mod_cast (show y + 1 ≤ Q by omega)
  have rq : (r : ℝ) < Q := by exact_mod_cast hrQ
  have slow : (0 : ℝ) ≤ (s : ℝ) / r := by positivity
  have ylow : (0 : ℝ) ≤ (y : ℝ) / Q := by positivity
  have sup : (s : ℝ) / r ≤ 1 - 1 / (r : ℝ) := by
    apply (div_le_iff₀ rpos).mpr
    field_simp
    nlinarith
  have yup : (y : ℝ) / Q ≤ 1 - 1 / (Q : ℝ) := by
    apply (div_le_iff₀ Qpos).mpr
    field_simp
    nlinarith
  have epsQ : 1 / (2 * (Q : ℝ)) < 1 / (Q : ℝ) :=
    one_div_lt_one_div_of_lt Qpos (by linarith)
  have epsr : 1 / (2 * (Q : ℝ)) < 1 / (r : ℝ) :=
    one_div_lt_one_div_of_lt rpos (by linarith)
  obtain ⟨z, hz⟩ := hnear
  have hzlo := (abs_le.mp hz).1
  have hzhi := (abs_le.mp hz).2
  have zlo : (-1 : ℝ) < z := by linarith
  have zhi : (z : ℝ) < 1 := by linarith
  have zz : z = 0 := by
    have : (-1 : ℤ) < z := by exact_mod_cast zlo
    have : z < (1 : ℤ) := by exact_mod_cast zhi
    omega
  simpa [zz, abs_sub_comm] using hz

/-- A concrete finite bound, independent of any unknown order. -/
theorem continued_fraction_convergents_finite (x : ℚ) :
    (convergents x).length ≤ x.den := by
  induction x using convergents.induct with
  | case1 x h => rw [convergents, dif_pos h]; exact x.pos
  | case2 x h ih =>
    rw [convergents, dif_neg h, List.length_cons, List.length_map]
    have := tail_den_lt x h
    omega

open QuantumShorOrderFindingCore QuantumPhaseEstimationGeneral

theorem period_lt_modulus (c : Parameters) : c.period < c.modulus :=
  ZMod.orderOf_lt c.modulus_ge_two _

/-- The measured modular-nearest event from the existing QPE model supplies the
entire deterministic recovery contract, with no period input to candidates. -/
theorem shor_nearest_candidate (c : Parameters) (n : ℕ)
    (hsize : c.modulus ^ 2 ≤ 2 ^ n) (s : Fin c.period) (y : Fin (2 ^ n))
    (hnear : Nearest (2 ^ n) (s.val / (c.period : ℝ)) y) :
    reduced s.val c.period ∈ candidates y.val (2 ^ n) c.modulus ∧
      (reduced s.val c.period).den ∣ c.period := by
  refine ⟨convergent_recovery_soundness c.period_pos (period_lt_modulus c) hsize ?_,
    (candidate_divisor_property s.val c.period c.period_pos).2⟩
  exact nearest_has_no_wrap c.period_pos s.isLt (period_lt_modulus c) hsize y.isLt hnear

/-- The reduced candidate is the order exactly when its numerator is coprime.
Other entries in the candidate list are not asserted to divide the order. -/
theorem shor_coprime_candidate (c : Parameters) (n : ℕ)
    (hsize : c.modulus ^ 2 ≤ 2 ^ n) (s : Fin c.period) (y : Fin (2 ^ n))
    (hnear : Nearest (2 ^ n) (s.val / (c.period : ℝ)) y)
    (hcop : Nat.Coprime s.val c.period) :
    c.period ∈ (candidates y.val (2 ^ n) c.modulus).map Rat.den := by
  obtain ⟨hmem, _⟩ := shor_nearest_candidate c n hsize s y hnear
  exact List.mem_map.mpr ⟨_, hmem,
    exact_order_recovery_when_coprime s.val c.period c.period_pos hcop⟩

private theorem second_den_sum_le (x : ℚ) (h : Int.fract x ≠ 0)
    (h' : Int.fract (Int.fract x)⁻¹ ≠ 0) :
    ((Int.fract (Int.fract x)⁻¹)⁻¹).den + ((Int.fract x)⁻¹).den ≤ x.den := by
  let t := Int.fract x
  let u := t⁻¹
  have ht : 0 < t := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm h)
  have hn : 0 < t.num := Rat.num_pos.mpr ht
  have hu : 1 ≤ u := by
    dsimp [u]; exact (one_le_inv₀ ht).mpr (Int.fract_lt_one x).le
  have hf : (1 : ℤ) ≤ ⌊u⌋ := by exact Int.le_floor.mpr hu
  have hnum : u.num = x.den := by
    dsimp [u, t]
    rw [Rat.num_inv, Int.sign_eq_one_of_pos hn, one_mul, Rat.den_intFract]
  have hden : (Int.fract u).den = u.den := Rat.den_intFract _
  have hnon : 0 ≤ (Int.fract u).num := Rat.num_nonneg.mpr (Int.fract_nonneg u)
  have heq : (Int.fract u).num + ⌊u⌋ * u.den = u.num := by
    have hv := Int.fract_add_floor u
    have hm := congrArg (fun z : ℚ => z * u.den) hv
    have mulden (z : ℚ) : z * (z.den : ℚ) = z.num :=
      (eq_div_iff (by exact_mod_cast z.den_ne_zero)).mp z.num_div_den.symm
    rw [add_mul, ← hden, mulden (Int.fract u), hden, mulden u] at hm
    exact_mod_cast hm
  have hle : (Int.fract u).num + (u.den : ℤ) ≤ (x.den : ℤ) := by
    rw [hnum] at heq
    have hp : (0 : ℤ) ≤ u.den := by positivity
    nlinarith
  change ((Int.fract u)⁻¹).den + u.den ≤ x.den
  rw [Rat.den_inv_of_ne_zero h']
  exact_mod_cast (show ((Int.fract u).num.natAbs : ℤ) + (u.den : ℤ) ≤ (x.den : ℤ) by
    simpa [Int.natCast_natAbs, abs_of_nonneg hnon] using hle)

/-- At most 2 floor(log₂ denominator)+1 Euclidean stages. This counts complete
quotients, not bit operations or all list-map operations. -/
theorem convergents_length_log (x : ℚ) :
    (convergents x).length ≤ 2 * Nat.log 2 x.den + 1 := by
  induction hd : x.den using Nat.strong_induction_on generalizing x with
  | h d ih =>
    by_cases h : Int.fract x = 0
    · rw [convergents, dif_pos h]; simp
    · let t := (Int.fract x)⁻¹
      have ht : t.den < d := by simpa [t, hd] using tail_den_lt x h
      by_cases h' : Int.fract t = 0
      · have hd2 : 2 ≤ d := lt_of_le_of_lt t.pos ht
        have hl : 1 ≤ Nat.log 2 d := Nat.le_log_of_pow_le (by decide) (by simpa using hd2)
        rw [convergents, dif_neg h, List.length_cons, List.length_map]
        change (convergents t).length + 1 ≤ _
        rw [convergents, dif_pos h', List.length_singleton]
        omega
      · let u := (Int.fract t)⁻¹
        have hu : u.den < t.den := tail_den_lt t h'
        have hsum : u.den + t.den ≤ d := by
          simpa [u, t, hd] using second_den_sum_le x h h'
        have hdouble : u.den * 2 ≤ d := by omega
        have hl : Nat.log 2 u.den + 1 ≤ Nat.log 2 d := by
          have hm := Nat.log_mono_right (b := 2) hdouble
          rwa [Nat.log_mul_base (by decide) u.den_ne_zero] at hm
        have hu' := ih u.den (hu.trans ht) u rfl
        rw [convergents, dif_neg h, List.length_cons, List.length_map]
        change (convergents t).length + 1 ≤ _
        rw [convergents, dif_neg h', List.length_cons, List.length_map]
        change (convergents u).length + 1 + 1 ≤ _
        omega

/-- A measured rational has reduced denominator at most its input register size. -/
theorem candidates_length_bound (y Q N : ℕ) (hQ : 0 < Q) :
    (candidates y Q N).length ≤ 2 * Nat.log 2 Q + 1 := by
  have hd := reduced_den_le y Q hQ
  have hm := Nat.log_mono_right (b := 2) hd
  have hl := convergents_length_log ((y : ℚ) / Q)
  have hf := List.length_filter_le (fun z : ℚ => decide (z.den < N))
    (convergents ((y : ℚ) / Q))
  change _ ≤ _ at hf
  unfold candidates
  dsimp [reduced] at hm
  omega

/-- The finite list of partial quotients, computed by the same Euclidean descent. -/
def partialQuotients (x : ℚ) : List ℤ :=
  if _h : Int.fract x = 0 then [⌊x⌋]
  else ⌊x⌋ :: partialQuotients (Int.fract x)⁻¹
termination_by x.den
decreasing_by exact tail_den_lt x _h

theorem partialQuotients_length (x : ℚ) :
    (partialQuotients x).length = (convergents x).length := by
  induction x using convergents.induct with
  | case1 x h => rw [partialQuotients, dif_pos h, convergents, dif_pos h]; rfl
  | case2 x h ih =>
    rw [partialQuotients, dif_neg h, convergents, dif_neg h,
      List.length_cons, List.length_cons, List.length_map, ih]

theorem euclidean_stages_log_bound (x : ℚ) :
    (partialQuotients x).length ≤ 2 * Nat.log 2 x.den + 1 := by
  rw [partialQuotients_length]; exact convergents_length_log x

/-- The executable modular check has only the multiple-of-order interpretation. -/
def passesModularCheck (a N q : ℕ) : Bool := decide (a ^ q % N = 1 % N)

theorem executable_modular_check (a N q : ℕ) :
    passesModularCheck a N q = true ↔ orderOf (a : ZMod N) ∣ q := by
  rw [passesModularCheck, decide_eq_true_eq,
    ← ZMod.natCast_eq_natCast_iff', Nat.cast_pow, Nat.cast_one]
  exact modular_check_soundness a N q

/-- Checked candidates can still be proper multiples of the order. -/
def checkedCandidates (a y Q N : ℕ) : List ℕ :=
  ((candidates y Q N).map Rat.den).filter (passesModularCheck a N)

theorem checked_candidate_multiple (a y Q N q : ℕ)
    (hq : q ∈ checkedCandidates a y Q N) : orderOf (a : ZMod N) ∣ q := by
  exact (executable_modular_check a N q).mp (List.mem_filter.mp hq).2

theorem shor_coprime_checked_candidate (c : Parameters) (n : ℕ)
    (hsize : c.modulus ^ 2 ≤ 2 ^ n) (s : Fin c.period) (y : Fin (2 ^ n))
    (hnear : Nearest (2 ^ n) (s.val / (c.period : ℝ)) y)
    (hcop : Nat.Coprime s.val c.period) :
    c.period ∈ checkedCandidates c.base y.val (2 ^ n) c.modulus := by
  apply List.mem_filter.mpr
  exact ⟨shor_coprime_candidate c n hsize s y hnear hcop,
    (executable_modular_check c.base c.modulus c.period).mpr (dvd_refl _)⟩

/-- Deterministic recovery at the already proved spectral peak; the lower bound
is for one component's contribution, not a guaranteed successful quantum run. -/
theorem shor_recovery_peak (c : Parameters) (n : ℕ)
    (hsize : c.modulus ^ 2 ≤ 2 ^ n) (s : Fin c.period) (y : Fin (2 ^ n))
    (hnear : Nearest (2 ^ n) (s.val / (c.period : ℝ)) y) :
    reduced s.val c.period ∈ candidates y.val (2 ^ n) c.modulus ∧
    4 / ((c.period : ℝ) * Real.pi ^ 2) ≤
      normSquared (runQPE c.modularOperator n c.input y) := by
  exact ⟨(shor_nearest_candidate c n hsize s y hnear).1,
    by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      c.shor_mixture_peak_lower_bound n s y hnear⟩

structure QuantumShorContinuedFractionsSuite : Prop where
  finite_algorithm : ∀ x : ℚ, (convergents x).length ≤ x.den
  exact_convergents : ∀ x z : ℚ,
    z ∈ convergents x ↔ ∃ k, Real.convergent (x : ℝ) k = z
  logarithmic_stages : ∀ x : ℚ,
    (partialQuotients x).length ≤ 2 * Nat.log 2 x.den + 1
  strict_legendre : ∀ {N Q r s y : ℕ}, 0 < r → r < N → N ^ 2 ≤ Q →
    |(y : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * (Q : ℝ)) →
    |(y : ℝ) / Q - (reduced s r : ℝ)| < 1 / (2 * ((reduced s r).den : ℝ) ^ 2)
  recovery : ∀ (c : Parameters) (n : ℕ), c.modulus ^ 2 ≤ 2 ^ n →
    ∀ (s : Fin c.period) (y : Fin (2 ^ n)),
    Nearest (2 ^ n) (s.val / (c.period : ℝ)) y →
    reduced s.val c.period ∈ candidates y.val (2 ^ n) c.modulus ∧
      (reduced s.val c.period).den ∣ c.period
  exact_coprime : ∀ (c : Parameters) (n : ℕ), c.modulus ^ 2 ≤ 2 ^ n →
    ∀ (s : Fin c.period) (y : Fin (2 ^ n)),
    Nearest (2 ^ n) (s.val / (c.period : ℝ)) y → Nat.Coprime s.val c.period →
    c.period ∈ checkedCandidates c.base y.val (2 ^ n) c.modulus
  check_sound : ∀ a N q, passesModularCheck a N q = true ↔ orderOf (a : ZMod N) ∣ q
  divisor_formula : ∀ s r, 0 < r →
    (reduced s r).den = r / Nat.gcd s r ∧ (reduced s r).den ∣ r

theorem quantum_shor_continued_fractions_master_suite : QuantumShorContinuedFractionsSuite where
  finite_algorithm := continued_fraction_convergents_finite
  exact_convergents := mem_convergents_iff
  logarithmic_stages := euclidean_stages_log_bound
  strict_legendre := legendre_approximation_condition
  recovery := shor_nearest_candidate
  exact_coprime := shor_coprime_checked_candidate
  check_sound := executable_modular_check
  divisor_formula := candidate_divisor_property

end QuantumShorContinuedFractions
