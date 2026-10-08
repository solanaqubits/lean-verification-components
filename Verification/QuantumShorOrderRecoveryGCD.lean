/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumShorContinuedFractions

/-! Deterministic LCM recovery from certified divisors. Candidate enumeration does
not select the correct spectral denominator. No sampling law is assumed or proved. -/
namespace QuantumShorOrderRecoveryGCD

open QuantumShorContinuedFractions QuantumShorOrderFindingCore

/-- Executable accumulator: neither the unknown order nor spectral numerators
are inputs. The empty LCM is one. -/
def listLCM : List ℕ → ℕ
  | [] => 1
  | q :: qs => Nat.lcm q (listLCM qs)

/-- Empty GCD is zero; repetition and order have no mathematical significance. -/
def listGCD (qs : List ℕ) : ℕ := qs.foldr Nat.gcd 0

@[simp] theorem list_lcm_empty_case : listLCM [] = 1 := rfl

@[simp] theorem list_gcd_nil : listGCD [] = 0 := rfl

@[simp] theorem list_gcd_cons (q : ℕ) (qs : List ℕ) :
    listGCD (q :: qs) = Nat.gcd q (listGCD qs) := rfl

theorem list_lcm_dvd_order (r : ℕ) (qs : List ℕ)
    (hdiv : ∀ q ∈ qs, q ∣ r) : listLCM qs ∣ r := by
  induction qs with
  | nil => exact one_dvd r
  | cons q qs ih =>
    exact Nat.lcm_dvd (hdiv q (by simp)) (ih (fun x hx => hdiv x (by simp [hx])))

theorem member_dvd_list_lcm {q : ℕ} {qs : List ℕ} (hq : q ∈ qs) : q ∣ listLCM qs := by
  induction qs with
  | nil => simp at hq
  | cons x xs ih =>
    rcases List.mem_cons.mp hq with rfl | h
    · exact Nat.dvd_lcm_left _ _
    · exact dvd_trans (ih h) (Nat.dvd_lcm_right _ _)

/-- Positive order excludes zero candidates whenever divisor provenance holds. -/
theorem divisor_positive {r q : ℕ} (hr : 0 < r) (hq : q ∣ r) : 0 < q :=
  Nat.pos_of_dvd_of_pos hq hr

theorem list_lcm_positive {r : ℕ} (hr : 0 < r) (qs : List ℕ)
    (hdiv : ∀ q ∈ qs, q ∣ r) : 0 < listLCM qs :=
  divisor_positive hr (list_lcm_dvd_order r qs hdiv)

/-- Complementation exchanges finite GCD and LCM in the divisor lattice.
The extra gcd with r makes the formula valid for the empty list. -/
theorem complementary_lcm (r : ℕ) (hr : 0 < r) (ds : List ℕ)
    (hd : ∀ d ∈ ds, d ∣ r) :
    listLCM (ds.map (fun d => r / d)) = r / Nat.gcd r (listGCD ds) := by
  induction ds with
  | nil => simp [Nat.div_self hr]
  | cons d ds ih =>
    simp only [List.map_cons, listLCM, list_gcd_cons]
    rw [ih (fun x hx => hd x (by simp [hx]))]
    rw [Nat.div_lcm_eq_div_gcd (hd d (by simp)) (Nat.gcd_dvd_left _ _)]
    rw [Nat.gcd_left_comm]

theorem quotient_complement {r q : ℕ} (hr : 0 < r) (hq : q ∣ r) :
    r / (r / q) = q := Nat.div_div_self hq hr.ne'

/-- General identity including the empty list. -/
theorem list_lcm_complement_identity (r : ℕ) (hr : 0 < r) (qs : List ℕ)
    (hq : ∀ q ∈ qs, q ∣ r) :
    listLCM qs = r / Nat.gcd r (listGCD (qs.map (fun q => r / q))) := by
  have hd : ∀ d ∈ qs.map (fun q => r / q), d ∣ r := by
    intro d h
    obtain ⟨q, hq', rfl⟩ := List.mem_map.mp h
    exact Nat.div_dvd_of_dvd (hq q hq')
  have h := complementary_lcm r hr (qs.map (fun q => r / q)) hd
  rw [List.map_map] at h
  have hm : qs.map ((fun d => r / d) ∘ (fun q => r / q)) = qs := by
    calc
      _ = qs.map id := List.map_congr_left (fun q hq' => quotient_complement hr (hq q hq'))
      _ = qs := List.map_id qs
  rwa [hm] at h

theorem list_gcd_dvd_member {q : ℕ} {qs : List ℕ} (hq : q ∈ qs) :
    listGCD qs ∣ q := by
  induction qs with
  | nil => simp at hq
  | cons x xs ih =>
    rcases List.mem_cons.mp hq with rfl | h
    · exact Nat.gcd_dvd_left _ _
    · exact dvd_trans (Nat.gcd_dvd_right _ _) (ih h)

theorem order_recovery_criterion_quotients (r : ℕ) (hr : 0 < r) (qs : List ℕ)
    (hne : qs ≠ []) (hq : ∀ q ∈ qs, q ∣ r) :
    listLCM qs = r ↔ qs.foldr (fun q acc => Nat.gcd (r / q) acc) 0 = 1 := by
  obtain ⟨q, hmem⟩ := List.exists_mem_of_ne_nil qs hne
  have hd : listGCD (qs.map (fun q => r / q)) ∣ r :=
    dvd_trans (list_gcd_dvd_member (List.mem_map.mpr ⟨q, hmem, rfl⟩))
      (Nat.div_dvd_of_dvd (hq q hmem))
  rw [list_lcm_complement_identity r hr qs hq, Nat.gcd_eq_right hd, Nat.div_eq_self]
  simp [hr.ne', listGCD, List.foldr_map]

/-- Reduced denominators from spectral numerators. This is a specification, not
an observable candidate-selection algorithm: r and the s values are unknown. -/
def spectralDenominators (r : ℕ) (ss : List ℕ) : List ℕ :=
  ss.map (fun s => r / Nat.gcd s r)

theorem spectral_denominators_divide (r : ℕ) (ss : List ℕ) :
    ∀ q ∈ spectralDenominators r ss, q ∣ r := by
  intro q h
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp h
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right s r)

theorem spectral_quotient (r s : ℕ) (hr : 0 < r) :
    r / (r / Nat.gcd s r) = Nat.gcd s r :=
  quotient_complement hr (Nat.gcd_dvd_right s r)

theorem spectral_lcm_formula (r : ℕ) (hr : 0 < r) (ss : List ℕ) :
    listLCM (spectralDenominators r ss) = r / Nat.gcd r (listGCD ss) := by
  induction ss with
  | nil => simp [spectralDenominators, Nat.div_self hr]
  | cons s ss ih =>
    change Nat.lcm (r / Nat.gcd s r) (listLCM (spectralDenominators r ss)) = _
    rw [ih, Nat.div_lcm_eq_div_gcd (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)]
    congr 1
    simp only [list_gcd_cons, Nat.gcd_assoc, Nat.gcd_left_comm, Nat.gcd_gcd_self_right_left]

/-- Valid also for an empty sample list: it recovers precisely order one. -/
theorem order_recovery_spectral_gcd (r : ℕ) (hr : 0 < r) (ss : List ℕ) :
    listLCM (spectralDenominators r ss) = r ↔ Nat.gcd r (ss.foldr Nat.gcd 0) = 1 := by
  rw [spectral_lcm_formula r hr ss, Nat.div_eq_self]
  simp [hr.ne', listGCD]

/-- Modular verification gives the reverse divisibility, not provenance. -/
theorem modular_check_soundness_exact (a N : ℕ) (qs : List ℕ)
    (hq : ∀ q ∈ qs, q ∣ orderOf (a : ZMod N))
    (hcheck : (a : ZMod N) ^ listLCM qs = 1) :
    listLCM qs = orderOf (a : ZMod N) :=
  checked_divisor_is_order a N _ hcheck (list_lcm_dvd_order _ qs hq)

/-- Entirely executable, but conditional on a separately proved divisor contract. -/
theorem executable_check_exact (a N : ℕ) (qs : List ℕ)
    (hq : ∀ q ∈ qs, q ∣ orderOf (a : ZMod N)) :
    passesModularCheck a N (listLCM qs) = true ↔ listLCM qs = orderOf (a : ZMod N) := by
  rw [executable_modular_check]
  exact ⟨fun h => Nat.dvd_antisymm (list_lcm_dvd_order _ qs hq) h, fun h => h ▸ dvd_refl _⟩

theorem concrete_recovery_example :
    listLCM [2, 3] = 6 ∧ 2 ≠ 6 ∧ 3 ≠ 6 := by decide

/-- Reordering and duplicate samples cannot affect the LCM, since it depends
only on membership and divisibility. -/
theorem list_lcm_membership_invariant (xs ys : List ℕ)
    (h : ∀ q, q ∈ xs ↔ q ∈ ys) : listLCM xs = listLCM ys := by
  apply Nat.dvd_antisymm
  · exact list_lcm_dvd_order _ xs (fun q hq => member_dvd_list_lcm ((h q).mp hq))
  · exact list_lcm_dvd_order _ ys (fun q hq => member_dvd_list_lcm ((h q).mpr hq))

theorem list_lcm_append (xs ys : List ℕ) :
    listLCM (xs ++ ys) = Nat.lcm (listLCM xs) (listLCM ys) := by
  induction xs with
  | nil => simp [listLCM]
  | cons x xs ih => simp only [List.cons_append, listLCM, ih, Nat.lcm_assoc]

/-- The exact denominators from module 119 agree with the spectral formula. -/
theorem reduced_denominators_eq (r : ℕ) (hr : 0 < r) (ss : List ℕ) :
    ss.map (fun s => (reduced s r).den) = spectralDenominators r ss := by
  exact List.map_congr_left (fun s _ => reduced_den s r hr)

/-- Each latent spectral component supplies one member of the observable list.
This assertion does not choose that member from the measurement alone. -/
theorem measured_candidate_provenance (c : Parameters) (n : ℕ)
    (hsize : c.modulus ^ 2 ≤ 2 ^ n)
    (samples : List (Fin c.period × Fin (2 ^ n)))
    (hnear : ∀ sample ∈ samples,
      QuantumPhaseEstimationGeneral.Nearest (2 ^ n)
        (sample.1.val / (c.period : ℝ)) sample.2) :
    ∀ sample ∈ samples,
      (reduced sample.1.val c.period).den ∈
        (candidates sample.2.val (2 ^ n) c.modulus).map Rat.den := by
  intro sample hs
  exact List.mem_map.mpr ⟨_, (shor_nearest_candidate c n hsize _ _ (hnear sample hs)).1, rfl⟩

/-- Conditional multi-sample recovery in the existing Shor parameter model.
The spectral labels in the statement are not inputs to listLCM. -/
theorem shor_order_recovery_criterion (c : Parameters) (ss : List (Fin c.period)) :
    listLCM (ss.map (fun s => (reduced s.val c.period).den)) = c.period ↔
      Nat.gcd c.period (listGCD (ss.map Fin.val)) = 1 := by
  have h := order_recovery_spectral_gcd c.period c.period_pos (ss.map Fin.val)
  simpa only [spectralDenominators, List.map_map, Function.comp_def,
    reduced_den _ _ c.period_pos, listGCD] using h

/-- A fully computed counterexample to taking all candidate denominators.
N=31, a=2 has order 5; y/Q=410/1024 is near 2/5. Candidate denominators
are [1,2,5], whose LCM 10 passes the modular check but is not the order. -/
theorem all_candidates_can_pass_nonminimally :
    orderOf (2 : ZMod 31) = 5 ∧
    (candidates 410 1024 31).map Rat.den = [1, 2, 5] ∧
    listLCM ((candidates 410 1024 31).map Rat.den) = 10 ∧
    passesModularCheck 2 31 10 = true ∧ 10 ≠ 5 := by
  have hp : orderOf (2 : ZMod 31) = 5 := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact orderOf_eq_prime (by decide) (by decide)
  exact ⟨hp, by decide +kernel, by decide +kernel, by decide, by decide⟩

structure QuantumShorOrderRecoverySuite : Prop where
  empty : listLCM [] = 1
  divisor : ∀ r qs, (∀ q ∈ qs, q ∣ r) → listLCM qs ∣ r
  quotients : ∀ r, 0 < r → ∀ qs, qs ≠ [] → (∀ q ∈ qs, q ∣ r) →
    (listLCM qs = r ↔ qs.foldr (fun q acc => Nat.gcd (r / q) acc) 0 = 1)
  spectral : ∀ r, 0 < r → ∀ ss,
    listLCM (spectralDenominators r ss) = r ↔ Nat.gcd r (ss.foldr Nat.gcd 0) = 1
  check_exact : ∀ a N qs, (∀ q ∈ qs, q ∣ orderOf (a : ZMod N)) →
    (passesModularCheck a N (listLCM qs) = true ↔ listLCM qs = orderOf (a : ZMod N))
  shor_bridge : ∀ (c : Parameters) (ss : List (Fin c.period)),
    listLCM (ss.map (fun s => (reduced s.val c.period).den)) = c.period ↔
      Nat.gcd c.period (listGCD (ss.map Fin.val)) = 1
  candidate_presence : ∀ (c : Parameters) (n : ℕ), c.modulus ^ 2 ≤ 2 ^ n →
    ∀ (samples : List (Fin c.period × Fin (2 ^ n))),
    (∀ sample ∈ samples, QuantumPhaseEstimationGeneral.Nearest (2 ^ n)
      (sample.1.val / (c.period : ℝ)) sample.2) →
    ∀ sample ∈ samples, (reduced sample.1.val c.period).den ∈
      (candidates sample.2.val (2 ^ n) c.modulus).map Rat.den
  example_recovery : listLCM [2, 3] = 6 ∧ 2 ≠ 6 ∧ 3 ≠ 6
  unsafe_all_candidates : orderOf (2 : ZMod 31) = 5 ∧
    (candidates 410 1024 31).map Rat.den = [1, 2, 5] ∧
    listLCM ((candidates 410 1024 31).map Rat.den) = 10 ∧
    passesModularCheck 2 31 10 = true ∧ 10 ≠ 5

theorem quantum_shor_order_recovery_master_suite : QuantumShorOrderRecoverySuite where
  empty := list_lcm_empty_case
  divisor := list_lcm_dvd_order
  quotients := order_recovery_criterion_quotients
  spectral := order_recovery_spectral_gcd
  check_exact := executable_check_exact
  shor_bridge := shor_order_recovery_criterion
  candidate_presence := measured_candidate_provenance
  example_recovery := concrete_recovery_example
  unsafe_all_candidates := all_candidates_can_pass_nonminimally

end QuantumShorOrderRecoveryGCD
