import Verification.QuantumShorOrderRecoveryGCD

open QuantumShorOrderRecoveryGCD QuantumShorContinuedFractions

example : listLCM [] = 1 := list_lcm_empty_case
example : listLCM [] < 6 := by decide
example : listLCM (spectralDenominators 1 []) = 1 := by decide
example : Nat.gcd 1 (listGCD []) = 1 := by decide
-- Nonemptiness is essential for the unanchored quotient-GCD criterion.
example : listLCM [] = 1 ∧ ([] : List ℕ).foldr (fun q acc => Nat.gcd (1 / q) acc) 0 ≠ 1 :=
  by decide
example : listLCM [0, 2] = 0 ∧ ¬ (0 ∣ 6) := by decide
example : listLCM [2, 3] = 6 ∧ 2 ≠ 6 ∧ 3 ≠ 6 := concrete_recovery_example
example : spectralDenominators 6 [3, 2] = [2, 3] ∧
    Nat.gcd 3 6 ≠ 1 ∧ Nat.gcd 2 6 ≠ 1 ∧
    listLCM (spectralDenominators 6 [3, 2]) = 6 := by decide
example : listLCM [3, 2, 3, 2] = 6 := by decide
example : listLCM [2, 2] = 2 ∧ listLCM [2, 2] ≠ 6 := by decide
example : listLCM (spectralDenominators 6 [0, 0]) = 1 := by decide
example : listLCM [2, 3] = listLCM [3, 2, 2] := by
  apply list_lcm_membership_invariant
  intro q
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto
example : passesModularCheck 2 7 (listLCM [1]) = false := by decide
example : passesModularCheck 2 7 (listLCM [1, 3]) = true := by decide
example (a N : ℕ) (qs : List ℕ) (h : ∀ q ∈ qs, q ∣ orderOf (a : ZMod N))
    (hc : passesModularCheck a N (listLCM qs) = true) :
    listLCM qs = orderOf (a : ZMod N) := (executable_check_exact a N qs h).mp hc
example (r : ℕ) (hr : 0 < r) (qs : List ℕ) (hne : qs ≠ [])
    (hd : ∀ q ∈ qs, q ∣ r) :
    listLCM qs = r ↔ qs.foldr (fun q acc => Nat.gcd (r / q) acc) 0 = 1 :=
  order_recovery_criterion_quotients r hr qs hne hd
example (r : ℕ) (hr : 0 < r) (ss : List ℕ) :
    listLCM (spectralDenominators r ss) = r ↔ Nat.gcd r (listGCD ss) = 1 :=
  order_recovery_spectral_gcd r hr ss
-- Counterexample satisfies the resolution and ordinary nearest-sample hypotheses.
example : 31 ^ 2 ≤ (1024 : ℕ) ∧ (5 : ℕ) < 31 ∧ (410 : ℕ) < 1024 := by decide
example : |(410 : ℝ) / 1024 - 2 / 5| ≤ 1 / (2 * 1024) := by norm_num
example : orderOf (2 : ZMod 31) = 5 ∧
    listLCM ((candidates 410 1024 31).map Rat.den) ≠ orderOf (2 : ZMod 31) ∧
    passesModularCheck 2 31 (listLCM ((candidates 410 1024 31).map Rat.den)) = true := by
  obtain ⟨ho, _, hl, hc, _⟩ := all_candidates_can_pass_nonminimally
  exact ⟨ho, by simp [ho, hl], by simpa [hl] using hc⟩

