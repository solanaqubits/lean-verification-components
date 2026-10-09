import Verification.QuantumDeutschJozsaNBitBalanced

open QuantumDeutschJozsaGeneral QuantumDeutschJozsaNBitBalanced

example : QuantumDeutschJozsaNBitBalancedSuite := quantum_deutsch_jozsa_nbit_balanced_master_suite

example (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (BalancedFamily n) = Nat.choose (2 ^ n) (2 ^ (n - 1)) :=
  balanced_card_formula_pos hn

example : Fintype.card (BalancedFamily 0) = 0 ∧ Fintype.card (BalancedFamily 1) = 2 ∧
    Fintype.card (BalancedFamily 2) = 6 ∧ Fintype.card (BalancedFamily 3) = 70 :=
  ⟨balanced_count_n0, balanced_count_n1, balanced_count_n2, balanced_count_n3⟩

-- Dropping n ≥ 1 from the cardinality formula gives a false statement.
example : Fintype.card (BalancedFamily 0) ≠ Nat.choose (2 ^ 0) (2 ^ (0 - 1)) := by
  rw [balanced_card_zero_qubits]
  decide

example : ¬ IsBalanced (ofSupport (Finset.univ : Finset (Bits 0))) :=
  (bits_zero_result _).2.1

example (n : ℕ) (S : Finset (Bits n)) : toSupport (ofSupport S) = S := toSupport_ofSupport S
example (n : ℕ) (f : Bits n → Bool) : ofSupport (toSupport f) = f := ofSupport_toSupport f

example (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    trueCount (fromFinOracle f) = trueCount f ∧
      (IsBalanced (fromFinOracle f) ↔ IsBalanced f) :=
  ⟨fin_oracle_trueCount f, fin_oracle_balanced f⟩

example (n : ℕ) (f : Bits n → Bool) :
    (runDJ f (zeroBits n) = 0 ↔ IsBalanced f) ∧
      (outcomeWeight f (zeroBits n) = 0 ↔ IsBalanced f) :=
  ⟨(balanced_iff_run_zero f).symm, (balanced_iff_outcome_zero f).symm⟩

example (n : ℕ) (hn : 1 ≤ n) :
    outcomeWeight (fun x : Bits n => x ⟨0, hn⟩) (zeroBits n) = 0 :=
  (balanced_iff_outcome_zero _).mp (constructive_witness_n_pos hn)

example (n : ℕ) : ¬ IsBalanced (fun _ : Bits n => false) :=
  constants_excluded _ (fun _ _ => rfl)

example (n : ℕ) (f : Bits n → Bool) (hp : DJPromise f) :
    (zeroStateProb f = 0 ↔ IsBalanced f) ∧ (zeroStateProb f = 1 ↔ IsConstant f) :=
  dj_promise_separation_exact f hp

-- The existing nonlinear balanced oracle remains in the classified family.
example : Nonempty (BalancedFamily 3) := ⟨⟨nonlinearBalanced, nonlinear_balanced⟩⟩
example : runDJ nonlinearBalanced (zeroBits 3) = 0 :=
  (balanced_iff_run_zero _).mp nonlinear_balanced
