import Verification.QuantumDeutschJozsaGeneral

noncomputable section
open QuantumDeutschJozsaGeneral

-- General operators, not a fixed list of dimensions or truth tables.
example (n : ℕ) (v w : State n) : inner (hadamard v) (hadamard w) = inner v w :=
  hadamard_inner v w
example (n : ℕ) (f : Bits n → Bool) (v : State n) :
    xorOracle f (productState v minus) = productState (phaseOracle f v) minus :=
  dj_phase_kickback f v
example (n : ℕ) (f : Bits n → Bool) : jointNorm (jointRun f) = 1 :=
  joint_run_normalized f
example (n : ℕ) (f : Bits n → Bool) (hp : DJPromise f) (y : Bits n)
    (hy : 0 < outcomeWeight f y) : y ≠ zeroBits n ↔ IsBalanced f :=
  (promised_outcome_correct f hp y hy).2
example (n : ℕ) (f : Bits n → Bool) (hb : IsBalanced f) :
    (∑ y ∈ Finset.univ.erase (zeroBits n), outcomeWeight f y) = 1 := nonzero_weight f hb

-- No arbitrary even-cardinality assumption is needed for constant functions.
example : zeroStateProb (fun _ : Fin 3 => true) = 1 :=
  dj_constant_amplitude _ (fun _ _ => rfl) (by decide)
-- An empty generic domain is excluded from the classification theorem.
example : IsConstant (fun _ : Fin 0 => false) ∧ IsBalanced (fun _ : Fin 0 => false) ∧
    zeroStateProb (fun _ : Fin 0 => false) = 0 := by
  refine ⟨fun _ _ => rfl, ?_, ?_⟩
  · unfold IsBalanced trueCount; decide
  · simp [zeroStateProb, zeroStateAmplitude]
example (f : Bits 0 → Bool) : ¬ IsBalanced f := (bits_zero_result f).2.1
example (v : State 0) : hadamard v = v := hadamard_zero v

-- Both old amplitudes and both old classification predicates are preserved.
example (f : Bool → Bool) :
    runDJ (liftOne f) (fun _ => false) = QuantumDeutschJozsa.amp0 f ∧
    runDJ (liftOne f) (fun _ => true) = QuantumDeutschJozsa.amp1 f := dj_compat_one_qubit f
example (f : Bool → Bool) : IsBalanced (liftOne f) ↔ QuantumDeutschJozsa.IsBalanced f :=
  balanced_compat f
example (f : Bool → Bool) : IsConstant (liftOne f) ↔ QuantumDeutschJozsa.IsConstant f :=
  constant_compat f
example (n : ℕ) : runDJ (fun _ : Bits n => true) = fun y => -basis (zeroBits n) y := by
  simpa [signOfBool] using run_constant (fun _ : Bits n => true) true (fun _ => rfl)

-- Promise failure and multiple nonzero outputs are different phenomena.
example : ¬ DJPromise (fun x : Bits 2 => x 0 && x 1) ∧
    outcomeWeight (fun x : Bits 2 => x 0 && x 1) (zeroBits 2) = 1/4 :=
  absent_promise_counterexample
example : IsBalanced nonlinearBalanced := nonlinear_balanced
example : outcomeWeight nonlinearBalanced ![true,false,false] = 1/4 ∧
    outcomeWeight nonlinearBalanced ![true,true,true] = 1/4 ∧
    (![true,false,false] : Bits 3) ≠ ![true,true,true] := balanced_not_single_output

-- A plus ancilla cannot replace minus in the kickback identity.
example : xorOracle (liftOne id) (productState (fun _ => 1) (fun _ => 1)) ≠
    productState (phaseOracle (liftOne id) (fun _ => 1)) (fun _ => 1) :=
  plus_does_not_kickback
example (u : Bool → ℝ) (b : Bool) :
    hadamard (fun x : Bits 1 => u (x 0)) (fun _ => b) = ancillaHadamard u b :=
  hadamard_one u b
example : ancillaHadamard (fun b => if b then 1 else 0) = minus := minus_prepared

example (n : ℕ) : normSquared (hadamard (fun _ : Bits n => 0)) = 0 := by
  rw [hadamard_norm]; simp [normSquared, inner]
example (n : ℕ) (a b : Bool) (x y : Bits n) :
    kernel (Fin.cons a x) (Fin.cons b y) =
      (signOfBool (a && b) / Real.sqrt 2) * kernel x y := kernel_tensor n a b x y
example : QuantumDeutschJozsaGeneralSuite := quantum_deutsch_jozsa_general_master_suite
