import Verification.QuantumSimonsAlgorithm

open QuantumSimonsAlgorithm
open QuantumDeutschJozsaGeneral (zeroBits)
open scoped BigOperators

-- Arbitrary complex inputs, with no promise or normalization precondition.
example (f : Register n → Register m) (a b : ℂ) (u v : JointState n m) :
    xorOracle f (fun x z => a*u x z+b*v x z) =
      fun x z => a*xorOracle f u x z+b*xorOracle f v x z := oracle_linear f a b u v
example (f : Register n → Register m) (v : JointState n m) :
    xorOracle f (xorOracle f v) = v := oracle_involution f v
example (f : Register n → Register m) (u v : JointState n m) :
    hermitian (xorOracle f u) v = hermitian u (xorOracle f v) := oracle_self_adjoint f u v
example (u v : JointState n m) :
    hermitian (inputHadamard u) (inputHadamard v) = hermitian u v := hadamard_inner u v
example (f : Register n → Register m) : (∑ y, probability f y) = 1 :=
  simon_distribution_normalized f

-- Smallest nonzero period, including a zero-qubit output register.
def onePeriod : Register 1 := fun _ => true
example : SimonPromise (fun _ : Register 1 => zeroBits 0) onePeriod := by
  unfold SimonPromise onePeriod xorVec zeroBits
  decide
example : probability (fun _ : Register 1 => zeroBits 0) (zeroBits 1) = 1 := by
  have h : SimonPromise (fun _ : Register 1 => zeroBits 0) onePeriod := by
    unfold SimonPromise onePeriod xorVec zeroBits; decide
  rw [simon_exact_probability_distribution h]
  norm_num [dot, encode, bit, zeroBits]
example : ¬ ∃ f : Register 0 → Register m, ∃ s, SimonPromise f s := by
  rintro ⟨f,s,h⟩
  exact h.1 (no_nonzero_period_n0 s)

-- Two-bit parity has period 11 and exactly the two allowed outcomes 00 and 11.
def parityOracle (x : Register 2) : Register 1 := fun _ => x 0 ^^ x 1
def period11 : Register 2 := ![true,true]
theorem parity_promise : SimonPromise parityOracle period11 := by
  unfold SimonPromise parityOracle period11 xorVec zeroBits
  decide
example : probability parityOracle ![false,false] = 1/2 := by
  rw [simon_exact_probability_distribution parity_promise]
  norm_num [dot, encode, bit, period11, Fin.sum_univ_two]
example : probability parityOracle ![true,true] = 1/2 := by
  rw [simon_exact_probability_distribution parity_promise]
  have h : dot ![true,true] period11 = 0 := rfl
  rw [if_pos h]; norm_num
example : probability parityOracle ![false,true] = 0 := by
  rw [simon_exact_probability_distribution parity_promise]
  have h : dot ![false,true] period11 = 1 := rfl
  rw [h]; norm_num
example (z : Register 1) : runSimon parityOracle ![true,false] z = 0 := by
  apply simon_amplitude_zero_when_odd_dot parity_promise
  rfl

-- A two-bit output with a fixed trailing zero leaves half its labels unreachable.
def paddedOracle (x : Register 2) : Register 2 := ![x 0 ^^ x 1, false]
example (y : Register 2) : runSimon paddedOracle y ![false,true] = 0 := by
  rw [simon_circuit_amplitude]
  have h : ∀ x, paddedOracle x ≠ ![false,true] := by
    intro x he; have := congrFun he 1; simp [paddedOracle] at this
  simp [fiberSum, h]

-- Rank is the dimension of the span, not the number of observations.
example (v : Register 2) :
    (∀ y ∈ ({period11} : Finset (Register 2)), dot y v = 0) ↔
      v = zeroBits 2 ∨ v = period11 := by
  apply simon_linear_system_recovery period11 {period11} parity_promise.1
  · intro y hy
    simp only [Finset.mem_singleton] at hy
    subst y
    rfl
  · have he : rowSpan {period11} = Submodule.span (ZMod 2) {encode period11} := by
      unfold rowSpan
      congr 1
      ext w
      simp
    have hn : encode period11 ≠ 0 := by
      intro h
      apply parity_promise.1
      apply encode_injective
      simpa using h
    rw [he, finrank_span_singleton hn]

-- Insufficient rank leaves extra solutions.
example : (∀ y ∈ (∅ : Finset (Register 2)), dot y ![true,false] = 0) ∧
    ![true,false] ≠ zeroBits 2 ∧ ![true,false] ≠ period11 := by
  constructor
  · simp
  · constructor <;> decide

-- Without the promise, a constant two-bit function gives weight 1 at zero, not 1/2.
example : probability (fun _ : Register 2 => zeroBits 0) (zeroBits 2) = 1 := by
  have ha (z : Register 0) :
      runSimon (fun _ : Register 2 => zeroBits 0) (zeroBits 2) z = 1 := by
    rw [simon_circuit_amplitude]
    have hz : z = zeroBits 0 := Subsingleton.elim _ _
    rw [hz]
    norm_num [fiberSum, Register, QuantumDeutschJozsaGeneral.Bits]
  simp [probability, ha, Register, QuantumDeutschJozsaGeneral.Bits]

example : ¬ SimonPromise (fun _ : Register 2 => zeroBits 0) period11 := by
  unfold SimonPromise period11 xorVec zeroBits
  decide

example : QuantumSimonsSuite := quantum_simons_master_suite
