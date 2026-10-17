/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumQutritSecretSharingExplicitDecoder

/-! Executable finite gate semantics and its exact matrix/channel refinement.
This is not a numerical simulator, circuit compiler, hardware model, fault-tolerance
claim, or proof of gate-count optimality. Circuits execute left to right. -/
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder Kronecker
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract
open QuantumKnillLaflammeEnvironmentCriterion QuantumReferencePreservingRecoveryContract
open QuantumErasureCorrectabilityContract QuantumQutritTwoOfThreeSecretSharingContract
open QuantumQutritSecretSharingExplicitDecoder
namespace QuantumQutritDecoderCircuitRefinement

/-- Basis permutations: controlled addition, exchange, and a local cyclic shift. -/
inductive Gate where
  | addFirst (coefficient : Fin 3)
  | addSecond (coefficient : Fin 3)
  | swap
  | shiftFirst (offset : Fin 3)
  deriving DecidableEq, Repr

def evalGate : Gate → Fin 3 × Fin 3 → Fin 3 × Fin 3
  | .addFirst c, (u,v) => (u+c*v,v)
  | .addSecond c, (u,v) => (u,v+c*u)
  | .swap, (u,v) => (v,u)
  | .shiftFirst c, (u,v) => (u+c,v)

def inverseGate : Gate → Gate
  | .addFirst c => .addFirst (-c)
  | .addSecond c => .addSecond (-c)
  | .swap => .swap
  | .shiftFirst c => .shiftFirst (-c)

theorem gate_inverse_left : ∀ g x, evalGate (inverseGate g) (evalGate g x) = x := by
  intro g
  cases g with
  | addFirst c => revert c; decide
  | addSecond c => revert c; decide
  | swap => decide
  | shiftFirst c => revert c; decide

theorem gate_inverse_right : ∀ g x, evalGate g (evalGate (inverseGate g) x) = x := by
  intro g
  cases g with
  | addFirst c => revert c; decide
  | addSecond c => revert c; decide
  | swap => decide
  | shiftFirst c => revert c; decide

/-- The head gate executes first. No complex arithmetic or choice is needed here. -/
def runCircuit : List Gate → Fin 3 × Fin 3 → Fin 3 × Fin 3
  | [], x => x
  | g :: gs, x => runCircuit gs (evalGate g x)

def inverseCircuit : List Gate → List Gate
  | [] => []
  | g :: gs => inverseCircuit gs ++ [inverseGate g]

theorem run_append (a b : List Gate) (x : Fin 3 × Fin 3) :
    runCircuit (a ++ b) x = runCircuit b (runCircuit a x) := by
  induction a generalizing x with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, runCircuit, ih]

theorem circuit_inverse_left (gs : List Gate) (x : Fin 3 × Fin 3) :
    runCircuit (inverseCircuit gs) (runCircuit gs x) = x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => simp only [inverseCircuit, run_append, runCircuit, ih, gate_inverse_left]

theorem circuit_inverse_right (gs : List Gate) (x : Fin 3 × Fin 3) :
    runCircuit gs (runCircuit (inverseCircuit gs) x) = x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => simp only [inverseCircuit, run_append, runCircuit, gate_inverse_right, ih]

/-- Two controlled subtractions in Z_3, followed by exchange of coordinates. -/
def decoderCircuit : List Gate := [.addSecond 2, .addFirst 2, .swap]

theorem decoder_coordinates : ∀ x, runCircuit decoderCircuit x = decodeCoordinates x := by
  decide

theorem decoder_length : decoderCircuit.length = 3 := rfl

/-- Executable basis-index evaluation, including the exact flattening convention. -/
def runIndex (gs : List Gate) (x : Fin 9) : Fin 9 :=
  finProdFinEquiv (runCircuit gs (finProdFinEquiv.symm x))

def circuitEquiv (gs : List Gate) : Fin 9 ≃ Fin 9 :=
  finProdFinEquiv.symm.trans ((Equiv.mk (runCircuit gs) (runCircuit (inverseCircuit gs))
    (circuit_inverse_left gs) (circuit_inverse_right gs)).trans finProdFinEquiv)

theorem index_equiv (gs : List Gate) (x : Fin 9) : runIndex gs x = circuitEquiv gs x := rfl

theorem decoder_index (x : Fin 9) : runIndex decoderCircuit x = decoderEquiv x := by
  simp [runIndex, decoderEquiv, decoder_coordinates]

/-- Deliberately incorrect variants; rejection is not a noise-correction result. -/
def wrongSign : List Gate := [.addSecond 1, .addFirst 2, .swap]
def missingSwap : List Gate := [.addSecond 2, .addFirst 2]
def wrongOrder : List Gate := [.addFirst 2, .addSecond 2, .swap]
def shiftedOutput : List Gate := decoderCircuit ++ [.shiftFirst 1]

theorem wrong_sign_witness : runCircuit wrongSign (1,0) ≠ decodeCoordinates (1,0) := by decide
theorem missing_swap_witness : runCircuit missingSwap (0,1) ≠ decodeCoordinates (0,1) := by decide
theorem wrong_order_witness : runCircuit wrongOrder (1,0) ≠ decodeCoordinates (1,0) := by decide
theorem shifted_output_witness :
    runCircuit shiftedOutput (0,0) ≠ decodeCoordinates (0,0) := by decide

noncomputable section

/-- Column x is the output basis vector of the executed circuit. -/
def circuitMatrix (gs : List Gate) : Q 9 :=
  fun y x => if y = circuitEquiv gs x then 1 else 0

theorem circuit_equiv_append (a b : List Gate) (x : Fin 9) :
    circuitEquiv (a ++ b) x = circuitEquiv b (circuitEquiv a x) := by
  simp [circuitEquiv, run_append]

/-- Matrix products reverse the written execution order: b acts after a. -/
theorem matrix_append (a b : List Gate) :
    circuitMatrix (a ++ b) = circuitMatrix b * circuitMatrix a := by
  ext y x
  simp [circuitMatrix, Matrix.mul_apply, mul_ite, circuit_equiv_append]

theorem circuit_unitary_left (gs : List Gate) :
    (circuitMatrix gs).conjTranspose * circuitMatrix gs = 1 := by
  ext x y
  simp [circuitMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    mul_ite, eq_comm]

theorem circuit_unitary_right (gs : List Gate) :
    circuitMatrix gs * (circuitMatrix gs).conjTranspose = 1 := by
  ext x y
  obtain ⟨u,rfl⟩ := (circuitEquiv gs).surjective x
  obtain ⟨v,rfl⟩ := (circuitEquiv gs).surjective y
  simp [circuitMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    mul_ite]

theorem decoder_matrix : circuitMatrix decoderCircuit = decoder := by
  ext y x
  change (if y = runIndex decoderCircuit x then (1 : ℂ) else 0) = _
  rw [decoder_index]
  rfl

/-- Explicit product of the three primitive gate matrices. -/
theorem decoder_gate_product :
    circuitMatrix [.swap] * circuitMatrix [.addFirst 2] * circuitMatrix [.addSecond 2] =
      decoder := by
  rw [← matrix_append, ← matrix_append]
  exact decoder_matrix

theorem decoder_action (Y : Q 9) :
    circuitMatrix decoderCircuit * Y * (circuitMatrix decoderCircuit).conjTranspose =
      decoder * Y * decoder.conjTranspose := by rw [decoder_matrix]

def circuitKraus (t : Fin 3) : Matrix (Fin 3) (Fin 9) ℂ :=
  erasureOperator 3 3 t * circuitMatrix decoderCircuit

theorem kraus_refinement (t : Fin 3) : circuitKraus t = recoveryOperator t := by
  simp only [circuitKraus, recoveryOperator, decoder_matrix]

theorem circuit_complete : ∑ t, (circuitKraus t).conjTranspose * circuitKraus t = 1 := by
  simp only [kraus_refinement]
  exact recovery_complete

def circuitRecovery : KrausChannel 9 3 3 where
  operators := circuitKraus
  complete := circuit_complete

/-- Equality on every physical input, not only encoded states. -/
theorem channel_refinement (Y : Q 9) :
    apply_channel circuitRecovery Y = apply_channel explicitRecovery Y := by
  simp only [apply_channel_eq, circuitRecovery, explicitRecovery, kraus_refinement]

theorem circuit_recovery (q : Fin 3) (X : Q 3) :
    apply_channel circuitRecovery (retainedPair q (encode code X)) = X := by
  rw [channel_refinement, explicit_recovery]

theorem circuit_reference_recovery (q : Fin 3) (m : ℕ) (X : Joint m 3) :
    liftedRecovery (erasureChannel 9 3) (groupedCode q) circuitRecovery m X = X :=
  erasure_reference_recovery _ _ (circuit_recovery q) m X

theorem circuit_pair_agreement (q : Fin 3) (X : Q 3) :
    apply_channel circuitRecovery (retainedPair q (encode code X)) =
      apply_channel (pairRecovery q) (retainedPair q (encode code X)) := by
  rw [channel_refinement, agrees_with_pairRecovery]

/-- A wrong output basis label gives a concrete unequal matrix column. -/
theorem matrix_ne_of_index_ne (gs : List Gate) (x : Fin 9)
    (h : runIndex gs x ≠ decoderEquiv x) : circuitMatrix gs ≠ decoder := by
  intro hm
  have entry := congrArg (fun M : Q 9 => M (runIndex gs x) x) hm
  simp [circuitMatrix, decoder, ← index_equiv, h] at entry

theorem wrong_sign_matrix : circuitMatrix wrongSign ≠ decoder :=
  matrix_ne_of_index_ne wrongSign 3 (by decide)
theorem missing_swap_matrix : circuitMatrix missingSwap ≠ decoder :=
  matrix_ne_of_index_ne missingSwap 1 (by decide)
theorem wrong_order_matrix : circuitMatrix wrongOrder ≠ decoder :=
  matrix_ne_of_index_ne wrongOrder 3 (by decide)
theorem shifted_output_matrix : circuitMatrix shiftedOutput ≠ decoder :=
  matrix_ne_of_index_ne shiftedOutput 0 (by decide)

structure QuantumQutritDecoderCircuitRefinementSuite : Prop where
  inverse_left : ∀ gs x, runCircuit (inverseCircuit gs) (runCircuit gs x) = x
  inverse_right : ∀ gs x, runCircuit gs (runCircuit (inverseCircuit gs) x) = x
  coordinates : ∀ x, runCircuit decoderCircuit x = decodeCoordinates x
  composition : ∀ a b, circuitMatrix (a ++ b) = circuitMatrix b * circuitMatrix a
  matrix : circuitMatrix decoderCircuit = decoder
  unitary_left : ∀ gs, (circuitMatrix gs).conjTranspose * circuitMatrix gs = 1
  unitary_right : ∀ gs, circuitMatrix gs * (circuitMatrix gs).conjTranspose = 1
  kraus : ∀ t, circuitKraus t = recoveryOperator t
  completeness : ∑ t, (circuitKraus t).conjTranspose * circuitKraus t = 1
  channel : ∀ Y, apply_channel circuitRecovery Y = apply_channel explicitRecovery Y
  recovery : ∀ q X, apply_channel circuitRecovery (retainedPair q (encode code X)) = X
  reference : ∀ q m X,
    liftedRecovery (erasureChannel 9 3) (groupedCode q) circuitRecovery m X = X
  agreement : ∀ q X, apply_channel circuitRecovery (retainedPair q (encode code X)) =
    apply_channel (pairRecovery q) (retainedPair q (encode code X))
  wrong_sign : runCircuit wrongSign (1,0) ≠ decodeCoordinates (1,0)
  missing_swap : runCircuit missingSwap (0,1) ≠ decodeCoordinates (0,1)
  wrong_order : runCircuit wrongOrder (1,0) ≠ decodeCoordinates (1,0)
  shifted_output : runCircuit shiftedOutput (0,0) ≠ decodeCoordinates (0,0)

theorem verification_suite : QuantumQutritDecoderCircuitRefinementSuite where
  inverse_left := circuit_inverse_left
  inverse_right := circuit_inverse_right
  coordinates := decoder_coordinates
  composition := matrix_append
  matrix := decoder_matrix
  unitary_left := circuit_unitary_left
  unitary_right := circuit_unitary_right
  kraus := kraus_refinement
  completeness := circuit_complete
  channel := channel_refinement
  recovery := circuit_recovery
  reference := circuit_reference_recovery
  agreement := circuit_pair_agreement
  wrong_sign := wrong_sign_witness
  missing_swap := missing_swap_witness
  wrong_order := wrong_order_witness
  shifted_output := shifted_output_witness

end
end QuantumQutritDecoderCircuitRefinement
