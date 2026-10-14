import Verification.CryptoBulletproofsBatchVerification

open CryptoBulletproofsBatchVerification CryptoBulletproofsRangeReduction CryptoBulletproofsInnerProduct
open scoped BigOperators ENNReal
instance : Fact (Nat.Prime 17) := ⟨by decide⟩
abbrev F := ZMod 17

def challenge : Fˣ := ⟨2, 9, by decide, by decide⟩
def params (k : ℕ) : Generators 17 F k :=
  ⟨3, 5, 7, fun i => (i.val + 1 : ℕ), fun i => (i.val + 6 : ℕ)⟩
def bits (k v : ℕ) : Vec k F := fun i => (v / 2^i.val % 2 : ℕ)
def xs (k : ℕ) : Fin k → Fˣ := fun _ => challenge

def instanceProof (k v : ℕ) (y : F := 1) : ProofInstance 17 F k :=
  ⟨value_commit (params k) (v : F) 4, y, 3, 4, xs k,
    range_prover (params k) (bits k v) (fun i => (i.val + 2 : ℕ)) (fun _ => 3)
      4 5 6 7 8 y 3 4 (xs k)⟩
def good : Fin 2 → ProofInstance 17 F 1 := ![instanceProof 1 0, instanceProof 1 3]
def bad : ProofInstance 17 F 1 := alter_T1 (instanceProof 1 3) 1
def badScalar : ProofInstance 17 F 1 :=
  { instanceProof 1 3 with transcript :=
    { (instanceProof 1 3).transcript with tx := (instanceProof 1 3).transcript.tx + 1 } }
def cancellationBatch : Fin 2 → ProofInstance 17 F 1 :=
  ![alter_T1 (instanceProof 1 3) 1, alter_T1 (instanceProof 1 3) (-1)]
def sampleWeights : Fin 4 → F := ![2, 3, 5, 7]

lemma scaled_one {n : ℕ} (H : Fin n → F) : scaled_H H (1 : F) = H := by
  funext i
  simp [scaled_H]

lemma honest (k v : ℕ) (hb : ∀ i, bits k v i * (bits k v i - 1) = 0)
    (hv : ∑ i, (2 : F)^i.val * bits k v i = (v : F)) :
    individual_verify (params k) (instanceProof k v) = true := by
  apply honest_individual_completeness <;> first | decide | assumption

example : individual_verify (params 0) (instanceProof 0 0) = true := honest _ _ (by decide) (by decide)
example : individual_verify (params 0) (instanceProof 0 1) = true := honest _ _ (by decide) (by decide)
example : individual_verify (params 1) (instanceProof 1 3) = true := honest _ _ (by decide) (by decide)
example : individual_verify (params 2) (instanceProof 2 15) = true := honest _ _ (by decide) (by decide)
example (r : Fin 0 → F) : verify_batch (params 1) (Fin.elim0 : Fin 0 → _) r = true := by
  apply batch_protocol_completeness
  intro j
  exact Fin.elim0 j
example : verify_batch (params 1) good sampleWeights = true := by
  apply batch_protocol_completeness
  intro j
  fin_cases j <;> exact honest _ _ (by decide) (by decide)
example (r : Fin 2 → F) : verify_batch (params 1) (fun _ : Fin 1 => instanceProof 1 3 0) r = false :=
  batch_zero_y_rejected (q := 17) (m := 1) (params 1)
    (fun _ => instanceProof 1 3 0) 0 rfl r
example (r : Fin 2 → F) : verify_batch (params 1)
    (fun _ : Fin 1 => { instanceProof 1 3 with x := 0 }) r = false :=
  batch_zero_x_rejected (q := 17) (m := 1) (params 1)
    (fun _ => { instanceProof 1 3 with x := 0 }) 0 rfl r
example : verify_batch (params 1) (fun _ : Fin 1 => bad) 0 = true := by
  simp only [verify_batch, batch_residual_sum, Pi.zero_apply, zero_smul,
    Finset.sum_const_zero, decide_true, Bool.and_true]
  decide
example (r : Fin 2 → F) : verify_batch (params 1) (fun _ : Fin 1 => bad) r =
    verify_batch_msm (params 1) (fun _ : Fin 1 => bad) r := verify_batch_msm_equiv _ _ _
example : polynomial_residual (params 1) bad ≠ 0 := by
  apply altered_T1_detectable _ _ _ (by decide) (by decide)
  exact ((individual_iff_residuals_zero _ _).mp (honest 1 3 (by decide) (by decide))).2.1
example : (PMF.uniformOfFintype (Fin 2 → F)).toOuterMeasure
    {r | verify_batch (params 1) (fun _ : Fin 1 => bad) r = true} ≤ 1 / (17 : ℝ≥0∞) := by
  apply batch_protocol_soundness (q := 17) (m := 1)
  refine ⟨0, fun h => ?_⟩
  have hbad := altered_T1_detectable (params 1) (instanceProof 1 3) (1 : F)
    (by decide) (by decide)
    (((individual_iff_residuals_zero _ _).mp (honest 1 3 (by decide) (by decide))).2.1)
  exact hbad ((individual_iff_residuals_zero _ _).mp h).2.1
example : batch_residual_sum (![1, -1] : Fin 2 → F) (![3, 3] : Fin 2 → F) = 0 := by decide
example : (1 : F) ≠ 0 := by decide
example : batch_residual_sum (![1, -1] : Fin 2 → F) (![3, 4] : Fin 2 → F) ≠ 0 := by decide
example (e : Equiv.Perm (Fin 2)) :
    verify_batch (params 1) (good ∘ e) (permute_weights e sampleWeights) =
      verify_batch (params 1) good sampleWeights := batch_joint_permutation_invariance _ _ _ _
example (D : Fin 4 → F) (h : ∃ j, D j ≠ 0) : acceptance_probability (q := 17) D ≤ 1 / 17 :=
  batch_soundness_error_bound _ h
example : CryptoBulletproofsBatchVerificationSuite := CryptoBulletproofsBatchVerification.verification_suite

def main : IO Unit := do
  let single (k v : ℕ) := verify_batch (params k) (fun _ : Fin 1 => instanceProof k v) ![3, 5]
  let cancellationAccepted := verify_batch (params 1) cancellationBatch ![1, 1, 0, 0]
  let badAcceptCount := ((List.range 17).flatMap fun a => (List.range 17).map fun b =>
    verify_batch (params 1) (fun _ : Fin 1 => bad) ![(a : F), (b : F)]).filter id |>.length
  let badScalarCount := ((List.range 17).flatMap fun a => (List.range 17).map fun b =>
    verify_batch_msm (params 1) (fun _ : Fin 1 => badScalar) ![(a : F), (b : F)]).filter id |>.length
  let cases : List Bool := [single 0 0, single 0 1, single 1 0, single 1 3, single 2 0, single 2 15,
    verify_batch (params 1) good sampleWeights,
    verify_batch_msm (params 1) good sampleWeights,
    verify_batch (params 2) (fun _ : Fin 1 => instanceProof 2 9 3) ![2, 7],
    verify_batch_msm (params 2) (fun _ : Fin 1 => instanceProof 2 9 3) ![2, 7],
    !(verify_batch (params 1) (fun _ : Fin 1 => bad) ![1, 0]),
    !(verify_batch_msm (params 1) (fun _ : Fin 1 => badScalar) ![1, 0]),
    !(verify_batch (params 1) (fun _ : Fin 1 => instanceProof 1 3 0) 0),
    !(verify_batch (params 1) (fun _ : Fin 1 => { instanceProof 1 3 with x := 0 }) 0),
    cancellationAccepted, decide (badAcceptCount = 17), decide (badScalarCount = 17),
    verify_batch (params 1) (good ∘ Equiv.swap 0 1) (permute_weights (Equiv.swap 0 1) sampleWeights)]
  if cases.all id then IO.println s!"BULLETPROOFS_BATCH_EXEC_OK: {cases.length} cases; invalid accept counts {badAcceptCount}/289, {badScalarCount}/289"
  else throw (IO.userError s!"Batch regression failed: {cases}")
#eval main
