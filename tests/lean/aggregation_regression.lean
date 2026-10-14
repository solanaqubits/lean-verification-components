import Verification.CryptoBulletproofsAggregation

open scoped BigOperators
open CryptoBulletproofsAggregation CryptoBulletproofsInnerProduct
open CryptoBulletproofsRangeReduction
abbrev F := ZMod 17
instance : Fact (Nat.Prime 17) := ⟨by decide⟩

def params (a b : ℕ) : AggGenerators F a b :=
  ⟨3, 5, 7, fun r => 11+(global_index r : F), fun r => 31+(global_index r : F)⟩
def bits (a b mode : ℕ) : Bits a b F := fun r =>
  if mode=0 then 0 else if mode=1 then 1 else if global_index r % 2=0 then 0 else 1
def maskS (a b : ℕ) : Bits a b F := fun r => 2+(global_index r : F)
def maskT (a b : ℕ) : Bits a b F := fun r => 4+(global_index r : F)
def blinds (b : ℕ) : Fin (2 ^ b) → F := fun j => 6+(j.val : F)
def xs (a b : ℕ) : Fin (a+b) → Fˣ := fun _ => Units.mk0 3 (by decide)
def proof (a b mode : ℕ) : AggregatedRangeProof 17 F a b :=
  agg_prover (params a b) (bits a b mode) (maskS a b) (maskT a b) (blinds b)
    8 9 10 12 2 3 5 (xs a b)
def commitments (a b mode : ℕ) : Fin (2 ^ b) → F := fun j =>
  agg_value_commit (params a b) (block_value (bits a b mode) j) (blinds b j)
def check (a b mode : ℕ) : Bool :=
  verify_aggregation (params a b) (commitments a b mode) 2 3 5 (xs a b) (proof a b mode)

theorem honest (a b mode : ℕ) : check a b mode = true := by
  apply agg_completeness (params a b) (bits a b mode) (maskS a b) (maskT a b)
    _ (blinds b) 8 9 10 12 2 3 5 (xs a b) (by decide) _ (fun _ => rfl)
  intro r
  by_cases h0 : mode = 0
  · simp [bits, h0]
  by_cases h1 : mode = 1
  · simp [bits, h1]
  by_cases h2 : global_index r % 2 = 0 <;> simp [bits, h0, h1, h2]

example : check 0 0 0 = true := honest _ _ _
example : check 0 0 1 = true := honest _ _ _
example : check 1 0 0 = true := honest _ _ _
example : check 1 0 1 = true := honest _ _ _
example : check 2 0 1 = true := honest _ _ _
example : check 0 1 1 = true := honest _ _ _
example : check 1 1 2 = true := honest _ _ _
example : check 2 1 2 = true := honest _ _ _
example : check 0 2 2 = true := honest _ _ _
example : check 1 2 2 = true := honest _ _ _
example : check 2 2 0 = true := honest _ _ _
example : check 2 2 1 = true := honest _ _ _
example : check 2 2 2 = true := honest _ _ _
example : block_value (bits 2 2 1) 0 = (15 : F) := by decide
example : block_value (bits 2 2 0) 3 = (0 : F) := by decide
example : 2 ^ (2 ^ 2) < 17 := by decide
example (y z : F) : agg_delta 1 4 y z = delta_fn y z 4 := agg_delta_m1_spec _ _
example (u v s t : Block 2 4 → F) y z x :
    block_dot (agg_l_poly u s z x) (agg_r_poly v t y z x) =
      agg_t0 u v y z+agg_t1 u v s t y z*x+agg_t2 s t y*x ^ 2 := agg_inner_product_expansion _ _ _ _ _ _ _
example (u v : Block 2 4 → F) (values : Fin 2 → F)
    (h : agg_formal_t0 u v = agg_formal_rhs values 4) :
    ∀ r, u r=0 ∨ u r=1 := (agg_poly_identity_implies_bits _ _ _ h).2.1
example (u v : Block 2 4 → F) (values : Fin 2 → ℕ) (hv : ∀ j, values j<17)
    (h : agg_formal_t0 u v = agg_formal_rhs (fun j => (values j : F)) 4) :
    ∀ j, values j<16 := agg_formal_natural_range _ _ _ hv (by decide) h
example (u v s t : Block 2 4 → F) values :
    agg_formal_curve u v s t = agg_formal_curve_rhs u v s t values ↔
      (∀ r, v r=u r-1) ∧ (∀ r, u r=0 ∨ u r=1) ∧
      (∀ j, block_value u j=values j) := agg_three_variable_iff _ _ _ _ _
example : verify_aggregation (params 1 1) (commitments 1 1 2) 0 3 5 (xs 1 1)
    (proof 1 1 2) = false := agg_zero_y_rejected _ _ _ _ _ _
example : verify_aggregation (params 0 1) (commitments 0 1 1) 2 3 5 (xs 0 1)
    { proof 0 1 1 with T1 := (proof 0 1 1).T1+1 } = false := by decide
example : verify_aggregation (params 0 1) (commitments 0 1 1) 2 3 5 (xs 0 1)
    { proof 0 1 1 with T2 := (proof 0 1 1).T2+1 } = false := by decide
example : verify_aggregation (params 0 1) (commitments 0 1 1) 2 3 5 (xs 0 1)
    { proof 0 1 1 with tx := (proof 0 1 1).tx+1 } = false := by decide
example : (group_payload (proof 2 2 1).ipa).length = 8 ∧
    (scalar_payload (proof 2 2 1).ipa).length = 2 := agg_ipa_transcript_size _
example : (agg_group_payload (proof 2 2 1)).length = 12 ∧
    (agg_scalar_payload (proof 2 2 1)).length = 5 := agg_full_proof_size _
example : (envelope_group_payload ⟨commitments 2 2 1, proof 2 2 1⟩).length = 16 :=
  agg_envelope_size _
example : global_index ((1 : Fin 2), (3 : Fin 4)) = 7 := by decide
example : block_weight (2 : F) ((1 : Fin 2), (0 : Fin 1)) ≠ 2 ^ 2 := by decide
example : (∑ j : Fin 2, (2 : F) ^ (j.val+2) * (j.val : F)) ≠
    ∑ j : Fin 2, (2 : F) ^ (j.val+2) * (1-(j.val : F)) := by decide
example : CryptoBulletproofsAggregationSuite := CryptoBulletproofsAggregation.verification_suite

example : ¬∃ u : Fin 4 → ℕ, (∀ i, u i ≤ 1) ∧
    CryptoPedersenRangeProofLinear.bitValue u = 16 := by
  rintro ⟨u, hb, hv⟩
  have h := CryptoPedersenRangeProofLinear.bitValue_lt u hb
  rw [hv] at h
  norm_num at h
example : agg_t0 (fun _ : Block 2 1 => (2 : F)) (fun _ => 1) 1 1 =
    (∑ j : Fin 2, (1 : F) ^ (j.val+2)*4) + agg_delta 2 1 (1 : F) 1 := by decide
example : agg_formal_t0 (fun _ : Block 2 1 => (2 : F)) (fun _ => 1) ≠
    agg_formal_rhs (fun _ : Fin 2 => (4 : F)) 1 := by
  intro h
  have hb := (agg_poly_identity_implies_bits _ _ _ h).2.1 (0,0)
  exact (by decide : ¬((2 : F) = 0 ∨ (2 : F) = 1)) hb

def main : IO Unit := do
  let matrix := (List.range 3).flatMap fun a => (List.range 3).flatMap fun b =>
    (List.range 3).map fun mode => check a b mode
  let tr := proof 1 1 2
  let verify := verify_aggregation (params 1 1) (commitments 1 1 2) 2 3 5 (xs 1 1)
  let extra : List Bool := [
    !(verify { tr with T1 := tr.T1+1 }), !(verify { tr with T2 := tr.T2+1 }),
    !(verify { tr with tx := tr.tx+1 }), !(verify { tr with mu := tr.mu+1 }),
    !(verify_aggregation (params 1 1) (commitments 1 1 2) 0 3 5 (xs 1 1) tr),
    decide (block_value (bits 2 2 1) 0 = (15 : F)),
    decide (block_value (bits 2 2 0) 3 = (0 : F)),
    decide (block_weight (2 : F) ((1 : Fin 2), (0 : Fin 1)) ≠ 2 ^ 2),
    decide ((agg_group_payload (proof 2 2 1)).length=12),
    decide ((agg_scalar_payload (proof 2 2 1)).length=5),
    decide ((envelope_group_payload ⟨commitments 2 2 1, proof 2 2 1⟩).length=16)]
  let cases := matrix ++ extra
  if cases.all id then IO.println s!"BULLETPROOFS_AGGREGATION_EXEC_OK: {cases.length} cases"
  else throw (IO.userError s!"Aggregation regression failed: {cases}")
#eval main
