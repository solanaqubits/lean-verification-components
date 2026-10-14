import Verification.CryptoBulletproofsRangeReduction

open CryptoBulletproofsRangeReduction CryptoBulletproofsInnerProduct
open scoped BigOperators
instance : Fact (Nat.Prime 17) := ⟨by decide⟩
abbrev F := ZMod 17

def challenge : Fˣ := ⟨2, 9, by decide, by decide⟩
def params (k : ℕ) : Generators 17 F k :=
  ⟨3, 5, 7, fun i => (i.val + 1 : ℕ), fun i => (i.val + 6 : ℕ)⟩
def bits (k v : ℕ) : Vec k F := fun i => (v / 2^i.val % 2 : ℕ)
def xs (k : ℕ) : Fin k → Fˣ := fun _ => challenge

def transcript (k v : ℕ) (y : F := 1) :=
  range_prover (params k) (bits k v) (fun i => (i.val + 2 : ℕ)) (fun _ => 3)
    4 5 6 7 8 y 3 4 (xs k)
def run (k v : ℕ) (y : F := 1) : Bool :=
  verify_range_reduction (params k) (value_commit (params k) (v : F) 4)
    y 3 4 (xs k) (transcript k v y)

def badTx : RangeReductionTranscript 17 F 1 := { transcript 1 3 with tx := (transcript 1 3).tx + 1 }
def badMu : RangeReductionTranscript 17 F 1 := { transcript 1 3 with mu := (transcript 1 3).mu + 1 }
def badT1 : RangeReductionTranscript 17 F 1 := { transcript 1 3 with T1 := (transcript 1 3).T1 + 1 }
def badIPA : RangeReductionTranscript 17 F 1 :=
  { transcript 1 3 with ipa := { (transcript 1 3).ipa with a_final := (transcript 1 3).ipa.a_final + 1 } }
def checkBad (tr : RangeReductionTranscript 17 F 1) :=
  verify_range_reduction (params 1) (value_commit (params 1) 3 4) 1 3 4 (xs 1) tr

lemma scaled_one {n : ℕ} (H : Fin n → F) : scaled_H H (1 : F) = H := by
  funext i
  simp [scaled_H]

-- Explicit inverse simplification keeps executable tests distinct from kernel proofs.
example : run 0 0 = true := by
  simp only [run, transcript, verify_range_reduction, range_prover, range_target, scaled_one]
  decide
example : run 0 1 = true := by
  simp only [run, transcript, verify_range_reduction, range_prover, range_target, scaled_one]
  decide
example : run 1 0 = true := by
  simp only [run, transcript, verify_range_reduction, range_prover, range_target, scaled_one]
  decide
example : run 1 3 = true := by
  simp only [run, transcript, verify_range_reduction, range_prover, range_target, scaled_one]
  decide
example : run 2 0 = true := by
  simp only [run, transcript, verify_range_reduction, range_prover, range_target, scaled_one]
  decide
example : run 2 15 = true := by
  simp only [run, transcript, verify_range_reduction, range_prover, range_target, scaled_one]
  decide
example : checkBad badTx = false := by
  simp only [checkBad, badTx, transcript, verify_range_reduction, range_prover, range_target, scaled_one]
  decide
example : checkBad badMu = false := by
  simp only [checkBad, badMu, transcript, verify_range_reduction, range_prover, range_target, scaled_one]
  decide
example : checkBad badT1 = false := by
  simp only [checkBad, badT1, transcript, verify_range_reduction, range_prover, range_target, scaled_one]
  decide
example : checkBad badIPA = false := by
  simp only [checkBad, badIPA, transcript, verify_range_reduction, range_prover, range_target, scaled_one]
  decide
example : run 2 15 0 = false := zero_y_rejected _ _ _ _ _ _
example : ¬ ∃ b : Fin 4 → ℕ, (∀ i, b i ≤ 1) ∧
    CryptoPedersenRangeProofLinear.bitValue b = 16 := by
  rw [← CryptoPedersenRangeProofLinear.nat_bit_decomp_iff]
  decide
example : (2 : F) * (2 - 1) ≠ 0 := by decide
example : CryptoBulletproofsRangeReduction.t0 (fun _ : Fin 1 => (2 : F)) (fun _ => 1) 1 2 =
    2^2 * (11 : F) + delta_fn (1 : F) 2 1 := by decide
example : formal_t0 (fun _ : Fin 1 => (2 : F)) (fun _ => 1) ≠ formal_rhs (11 : F) 1 := by
  intro h
  have hb := (formal_coefficients_imply_range _ _ _ h).2.1 0
  exact (by decide : ¬ ((2 : F) = 0 ∨ (2 : F) = 1)) hb
example : formal_curve (bits 2 15) (fun i => bits 2 15 i - 1)
    (fun _ => 2) (fun _ => 3) = formal_curve_rhs (bits 2 15)
      (fun i => bits 2 15 i - 1) (fun _ => 2) (fun _ => 3) (15 : F) := by
  apply (formal_three_variable_iff _ _ _ _ _).mpr
  exact ⟨fun _ => rfl, by decide, by decide⟩
example (a b : Fin 4 → F) (h : formal_t0 a b = formal_rhs (15 : F) 4) : 15 < 2^4 :=
  formal_identity_natural_range a b 15 (by decide) (by decide) h
example (y : F) (hy : y ≠ 0) (i : Fin 4) :
    y^i.val • scaled_H (params 2).H y i = (params 2).H i := scaled_generators_valid _ _ hy _
example : CryptoBulletproofsRangeReductionSuite := CryptoBulletproofsRangeReduction.verification_suite

def main : IO Unit := do
  let cases : List Bool := [run 0 0, run 0 1, run 1 0, run 1 3, run 2 0, run 2 15,
    run 2 9 3, run 2 15 2, !(run 2 15 0), !(checkBad badTx), !(checkBad badMu),
    !(checkBad badT1), !(checkBad badIPA)]
  if cases.all id then IO.println "RANGE_REDUCTION_EXEC_OK: 13 cases"
  else throw (IO.userError s!"Range reduction regression failed: {cases}")
#eval main
