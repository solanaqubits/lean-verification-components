import Verification.CryptoBulletproofsInnerProduct

open CryptoBulletproofsInnerProduct
open scoped BigOperators

instance : Fact (Nat.Prime 17) := ⟨by decide⟩
abbrev F := ZMod 17

def x2 : Fˣ := ⟨2, 9, by decide, by decide⟩
def x3 : Fˣ := ⟨3, 6, by decide, by decide⟩
def g0 : Vec 0 F := fun _ => 3
def h0 : Vec 0 F := fun _ => 5
def a0 : Vec 0 F := fun _ => 6
def b0 : Vec 0 F := fun _ => 7
def g1 : Vec 1 F := ![1, 2]
def h1 : Vec 1 F := ![3, 4]
def a1 : Vec 1 F := ![6, 7]
def b1 : Vec 1 F := ![8, 9]
def g2 : Vec 2 F := ![1, 2, 3, 4]
def h2 : Vec 2 F := ![5, 6, 7, 8]
def a2 : Vec 2 F := ![9, 10, 11, 12]
def b2 : Vec 2 F := ![13, 14, 15, 16]
def xs0 : Fin 0 → Fˣ := Fin.elim0
def xs1 : Fin 1 → Fˣ := fun _ => x2
def xs2 : Fin 2 → Fˣ := ![x2, x3]
def t0 := prover (5 : F) g0 h0 a0 b0 xs0
def t1 := prover (5 : F) g1 h1 a1 b1 xs1
def t2 := prover (5 : F) g2 h2 a2 b2 xs2

def badL : IPATranscript 17 F 1 :=
  { t1 with rounds := fun i => { t1.rounds i with L := (t1.rounds i).L + 1 } }
def badR : IPATranscript 17 F 1 :=
  { t1 with rounds := fun i => { t1.rounds i with R := (t1.rounds i).R + 1 } }
def badA : IPATranscript 17 F 0 := { t0 with a_final := t0.a_final + 1 }
def badB : IPATranscript 17 F 0 := { t0 with b_final := t0.b_final + 1 }

example : verifier (5 : F) g0 h0 (ipa_target 5 g0 h0 a0 b0) xs0 t0 = true := by decide
example : verifier (5 : F) g1 h1 (ipa_target 5 g1 h1 a1 b1) xs1 t1 = true := by decide
example : verifier (5 : F) g2 h2 (ipa_target 5 g2 h2 a2 b2) xs2 t2 = true := by decide
example : batch_verifier (5 : F) g2 h2 (ipa_target 5 g2 h2 a2 b2) xs2 t2 = true := by decide
example : verifier (5 : F) g1 h1 (ipa_target 5 g1 h1 a1 b1) xs1 badL = false := by decide
example : verifier (5 : F) g1 h1 (ipa_target 5 g1 h1 a1 b1) xs1 badR = false := by decide
example : verifier (5 : F) g0 h0 (ipa_target 5 g0 h0 a0 b0) xs0 badA = false := by decide
example : verifier (5 : F) g0 h0 (ipa_target 5 g0 h0 a0 b0) xs0 badB = false := by decide
example : (group_payload t0).length = 0 ∧ (scalar_payload t0).length = 2 := by decide
example : (group_payload t1).length = 2 ∧ (scalar_payload t1).length = 2 := by decide
example : (group_payload t2).length = 4 ∧ (scalar_payload t2).length = 2 := by decide
example : ¬ ∃ x : Fˣ, (x : F) = 0 := by
  rintro ⟨x, hx⟩
  exact challenge_nonzero x hx
example : verifier (5 : F) g2 h2 0 xs2 (prover 5 g2 h2 0 0 xs2) = true := by decide
example : verifier (5 : F) g2 h2 (ipa_target 5 g2 h2 a2 b2) xs2 t2 =
    batch_verifier 5 g2 h2 (ipa_target 5 g2 h2 a2 b2) xs2 t2 := by decide
example : verifier (5 : F) g1 h1 (ipa_target 5 g1 h1 a1 b1) xs1 badL =
    batch_verifier 5 g1 h1 (ipa_target 5 g1 h1 a1 b1) xs1 badL := by decide
example : weights_G 2 xs2 = ![3, 10, 12, 6] := by decide
example : final_G xs2 g2 = multiscalar_mul (weights_G 2 xs2) g2 := final_G_expansion _ _
example : final_H xs2 h2 = multiscalar_mul (weights_H 2 xs2) h2 := final_H_expansion _ _
example : update_target x2 (round_messages (5 : F) g1 h1 a1 b1)
    (ipa_target 5 g1 h1 a1 b1) = ipa_target 5 (fold_generators_G x2 g1)
      (fold_generators_H x2 h1) (fold_vector_a x2 a1) (fold_vector_b x2 b1) := by decide
example : (prover (5 : F) g1 h1 a1 b1 (fun _ => x2)).rounds 0 =
    (prover (5 : F) g1 h1 a1 b1 (fun _ => x3)).rounds 0 := rfl
example : CryptoBulletproofsInnerProductSuite := verification_suite
example : Nonempty (CryptoPedersenHomomorphicSum.Setup 17 F) :=
  CryptoPedersenHomomorphicSum.setup_satisfiable 17

-- Compiled execution tests supplement kernel-checked propositions above.
def main : IO Unit := do
  let cases : List Bool := [
    verifier (5 : F) g0 h0 (ipa_target 5 g0 h0 a0 b0) xs0 t0,
    verifier (5 : F) g1 h1 (ipa_target 5 g1 h1 a1 b1) xs1 t1,
    verifier (5 : F) g2 h2 (ipa_target 5 g2 h2 a2 b2) xs2 t2,
    batch_verifier (5 : F) g2 h2 (ipa_target 5 g2 h2 a2 b2) xs2 t2,
    !(verifier (5 : F) g1 h1 (ipa_target 5 g1 h1 a1 b1) xs1 badL),
    !(verifier (5 : F) g1 h1 (ipa_target 5 g1 h1 a1 b1) xs1 badR),
    !(verifier (5 : F) g0 h0 (ipa_target 5 g0 h0 a0 b0) xs0 badA),
    !(verifier (5 : F) g0 h0 (ipa_target 5 g0 h0 a0 b0) xs0 badB),
    verifier (5 : F) g2 h2 0 xs2 (prover 5 g2 h2 0 0 xs2),
    decide ((group_payload t2).length = 4),
    decide ((scalar_payload t2).length = 2),
    decide (verifier (5 : F) g1 h1 (ipa_target 5 g1 h1 a1 b1) xs1 badR =
      batch_verifier 5 g1 h1 (ipa_target 5 g1 h1 a1 b1) xs1 badR)]
  if cases.all id then IO.println "IPA_EXEC_OK: 12 cases"
  else throw (IO.userError "IPA regression failed")

#eval main
