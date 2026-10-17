import Verification.CryptoPedersenCommitmentOpeningExtractionContract
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open scoped BigOperators
open CryptoPedersenCommitmentOpeningExtractionContract
open CryptoBulletproofsInnerProduct CryptoBulletproofsRangeReduction
open CryptoBulletproofsRangeWitnessExtraction
open CryptoBulletproofsTreeExtraction (honestTree)
open CryptoBulletproofsWitnessExtraction.Examples (units)
namespace OpeningBridgeRegression
local instance : Fact (Nat.Prime 101) := ⟨by decide +kernel⟩
abbrev F := ZMod 101

def p : Generators 101 F 1 := ⟨1, 1, 1, ![1, 1], ![1, 1]⟩
def cert : OpeningCertificate 101 1 := ⟨![1, 1], ![0, 0], 0, 0, 0, 0, 3, 0⟩
def Ac (c : OpeningCertificate 101 1) : F := vector_commit p c.a c.b c.alpha
def Sc (c : OpeningCertificate 101 1) : F := vector_commit p c.s c.t c.rho
def Vc (c : OpeningCertificate 101 1) : F := value_commit p c.v c.gamma

def family (c : OpeningCertificate 101 1) : TranscriptFamily 101 F 1 where
  y := ![1, 2]
  z := ![0, 1, 2]
  x := fun _ _ => ![0, 1, 2]
  T1 := fun i j => value_commit p (t1 c.a c.b c.s c.t (![1, 2] i) (![0, 1, 2] j)) 0
  T2 := fun i _ => value_commit p (t2 c.s c.t (![1, 2] i)) 0
  tx := fun i j l => dot (l_poly c.a c.s (![0, 1, 2] j) (![0, 1, 2] l))
    (r_poly c.b c.t (![1, 2] i) (![0, 1, 2] j) (![0, 1, 2] l))
  taux := fun _ j _ => (![0, 1, 2] j) ^ 2 * c.gamma
  mu := fun _ _ l => c.alpha + (![0, 1, 2] l) * c.rho
  trees := fun i j l => honestTree (k := 1) units p.U p.G (scaled_H (q := 101) p.H (![1, 2] i))
    (l_poly c.a c.s (![0, 1, 2] j) (![0, 1, 2] l))
    (r_poly c.b c.t (![1, 2] i) (![0, 1, 2] j) (![0, 1, 2] l))

theorem family_tree_valid (c : OpeningCertificate 101 1) (i : Fin 2) (j l : Fin 3) :
    Tree.ValidAcceptingTree (branch_statement p (Ac c) (Sc c) (family c) i j l)
      ((family c).trees i j l) := by
  have h := CryptoBulletproofsTreeExtraction.honestTree_valid units (by decide +kernel)
    p.U p.G (scaled_H (q := 101) p.H (![1, 2] i))
    (l_poly c.a c.s (![0, 1, 2] j) (![0, 1, 2] l))
    (r_poly c.b c.t (![1, 2] i) (![0, 1, 2] j) (![0, 1, 2] l))
  have hy : (![1, 2] i : F) ≠ 0 := by fin_cases i <;> decide
  simpa only [branch_statement, family, Ac, Sc,
    CryptoBulletproofsTreeExtraction.witness_statement, range_ipa_target_invariant _ _ _ _ _ _ _ _ _ _ hy]
    using h

theorem honest_valid : ValidFamily p (Ac cert) (Sc cert) (Vc cert) (family cert) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, family_tree_valid cert⟩


def forks : OpeningForks 101 1 F where
  a₁ := honestTranscript (rangeVectorMap p) ((cert.a, cert.b), cert.alpha) ((1, 2), 3) 0
  a₂ := honestTranscript (rangeVectorMap p) ((cert.a, cert.b), cert.alpha) ((1, 2), 3) 1
  s₁ := honestTranscript (rangeVectorMap p) ((cert.s, cert.t), cert.rho) ((4, 5), 6) 0
  s₂ := honestTranscript (rangeVectorMap p) ((cert.s, cert.t), cert.rho) ((4, 5), 6) 1
  v₁ := honestTranscript (scalarMap p.B p.Hblind) (cert.v, cert.gamma) (7, 8) 0
  v₂ := honestTranscript (scalarMap p.B p.Hblind) (cert.v, cert.gamma) (7, 8) 1

theorem forks_valid : ValidOpeningForks p (Ac cert) (Sc cert) (Vc cert) forks :=
  ⟨honest_fork_valid (rangeVectorMap p) ((cert.a, cert.b), cert.alpha)
      ((1, 2), 3) (0 : F) 1 (by decide),
   honest_fork_valid (rangeVectorMap p) ((cert.s, cert.t), cert.rho)
      ((4, 5), 6) (0 : F) 1 (by decide),
   honest_fork_valid (scalarMap p.B p.Hblind) (cert.v, cert.gamma)
      (7, 8) (0 : F) 1 (by decide)⟩

example : extractCertificate forks = cert := by
  simp [extractCertificate, forks, honest_extracts, cert]
example : ValidOpenings p (Ac cert) (Sc cert) (Vc cert) (extractCertificate forks) :=
  extracted_certificate_valid p _ _ _ forks forks_valid
example : ResultValid p (Vc cert) (extract (extractCertificate forks) (family cert)) :=
  range_extraction_from_opening_forks p _ _ _ forks (family cert) forks_valid honest_valid (by decide +kernel)
example : (extractCertificate forks).v = 3 := by decide +kernel
example : (extractCertificate forks).a = ![1, 1] := by decide +kernel
example : (extractCertificate forks).alpha = 0 := by decide +kernel
example : (extractCertificate forks).gamma = 0 := by decide +kernel
example : ¬ ValidOpeningForks p (Ac cert + 1) (Sc cert) (Vc cert) forks := by decide +kernel
example : ¬ ValidOpeningForks p (Ac cert) (Sc cert + 1) (Vc cert) forks := by decide +kernel
example : ¬ ValidOpeningForks p (Ac cert) (Sc cert) (Vc cert + 1) forks := by decide +kernel

#eval match extract (extractCertificate forks) (family cert) with
  | .inl w => "witness:" ++ toString w.value
  | .inr _ => "relation"
end OpeningBridgeRegression
