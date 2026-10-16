import Verification.CryptoBulletproofsRangeWitnessExtraction

open scoped BigOperators
open CryptoBulletproofsInnerProduct CryptoBulletproofsRangeReduction
open CryptoBulletproofsRangeWitnessExtraction
open CryptoBulletproofsTreeExtraction (honestTree)
open CryptoBulletproofsWitnessExtraction.Examples (units)

namespace RangeWitnessRegression
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩
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

def run (c : OpeningCertificate 101 1) (f : TranscriptFamily 101 F 1) :=
  checked_extract p (Ac c) (Sc c) (Vc c) c f

-- Executable summaries keep function-valued witnesses and coefficients inspectable.
def summary (res : Except ExtractionError (ExtractionResult 101 1)) : String :=
  match res with
  | .error e => "error:" ++ reprStr e
  | .ok (.inl w) => "witness:" ++ toString w.value
  | .ok (.inr r) => "relation:" ++ toString [r.g 0 |>.val, r.g 1 |>.val,
      r.h 0 |>.val, r.h 1 |>.val, r.base.val, r.blind.val, r.ipa.val]

set_option maxRecDepth 4096 in
example : ValidOpenings p (Ac cert) (Sc cert) (Vc cert) cert := by decide

#eval summary (run cert (family cert))

-- Polynomial mismatch: all generators are nonzero, B = Hblind permits cancellation.
def badBits : OpeningCertificate 101 1 := ⟨![2, 0], 0, 0, 0, 0, 0, 100, 0⟩
def polynomialCollision : TranscriptFamily 101 F 1 :=
  { family badBits with
    taux := fun i j _ => -(t0 badBits.a badBits.b ((family badBits).y i) ((family badBits).z j) -
      ((family badBits).z j) ^ 2 * badBits.v -
        delta_fn ((family badBits).y i) ((family badBits).z j) 2) }
#eval summary (run badBits polynomialCollision)

-- Different IPA vectors open the same root: G0 = G1, but no independence is assumed.
def alternateTree := honestTree (k := 1) units p.U p.G (scaled_H (q := 101) p.H 1)
  (![2, 0] : Vec 1 F) (![0, 0] : Vec 1 F)

def mismatchedTree : TranscriptFamily 101 F 1 :=
  { family cert with trees := fun i j l =>
    if i = 0 ∧ j = 0 ∧ l = 0 then alternateTree else (family cert).trees i j l }
#eval summary (run cert mismatchedTree)

#eval summary (checked_extract p (Ac cert + 1) (Sc cert) (Vc cert) cert (family cert))
#eval summary (checked_extract p (Ac cert) (Sc cert + 1) (Vc cert) cert (family cert))
#eval summary (checked_extract p (Ac cert) (Sc cert) (Vc cert + 1) cert (family cert))
#eval summary (run cert { family cert with y := fun _ => 1 })
#eval summary (run cert { family cert with y := ![0, 1] })
#eval summary (run cert { family cert with z := ![0, 1, 1] })
#eval summary (run cert { family cert with x := fun _ _ => ![0, 1, 1] })
#eval summary (run cert { family cert with tx := fun _ _ _ => 77 })
#eval summary (run cert { family cert with mu := fun _ _ _ => 77 })

theorem family_tree_valid (c : OpeningCertificate 101 1) (i : Fin 2) (j l : Fin 3) :
    Tree.ValidAcceptingTree (branch_statement p (Ac c) (Sc c) (family c) i j l)
      ((family c).trees i j l) := by
  have h := CryptoBulletproofsTreeExtraction.honestTree_valid units (by decide)
    p.U p.G (scaled_H (q := 101) p.H (![1, 2] i))
    (l_poly c.a c.s (![0, 1, 2] j) (![0, 1, 2] l))
    (r_poly c.b c.t (![1, 2] i) (![0, 1, 2] j) (![0, 1, 2] l))
  have hy : (![1, 2] i : F) ≠ 0 := by fin_cases i <;> decide
  simpa only [branch_statement, family, Ac, Sc,
    CryptoBulletproofsTreeExtraction.witness_statement, range_ipa_target_invariant _ _ _ _ _ _ _ _ _ _ hy]
    using h

theorem family_local_zero (c : OpeningCertificate 101 1) (i : Fin 2) (j l : Fin 3) :
    local_coeff c (family c) i j l = 0 := by
  have hx := CryptoBulletproofsTreeExtraction.honestTree_exact units (by decide)
    p.U p.G (scaled_H (q := 101) p.H (![1, 2] i))
    (l_poly c.a c.s (![0, 1, 2] j) (![0, 1, 2] l))
    (r_poly c.b c.t (![1, 2] i) (![0, 1, 2] j) (![0, 1, 2] l))
  simp only [local_coeff, family, hx]
  apply (lift_scaled_zero_iff _ (show (![1, 2] i : F) ≠ 0 by fin_cases i <;> decide) _ _ _ _).mpr
  refine ⟨sub_self _, sub_self _, ?_, sub_self _⟩
  ring

theorem honest_valid : ValidFamily p (Ac cert) (Sc cert) (Vc cert) (family cert) :=
  ⟨by decide, by decide, by decide, by decide, by decide, family_tree_valid cert⟩

theorem honest_result : extract cert (family cert) = .inl (certificate_witness cert) := by
  unfold extract
  rw [(local_candidates_none cert (family cert)).mpr (family_local_zero cert)]
  have hz : ∀ i j, grid_coeff cert (family cert) i j = 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [grid_coeff, family, cert, t0, dot, l_poly, r_poly, delta_fn,
        CryptoBulletproofsWitnessExtraction.interpolate_quad, Fin.sum_univ_succ]
    all_goals rfl
  rw [(grid_candidates_none cert (family cert)).mpr hz]

example : run cert (family cert) = .ok (.inl (certificate_witness cert)) := by
  apply (checked_extract_success_iff _ _ _ _ _ _ _).mpr
  exact ⟨by decide, by decide, by decide, honest_valid, honest_result⟩

example : WitnessValid p (Vc cert) (certificate_witness cert) := by
  have h := extraction_soundness p (Ac cert) (Sc cert) (Vc cert) cert (family cert)
    (by decide) honest_valid (by decide)
  simpa only [honest_result, ResultValid] using h

example : relation_eval p (⟨0, 0, 3, -3, 0⟩ : RelationCoefficients 101 1) = 0 := by decide
example : (⟨0, 0, 3, -3, 0⟩ : RelationCoefficients 101 1) ≠ 0 := by decide
example : relation_eval p (⟨![1, -1], 0, 0, 0, 0⟩ : RelationCoefficients 101 1) = 0 := by decide
example : (⟨![1, -1], 0, 0, 0, 0⟩ : RelationCoefficients 101 1) ≠ 0 := by decide
example : badBits.a 0 ≠ 0 ∧ badBits.a 0 ≠ 1 := by decide
example : ¬ badBits.v.val < 2 ^ (2 ^ 1) := by decide
example : ValidOpenings p (Ac badBits) (Sc badBits) (Vc badBits) badBits := by decide

theorem polynomial_collision_valid :
    ValidFamily p (Ac badBits) (Sc badBits) (Vc badBits) polynomialCollision :=
  ⟨by decide, by decide, by decide, by decide, by decide, family_tree_valid badBits⟩

example : ResultValid p (Vc badBits) (extract badBits polynomialCollision) :=
  extraction_soundness p (Ac badBits) (Sc badBits) (Vc badBits) badBits polynomialCollision
    (by decide) polynomial_collision_valid (by decide)

theorem mismatch_valid : ValidFamily p (Ac cert) (Sc cert) (Vc cert) mismatchedTree := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro i j l
  by_cases h : i = 0 ∧ j = 0 ∧ l = 0
  · rcases h with ⟨rfl, rfl, rfl⟩
    have he : branch_statement p (Ac cert) (Sc cert) mismatchedTree 0 0 0 =
        CryptoBulletproofsTreeExtraction.witness_statement p.U p.G (scaled_H (q := 101) p.H 1)
          (![2, 0] : Vec 1 F) (![0, 0] : Vec 1 F) := by decide +kernel
    rw [he]
    change Tree.ValidAcceptingTree _ alternateTree
    exact CryptoBulletproofsTreeExtraction.honestTree_valid units (by decide) _ _ _ _ _
  · simpa [mismatchedTree, h, branch_statement] using family_tree_valid cert i j l

example : ResultValid p (Vc cert) (extract cert mismatchedTree) :=
  extraction_soundness p (Ac cert) (Sc cert) (Vc cert) cert mismatchedTree
    (by decide) mismatch_valid (by decide)

example : checked_extract p (Ac cert + 1) (Sc cert) (Vc cert) cert (family cert) =
    .error .invalidOpenings := by decide
example : run cert { family cert with y := fun _ => 1 } = .error .invalidFamily := by decide
example : run cert { family cert with y := ![0, 1] } = .error .invalidFamily := by decide
example : run cert { family cert with z := ![0, 1, 1] } = .error .invalidFamily := by decide
example : run cert { family cert with x := fun _ _ => ![0, 1, 1] } =
    .error .invalidFamily := by decide

-- Nonzero masks and blinding values exercise the X-dependent terms.
def masked : OpeningCertificate 101 1 :=
  { cert with s := ![2, 4], t := ![6, 8], alpha := 9, rho := 10, gamma := 12 }
#eval summary (run masked (family masked))

def corruptRoot : Tree.IPATranscriptTree 101 F 1 :=
  match (family cert).trees 0 0 0 with
  | .node s msg u cs => .node { s with P := s.P + 1 } msg u cs
#eval summary (run cert { family cert with trees := fun _ _ _ => corruptRoot })

def zeroChallenge : Tree.IPATranscriptTree 101 F 1 :=
  match (family cert).trees 0 0 0 with
  | .node s msg _ cs => .node s msg ![0, 2, 3, 4] cs
#eval summary (run cert { family cert with trees := fun _ _ _ => zeroChallenge })

def squaredCollision : Tree.IPATranscriptTree 101 F 1 :=
  match (family cert).trees 0 0 0 with
  | .node s msg _ cs => .node s msg ![1, -1, 3, 4] cs
#eval summary (run cert { family cert with trees := fun _ _ _ => squaredCollision })

example (y : F) (hy : y ≠ 0)
    (cs : CryptoBulletproofsTreeExtraction.GeneratorCoefficients 101 1) (h : cs ≠ 0) :
    lift_scaled y cs.1 cs.2.1 0 cs.2.2 ≠ 0 := lift_tree_relation_nontrivial y hy cs h

example (a b : Vec 1 F) (y z x mu tx : F) (hy : y ≠ 0) :
    discrepancy cert y z x mu tx a b = 0 ↔
      a = l_poly cert.a cert.s z x ∧ b = r_poly cert.b cert.t y z x ∧
      mu = cert.alpha + x * cert.rho ∧ dot a b = tx :=
  discrepancy_zero_iff cert y z x mu tx hy a b

-- A genuine depth-two IPA relation is lifted through a nontrivial Y scaling.
def deepP : Generators 101 F 2 :=
  ⟨1, 1, 11, ![1, 2, 1, 1], fun i => (2 : F) ^ i.val * (![4, 6, 1, 1] i)⟩
def deepCoefficients := CryptoBulletproofsTreeExtraction.coefficients
  (Tree.extractTree CryptoBulletproofsTreeExtraction.Examples.deep_tree)
def deepLift := lift_scaled 2 deepCoefficients.1 deepCoefficients.2.1 0 deepCoefficients.2.2

example : deepLift ≠ 0 := lift_tree_relation_nontrivial 2 (by decide) _
  CryptoBulletproofsTreeExtraction.Examples.deep_relation_sound.1

example : relation_eval deepP deepLift = 0 := by
  have hh : scaled_H (q := 101) deepP.H 2 =
      CryptoBulletproofsTreeExtraction.Examples.deep_statement.H := by
    funext i
    fin_cases i <;> decide +kernel
  rw [deepLift, lift_scaled_eval, hh]
  simpa [CryptoBulletproofsTreeExtraction.evaluate, deepP, deepCoefficients,
    CryptoBulletproofsTreeExtraction.Examples.deep_statement] using
      CryptoBulletproofsTreeExtraction.Examples.deep_relation_sound.2

#eval (decide (deepLift ≠ 0), decide (relation_eval deepP deepLift = 0))

example : CryptoBulletproofsRangeWitnessExtractionSuite := verification_suite
end RangeWitnessRegression

open CryptoBulletproofsRangeWitnessExtraction in
example {q k} [Fact (Nat.Prime q)] {A : Type} [AddCommGroup A] [Module (ZMod q) A]
    [DecidableEq A] (p : Generators q A k) (Ac Sc V : A) (c : OpeningCertificate q k)
    (f : TranscriptFamily q A k) (h : ¬ 1 ≤ k) :
    checked_extract p Ac Sc V c f = .error .invalidDepth := by simp [checked_extract, h]

open CryptoBulletproofsRangeWitnessExtraction in
example {q k} [Fact (Nat.Prime q)] {A : Type} [AddCommGroup A] [Module (ZMod q) A]
    [DecidableEq A] (p : Generators q A k) (Ac Sc V : A) (c : OpeningCertificate q k)
    (f : TranscriptFamily q A k) (hk : 1 ≤ k) (hq : ¬ 2 ^ (2 ^ k) < q) :
    checked_extract p Ac Sc V c f = .error .insufficientField := by
  simp [checked_extract, hk, hq]
