import Verification.CryptoBulletproofsTreeExtraction

namespace TreeExtractionRegression
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
open CryptoBulletproofsTreeExtraction.Examples
open CryptoBulletproofsWitnessExtraction.Examples (units)
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

abbrev Tree := IPATranscriptTree 101 (ZMod 101)

def tamper_claim : {k : ℕ} → Tree k → Tree k
  | 0, .leaf c a b => .leaf { c with P := c.P+1 } a b
  | _+1, .node c msg u ts => .node { c with P := c.P+1 } msg u ts

def tamper_leaf : {k : ℕ} → Tree k → Tree k
  | 0, .leaf c a b => .leaf c (a+1) b
  | _+1, .node c msg u ts => .node c msg u (fun i => if i = 0 then tamper_leaf (ts i) else ts i)

def tamper_child {k : ℕ} : Tree (k+1) → Tree (k+1)
  | .node c msg u ts => .node c msg u (fun i => if i = 0 then tamper_claim (ts i) else ts i)

def zero_challenge {k : ℕ} : Tree (k+1) → Tree (k+1)
  | .node c msg u ts => .node c msg (Function.update u 2 0) ts

def symmetric_challenge {k : ℕ} : Tree (k+1) → Tree (k+1)
  | .node c msg u ts => .node c msg (Function.update u 1 (-u 0)) ts

def repeated_challenge {k : ℕ} : Tree (k+1) → Tree (k+1)
  | .node c msg u ts => .node c msg (Function.update u 1 (u 0)) ts

def tamper_message {k : ℕ} : Tree (k+1) → Tree (k+1)
  | .node c msg u ts => .node c { msg with L := msg.L+1 } u ts

def bad_other_branch : Tree 2 :=
  .node deep_statement deep_messages (fun i => units i)
    (fun i => if i = 0 then malicious_child else if i = 3 then tamper_leaf (filler_child i)
      else filler_child i)

def accepted {k : ℕ} (s : Statement 101 (ZMod 101) k) (t : Tree k) : Bool :=
  (checked_extract s t).isOk

def rejected {k : ℕ} (s : Statement 101 (ZMod 101) k) (t : Tree k) : Bool :=
  decide (checked_extract s t = .error "invalidTree")

def exactHonest (k : ℕ) : Bool :=
  decide (checked_extract (s k) (honest k) = .ok (.witness (a k) (b k)))

example : exactHonest 0 = true := by exact decide_eq_true (honest_all_depths 0)
example : exactHonest 1 = true := by exact decide_eq_true (honest_all_depths 1)
example : exactHonest 2 = true := by exact decide_eq_true (honest_all_depths 2)
example : exactHonest 3 = true := by exact decide_eq_true (honest_all_depths 3)
example : leaf_count (honest 0) = 1 := by decide +kernel
example : leaf_count (honest 1) = 4 := by decide +kernel
example : leaf_count (honest 2) = 16 := by decide +kernel
example : leaf_count (honest 3) = 64 := by decide +kernel
example : rejected (s 0) (tamper_leaf (honest 0)) = true := by decide +kernel
example : rejected (s 1) (tamper_leaf (honest 1)) = true := by decide +kernel
example : rejected (s 2) (tamper_leaf (honest 2)) = true := by decide +kernel
example : rejected (s 1) (tamper_claim (honest 1)) = true := by decide +kernel
example : rejected (s 1) (tamper_child (honest 1)) = true := by decide +kernel
example : rejected (s 2) (tamper_child (honest 2)) = true := by decide +kernel
example : rejected (s 1) (zero_challenge (honest 1)) = true := by decide +kernel
example : rejected (s 2) (zero_challenge (honest 2)) = true := by decide +kernel
example : rejected (s 1) (symmetric_challenge (honest 1)) = true := by decide +kernel
example : rejected (s 2) (repeated_challenge (honest 2)) = true := by decide +kernel
example : rejected (s 1) (tamper_message (honest 1)) = true := by decide +kernel
example : accepted deep_statement deep_tree = true := by
  exact (checked_extract_success_iff _ _).mpr deep_tree_valid
example : isRelation (extractTree malicious_child) = true := by decide +kernel
example : extractTree deep_tree = .relation
    (lift_generator_relation (units 0) (coefficients (extractTree malicious_child))) := by
  rw [deep_tree, extract_unit_node, combine_first_relation]
  · rfl
  · decide +kernel
example : isRelation (extractTree deep_tree) = true := deep_relation_returned
example : ResultValid deep_statement (extractTree deep_tree) :=
  tree_extraction_soundness _ _ deep_tree_valid
example : rejected deep_statement bad_other_branch = true := by decide +kernel
example : isRelation (extractTree bad_other_branch) = true := by decide +kernel
example : lift_generator_relation (units 2) (0 : GeneratorCoefficients 101 2) = 0 :=
  lift_generator_relation_zero _
example : lift_generator_relation (units 2) ((1,0,0) : GeneratorCoefficients 101 1) ≠ 0 := by
  exact lift_generator_relation_nontrivial _ _ (by decide)
example : verifier (s 2).U (s 2).G (s 2).H (s 2).P (fun _ => units 0)
    (path_transcript (honest 2) (fun _ => 0)) = true := by decide +kernel
example : verifier (s 3).U (s 3).G (s 3).H (s 3).P (fun i => units (Fin.ofNat 4 i.val))
    (path_transcript (honest 3) (fun i => Fin.ofNat 4 i.val)) = true := by decide +kernel

end TreeExtractionRegression
open TreeExtractionRegression CryptoBulletproofsTreeExtraction CryptoBulletproofsTreeExtraction.Examples

def main : IO Unit := do
  let checks : List Bool := [exactHonest 0, exactHonest 1, exactHonest 2, exactHonest 3,
    decide (leaf_count (honest 0) = 1), decide (leaf_count (honest 1) = 4),
    decide (leaf_count (honest 2) = 16), decide (leaf_count (honest 3) = 64),
    rejected (s 0) (tamper_leaf (honest 0)), rejected (s 1) (tamper_leaf (honest 1)),
    rejected (s 2) (tamper_leaf (honest 2)), rejected (s 3) (tamper_leaf (honest 3)),
    rejected (s 1) (tamper_claim (honest 1)), rejected (s 2) (tamper_claim (honest 2)),
    rejected (s 1) (tamper_child (honest 1)), rejected (s 2) (tamper_child (honest 2)),
    rejected (s 3) (tamper_child (honest 3)), rejected (s 1) (zero_challenge (honest 1)),
    rejected (s 2) (zero_challenge (honest 2)), rejected (s 1) (symmetric_challenge (honest 1)),
    rejected (s 2) (repeated_challenge (honest 2)), rejected (s 1) (tamper_message (honest 1)),
    accepted deep_statement deep_tree, isRelation (extractTree malicious_child),
    isRelation (extractTree deep_tree), decide (ResultValid deep_statement (extractTree deep_tree)),
    rejected deep_statement bad_other_branch, isRelation (extractTree bad_other_branch)]
  for (check, i) in checks.zipIdx do
    unless check do throw (IO.userError s!"TREE_EXTRACTION_FAILED {i}")
  IO.println s!"TREE_EXTRACTION_OK {checks.length}"
