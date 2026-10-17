/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsIPAForkingExtractionContract

namespace IPAForkingRegression
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
open CryptoBulletproofsIPAForkingExtractionContract

set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-- Six accepted challenges need not supply four square classes. -/
def sixSigns : Finset (ZMod 101) := {1, -1, 2, -2, 3, -3}

/-- The sharp seven-point case contains only four square classes. -/
def sevenSigns : Finset (ZMod 101) := insert 4 sixSigns

/-- Counting a zero response as a usable rewind would invalidate the threshold. -/
def sixAndZero : Finset (ZMod 101) := insert 0 sixSigns

example : sixSigns.card = 6 := by decide +kernel
example : (sixSigns.image (fun x => x ^ 2)).card = 3 := by decide +kernel
example : ∀ x ∈ sixSigns, x ≠ 0 := by decide +kernel
example : sevenSigns.card = 7 := by decide +kernel
example : (sevenSigns.image (fun x => x ^ 2)).card = 4 := by decide +kernel
example : ∀ x ∈ sevenSigns, x ≠ 0 := by decide +kernel
example : sixAndZero.card = 7 := by decide +kernel
example : (sixAndZero.filter (· ≠ 0)).card = 6 := by decide +kernel
example : ((sixAndZero.filter (· ≠ 0)).image (fun x => x ^ 2)).card = 3 := by
  decide +kernel
example : (1 : ZMod 101) ≠ -1 ∧ (1 : ZMod 101) ^ 2 = (-1 : ZMod 101) ^ 2 := by
  decide +kernel

def sixCalls : List (ZMod 101) := [1, -1, 2, -2, 3, -3]
def sevenCalls : List (ZMod 101) := [1, -1, 2, -2, 3, -3, 4]
def fourCalls : List (ZMod 101) := [1, 2, 3, 4]
def repeatedCalls : List (ZMod 101) := [1, 1, 2, 2, 3, 3, 1]

example : ¬ ∃ u, IsFork sixSigns u := by
  rw [← four_square_classes_iff_fork]
  decide +kernel

example : ∃ u, IsFork sevenSigns u :=
  (four_square_classes_iff_fork sevenSigns).mp
    (seven_implies_four_square_classes sevenSigns (by decide +kernel))

example : (selectFork sevenCalls).isSome = true :=
  selectFork_of_seven sevenCalls (by decide +kernel)

example : selectFork sixCalls = none := by decide +kernel
example : selectFork repeatedCalls = none := by decide +kernel
example : selectFork fourCalls = some ![1, 2, 3, 4] := by decide +kernel
example : selectFork sevenCalls = some ![1, 2, 3, 4] := by decide +kernel
example : IsFork sevenCalls.toFinset ![1, 2, 3, 4] :=
  selectFork_sound sevenCalls _ (by decide +kernel)

abbrev Oracle := FiniteOracleTree 101 (ZMod 101)

def challengeUnit (x : ZMod 101) : (ZMod 101)ˣ :=
  if hx : x ≠ 0 then Units.mk0 x hx else 1

/-- Responses are generated for each queried challenge, without a supplied four-fork. -/
def honestOracle (calls : ℕ → List (ZMod 101)) : {k : ℕ} →
    (U : ZMod 101) → (G H a b : Vec k (ZMod 101)) → Oracle k
  | 0, U, G, H, a, b => .leaf (witness_statement U G H a b) (a 0) (b 0)
  | k+1, U, G, H, a, b =>
    .node (witness_statement U G H a b) (round_messages U G H a b) (calls (k+1))
      (fun x => honestOracle calls U (fold_generators_G (challengeUnit x) G)
        (fold_generators_H (challengeUnit x) H) (fold_vector_a (challengeUnit x) a)
        (fold_vector_b (challengeUnit x) b))

def honestInput (calls : ℕ → List (ZMod 101)) (k : ℕ) : Oracle k :=
  honestOracle calls 17 (CryptoBulletproofsTreeExtraction.Examples.G k) (CryptoBulletproofsTreeExtraction.Examples.H k) (CryptoBulletproofsTreeExtraction.Examples.a k) (CryptoBulletproofsTreeExtraction.Examples.b k)

def wrongClaim : {k : ℕ} → Oracle k → Oracle k
  | 0, .leaf c a b => .leaf { c with P := c.P+1 } a b
  | _+1, .node c msg calls children => .node { c with P := c.P+1 } msg calls children

def badFourth {k : ℕ} : Oracle (k+1) → Oracle (k+1)
  | .node c msg calls children =>
    .node c msg calls (fun x => if x = 4 then wrongClaim (children x) else children x)

def wrongPrefix {k : ℕ} : Oracle (k+1) → Oracle (k+1)
  | .node c msg calls children => .node c { msg with L := msg.L+1 } calls children

def fromTree : {k : ℕ} → IPATranscriptTree 101 (ZMod 101) k → Oracle k
  | 0, .leaf c a b => .leaf c a b
  | _+1, .node c msg u ts => .node c msg [u 0, u 1, u 2, u 3]
      (fun x => if x = u 0 then fromTree (ts 0) else if x = u 1 then fromTree (ts 1)
        else if x = u 2 then fromTree (ts 2) else fromTree (ts 3))

def exactHonest (calls : ℕ → List (ZMod 101)) (k : ℕ) : Bool :=
  match checked_forking_extract (CryptoBulletproofsTreeExtraction.Examples.s k) (honestInput calls k) with
  | .ok (.witness a b) =>
    decide ((∀ i, a i = CryptoBulletproofsTreeExtraction.Examples.a k i) ∧
      (∀ i, b i = CryptoBulletproofsTreeExtraction.Examples.b k i))
  | _ => false

def rejected {k : ℕ} (oracle : Oracle k) : Bool :=
  (acquire (CryptoBulletproofsTreeExtraction.Examples.s k) oracle).isNone

example : exactHonest (fun _ => sevenCalls) 0 = true := by decide +kernel
example : exactHonest (fun _ => sevenCalls) 1 = true := by decide +kernel
example : exactHonest (fun _ => sevenCalls) 2 = true := by decide +kernel
example : (acquire (CryptoBulletproofsTreeExtraction.Examples.s 2) (honestInput (fun _ => sevenCalls) 2)).map leaf_count = some 16 := by
  decide +kernel
example : rejected (honestInput (fun _ => sixCalls) 1) = true := by decide +kernel
example : rejected (honestInput (fun k => if k = 1 then sixCalls else sevenCalls) 2) = true := by
  decide +kernel
example : rejected (honestInput (fun k => if k = 2 then sixCalls else sevenCalls) 2) = true := by
  decide +kernel
example : rejected (honestInput (fun _ => 0 :: sixCalls) 1) = true := by decide +kernel
example : exactHonest (fun _ => 0 :: sevenCalls) 1 = true := by decide +kernel
example : rejected (honestInput (fun _ => repeatedCalls) 1) = true := by decide +kernel
example : rejected (wrongClaim (honestInput (fun _ => sevenCalls) 1)) = true := by decide +kernel
example : rejected (wrongPrefix (honestInput (fun _ => sevenCalls) 1)) = true := by decide +kernel
example : rejected (badFourth (honestInput (fun _ => sevenCalls) 1)) = true := by decide +kernel
example : (acquire CryptoBulletproofsTreeExtraction.Examples.deep_statement (fromTree CryptoBulletproofsTreeExtraction.Examples.deep_tree)).isSome = true := by decide +kernel
example : (checked_forking_extract CryptoBulletproofsTreeExtraction.Examples.deep_statement (fromTree CryptoBulletproofsTreeExtraction.Examples.deep_tree)).map isRelation =
    .ok true := by decide +kernel

theorem seven_ready_depth_two :
    sevenReady (CryptoBulletproofsTreeExtraction.Examples.s 2)
      (honestInput (fun _ => sevenCalls) 2) = true := by decide +kernel

example : OracleReady (CryptoBulletproofsTreeExtraction.Examples.s 2)
    (honestInput (fun _ => sevenCalls) 2) :=
  sevenReady_implies_ready _ _ seven_ready_depth_two

example : (acquire (CryptoBulletproofsTreeExtraction.Examples.s 2)
    (honestInput (fun _ => sevenCalls) 2)).isSome = true :=
  sevenReady_acquire_success _ _ seven_ready_depth_two

example : (acquire (CryptoBulletproofsTreeExtraction.Examples.s 1)
    (honestInput (fun _ => fourCalls) 1)).isSome = true :=
  (acquire_success_iff _ _).mpr (by decide +kernel)

example : sevenReady (CryptoBulletproofsTreeExtraction.Examples.s 1)
    (honestInput (fun _ => fourCalls) 1) = false := by decide +kernel

example : sevenReady (CryptoBulletproofsTreeExtraction.Examples.s 2)
    (honestInput (fun k => if k = 1 then sixCalls else sevenCalls) 2) = false := by decide +kernel

example : (acquire (CryptoBulletproofsTreeExtraction.Examples.s 1)
    (badFourth (honestInput (fun _ => sevenCalls ++ [5]) 1))).isSome = true := by decide +kernel

end IPAForkingRegression

open IPAForkingRegression CryptoBulletproofsTreeExtraction
open CryptoBulletproofsIPAForkingExtractionContract

def main : IO Unit := do
  let checks : List Bool := [
    decide (sixSigns.card = 6), decide ((squareClasses sixSigns).card = 3),
    decide (sevenSigns.card = 7), decide ((squareClasses sevenSigns).card = 4),
    (selectFork sevenCalls).isSome, (selectFork sixCalls).isNone,
    (selectFork repeatedCalls).isNone,
    IPAForkingRegression.exactHonest (fun _ => sevenCalls) 0,
    IPAForkingRegression.exactHonest (fun _ => sevenCalls) 1,
    IPAForkingRegression.exactHonest (fun _ => sevenCalls) 2,
    IPAForkingRegression.exactHonest (fun _ => fourCalls) 2,
    IPAForkingRegression.exactHonest (fun _ => 0 :: sevenCalls) 1,
    rejected (honestInput (fun _ => sixCalls) 1),
    rejected (honestInput (fun k => if k = 1 then sixCalls else sevenCalls) 2),
    rejected (honestInput (fun k => if k = 2 then sixCalls else sevenCalls) 2),
    rejected (honestInput (fun _ => 0 :: sixCalls) 1),
    rejected (honestInput (fun _ => repeatedCalls) 1),
    rejected (wrongClaim (honestInput (fun _ => sevenCalls) 1)),
    rejected (wrongPrefix (honestInput (fun _ => sevenCalls) 1)),
    rejected (badFourth (honestInput (fun _ => sevenCalls) 1)),
    sevenReady (CryptoBulletproofsTreeExtraction.Examples.s 2)
      (honestInput (fun _ => sevenCalls) 2),
    !(sevenReady (CryptoBulletproofsTreeExtraction.Examples.s 1)
      (honestInput (fun _ => fourCalls) 1)),
    (acquire (CryptoBulletproofsTreeExtraction.Examples.s 1)
      (badFourth (honestInput (fun _ => sevenCalls ++ [5]) 1))).isSome,
    (acquire CryptoBulletproofsTreeExtraction.Examples.deep_statement
      (fromTree CryptoBulletproofsTreeExtraction.Examples.deep_tree)).isSome,
    decide ((checked_forking_extract CryptoBulletproofsTreeExtraction.Examples.deep_statement
      (fromTree CryptoBulletproofsTreeExtraction.Examples.deep_tree)).map isRelation = .ok true)]
  for (check, i) in checks.zipIdx do
    unless check do throw (IO.userError s!"IPA_FORKING_FAILED {i}")
  IO.println s!"IPA_FORKING_OK {checks.length}"
