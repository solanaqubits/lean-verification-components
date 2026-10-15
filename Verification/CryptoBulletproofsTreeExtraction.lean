/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsInnerProduct
import Verification.CryptoBulletproofsWitnessExtraction

/-! Deterministic extraction from a supplied complete accepting IPA tree.
No transcript-tree generation, hardness assumption or generator independence. -/
namespace CryptoBulletproofsTreeExtraction
open scoped BigOperators
open CryptoBulletproofsInnerProduct
namespace Local
export CryptoBulletproofsWitnessExtraction (extract_local extract_local_correct
  extract_local_honest)
end Local

variable {q : ℕ} [Fact (Nat.Prime q)]
variable {A : Type} [AddCommGroup A] [Module (ZMod q) A]
variable {k : ℕ}

structure Statement (q : ℕ) (A : Type) (k : ℕ) where
  U : A
  G : Vec k A
  H : Vec k A
  P : A
  deriving DecidableEq

def child_statement (s : Statement q A (k + 1)) (msg : RoundMessages A)
    (u : (ZMod q)ˣ) : Statement q A k :=
  ⟨s.U, fold_generators_G u s.G, fold_generators_H u s.H, update_target u msg s.P⟩

abbrev GeneratorCoefficients (q k : ℕ) := Vec k (ZMod q) × Vec k (ZMod q) × ZMod q

def evaluate (s : Statement q A k) (c : GeneratorCoefficients q k) : A :=
  multiscalar_mul c.1 s.G + multiscalar_mul c.2.1 s.H + c.2.2 • s.U

def lift_generator_relation (u : (ZMod q)ˣ) (c : GeneratorCoefficients q k) :
    GeneratorCoefficients q (k + 1) :=
  (join (fun i => c.1 i * (u : ZMod q)⁻¹) (fun i => c.1 i * u),
   join (fun i => c.2.1 i * u) (fun i => c.2.1 i * (u : ZMod q)⁻¹), c.2.2)

theorem lift_generator_relation_eval_eq (s : Statement q A (k + 1))
    (msg : RoundMessages A) (u : (ZMod q)ˣ) (c : GeneratorCoefficients q k) :
    evaluate s (lift_generator_relation u c) = evaluate (child_statement s msg u) c := by
  simp only [evaluate, lift_generator_relation, child_statement]
  rw [multiscalar_join, multiscalar_join]
  simp only [multiscalar_mul, fold_generators_G, fold_generators_H,
    smul_add, smul_smul, Finset.sum_add_distrib, Units.val_inv_eq_inv_val]

theorem lift_generator_relation_injective (u : (ZMod q)ˣ) :
    Function.Injective (lift_generator_relation (k := k) u) := by
  intro c d h
  have hg := congrArg (fun t : GeneratorCoefficients q (k + 1) => split_hi t.1) h
  have hh := congrArg (fun t : GeneratorCoefficients q (k + 1) => split_lo t.2.1) h
  have hu := congrArg (fun t : GeneratorCoefficients q (k + 1) => t.2.2) h
  simp only [lift_generator_relation, split_hi_join, split_lo_join] at hg hh hu
  apply Prod.ext
  · funext i
    exact mul_right_cancel₀ (Units.ne_zero u) (congrFun hg i)
  · apply Prod.ext
    · funext i
      exact mul_right_cancel₀ (Units.ne_zero u) (congrFun hh i)
    · exact hu

@[simp] theorem lift_generator_relation_zero (u : (ZMod q)ˣ) :
    lift_generator_relation (k := k) u 0 = 0 := by
  simp only [lift_generator_relation, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_mul]
  ext i <;> simp only [join, Fin.append, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
  all_goals
    generalize Fin.cast _ i = j
    induction j using Fin.addCases <;> simp only [Fin.addCases_left, Fin.addCases_right]

theorem lift_generator_relation_nontrivial (u : (ZMod q)ˣ)
    (c : GeneratorCoefficients q k) (hc : c ≠ 0) : lift_generator_relation u c ≠ 0 := by
  intro h
  apply hc
  apply lift_generator_relation_injective u
  simpa using h

inductive TreeExtractionResult (q k : ℕ) where
  | witness (a b : Vec k (ZMod q))
  | relation (coefficients : GeneratorCoefficients q k)
  deriving DecidableEq

def ResultValid (s : Statement q A k) : TreeExtractionResult q k → Prop
  | .witness a b => s.P = ipa_target s.U s.G s.H a b
  | .relation c => c ≠ 0 ∧ evaluate s c = 0

instance [DecidableEq A] (s : Statement q A k) (r : TreeExtractionResult q k) :
    Decidable (ResultValid s r) := by cases r <;> unfold ResultValid <;> infer_instance

def isRelation : TreeExtractionResult q k → Bool
  | .witness _ _ => false
  | .relation _ => true

def coefficients : TreeExtractionResult q k → GeneratorCoefficients q k
  | .witness _ _ => 0
  | .relation c => c

def witnessA : TreeExtractionResult q k → Vec k (ZMod q)
  | .witness a _ => a
  | .relation _ => 0

def witnessB : TreeExtractionResult q k → Vec k (ZMod q)
  | .witness _ b => b
  | .relation _ => 0

def fromLocal : CryptoBulletproofsWitnessExtraction.ExtractionResult q k →
    TreeExtractionResult q (k + 1)
  | .witness a b => .witness a b
  | .relation c => .relation c

def combine (u : Fin 4 → (ZMod q)ˣ) (r : Fin 4 → TreeExtractionResult q k) :
    TreeExtractionResult q (k + 1) :=
  let bad := Finset.univ.filter (fun i => isRelation (r i))
  if h : bad.Nonempty then
    let i := bad.min' h
    .relation (lift_generator_relation (u i) (coefficients (r i)))
  else fromLocal (Local.extract_local u (fun i => witnessA (r i)) (fun i => witnessB (r i)))

theorem combine_correct (s : Statement q A (k + 1)) (msg : RoundMessages A)
    (u : Fin 4 → (ZMod q)ˣ) (r : Fin 4 → TreeExtractionResult q k)
    (hd : Function.Injective (fun i => (u i : ZMod q) ^ 2))
    (hr : ∀ i, ResultValid (child_statement s msg (u i)) (r i)) :
    ResultValid s (combine u r) := by
  unfold combine
  dsimp only
  split_ifs with h
  · let bad := Finset.univ.filter (fun i => isRelation (r i))
    let i := bad.min' h
    have hm : isRelation (r i) = true := (Finset.mem_filter.mp (bad.min'_mem h)).2
    have hv := hr i
    change ResultValid s (.relation (lift_generator_relation (u i) (coefficients (r i))))
    cases he : r i with
    | witness a b => simp [he, isRelation] at hm
    | relation c =>
      simp only [he, ResultValid] at hv
      exact ⟨lift_generator_relation_nontrivial _ _ hv.1,
        (lift_generator_relation_eval_eq s msg (u i) c).trans hv.2⟩
  · have ha (i : Fin 4) : CryptoBulletproofsWitnessExtraction.Accepts
        ⟨s.U, s.G, s.H, s.P, msg⟩ (u i) (witnessA (r i)) (witnessB (r i)) := by
      have hn : isRelation (r i) ≠ true := by
        intro hi
        exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      have hv := hr i
      cases he : r i with
      | relation c => simp [he, isRelation] at hn
      | witness a b => simpa only [he, ResultValid, child_statement, witnessA, witnessB,
          CryptoBulletproofsWitnessExtraction.Accepts] using hv
    have hv := Local.extract_local_correct ⟨s.U, s.G, s.H, s.P, msg⟩ u
      (fun i => witnessA (r i)) (fun i => witnessB (r i)) hd ha
    cases he : Local.extract_local u (fun i => witnessA (r i)) (fun i => witnessB (r i)) <;>
      simpa [he, fromLocal, ResultValid, CryptoBulletproofsWitnessExtraction.ResultValid,
        evaluate, CryptoBulletproofsWitnessExtraction.evaluate] using hv

/-- Each claimed statement is checked against the independently computed context. -/
inductive IPATranscriptTree (q : ℕ) (A : Type) : ℕ → Type where
  | leaf (claimed : Statement q A 0) (a b : ZMod q) : IPATranscriptTree q A 0
  | node {k : ℕ} (claimed : Statement q A (k + 1)) (msg : RoundMessages A)
      (challenges : Fin 4 → ZMod q) (children : Fin 4 → IPATranscriptTree q A k) :
      IPATranscriptTree q A (k + 1)

def ValidAcceptingTree : {k : ℕ} → Statement q A k → IPATranscriptTree q A k → Prop
  | 0, s, .leaf c a b => c = s ∧ s.P = a • s.G 0 + b • s.H 0 + (a * b) • s.U
  | _ + 1, s, .node c msg u ts => c = s ∧
      if hn : ∀ i, u i ≠ 0 then
        Function.Injective (fun i => u i ^ 2) ∧
        ∀ i, ValidAcceptingTree (child_statement s msg (Units.mk0 (u i) (hn i))) (ts i)
      else False

instance treeDecidable [DecidableEq A] : {k : ℕ} → (s : Statement q A k) →
    (t : IPATranscriptTree q A k) → Decidable (ValidAcceptingTree s t)
  | 0, _, .leaf _ _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | _ + 1, s, .node c msg u ts => by
    simp only [ValidAcceptingTree]
    have insts (i : Fin 4) (s : Statement q A _) := treeDecidable s (ts i)
    exact inferInstance

/-- Store coordinates in arrays before returning function views of them. -/
def materialize (r : TreeExtractionResult q k) : TreeExtractionResult q k :=
  match r with
  | .witness a b =>
      let av := Vector.ofFn a
      let bv := Vector.ofFn b
      .witness (fun i => av[i]) (fun i => bv[i])
  | .relation c =>
      let gv := Vector.ofFn c.1
      let hv := Vector.ofFn c.2.1
      .relation (fun i => gv[i], (fun i => hv[i]), c.2.2)

omit [Fact (Nat.Prime q)] in
theorem materialize_eq (r : TreeExtractionResult q k) : materialize r = r := by
  cases r <;> simp [materialize]

/-- Total algebraic core; the checked interface rejects invalid inputs before using it. -/
def extractTree : {k : ℕ} → IPATranscriptTree q A k → TreeExtractionResult q k
  | 0, .leaf _ a b => .witness (fun _ => a) (fun _ => b)
  | _ + 1, .node _ _ u ts =>
      if hn : ∀ i, u i ≠ 0 then
        let results := Vector.ofFn (fun i => extractTree (ts i))
        materialize (combine (fun i => Units.mk0 (u i) (hn i)) (fun i => results[i]))
      else .witness 0 0

omit [AddCommGroup A] [Module (ZMod q) A] in
theorem extract_unit_node (c : Statement q A (k + 1)) (msg : RoundMessages A)
    (u : Fin 4 → (ZMod q)ˣ) (ts : Fin 4 → IPATranscriptTree q A k) :
    extractTree (.node c msg (fun i => u i) ts) = combine u (fun i => extractTree (ts i)) := by
  rw [extractTree, dif_pos (fun i => Units.ne_zero (u i))]
  simp only [materialize_eq, Units.mk0_val, Fin.getElem_fin, Vector.getElem_ofFn]

theorem combine_first_relation (u : Fin 4 → (ZMod q)ˣ)
    (r : Fin 4 → TreeExtractionResult q k) (h : isRelation (r 0) = true) :
    combine u r = .relation (lift_generator_relation (u 0) (coefficients (r 0))) := by
  let bad := Finset.univ.filter (fun i => isRelation (r i))
  have hm : (0 : Fin 4) ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  have hn : bad.Nonempty := ⟨0, hm⟩
  have he : bad.min' hn = 0 := le_antisymm (Finset.min'_le bad 0 hm) (Fin.zero_le _)
  change (if hn : bad.Nonempty then _ else _) = _
  rw [dif_pos hn, he]

theorem tree_extraction_soundness {k : ℕ} (s : Statement q A k)
    (t : IPATranscriptTree q A k) (h : ValidAcceptingTree s t) :
    ResultValid s (extractTree t) := by
  induction t with
  | leaf c a b =>
    simpa [extractTree, ResultValid, ipa_target, multiscalar_mul, dot_product]
      using h.2
  | node c msg u ts ih =>
    simp only [ValidAcceptingTree] at h
    obtain ⟨_, h⟩ := h
    simp only [extractTree]
    split_ifs with hn
    · rw [dif_pos hn] at h
      simp only [materialize_eq, Fin.getElem_fin, Vector.getElem_ofFn]
      exact combine_correct s msg _ _ h.1 (fun i => ih i _ (h.2 i))
    · rw [dif_neg hn] at h
      exact False.elim h

/-- Full validation includes every child even when extraction can return an early relation. -/
def checked_extract [DecidableEq A] (s : Statement q A k) (t : IPATranscriptTree q A k) :
    Except String (TreeExtractionResult q k) :=
  if ValidAcceptingTree s t then .ok (extractTree t) else .error "invalidTree"

theorem checked_extract_sound [DecidableEq A] (s : Statement q A k)
    (t : IPATranscriptTree q A k) (r : TreeExtractionResult q k)
    (h : checked_extract s t = .ok r) : ResultValid s r := by
  unfold checked_extract at h
  split_ifs at h with hv
  · cases h
    exact tree_extraction_soundness s t hv

theorem checked_extract_success_iff [DecidableEq A] (s : Statement q A k)
    (t : IPATranscriptTree q A k) : (checked_extract s t).isOk = true ↔ ValidAcceptingTree s t := by
  by_cases h : ValidAcceptingTree s t <;> simp [checked_extract, h, Except.isOk, Except.toBool]


theorem join_halves {B : Type} (a : Vec (k + 1) B) : join (split_lo a) (split_hi a) = a := by
  funext i
  change Fin.append (fun t => a (loIndex t)) (fun t => a (hiIndex t)) (Fin.cast _ i) = a i
  have h (j : Fin (2 ^ k + 2 ^ k)) :
      Fin.append (fun t => a (Fin.cast (by simp [pow_succ, Nat.mul_two]) (Fin.castAdd (2 ^ k) t)))
        (fun t => a (Fin.cast (by simp [pow_succ, Nat.mul_two]) (Fin.natAdd (2 ^ k) t))) j =
          a (Fin.cast (by simp [pow_succ, Nat.mul_two]) j) := by
    induction j using Fin.addCases <;> simp only [Fin.append_left, Fin.append_right]
  exact (h (Fin.cast (by simp [pow_succ, Nat.mul_two]) i)).trans (congrArg a (Fin.ext rfl))

theorem combine_honest (u : Fin 4 → (ZMod q)ˣ) (a b : Vec (k + 1) (ZMod q))
    (hd : (u 0 : ZMod q) ^ 2 ≠ (u 1 : ZMod q) ^ 2) :
    combine u (fun i => .witness (fold_vector_a (u i) a) (fold_vector_b (u i) b)) =
      .witness a b := by
  simp only [combine, isRelation, Bool.false_eq_true, Finset.filter_false,
    Finset.not_nonempty_empty, witnessA, witnessB]
  have h := Local.extract_local_honest u (split_lo a) (split_hi a) (split_lo b) (split_hi b) hd
  rw [join_halves, join_halves] at h
  rw [h]
  rfl

def witness_statement (U : A) (G H : Vec k A) (a b : Vec k (ZMod q)) : Statement q A k :=
  ⟨U, G, H, ipa_target U G H a b⟩

def honestTree (u : Fin 4 → (ZMod q)ˣ) : {k : ℕ} → (U : A) → (G H : Vec k A) →
    (a b : Vec k (ZMod q)) → IPATranscriptTree q A k
  | 0, U, G, H, a, b => .leaf (witness_statement U G H a b) (a 0) (b 0)
  | _ + 1, U, G, H, a, b =>
      .node (witness_statement U G H a b) (round_messages U G H a b) (fun i => u i)
        (fun i => honestTree u U (fold_generators_G (u i) G) (fold_generators_H (u i) H)
          (fold_vector_a (u i) a) (fold_vector_b (u i) b))

theorem honestTree_valid (u : Fin 4 → (ZMod q)ˣ)
    (hd : Function.Injective (fun i => (u i : ZMod q) ^ 2))
    (U : A) (G H : Vec k A) (a b : Vec k (ZMod q)) :
    ValidAcceptingTree (witness_statement U G H a b) (honestTree u U G H a b) := by
  induction k with
  | zero => simp [honestTree, ValidAcceptingTree, witness_statement, ipa_target,
      multiscalar_mul, dot_product]
  | succ k ih =>
    have hn : ∀ i, (u i : ZMod q) ≠ 0 := fun i => Units.ne_zero (u i)
    rw [honestTree, ValidAcceptingTree]
    refine ⟨rfl, ?_⟩
    rw [dif_pos hn]
    simp only [Units.mk0_val]
    refine ⟨hd, fun i => ?_⟩
    simpa only [child_statement, witness_statement, ipa_round_invariant] using
      ih (fold_generators_G (u i) G) (fold_generators_H (u i) H)
        (fold_vector_a (u i) a) (fold_vector_b (u i) b)

theorem honestTree_exact (u : Fin 4 → (ZMod q)ˣ)
    (hd : (u 0 : ZMod q) ^ 2 ≠ (u 1 : ZMod q) ^ 2)
    (U : A) (G H : Vec k A) (a b : Vec k (ZMod q)) :
    extractTree (honestTree u U G H a b) = .witness a b := by
  induction k with
  | zero =>
    have ha : (fun _ : Fin (2 ^ 0) => a 0) = a := by ext i; fin_cases i; rfl
    have hb : (fun _ : Fin (2 ^ 0) => b 0) = b := by ext i; fin_cases i; rfl
    simp only [honestTree, extractTree, ha, hb]
  | succ k ih =>
    have hn : ∀ i, (u i : ZMod q) ≠ 0 := fun i => Units.ne_zero (u i)
    rw [honestTree, extractTree, dif_pos hn]
    simp only [Units.mk0_val, materialize_eq, Fin.getElem_fin, Vector.getElem_ofFn, ih]
    exact combine_honest u a b hd

theorem checked_honestTree_exact [DecidableEq A] (u : Fin 4 → (ZMod q)ˣ)
    (hd : Function.Injective (fun i => (u i : ZMod q) ^ 2))
    (U : A) (G H : Vec k A) (a b : Vec k (ZMod q)) :
    checked_extract (witness_statement U G H a b) (honestTree u U G H a b) =
      .ok (.witness a b) := by
  rw [checked_extract, if_pos (honestTree_valid u hd U G H a b),
    honestTree_exact u (hd.ne (by decide))]

/-- Count actual leaves of the recursively stored tree, not proof payload elements. -/
def leaf_count : {k : ℕ} → IPATranscriptTree q A k → ℕ
  | 0, .leaf _ _ _ => 1
  | _ + 1, .node _ _ _ ts => ∑ i, leaf_count (ts i)

omit [Fact (Nat.Prime q)] [AddCommGroup A] [Module (ZMod q) A] in
theorem tree_leaf_count_eq (t : IPATranscriptTree q A k) : leaf_count t = 4 ^ k := by
  induction t with
  | leaf => rfl
  | node _ _ _ _ ih => simp [leaf_count, ih, pow_succ, Nat.mul_comm]

omit [Fact (Nat.Prime q)] [AddCommGroup A] [Module (ZMod q) A] in
theorem tree_leaf_count_square (t : IPATranscriptTree q A k) : leaf_count t = (2 ^ k) ^ 2 := by
  rw [tree_leaf_count_eq, ← pow_mul, Nat.mul_comm k 2, pow_mul]
  rfl

theorem leaf_verifier_bridge [DecidableEq A] (s : Statement q A 0) (a b : ZMod q) :
    ValidAcceptingTree s (.leaf s a b) ↔
      verifier s.U s.G s.H s.P (Fin.elim0) ⟨Fin.elim0, a, b⟩ = true := by
  simp [ValidAcceptingTree, verifier]


/-- Project one branch path to the existing IPA transcript type. -/
def path_transcript : {k : ℕ} → IPATranscriptTree q A k → (Fin k → Fin 4) → IPATranscript q A k
  | 0, .leaf _ a b, _ => ⟨Fin.elim0, a, b⟩
  | _ + 1, .node _ msg _ ts, path =>
      let tail := path_transcript (ts (path 0)) (Fin.tail path)
      ⟨Fin.cons msg tail.rounds, tail.a_final, tail.b_final⟩

def PathMatches : {k : ℕ} → IPATranscriptTree q A k → (Fin k → Fin 4) →
    (Fin k → (ZMod q)ˣ) → Prop
  | 0, .leaf _ _ _, _, _ => True
  | _ + 1, .node _ _ u ts, path, xs => u (path 0) = (xs 0 : ZMod q) ∧
      PathMatches (ts (path 0)) (Fin.tail path) (Fin.tail xs)

theorem accepting_path_verifier [DecidableEq A] (s : Statement q A k)
    (t : IPATranscriptTree q A k) (path : Fin k → Fin 4) (xs : Fin k → (ZMod q)ˣ)
    (hv : ValidAcceptingTree s t) (hm : PathMatches t path xs) :
    verifier s.U s.G s.H s.P xs (path_transcript t path) = true := by
  induction t with
  | leaf c a b =>
    change decide (s.P = a • s.G 0 + b • s.H 0 + (a * b) • s.U) = true
    exact decide_eq_true hv.2
  | node c msg u ts ih =>
    obtain ⟨_, hv⟩ := hv
    by_cases hn : ∀ i, u i ≠ 0
    · rw [dif_pos hn] at hv
      have he : Units.mk0 (u (path 0)) (hn (path 0)) = xs 0 := Units.ext hm.1
      have hh := ih (path 0) (child_statement s msg (xs 0)) (Fin.tail path) (Fin.tail xs)
        (he ▸ hv.2 (path 0)) hm.2
      simpa only [path_transcript, verifier, Fin.cons_zero, transcript_tail, Fin.tail_cons,
        child_statement] using hh
    · rw [dif_neg hn] at hv
      exact False.elim hv


theorem reject_zero_challenge [DecidableEq A] (s c : Statement q A (k + 1))
    (msg : RoundMessages A) (u : Fin 4 → ZMod q) (ts : Fin 4 → IPATranscriptTree q A k)
    (i : Fin 4) (hi : u i = 0) : checked_extract s (.node c msg u ts) = .error "invalidTree" := by
  have hn : ¬∀ j, u j ≠ 0 := fun h => h i hi
  simp [checked_extract, ValidAcceptingTree, hn]

theorem reject_symmetric_challenges [DecidableEq A] (s c : Statement q A (k + 1))
    (msg : RoundMessages A) (u : Fin 4 → ZMod q) (ts : Fin 4 → IPATranscriptTree q A k)
    (hi : u 1 = -u 0) : checked_extract s (.node c msg u ts) = .error "invalidTree" := by
  have hd : ¬Function.Injective (fun i => u i ^ 2) := by
    intro h
    have he : u 0 ^ 2 = u 1 ^ 2 := by rw [hi, neg_sq]
    exact (by decide : (0 : Fin 4) ≠ 1) (h he)
  by_cases hn : ∀ j, u j ≠ 0 <;> simp [checked_extract, ValidAcceptingTree, hn, hd]

omit [Fact (Nat.Prime q)] [AddCommGroup A] [Module (ZMod q) A] in
theorem leaves_exceed_single_transcript_group_count (t : IPATranscriptTree q A k) :
    2 * k < leaf_count t := by
  rw [tree_leaf_count_eq]
  have h : ∀ j : ℕ, 2 * j < 4 ^ j := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
      rw [pow_succ]
      nlinarith [pow_pos (by decide : 0 < (4 : ℕ)) j]
  exact h k

namespace Examples
open CryptoBulletproofsWitnessExtraction.Examples (units)

def G (k : ℕ) : Vec k (ZMod 101) := fun i => i.val + 2
def H (k : ℕ) : Vec k (ZMod 101) := fun i => i.val + 11
def a (k : ℕ) : Vec k (ZMod 101) := fun i => i.val + 3
def b (k : ℕ) : Vec k (ZMod 101) := fun i => i.val + 7
def s (k : ℕ) := witness_statement (17 : ZMod 101) (G k) (H k) (a k) (b k)
def honest (k : ℕ) := honestTree units (17 : ZMod 101) (G k) (H k) (a k) (b k)

theorem honest_all_depths (k : ℕ) : checked_extract (s k) (honest k) = .ok (.witness (a k) (b k)) :=
  checked_honestTree_exact units (by decide) _ _ _ _ _

/-- A valid inconsistent local family embedded one level below the root. -/
def deep_statement : Statement 101 (ZMod 101) 2 := ⟨11, ![1, 2, 1, 1], ![4, 6, 1, 1], 59⟩
def deep_messages : RoundMessages (ZMod 101) := ⟨0, 0⟩
def deep_child (i : Fin 4) := child_statement deep_statement deep_messages (units i)
def malicious_child : IPATranscriptTree 101 (ZMod 101) 1 :=
  let s := deep_child 0
  let msg := CryptoBulletproofsWitnessExtraction.Examples.p.messages
  .node s msg (fun i => units i) (fun i => .leaf (child_statement s msg (units i))
    1 ((![72, 37, 60, 26] : Fin 4 → ZMod 101) i))
def filler_child (i : Fin 4) : IPATranscriptTree 101 (ZMod 101) 1 :=
  let s := deep_child i
  honestTree units s.U s.G s.H (![s.P / s.G 0, 0]) 0

def deep_tree : IPATranscriptTree 101 (ZMod 101) 2 :=
  .node deep_statement deep_messages (fun i => units i)
    (fun i => if i = 0 then malicious_child else filler_child i)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
-- Kernel reduction of a complete depth-two tree over ZMod 101.
theorem deep_tree_valid : ValidAcceptingTree deep_statement deep_tree := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
-- Kernel reduction of a complete depth-two tree over ZMod 101.
theorem deep_relation_returned : isRelation (extractTree deep_tree) = true := by decide +kernel

theorem deep_relation_sound :
    coefficients (extractTree deep_tree) ≠ 0 ∧
      evaluate deep_statement (coefficients (extractTree deep_tree)) = 0 := by
  have h := tree_extraction_soundness deep_statement deep_tree deep_tree_valid
  have hr := deep_relation_returned
  cases he : extractTree deep_tree with
  | witness a b => simp [he, isRelation] at hr
  | relation c => simpa only [he, ResultValid, coefficients] using h

end Examples

structure CryptoBulletproofsTreeExtractionSuite : Prop where
  lifting : ∀ (q : ℕ) [Fact q.Prime] (k : ℕ) (u : (ZMod q)ˣ),
    Function.Injective (lift_generator_relation (k := k) u)
  extraction : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    (k : ℕ) (s : Statement q A k) (t : IPATranscriptTree q A k),
    ValidAcceptingTree s t → ResultValid s (extractTree t)
  checked : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    [DecidableEq A] (k : ℕ) (s : Statement q A k) (t : IPATranscriptTree q A k)
    (r : TreeExtractionResult q k), checked_extract s t = .ok r → ResultValid s r
  leaves : ∀ (q : ℕ) (A : Type) (k : ℕ) (t : IPATranscriptTree q A k), leaf_count t = (2 ^ k) ^ 2
  honest : ∀ k, checked_extract (Examples.s k) (Examples.honest k) =
    .ok (.witness (Examples.a k) (Examples.b k))
  deep_relation : coefficients (extractTree Examples.deep_tree) ≠ 0 ∧
    evaluate Examples.deep_statement (coefficients (extractTree Examples.deep_tree)) = 0

theorem verification_suite : CryptoBulletproofsTreeExtractionSuite where
  lifting := fun _ _ _ => lift_generator_relation_injective
  extraction := fun _ _ _ _ _ _ => tree_extraction_soundness
  checked := fun _ _ _ _ _ _ _ => checked_extract_sound
  leaves := fun _ _ _ => tree_leaf_count_square
  honest := Examples.honest_all_depths
  deep_relation := Examples.deep_relation_sound

end CryptoBulletproofsTreeExtraction
