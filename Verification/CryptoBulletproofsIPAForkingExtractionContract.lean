/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsTreeExtraction

/-! Finite, prefix-shared challenge acquisition. This is a deterministic finite
combinatorial bridge, not a probabilistic or random-oracle forking lemma. -/
namespace CryptoBulletproofsIPAForkingExtractionContract
open scoped BigOperators
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction

section Combinatorics
variable {F : Type} [Field F] [DecidableEq F]

def squareClasses (s : Finset F) : Finset F := s.image (fun x => x ^ 2)

theorem square_fiber_card_le_two (s : Finset F) (y : F) :
    (s.filter (fun x => x ^ 2 = y)).card ≤ 2 := by
  by_cases h : (s.filter (fun x => x ^ 2 = y)).Nonempty
  · obtain ⟨x, hx⟩ := h
    have hx' := (Finset.mem_filter.mp hx).2
    apply le_trans (Finset.card_le_card (t := {x, -x}) ?_) Finset.card_le_two
    intro z hz
    have he : z ^ 2 = x ^ 2 := (Finset.mem_filter.mp hz).2.trans hx'.symm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      (sq_eq_sq_iff_eq_or_eq_neg.mp he)
  · simp only [Finset.not_nonempty_iff_eq_empty] at h
    simp [h]

theorem card_le_twice_square_classes (s : Finset F) :
    s.card ≤ 2 * (squareClasses s).card := by
  calc
    s.card = ∑ y ∈ squareClasses s, (s.filter (fun x => x ^ 2 = y)).card :=
      Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    _ ≤ ∑ _y ∈ squareClasses s, 2 :=
      Finset.sum_le_sum (fun y _ => square_fiber_card_le_two s y)
    _ = 2 * (squareClasses s).card := by simp [Nat.mul_comm]

theorem seven_implies_four_square_classes (s : Finset F) (h : 7 ≤ s.card) :
    4 ≤ (squareClasses s).card := by
  have := card_le_twice_square_classes s
  omega

/-- Four distinct square classes, with all representatives in the supplied set. -/
def IsFork (s : Finset F) (u : Fin 4 → F) : Prop :=
  (∀ i, u i ∈ s) ∧ Function.Injective (fun i => u i ^ 2)

instance (s : Finset F) (u : Fin 4 → F) : Decidable (IsFork s u) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem four_square_classes_iff_fork (s : Finset F) :
    4 ≤ (squareClasses s).card ↔ ∃ u, IsFork s u := by
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, c, hc, d, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
      Finset.three_lt_card.mp (by omega : 3 < (squareClasses s).card)
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hd
    refine ⟨![a', b', c', d'], ?_, ?_⟩
    · intro i; fin_cases i <;> simp [ha', hb', hc', hd']
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  · rintro ⟨u, hu, hi⟩
    have hs : Finset.univ.image (fun i => u i ^ 2) ⊆ squareClasses s := by
      intro y hy
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨u i, hu i, rfl⟩
    have hc := Finset.card_le_card hs
    simpa [Finset.card_image_of_injective _ hi] using hc

/-- Enumerate only supplied challenges: no search over the entire scalar field. -/
def forkCandidates (s : List F) : List (Fin 4 → F) :=
  s.flatMap fun a => s.flatMap fun b =>
    s.flatMap fun c => s.map fun d => ![a, b, c, d]

omit [Field F] [DecidableEq F] in
theorem mem_forkCandidates (s : List F) (u : Fin 4 → F) :
    u ∈ forkCandidates s ↔ ∀ i, u i ∈ s := by
  simp only [forkCandidates, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ i
    fin_cases i <;> simp [ha, hb, hc, hd]
  · intro h
    refine ⟨u 0, h 0, u 1, h 1, u 2, h 2, u 3, h 3, ?_⟩
    funext i; fin_cases i <;> rfl

def selectFork (s : List F) : Option (Fin 4 → F) :=
  (forkCandidates s).find? (fun u => decide (Function.Injective (fun i => u i ^ 2)))

theorem selectFork_sound (s : List F) (u : Fin 4 → F)
    (h : selectFork s = some u) : IsFork s.toFinset u := by
  constructor
  · intro i
    exact List.mem_toFinset.mpr
      ((mem_forkCandidates s u).mp (List.mem_of_find?_eq_some h) i)
  · have he := List.find?_some
      (p := fun u : Fin 4 → F => decide (Function.Injective (fun i => u i ^ 2))) h
    exact of_decide_eq_true he

/-- Nonzero oracle inputs yield nonzero selected challenges and squares. -/
theorem selectFork_nonzero (s : List F) (u : Fin 4 → F)
    (hn : ∀ x ∈ s, x ≠ 0) (h : selectFork s = some u) :
    ∀ i, u i ≠ 0 ∧ u i ^ 2 ≠ 0 := by
  intro i
  have hi := hn (u i) (List.mem_toFinset.mp ((selectFork_sound s u h).1 i))
  exact ⟨hi, pow_ne_zero _ hi⟩

theorem selectFork_success_iff (s : List F) :
    (selectFork s).isSome = true ↔ 4 ≤ (squareClasses s.toFinset).card := by
  rw [selectFork, List.find?_isSome, four_square_classes_iff_fork]
  simp only [mem_forkCandidates, decide_eq_true_eq, IsFork, List.mem_toFinset]

theorem selectFork_of_seven (s : List F) (h : 7 ≤ s.toFinset.card) :
    (selectFork s).isSome = true :=
  (selectFork_success_iff s).mpr (seven_implies_four_square_classes s.toFinset h)

end Combinatorics


variable {q : ℕ} [Fact (Nat.Prime q)]
variable {A : Type} [AddCommGroup A] [Module (ZMod q) A] [DecidableEq A]
variable {k : ℕ}

/-- A raw finite rewind oracle. The round message is shared by every response;
children are indexed by the actual challenge, so repeated calls cannot add mass. -/
inductive FiniteOracleTree (q : ℕ) (A : Type) : ℕ → Type where
  | leaf (claimed : Statement q A 0) (a b : ZMod q) : FiniteOracleTree q A 0
  | node {k : ℕ} (claimed : Statement q A (k + 1)) (msg : RoundMessages A)
      (calls : List (ZMod q)) (children : ZMod q → FiniteOracleTree q A k) :
      FiniteOracleTree q A (k + 1)

/-- Rejected and zero challenges contribute no square classes. -/
def acceptedChallenges (calls : List (ZMod q))
    (replies : ZMod q → Option (IPATranscriptTree q A k)) : List (ZMod q) :=
  calls.filter (fun x => decide (x ≠ 0) && (replies x).isSome)

omit [AddCommGroup A] [Module (ZMod q) A] [DecidableEq A] in
theorem mem_acceptedChallenges (calls : List (ZMod q))
    (replies : ZMod q → Option (IPATranscriptTree q A k)) (x : ZMod q) :
    x ∈ acceptedChallenges calls replies ↔
      x ∈ calls ∧ x ≠ 0 ∧ (replies x).isSome = true := by
  simp [acceptedChallenges]

/-- This fallback is never used by a successfully selected branch. -/
def emptyTree : (k : ℕ) → IPATranscriptTree q A k
  | 0 => .leaf ⟨0, 0, 0, 0⟩ 0 0
  | k + 1 => .node ⟨0, 0, 0, 0⟩ ⟨0, 0⟩ (fun _ => 0) (fun _ => emptyTree k)

def assemble (s : Statement q A (k + 1)) (msg : RoundMessages A)
    (calls : List (ZMod q)) (replies : ZMod q → Option (IPATranscriptTree q A k)) :
    Option (IPATranscriptTree q A (k + 1)) :=
  (selectFork (acceptedChallenges calls replies)).map fun u =>
    .node s msg u (fun i => (replies (u i)).getD (emptyTree k))

omit [Module (ZMod q) A] [DecidableEq A] in
theorem assemble_success_iff (s : Statement q A (k + 1)) (msg : RoundMessages A)
    (calls : List (ZMod q)) (replies : ZMod q → Option (IPATranscriptTree q A k)) :
    (assemble s msg calls replies).isSome = true ↔
      4 ≤ (squareClasses (acceptedChallenges calls replies).toFinset).card := by
  simpa [assemble] using selectFork_success_iff (acceptedChallenges calls replies)

omit [Module (ZMod q) A] [DecidableEq A] in
theorem assemble_of_seven (s : Statement q A (k + 1)) (msg : RoundMessages A)
    (calls : List (ZMod q)) (replies : ZMod q → Option (IPATranscriptTree q A k))
    (h : 7 ≤ (acceptedChallenges calls replies).toFinset.card) :
    (assemble s msg calls replies).isSome = true :=
  (assemble_success_iff s msg calls replies).mpr
    (seven_implies_four_square_classes _ h)

omit [DecidableEq A] in
theorem assemble_sound (s : Statement q A (k + 1)) (msg : RoundMessages A)
    (calls : List (ZMod q)) (replies : ZMod q → Option (IPATranscriptTree q A k))
    (hv : ∀ x (hx : x ≠ 0) t, replies x = some t →
      ValidAcceptingTree (child_statement s msg (Units.mk0 x hx)) t)
    (t : IPATranscriptTree q A (k + 1)) (ht : assemble s msg calls replies = some t) :
    ValidAcceptingTree s t := by
  unfold assemble at ht
  cases he : selectFork (acceptedChallenges calls replies) with
  | none => simp [he] at ht
  | some u =>
    simp only [he, Option.map_some, Option.some.injEq] at ht
    subst t
    have hu := selectFork_sound _ _ he
    have hm (i : Fin 4) := (mem_acceptedChallenges calls replies (u i)).mp
      (List.mem_toFinset.mp (hu.1 i))
    have hn : ∀ i, u i ≠ 0 := fun i => (hm i).2.1
    simp only [ValidAcceptingTree, dif_pos hn, true_and]
    refine ⟨hu.2, ?_⟩
    intro i
    cases hr : replies (u i) with
    | none => have hi := (hm i).2.2; simp [hr] at hi
    | some r => simpa [hr] using hv (u i) (hn i) r hr

/-- Validate replies recursively, then acquire four distinct square classes.
The external statement determines every child context independently. -/
def acquire : {k : ℕ} → Statement q A k → FiniteOracleTree q A k →
    Option (IPATranscriptTree q A k)
  | 0, s, .leaf c a b =>
    if ValidAcceptingTree s (.leaf c a b) then some (.leaf c a b) else none
  | _ + 1, s, .node c msg calls children =>
    if c = s then
      assemble s msg calls (fun x => if hx : x ≠ 0 then
        acquire (child_statement s msg (Units.mk0 x hx)) (children x) else none)
    else none

theorem acquire_sound {k : ℕ} (s : Statement q A k) (oracle : FiniteOracleTree q A k)
    (t : IPATranscriptTree q A k) (h : acquire s oracle = some t) :
    ValidAcceptingTree s t := by
  induction oracle with
  | leaf c a b =>
    simp only [acquire] at h
    split_ifs at h with hv
    · cases h; exact hv
  | node c msg calls children ih =>
    simp only [acquire] at h
    split_ifs at h with hc
    · apply assemble_sound s msg calls _ _ t h
      intro x hx r hr
      rw [dif_pos hx] at hr
      exact ih x _ r hr

/-- Recursively count accepted square classes from raw replies, independently of
which four branches the selector will take. Invalid replies may be present. -/
def ready : {k : ℕ} → Statement q A k → FiniteOracleTree q A k → Bool
  | 0, s, .leaf c a b => decide (ValidAcceptingTree s (.leaf c a b))
  | _ + 1, s, .node c msg calls children => decide (c = s) &&
    decide (4 ≤ (squareClasses (calls.filter (fun x => if hx : x ≠ 0 then
      ready (child_statement s msg (Units.mk0 x hx)) (children x) else false)).toFinset).card)

def OracleReady (s : Statement q A k) (oracle : FiniteOracleTree q A k) : Prop :=
  ready s oracle = true

instance (s : Statement q A k) (oracle : FiniteOracleTree q A k) :
    Decidable (OracleReady s oracle) := inferInstanceAs (Decidable (_ = _))

theorem acquire_success_iff {k : ℕ} (s : Statement q A k) (oracle : FiniteOracleTree q A k) :
    (acquire s oracle).isSome = true ↔ OracleReady s oracle := by
  unfold OracleReady
  induction oracle with
  | leaf c a b => simp [acquire, ready]
  | node c msg calls children ih =>
    by_cases hc : c = s
    · simp only [acquire, if_pos hc, ready]
      rw [assemble_success_iff]
      have he : acceptedChallenges calls (fun x => if hx : x ≠ 0 then
          acquire (child_statement s msg (Units.mk0 x hx)) (children x) else none) =
          calls.filter (fun x => if hx : x ≠ 0 then
            ready (child_statement s msg (Units.mk0 x hx)) (children x) else false) := by
        unfold acceptedChallenges
        apply List.filter_congr
        intro x _
        by_cases hx : x ≠ 0
        · simp only [dif_pos hx]
          simpa [hx] using Bool.eq_iff_iff.mpr (ih x (child_statement s msg (Units.mk0 x hx)))
        · simp [hx]
      rw [he]
      simp [hc]
    · simp [acquire, ready, hc]

/-- Feed the acquired tree to the existing checked extractor, with no modified
statement, hidden blinding field, or extra claim about an external dot product. -/
def checked_forking_extract (s : Statement q A k) (oracle : FiniteOracleTree q A k) :
    Except String (TreeExtractionResult q k) :=
  match acquire s oracle with
  | none => .error "insufficientAcceptingSquareClasses"
  | some t => checked_extract s t

theorem checked_forking_extract_sound (s : Statement q A k) (oracle : FiniteOracleTree q A k)
    (r : TreeExtractionResult q k) (h : checked_forking_extract s oracle = .ok r) :
    ResultValid s r := by
  unfold checked_forking_extract at h
  cases he : acquire s oracle with
  | none => simp [he] at h
  | some t => exact checked_extract_sound s t r (by simpa [he] using h)

theorem checked_forking_extract_complete (s : Statement q A k) (oracle : FiniteOracleTree q A k)
    (h : OracleReady s oracle) :
    ∃ r, checked_forking_extract s oracle = .ok r ∧ ResultValid s r := by
  have ha := (acquire_success_iff s oracle).mpr h
  cases he : acquire s oracle with
  | none => simp [he] at ha
  | some t =>
    have hv := acquire_sound s oracle t he
    refine ⟨extractTree t, ?_, tree_extraction_soundness s t hv⟩
    simp [checked_forking_extract, he, checked_extract, hv]

theorem finite_forking_dichotomy (s : Statement q A k) (oracle : FiniteOracleTree q A k)
    (h : OracleReady s oracle) :
    (∃ a b, checked_forking_extract s oracle = .ok (.witness a b) ∧
      s.P = ipa_target s.U s.G s.H a b) ∨
    (∃ c, checked_forking_extract s oracle = .ok (.relation c) ∧
      c ≠ 0 ∧ evaluate s c = 0) := by
  obtain ⟨r, hr, hv⟩ := checked_forking_extract_complete s oracle h
  cases r with
  | witness a b => exact Or.inl ⟨a, b, hr, hv⟩
  | relation c => exact Or.inr ⟨c, hr, hv⟩

/-- A simple numerical sufficient condition at every accepted node. Duplicated
calls, zero challenges, and invalid child responses never increase this count. -/
def sevenReady : {k : ℕ} → Statement q A k → FiniteOracleTree q A k → Bool
  | 0, s, .leaf c a b => decide (ValidAcceptingTree s (.leaf c a b))
  | _ + 1, s, .node c msg calls children => decide (c = s) &&
    decide (7 ≤ (calls.filter (fun x => if hx : x ≠ 0 then
      sevenReady (child_statement s msg (Units.mk0 x hx)) (children x) else false)).toFinset.card)

theorem sevenReady_implies_ready {k : ℕ} (s : Statement q A k)
    (oracle : FiniteOracleTree q A k) (h : sevenReady s oracle = true) :
    OracleReady s oracle := by
  unfold OracleReady
  induction oracle with
  | leaf c a b => exact h
  | node c msg calls children ih =>
    simp only [sevenReady, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [ready, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨h.1, ?_⟩
    have hs : (calls.filter (fun x => if hx : x ≠ 0 then
        sevenReady (child_statement s msg (Units.mk0 x hx)) (children x) else false)).toFinset ⊆
        (calls.filter (fun x => if hx : x ≠ 0 then
          ready (child_statement s msg (Units.mk0 x hx)) (children x) else false)).toFinset := by
      intro x hx
      simp only [List.mem_toFinset, List.mem_filter] at hx ⊢
      refine ⟨hx.1, ?_⟩
      split_ifs at hx ⊢ with hn
      · exact ih x _ hx.2
      · simp at hx
    exact le_trans (seven_implies_four_square_classes _ h.2)
      (Finset.card_le_card (Finset.image_subset_image hs))

theorem sevenReady_acquire_success (s : Statement q A k) (oracle : FiniteOracleTree q A k)
    (h : sevenReady s oracle = true) : (acquire s oracle).isSome = true :=
  (acquire_success_iff s oracle).mpr (sevenReady_implies_ready s oracle h)

omit [Module (ZMod q) A] [DecidableEq A] in
/-- Successful nodes use this exact statement and shared message. Authentic
rewind execution and response provenance remain external obligations. -/
theorem assemble_preserves_prefix (s : Statement q A (k + 1)) (msg : RoundMessages A)
    (calls : List (ZMod q)) (replies : ZMod q → Option (IPATranscriptTree q A k))
    (t : IPATranscriptTree q A (k + 1)) (h : assemble s msg calls replies = some t) :
    ∃ u children, t = .node s msg u children := by
  unfold assemble at h
  cases he : selectFork (acceptedChallenges calls replies) with
  | none => simp [he] at h
  | some u =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    exact ⟨u, _, h.symm⟩

/-- No fork can be acquired from three or fewer square classes, regardless of
how often the same calls are repeated. -/
theorem selectFork_rejects_three {F : Type} [Field F] [DecidableEq F] (calls : List F)
    (h : (squareClasses calls.toFinset).card ≤ 3) : selectFork calls = none := by
  cases he : selectFork calls with
  | none => rfl
  | some u =>
    have hs := (selectFork_success_iff calls).mp (by simp [he])
    omega

structure CryptoBulletproofsIPAForkingExtractionContractSuite : Prop where
  fibers : ∀ (F : Type) [Field F] [DecidableEq F] (s : Finset F) (y : F),
    (s.filter (fun x => x ^ 2 = y)).card ≤ 2
  threshold : ∀ (F : Type) [Field F] [DecidableEq F] (calls : List F),
    7 ≤ calls.toFinset.card → (selectFork calls).isSome = true
  selection : ∀ (F : Type) [Field F] [DecidableEq F] (calls : List F) (u : Fin 4 → F),
    selectFork calls = some u → IsFork calls.toFinset u
  acquisition : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    [DecidableEq A] (k : ℕ) (s : Statement q A k) (o : FiniteOracleTree q A k)
    (t : IPATranscriptTree q A k), acquire s o = some t → ValidAcceptingTree s t
  coverage : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    [DecidableEq A] (k : ℕ) (s : Statement q A k) (o : FiniteOracleTree q A k),
    sevenReady s o = true → OracleReady s o
  extraction : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    [DecidableEq A] (k : ℕ) (s : Statement q A k) (o : FiniteOracleTree q A k),
    OracleReady s o → ∃ r, checked_forking_extract s o = .ok r ∧ ResultValid s r
  rejection : ∀ (F : Type) [Field F] [DecidableEq F] (calls : List F),
    (squareClasses calls.toFinset).card ≤ 3 → selectFork calls = none

theorem verification_suite : CryptoBulletproofsIPAForkingExtractionContractSuite where
  fibers := fun _ _ _ => square_fiber_card_le_two
  threshold := fun _ _ _ => selectFork_of_seven
  selection := fun _ _ _ => selectFork_sound
  acquisition := fun _ _ _ _ _ _ _ => acquire_sound
  coverage := fun _ _ _ _ _ _ _ => sevenReady_implies_ready
  extraction := fun _ _ _ _ _ _ _ => checked_forking_extract_complete
  rejection := fun _ _ _ => selectFork_rejects_three

end CryptoBulletproofsIPAForkingExtractionContract
