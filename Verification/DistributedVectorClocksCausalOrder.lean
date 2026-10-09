import Verification.DistributedVectorClocks
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

set_option linter.style.header false

namespace DistributedVectorClocksCausalOrder

abbrev NodeId (n : ℕ) := Fin n
abbrev VectorClock (n : ℕ) := NodeId n → ℕ

def tick {n : ℕ} (p : NodeId n) (v : VectorClock n) : VectorClock n :=
  fun i => if i = p then v i + 1 else v i

def merge {n : ℕ} (v w : VectorClock n) : VectorClock n := fun i => max (v i) (w i)
def VectorLE {n : ℕ} (v w : VectorClock n) : Prop := ∀ i, v i ≤ w i
def VectorLT {n : ℕ} (v w : VectorClock n) : Prop := VectorLE v w ∧ v ≠ w

inductive EventType (n : ℕ) where
  | local
  | send (msgId : ℕ) (dest : NodeId n)
  | recv (msgId : ℕ)
  deriving DecidableEq, Repr

structure Event (n : ℕ) where
  proc : NodeId n
  seq : ℕ
  payload : EventType n
  deriving DecidableEq, Repr

/-- Event identities are positions, not payloads. Local numbering starts at one.
The finite trace representation admits outstanding sends and non-FIFO delivery. -/
structure History (n length : ℕ) where
  event : Fin length → Event n

variable {n l : ℕ}

def History.localPred (H : History n l) (e : Fin l) : Finset (Fin l) :=
  Finset.univ.filter fun d => d < e ∧ (H.event d).proc = (H.event e).proc

def History.messageEdge (H : History n l) (d e : Fin l) : Prop :=
  ∃ id, (H.event d).payload = .send id (H.event e).proc ∧
    (H.event e).payload = .recv id

def messageMatch (a b : Event n) : Prop :=
  match a.payload, b.payload with
  | .send id dest, .recv id' => id = id' ∧ dest = b.proc
  | _, _ => False

instance (a b : Event n) : Decidable (messageMatch a b) := by
  unfold messageMatch
  split <;> infer_instance

theorem message_match_iff (H : History n l) (d e : Fin l) :
    messageMatch (H.event d) (H.event e) ↔ H.messageEdge d e := by
  unfold messageMatch History.messageEdge
  cases (H.event d).payload <;> cases (H.event e).payload <;> simp

instance (H : History n l) (d e : Fin l) : Decidable (H.messageEdge d e) :=
  decidable_of_iff (messageMatch (H.event d) (H.event e)) (message_match_iff H d e)

def History.Direct (H : History n l) (d e : Fin l) : Prop :=
  d < e ∧ ((H.event d).proc = (H.event e).proc ∨ H.messageEdge d e)
instance (H : History n l) (d e : Fin l) : Decidable (H.Direct d e) :=
  inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))

def History.pred (H : History n l) (e : Fin l) : Finset (Fin l) :=
  Finset.univ.filter fun d => H.Direct d e

/-- Causality uses only events, their positions and message identities, never clocks. -/
def HappensBefore (H : History n l) := Relation.TransGen H.Direct
def CausalPast (H : History n l) (d e : Fin l) : Prop := d = e ∨ HappensBefore H d e

structure History.Legal (H : History n l) : Prop where
  numbering : ∀ e, (H.event e).seq = (H.localPred e).sup (fun d => (H.event d).seq) + 1
  send_unique : ∀ d e id u v, (H.event d).payload = .send id u →
    (H.event e).payload = .send id v → d = e
  receive_unique : ∀ d e id, (H.event d).payload = .recv id →
    (H.event e).payload = .recv id → d = e
  receive_sent : ∀ e id, (H.event e).payload = .recv id →
    ∃ d, d < e ∧ (H.event d).payload = .send id (H.event e).proc

/-- A prefix recurrence: merge preceding local knowledge and delivered send
knowledge, then increment exactly the executing process. -/
structure Execution (H : History n l) where
  legal : H.Legal
  stamp : Fin l → VectorClock n
  step : ∀ e i, stamp e i = tick (H.event e).proc
    (fun j => (H.pred e).sup (fun d => stamp d j)) i

@[simp] theorem mem_pred (H : History n l) (d e : Fin l) :
    d ∈ H.pred e ↔ H.Direct d e := by simp [History.pred]
@[simp] theorem mem_localPred (H : History n l) (d e : Fin l) :
    d ∈ H.localPred e ↔ d < e ∧ (H.event d).proc = (H.event e).proc := by
  simp [History.localPred]

theorem happens_before_index {H : History n l} {d e : Fin l}
    (h : HappensBefore H d e) : d < e := by
  induction h with
  | single h => exact h.1
  | tail _ h ih => exact lt_trans ih h.1

theorem happens_before_irrefl (H : History n l) (e : Fin l) : ¬ HappensBefore H e e :=
  fun h => (lt_irrefl e) (happens_before_index h)

theorem happens_before_trans {H : History n l} {d e f : Fin l}
    (h : HappensBefore H d e) (k : HappensBefore H e f) : HappensBefore H d f := h.trans k

theorem past_index {H : History n l} {d e : Fin l} (h : CausalPast H d e) : d ≤ e := by
  rcases h with rfl | h
  · exact le_rfl
  · exact le_of_lt (happens_before_index h)

theorem past_trans {H : History n l} {d e f : Fin l}
    (h : CausalPast H d e) (k : CausalPast H e f) : CausalPast H d f := by
  rcases h with rfl | h
  · exact k
  rcases k with rfl | k
  · exact Or.inr h
  · exact Or.inr (h.trans k)

theorem past_decompose (H : History n l) (d e : Fin l) :
    CausalPast H d e ↔ d = e ∨ ∃ p ∈ H.pred e, CausalPast H d p := by
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · obtain ⟨p, hp, pe⟩ := Relation.TransGen.tail'_iff.mp h
      refine Or.inr ⟨p, (mem_pred H p e).mpr pe, ?_⟩
      rcases Relation.ReflTransGen.cases_tail hp with h | ⟨q, hq, qp⟩
      · exact Or.inl h.symm
      · exact Or.inr (Relation.TransGen.tail' hq qp)
  · rintro (h | ⟨p, hp, h⟩)
    · exact Or.inl h
    · apply Or.inr
      have pe := (mem_pred H p e).mp hp
      rcases h with rfl | h
      · exact Relation.TransGen.single pe
      · exact h.tail pe

theorem seq_pos {H : History n l} (h : H.Legal) (e : Fin l) : 0 < (H.event e).seq := by
  rw [h.numbering]; omega

theorem seq_strict {H : History n l} (h : H.Legal) {d e : Fin l}
    (hi : d < e) (hp : (H.event d).proc = (H.event e).proc) :
    (H.event d).seq < (H.event e).seq := by
  have hx := Finset.le_sup (f := fun d => (H.event d).seq)
    ((mem_localPred H d e).mpr ⟨hi, hp⟩)
  rw [h.numbering e]; omega

theorem seq_le_iff_index {H : History n l} (h : H.Legal) {d e : Fin l}
    (hp : (H.event d).proc = (H.event e).proc) :
    (H.event d).seq ≤ (H.event e).seq ↔ d ≤ e := by
  constructor
  · intro he
    by_contra hn
    have := seq_strict h (lt_of_not_ge hn) hp.symm
    omega
  · intro hi
    rcases lt_or_eq_of_le hi with hi | rfl
    · exact le_of_lt (seq_strict h hi hp)
    · exact le_rfl

noncomputable def pastEvents (H : History n l) (e : Fin l) (i : NodeId n) : Finset (Fin l) :=
  @Finset.filter _ (fun d => CausalPast H d e ∧ (H.event d).proc = i)
    (Classical.decPred _) Finset.univ
noncomputable def pastClock (H : History n l) (e : Fin l) (i : NodeId n) : ℕ :=
  (pastEvents H e i).sup fun d => (H.event d).seq

@[simp] theorem mem_pastEvents (H : History n l) (d e : Fin l) (i : NodeId n) :
    d ∈ pastEvents H e i ↔ CausalPast H d e ∧ (H.event d).proc = i := by
  classical
  simp [pastEvents]

theorem pastClock_self {H : History n l} (h : H.Legal) (e : Fin l) :
    pastClock H e (H.event e).proc = (H.event e).seq := by
  apply le_antisymm
  · unfold pastClock
    apply Finset.sup_le
    intro d hd
    obtain ⟨hd, hp⟩ := (mem_pastEvents H d e _).mp hd
    exact (seq_le_iff_index h hp).mpr (past_index hd)
  · exact Finset.le_sup (f := fun d => (H.event d).seq)
      ((mem_pastEvents H e e _).mpr ⟨Or.inl rfl, rfl⟩)

/-- The causal-prefix maximum satisfies the operational max-and-tick rule.
This is a theorem about independent reachability, not a legality assumption. -/
theorem pastClock_step {H : History n l} (h : H.Legal) (e : Fin l) (i : NodeId n) :
    pastClock H e i = tick (H.event e).proc
      (fun j => (H.pred e).sup (fun d => pastClock H d j)) i := by
  classical
  by_cases hi : i = (H.event e).proc
  · subst i
    rw [pastClock_self h, tick, if_pos rfl, h.numbering e]
    congr 1
    apply le_antisymm
    · apply Finset.sup_le
      intro d hd
      have hm := (mem_localPred H d e).mp hd
      have hp : d ∈ H.pred e := (mem_pred H d e).mpr ⟨hm.1, Or.inl hm.2⟩
      have hs : (H.event d).seq = pastClock H d (H.event e).proc := by
        rw [← hm.2, pastClock_self h]
      rw [hs]
      exact Finset.le_sup (f := fun d => pastClock H d (H.event e).proc) hp
    · apply Finset.sup_le
      intro d hd
      unfold pastClock
      apply Finset.sup_le
      intro a ha
      obtain ⟨ha, hp⟩ := (mem_pastEvents H a d _).mp ha
      have hae : a < e := lt_of_le_of_lt (past_index ha) ((mem_pred H d e).mp hd).1
      exact Finset.le_sup (f := fun d => (H.event d).seq) ((mem_localPred H a e).mpr ⟨hae, hp⟩)
  · rw [tick, if_neg hi]
    apply le_antisymm
    · unfold pastClock
      apply Finset.sup_le
      intro a ha
      obtain ⟨ha, hp⟩ := (mem_pastEvents H a e i).mp ha
      rcases (past_decompose H a e).mp ha with rfl | ⟨d, hd, had⟩
      · exact (hi hp.symm).elim
      · exact Finset.le_sup_of_le hd
          (Finset.le_sup (f := fun d => (H.event d).seq) ((mem_pastEvents H a d i).mpr ⟨had, hp⟩))
    · apply Finset.sup_le
      intro d hd
      unfold pastClock
      apply Finset.sup_le
      intro a ha
      obtain ⟨ha, hp⟩ := (mem_pastEvents H a d i).mp ha
      exact Finset.le_sup (f := fun d => (H.event d).seq) ((mem_pastEvents H a e i).mpr
        ⟨(past_decompose H a e).mpr (Or.inr ⟨d, hd, ha⟩), hp⟩)

/-- Induction over trace prefixes connects operational clocks to causal maxima. -/
theorem causal_past_invariant {H : History n l} (E : Execution H) (e : Fin l) (i : NodeId n) :
    E.stamp e i = pastClock H e i := by
  have aux : ∀ k, ∀ e : Fin l, e.val = k → ∀ i, E.stamp e i = pastClock H e i := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro e he i
      rw [E.step, pastClock_step E.legal]
      have hh : (fun j => (H.pred e).sup (fun d => E.stamp d j)) =
          (fun j => (H.pred e).sup (fun d => pastClock H d j)) := by
        funext j
        apply Finset.sup_congr rfl
        intro d hd
        exact ih d.val (he ▸ ((mem_pred H d e).mp hd).1) d rfl j
      rw [hh]
  exact aux e.val e rfl i


/-- Membership in the reflexive causal past is exactly the threshold at the
source process. Positivity of local numbering excludes a spurious zero witness. -/
theorem causal_past_iff_coordinate {H : History n l} (E : Execution H) (d e : Fin l) :
    CausalPast H d e ↔ (H.event d).seq ≤ E.stamp e (H.event d).proc := by
  rw [causal_past_invariant E]
  constructor
  · intro h
    exact Finset.le_sup (f := fun a => (H.event a).seq)
      ((mem_pastEvents H d e _).mpr ⟨h, rfl⟩)
  · intro h
    obtain ⟨a, ha, hs⟩ := (Finset.le_sup_iff (seq_pos E.legal d)).mp h
    obtain ⟨ha, hp⟩ := (mem_pastEvents H a e _).mp ha
    have hd := (seq_le_iff_index E.legal hp.symm).mp hs
    rcases lt_or_eq_of_le hd with hd | rfl
    · exact past_trans (Or.inr (Relation.TransGen.single ⟨hd, Or.inl hp.symm⟩)) ha
    · exact ha

theorem stamp_self {H : History n l} (E : Execution H) (e : Fin l) :
    E.stamp e (H.event e).proc = (H.event e).seq := by
  rw [causal_past_invariant E, pastClock_self E.legal]

theorem past_stamp_le {H : History n l} (E : Execution H) {d e : Fin l}
    (h : CausalPast H d e) : VectorLE (E.stamp d) (E.stamp e) := by
  intro i
  rw [causal_past_invariant E, causal_past_invariant E]
  unfold pastClock
  apply Finset.sup_le
  intro a ha
  obtain ⟨ha, hp⟩ := (mem_pastEvents H a d i).mp ha
  exact Finset.le_sup (f := fun a => (H.event a).seq)
    ((mem_pastEvents H a e i).mpr ⟨past_trans ha h, hp⟩)

theorem causal_past_iff_vector_le {H : History n l} (E : Execution H) (d e : Fin l) :
    CausalPast H d e ↔ VectorLE (E.stamp d) (E.stamp e) := by
  refine ⟨past_stamp_le E, ?_⟩
  intro h
  apply (causal_past_iff_coordinate E d e).mpr
  rw [← stamp_self E d]
  exact h _

theorem event_timestamp_injective {H : History n l} (E : Execution H) :
    Function.Injective E.stamp := by
  intro d e h
  apply le_antisymm
  · exact past_index ((causal_past_iff_vector_le E d e).mpr (fun i => le_of_eq (congrFun h i)))
  · exact past_index ((causal_past_iff_vector_le E e d).mpr (fun i => le_of_eq (congrFun h.symm i)))

theorem happens_before_iff_vector_lt {H : History n l} (E : Execution H) (d e : Fin l) :
    HappensBefore H d e ↔ VectorLT (E.stamp d) (E.stamp e) := by
  constructor
  · intro h
    exact ⟨past_stamp_le E (Or.inr h), fun he =>
      (ne_of_lt (happens_before_index h)) (event_timestamp_injective E he)⟩
  · rintro ⟨hle, hne⟩
    rcases (causal_past_iff_vector_le E d e).mpr hle with rfl | h
    · exact (hne rfl).elim
    · exact h

def Concurrent (H : History n l) (d e : Fin l) : Prop :=
  d ≠ e ∧ ¬ HappensBefore H d e ∧ ¬ HappensBefore H e d

theorem concurrent_iff_vector_incomparable {H : History n l} (E : Execution H)
    (d e : Fin l) : Concurrent H d e ↔
    ¬ VectorLE (E.stamp d) (E.stamp e) ∧ ¬ VectorLE (E.stamp e) (E.stamp d) := by
  rw [← causal_past_iff_vector_le, ← causal_past_iff_vector_le]
  simp only [Concurrent, CausalPast]
  constructor
  · rintro ⟨hne, hde, hed⟩
    exact ⟨fun h => h.elim hne hde, fun h => h.elim (Ne.symm hne) hed⟩
  · rintro ⟨hde, hed⟩
    exact ⟨fun h => hde (Or.inl h), fun h => hde (Or.inr h), fun h => hed (Or.inr h)⟩

theorem distinct_concurrency_criterion {H : History n l} (E : Execution H)
    {d e : Fin l} (hne : d ≠ e) :
    (¬ HappensBefore H d e ∧ ¬ HappensBefore H e d) ↔
    ¬ VectorLE (E.stamp d) (E.stamp e) ∧ ¬ VectorLE (E.stamp e) (E.stamp d) := by
  simpa [Concurrent, hne] using concurrent_iff_vector_incomparable E d e

theorem reg_no_self_concurrency (H : History n l) (e : Fin l) : ¬ Concurrent H e e :=
  fun h => h.1 rfl

/-- The usual same-process seq edge coincides with the index-based local edge. -/
theorem local_order_iff {H : History n l} (h : H.Legal) {d e : Fin l}
    (hp : (H.event d).proc = (H.event e).proc) :
    (H.event d).seq < (H.event e).seq ↔ d < e := by
  constructor
  · intro hs
    by_contra hn
    have := (seq_le_iff_index h hp.symm).mpr (le_of_not_gt hn)
    omega
  · exact fun hi => seq_strict h hi hp

/-- All matching message edges point forward, by unique sends and legal receives. -/
theorem matching_send_precedes {H : History n l} (h : H.Legal) {d e : Fin l}
    (hm : H.messageEdge d e) : d < e := by
  obtain ⟨id, hd, he⟩ := hm
  obtain ⟨a, ha, hs⟩ := h.receive_sent e id he
  have := h.send_unique a d id _ _ hs hd
  simpa [this] using ha


/-- Executable clock assignment, recursively using strictly earlier events.
Only the explanatory causal supremum is noncomputable. -/
def compute (H : History n l) (e : Fin l) (i : NodeId n) : ℕ :=
  tick (H.event e).proc
    (fun j => (H.pred e).attach.sup (fun d => compute H d.val j)) i
termination_by e.val
decreasing_by exact ((mem_pred H _ _).mp d.property).1

theorem compute_step (H : History n l) (e : Fin l) (i : NodeId n) :
    compute H e i = tick (H.event e).proc
      (fun j => (H.pred e).sup (fun d => compute H d j)) i := by
  rw [compute]
  apply congrArg (fun f => tick (H.event e).proc f i)
  funext j
  exact Finset.sup_attach (H.pred e) (fun d => compute H d j)

def execute (H : History n l) (h : H.Legal) : Execution H :=
  ⟨h, compute H, compute_step H⟩

theorem execution_unique {H : History n l} (E F : Execution H) : E.stamp = F.stamp := by
  funext e i
  rw [causal_past_invariant E, causal_past_invariant F]

def localBefore {H : History n l} (E : Execution H) (e : Fin l) : VectorClock n :=
  fun i => (H.localPred e).sup (fun d => E.stamp d i)
def History.messagePred (H : History n l) (e : Fin l) : Finset (Fin l) :=
  Finset.univ.filter fun d => d < e ∧ H.messageEdge d e

def deliveredClock {H : History n l} (E : Execution H) (e : Fin l) : VectorClock n :=
  fun i => (H.messagePred e).sup (fun d => E.stamp d i)

theorem pred_union (H : History n l) (e : Fin l) :
    H.pred e = H.localPred e ∪ H.messagePred e := by
  ext d
  simp [History.pred, History.localPred, History.messagePred, History.Direct, and_or_left]

theorem operational_update {H : History n l} (E : Execution H) (e : Fin l) :
    E.stamp e = tick (H.event e).proc (merge (localBefore E e) (deliveredClock E e)) := by
  funext i
  rw [E.step, pred_union]
  simp only [Finset.sup_union]
  rfl

/-- The local prefix fold equals the last actual local timestamp. -/
theorem localBefore_latest {H : History n l} (E : Execution H) {d e : Fin l}
    (hd : d ∈ H.localPred e) (latest : ∀ a ∈ H.localPred e, a ≤ d) :
    localBefore E e = E.stamp d := by
  funext i
  apply le_antisymm
  · apply Finset.sup_le
    intro a ha
    have hap := ((mem_localPred H a e).mp ha).2
    have hdp := ((mem_localPred H d e).mp hd).2
    rcases lt_or_eq_of_le (latest a ha) with hi | rfl
    · exact past_stamp_le E (Or.inr (Relation.TransGen.single ⟨hi, Or.inl (hap.trans hdp.symm)⟩)) i
    · exact le_rfl
  · exact Finset.le_sup (f := fun a => E.stamp a i) hd

theorem localBefore_initial {H : History n l} (E : Execution H) {e : Fin l}
    (he : H.localPred e = ∅) : localBefore E e = fun _ => 0 := by
  funext i
  simp [localBefore, he]

theorem deliveredClock_receive {H : History n l} (E : Execution H) {d e : Fin l}
    (hm : H.messageEdge d e) : deliveredClock E e = E.stamp d := by
  have hd : d < e := matching_send_precedes E.legal hm
  have hx : H.messagePred e = {d} := by
    ext a
    simp only [History.messagePred, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨_, id, ha, he⟩
      obtain ⟨id', hd', he'⟩ := hm
      have hid : id = id' := EventType.recv.inj (he.symm.trans he')
      subst id'
      exact E.legal.send_unique a d id _ _ ha hd'
    · rintro rfl
      exact ⟨hd, hm⟩
  funext i
  simp [deliveredClock, hx]

theorem deliveredClock_local {H : History n l} (E : Execution H) {e : Fin l}
    (he : (H.event e).payload = .local) : deliveredClock E e = fun _ => 0 := by
  have hx : H.messagePred e = ∅ := by
    ext d
    simp [History.messagePred, History.messageEdge, he]
  funext i
  simp [deliveredClock, hx]

theorem deliveredClock_send {H : History n l} (E : Execution H)
    {e : Fin l} {id : ℕ} {dest : NodeId n}
    (he : (H.event e).payload = .send id dest) : deliveredClock E e = fun _ => 0 := by
  have hx : H.messagePred e = ∅ := by
    ext d
    simp [History.messagePred, History.messageEdge, he]
  funext i
  simp [deliveredClock, hx]

theorem receive_update {H : History n l} (E : Execution H) {d e : Fin l}
    (hm : H.messageEdge d e) :
    E.stamp e = tick (H.event e).proc (merge (localBefore E e) (E.stamp d)) := by
  rw [operational_update, deliveredClock_receive E hm]

theorem local_update {H : History n l} (E : Execution H) {e : Fin l}
    (he : (H.event e).payload = .local) : E.stamp e = tick (H.event e).proc (localBefore E e) := by
  rw [operational_update, deliveredClock_local E he]
  congr 1
  funext i
  exact Nat.max_zero _

theorem send_update {H : History n l} (E : Execution H)
    {e : Fin l} {id : ℕ} {dest : NodeId n}
    (he : (H.event e).payload = .send id dest) :
    E.stamp e = tick (H.event e).proc (localBefore E e) := by
  rw [operational_update, deliveredClock_send E he]
  congr 1
  funext i
  exact Nat.max_zero _

/-- The two-process bridge preserves the reviewed predecessor API unchanged. -/
def toPair (v : VectorClock 2) : DistributedVectorClocks.VClock2 := ⟨v 0, v 1⟩

theorem n2_tick1_bridge (v : VectorClock 2) :
    toPair (tick 0 v) = DistributedVectorClocks.tick1 (toPair v) := by
  rfl

theorem n2_tick2_bridge (v : VectorClock 2) :
    toPair (tick 1 v) = DistributedVectorClocks.tick2 (toPair v) := by
  rfl

theorem n2_merge_bridge (v w : VectorClock 2) :
    toPair (merge v w) = DistributedVectorClocks.merge (toPair v) (toPair w) := rfl

theorem n2_receive1_bridge (v w : VectorClock 2) :
    toPair (tick 0 (merge v w)) = DistributedVectorClocks.receive1 (toPair v) (toPair w) := rfl

theorem n2_receive2_bridge (v w : VectorClock 2) :
    toPair (tick 1 (merge v w)) = DistributedVectorClocks.receive2 (toPair v) (toPair w) := rfl

theorem n2_le_bridge (v w : VectorClock 2) :
    VectorLE v w ↔ DistributedVectorClocks.le (toPair v) (toPair w) := by
  constructor
  · intro h; exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i <;> assumption

theorem n2_pair_injective : Function.Injective toPair := by
  intro v w h
  funext i
  fin_cases i
  · exact congrArg DistributedVectorClocks.VClock2.c1 h
  · exact congrArg DistributedVectorClocks.VClock2.c2 h

theorem n2_lt_bridge (v w : VectorClock 2) :
    VectorLT v w ↔ DistributedVectorClocks.lt (toPair v) (toPair w) := by
  simp only [VectorLT, DistributedVectorClocks.lt, n2_le_bridge, n2_pair_injective.ne_iff]


/-- Small executions are checked by kernel reduction, including all legality
conditions, rather than by substituting arbitrary vectors into the final theorem. -/
def independentHistory : History 2 2 :=
  ⟨![⟨0, 1, .local⟩, ⟨1, 1, .local⟩]⟩

theorem independent_legal : independentHistory.Legal := by
  constructor
  · decide
  · intro d e id u v hd he
    fin_cases d <;> simp [independentHistory] at hd
  · intro d e id hd he
    fin_cases d <;> simp [independentHistory] at hd
  · intro e id he
    fin_cases e <;> simp [independentHistory] at he

def independentExecution : Execution independentHistory := execute _ independent_legal

theorem reg_independent_stamps :
    independentExecution.stamp 0 = ![1, 0] ∧ independentExecution.stamp 1 = ![0, 1] := by
  decide +kernel

theorem reg_independent_concurrent : Concurrent independentHistory 0 1 := by
  apply (concurrent_iff_vector_incomparable independentExecution 0 1).mpr
  rw [reg_independent_stamps.1, reg_independent_stamps.2]
  constructor
  · intro h; have := h 0; norm_num at this
  · intro h; have := h 1; norm_num at this

def relayHistory : History 3 4 :=
  ⟨![⟨0, 1, .send 0 1⟩, ⟨1, 1, .recv 0⟩,
     ⟨1, 2, .send 1 2⟩, ⟨2, 1, .recv 1⟩]⟩

theorem relay_legal : relayHistory.Legal := by
  constructor
  · decide
  · intro d e id u v hd he
    fin_cases d <;> fin_cases e <;> dsimp [relayHistory] at hd he ⊢ <;> cases hd <;> cases he
  · intro d e id hd he
    fin_cases d <;> fin_cases e <;> dsimp [relayHistory] at hd he ⊢ <;> cases hd <;> cases he
  · intro e id he
    fin_cases e <;> dsimp [relayHistory] at he <;> cases he
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨2, by decide, rfl⟩

def relayExecution : Execution relayHistory := execute _ relay_legal

theorem reg_relay_stamps :
    relayExecution.stamp 0 = ![1, 0, 0] ∧ relayExecution.stamp 1 = ![1, 1, 0] ∧
    relayExecution.stamp 2 = ![1, 2, 0] ∧ relayExecution.stamp 3 = ![1, 2, 1] := by decide +kernel

theorem reg_three_process_causality : HappensBefore relayHistory 0 3 := by
  apply (happens_before_iff_vector_lt relayExecution 0 3).mpr
  rw [reg_relay_stamps.1, reg_relay_stamps.2.2.2]
  constructor
  · intro i; fin_cases i <;> decide
  · intro h; have := congrFun h 2; change (0 : ℕ) = 1 at this; omega

/-- Sends 0 then 1; receives 1 then 0. A fifth event sends an outstanding message. -/
def reorderedHistory : History 2 5 :=
  ⟨![⟨0, 1, .send 0 1⟩, ⟨0, 2, .send 1 1⟩,
     ⟨1, 1, .recv 1⟩, ⟨1, 2, .recv 0⟩, ⟨0, 3, .send 2 1⟩]⟩

theorem reordered_legal : reorderedHistory.Legal := by
  constructor
  · decide
  · intro d e id u v hd he
    fin_cases d <;> fin_cases e <;> dsimp [reorderedHistory] at hd he ⊢ <;> cases hd <;> cases he
  · intro d e id hd he
    fin_cases d <;> fin_cases e <;> dsimp [reorderedHistory] at hd he ⊢ <;> cases hd <;> cases he
  · intro e id he
    fin_cases e <;> dsimp [reorderedHistory] at he <;> cases he
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨0, by decide, rfl⟩

def reorderedExecution : Execution reorderedHistory := execute _ reordered_legal

theorem reg_out_of_order_stamps :
    reorderedExecution.stamp 2 = ![2, 1] ∧ reorderedExecution.stamp 3 = ![2, 2] ∧
    reorderedExecution.stamp 4 = ![3, 0] := by decide +kernel

theorem reg_out_of_order_causality : HappensBefore reorderedHistory 0 3 ∧
    HappensBefore reorderedHistory 1 2 := by
  constructor <;> apply Relation.TransGen.single <;> decide

theorem reg_undelivered_message :
    (reorderedHistory.event 4).payload = .send 2 1 ∧
    ∀ e, (reorderedHistory.event e).payload ≠ .recv 2 := by decide

def sequentialHistory : History 1 2 := ⟨![⟨0, 1, .local⟩, ⟨0, 2, .local⟩]⟩

theorem sequential_legal : sequentialHistory.Legal := by
  constructor
  · decide
  · intro d e id u v hd he
    fin_cases d <;> simp [sequentialHistory] at hd
  · intro d e id hd he
    fin_cases d <;> simp [sequentialHistory] at hd
  · intro e id he
    fin_cases e <;> simp [sequentialHistory] at he

/-- Omitting tick from two local steps leaves both stamps at the initial zero. -/
theorem counterexample_no_increment : sequentialHistory.Legal ∧
    HappensBefore sequentialHistory 0 1 ∧
    ¬ VectorLT (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0) := by
  refine ⟨sequential_legal, Relation.TransGen.single (by decide), ?_⟩
  exact fun h => h.2 rfl

/-- Omitting merge at the first receive leaves the receiver at its own unit
vector, despite an actual matching send-receive edge. -/
theorem counterexample_no_merge : relayHistory.Legal ∧ HappensBefore relayHistory 0 1 ∧
    ¬ VectorLE (tick (0 : Fin 3) (fun _ => 0)) (tick (1 : Fin 3) (fun _ => 0)) := by
  refine ⟨relay_legal, Relation.TransGen.single (by decide), ?_⟩
  intro h
  have := h 0
  simp [tick] at this


structure DistributedVectorClocksCausalOrderSuite : Prop where
  causalPast : ∀ {n l} {H : History n l} (E : Execution H) e i,
    E.stamp e i = pastClock H e i
  exactOrder : ∀ {n l} {H : History n l} (E : Execution H) d e,
    HappensBefore H d e ↔ VectorLT (E.stamp d) (E.stamp e)
  injective : ∀ {n l} {H : History n l} (E : Execution H), Function.Injective E.stamp
  irrefl : ∀ {n l} (H : History n l) e, ¬ HappensBefore H e e
  trans : ∀ {n l} {H : History n l} {d e f},
    HappensBefore H d e → HappensBefore H e f → HappensBefore H d f
  concurrency : ∀ {n l} {H : History n l} (E : Execution H) d e,
    Concurrent H d e ↔ ¬ VectorLE (E.stamp d) (E.stamp e) ∧ ¬ VectorLE (E.stamp e) (E.stamp d)
  executable : ∀ {n l} (H : History n l) e i,
    compute H e i = tick (H.event e).proc (fun j => (H.pred e).sup (fun d => compute H d j)) i
  receiveRule : ∀ {n l} {H : History n l} (E : Execution H) {d e}, H.messageEdge d e →
    E.stamp e = tick (H.event e).proc (merge (localBefore E e) (E.stamp d))
  pairTick1 : ∀ v, toPair (tick 0 v) = DistributedVectorClocks.tick1 (toPair v)
  pairTick2 : ∀ v, toPair (tick 1 v) = DistributedVectorClocks.tick2 (toPair v)
  pairMerge : ∀ v w, toPair (merge v w) = DistributedVectorClocks.merge (toPair v) (toPair w)
  pairReceive1 : ∀ v w,
    toPair (tick 0 (merge v w)) = DistributedVectorClocks.receive1 (toPair v) (toPair w)
  pairReceive2 : ∀ v w,
    toPair (tick 1 (merge v w)) = DistributedVectorClocks.receive2 (toPair v) (toPair w)
  independent : Concurrent independentHistory 0 1
  relay : HappensBefore relayHistory 0 3
  reordered : HappensBefore reorderedHistory 0 3 ∧ HappensBefore reorderedHistory 1 2
  outstanding : (reorderedHistory.event 4).payload = .send 2 1 ∧
    ∀ e, (reorderedHistory.event e).payload ≠ .recv 2
  noIncrement : sequentialHistory.Legal ∧ HappensBefore sequentialHistory 0 1 ∧
    ¬ VectorLT (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
  noMerge : relayHistory.Legal ∧ HappensBefore relayHistory 0 1 ∧
    ¬ VectorLE (tick (0 : Fin 3) (fun _ => 0)) (tick (1 : Fin 3) (fun _ => 0))

theorem distributed_vector_clocks_causal_order_master_suite :
    DistributedVectorClocksCausalOrderSuite := {
  causalPast := causal_past_invariant
  exactOrder := happens_before_iff_vector_lt
  injective := event_timestamp_injective
  irrefl := happens_before_irrefl
  trans := happens_before_trans
  concurrency := concurrent_iff_vector_incomparable
  executable := compute_step
  receiveRule := receive_update
  pairTick1 := n2_tick1_bridge
  pairTick2 := n2_tick2_bridge
  pairMerge := n2_merge_bridge
  pairReceive1 := n2_receive1_bridge
  pairReceive2 := n2_receive2_bridge
  independent := reg_independent_concurrent
  relay := reg_three_process_causality
  reordered := reg_out_of_order_causality
  outstanding := reg_undelivered_message
  noIncrement := counterexample_no_increment
  noMerge := counterexample_no_merge
}

#print axioms distributed_vector_clocks_causal_order_master_suite

end DistributedVectorClocksCausalOrder
