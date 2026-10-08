/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Tactic.NormNum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! Raymond's local handlers, with asynchronous exact-once message delivery.
Internal phases serialize ASSIGN_PRIVILEGE followed by MAKE_REQUEST. A phase is
local bookkeeping, not a network ordering assumption. The network may reorder
REQUEST and PRIVILEGE. Message serials identify occurrences; handlers never compare
them. Safety is a reachable-state theorem, not a guard on transitions.
-/
namespace DistributedRaymondTreeMutex

abbrev NodeId (n : ℕ) := Fin n

inductive Mode where
  | idle | requesting | inCS
  deriving DecidableEq, Repr

inductive Phase where
  | ready | assign | makeRequest
  deriving DecidableEq, Repr

structure Request (n : ℕ) where
  sender : NodeId n
  dest : NodeId n
  serial : ℕ
  deriving DecidableEq, Repr

structure State (n : ℕ) where
  mode : NodeId n → Mode
  holder : NodeId n → NodeId n
  queue : NodeId n → List (NodeId n)
  asked : NodeId n → Bool
  phase : NodeId n → Phase
  serial : NodeId n → ℕ
  owners : Finset (NodeId n)
  flight : Option (NodeId n × NodeId n)
  sent : Finset (Request n)
  received : Finset (Request n)
  requestSends : ℕ
  privilegeSends : ℕ

def initial (owner : NodeId n) (route : NodeId n → NodeId n) : State n :=
  ⟨fun _ => .idle, route, fun _ => [], fun _ => false, fun _ => .ready,
    fun _ => 0, {owner}, none, ∅, ∅, 0, 0⟩

def tokenCount (s : State n) : ℕ := s.owners.card + s.flight.toList.length

inductive Event (n : ℕ) where
  | request (i : NodeId n)
  | receive (r : Request n)
  | deliver (src dest : NodeId n)
  | leave (i : NodeId n)
  | assign (i : NodeId n)
  | makeRequest (i : NodeId n)
  | idle
  deriving DecidableEq, Repr

def Enabled (s : State n) : Event n → Prop
  | .request i => s.phase i = .ready ∧ s.mode i = .idle
  | .receive r => s.phase r.dest = .ready ∧ r ∈ s.sent ∧ r ∉ s.received
  | .deliver i j => s.phase j = .ready ∧ s.flight = some (i, j)
  | .leave i => s.phase i = .ready ∧ s.mode i = .inCS
  | .assign i => s.phase i = .assign
  | .makeRequest i => s.phase i = .makeRequest
  | .idle => True

instance (s : State n) (e : Event n) : Decidable (Enabled s e) := by
  cases e <;> simp only [Enabled] <;> infer_instance

/-- The dequeue precedes the handoff. ASKED is cleared when an outstanding
request is satisfied by assignment of the privilege. -/
def assignPrivilege (s : State n) (i : NodeId n) : State n :=
  let t := { s with phase := Function.update s.phase i .makeRequest }
  if i ∈ s.owners ∧ s.mode i ≠ .inCS then
    match s.queue i with
    | [] => t
    | j :: tail =>
      let u := { t with queue := Function.update s.queue i tail
                        asked := Function.update s.asked i false
                        holder := Function.update s.holder i j }
      if j = i then { u with mode := Function.update s.mode i .inCS }
      else { u with owners := s.owners.erase i, flight := some (i, j)
                    privilegeSends := s.privilegeSends + 1 }
  else t

def makeRequest (s : State n) (i : NodeId n) : State n :=
  let t := { s with phase := Function.update s.phase i .ready }
  if s.holder i ≠ i ∧ s.queue i ≠ [] ∧ s.asked i = false then
    { t with asked := Function.update s.asked i true
             serial := Function.update s.serial i (s.serial i + 1)
             sent := insert ⟨i, s.holder i, s.serial i⟩ s.sent
             requestSends := s.requestSends + 1 }
  else t

def next (s : State n) : Event n → State n
  | .request i =>
    { s with mode := Function.update s.mode i .requesting
             queue := Function.update s.queue i (s.queue i ++ [i])
             phase := Function.update s.phase i .assign }
  | .receive r =>
    { s with queue := Function.update s.queue r.dest (s.queue r.dest ++ [r.sender])
             received := insert r s.received
             phase := Function.update s.phase r.dest .assign }
  | .deliver _i j =>
    { s with owners := insert j s.owners, flight := none
             holder := Function.update s.holder j j
             phase := Function.update s.phase j .assign }
  | .leave i =>
    { s with mode := Function.update s.mode i .idle
             phase := Function.update s.phase i .assign }
  | .assign i => assignPrivilege s i
  | .makeRequest i => makeRequest s i
  | .idle => s

def Step (s : State n) (e : Event n) (t : State n) : Prop :=
  Enabled s e ∧ t = next s e

inductive Execution : State n → State n → Prop where
  | refl (s) : Execution s s
  | tail {s t u e} : Execution s t → Step t e u → Execution s u

def Reachable (owner : NodeId n) (route : NodeId n → NodeId n) (s : State n) : Prop :=
  Execution (initial owner route) s

structure Safety (s : State n) : Prop where
  conserved : tokenCount s = 1
  cs_owner : ∀ i, s.mode i = .inCS → i ∈ s.owners

theorem owner_singleton {s : State n} (h : tokenCount s = 1) {i} (hi : i ∈ s.owners) :
    s.owners = {i} ∧ s.flight = none := by
  have hp := Finset.card_pos.mpr ⟨i, hi⟩
  cases hf : s.flight with
  | none =>
    have hc : s.owners.card = 1 := by simpa [tokenCount, hf] using h
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
    have hij : i = j := by simpa [hj] using hi
    exact ⟨by simpa [hij] using hj, rfl⟩
  | some j =>
    have hc : s.owners.card = 0 := by simpa [tokenCount, hf] using h
    omega

theorem flight_empty_owners {s : State n} (h : tokenCount s = 1) {i j}
    (hf : s.flight = some (i, j)) : s.owners = ∅ := by
  have hc : s.owners.card = 0 := by simpa [tokenCount, hf] using h
  exact Finset.card_eq_zero.mp hc

theorem safety_initial (owner : NodeId n) (route : NodeId n → NodeId n) :
    Safety (initial owner route) := by
  constructor
  · simp [tokenCount, initial]
  · simp [initial]

theorem safety_assign {s : State n} (h : Safety s) (a : NodeId n) :
    Safety (assignPrivilege s a) := by
  unfold assignPrivilege
  split
  · rename_i ha
    split
    · exact ⟨h.conserved, h.cs_owner⟩
    · rename_i j tail hq
      split
      · constructor
        · exact h.conserved
        · intro i hi
          by_cases hia : i = a
          · subst i; exact ha.1
          · exact h.cs_owner i (by simpa [hia] using hi)
      · obtain ⟨ho, _⟩ := owner_singleton h.conserved ha.1
        constructor
        · simp [tokenCount, ho]
        · intro i hi
          have hia : i = a := by simpa [ho] using h.cs_owner i hi
          subst i
          exact False.elim (ha.2 hi)
  · exact ⟨h.conserved, h.cs_owner⟩

theorem safety_makeRequest {s : State n} (h : Safety s) (a : NodeId n) :
    Safety (makeRequest s a) := by
  unfold makeRequest
  split <;> exact ⟨h.conserved, h.cs_owner⟩

theorem safety_step {s : State n} (h : Safety s) {e} (he : Enabled s e) :
    Safety (next s e) := by
  cases e with
  | request a =>
    constructor
    · exact h.conserved
    · intro i hi
      by_cases ha : i = a
      · subst i; simp [next] at hi
      · exact h.cs_owner i (by simpa [next, ha] using hi)
  | receive => exact ⟨h.conserved, h.cs_owner⟩
  | deliver i j =>
    have ho := flight_empty_owners h.conserved he.2
    constructor
    · simp [tokenCount, next, ho]
    · intro k hk; exact Finset.mem_insert_of_mem (h.cs_owner k hk)
  | leave a =>
    constructor
    · exact h.conserved
    · intro i hi
      by_cases ha : i = a
      · subst i; simp [next] at hi
      · exact h.cs_owner i (by simpa [next, ha] using hi)
  | assign a => exact safety_assign h a
  | makeRequest a => exact safety_makeRequest h a
  | idle => exact h

theorem reachable_safety {owner : NodeId n} {route} {s : State n}
    (h : Reachable owner route s) : Safety s := by
  induction h with
  | refl => exact safety_initial _ _
  | tail _ hs ih => rcases hs with ⟨he, rfl⟩; exact safety_step ih he

theorem privilege_conservation_invariant {owner : NodeId n} {route} {s : State n}
    (h : Reachable owner route s) : tokenCount s = 1 := (reachable_safety h).conserved

theorem mutual_exclusion_safety {owner : NodeId n} {route} {s : State n}
    (h : Reachable owner route s) {i j} (hne : i ≠ j)
    (hi : s.mode i = .inCS) (hj : s.mode j = .inCS) : False := by
  have hs := reachable_safety h
  have ho := (owner_singleton hs.conserved (hs.cs_owner i hi)).1
  exact hne (Finset.mem_singleton.mp (ho ▸ hs.cs_owner j hj)).symm

/-- Every live pointer and queued neighbour respects the fixed network.
Self requests are local and do not generate network messages. -/
structure EdgeLocality (G : SimpleGraph (NodeId n)) (s : State n) : Prop where
  holder : ∀ i, s.holder i = i ∨ G.Adj i (s.holder i)
  queue : ∀ i j, j ∈ s.queue i → j = i ∨ G.Adj i j
  sent : ∀ r ∈ s.sent, G.Adj r.sender r.dest
  flight : ∀ i j, s.flight = some (i, j) → G.Adj i j

theorem locality_initial {G : SimpleGraph (NodeId n)} (owner : NodeId n) {route}
    (hr : ∀ i, route i = i ∨ G.Adj i (route i)) : EdgeLocality G (initial owner route) := by
  refine ⟨hr, ?_, ?_, ?_⟩ <;> simp [initial]

theorem locality_assign {G : SimpleGraph (NodeId n)} {s : State n}
    (h : EdgeLocality G s) (a : NodeId n) : EdgeLocality G (assignPrivilege s a) := by
  unfold assignPrivilege
  split
  · split
    · exact ⟨h.holder, h.queue, h.sent, h.flight⟩
    · rename_i j tail hq
      have hj := h.queue a j (by simp [hq])
      have htail : ∀ i k, k ∈ Function.update s.queue a tail i → k = i ∨ G.Adj i k := by
        intro i k hk
        by_cases hi : i = a
        · subst i
          have ht : k ∈ tail := by simpa using hk
          exact h.queue a k (by simp [hq, ht])
        · exact h.queue i k (by simpa [hi] using hk)
      have hh : ∀ i, Function.update s.holder a j i = i ∨
          G.Adj i (Function.update s.holder a j i) := by
        intro i
        by_cases hi : i = a
        · subst i; simpa using hj
        · simpa [hi] using h.holder i
      split
      · exact ⟨hh, htail, h.sent, h.flight⟩
      · rename_i hne
        refine ⟨hh, htail, h.sent, ?_⟩
        intro i k hik
        have heq : a = i ∧ j = k := by simpa using hik
        obtain ⟨rfl, rfl⟩ := heq
        exact hj.resolve_left hne
  · exact ⟨h.holder, h.queue, h.sent, h.flight⟩

theorem locality_makeRequest {G : SimpleGraph (NodeId n)} {s : State n}
    (h : EdgeLocality G s) (a : NodeId n) : EdgeLocality G (makeRequest s a) := by
  unfold makeRequest
  split
  · rename_i ha
    refine ⟨h.holder, h.queue, ?_, h.flight⟩
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact (h.holder a).resolve_left ha.1
    · exact h.sent r hr
  · exact ⟨h.holder, h.queue, h.sent, h.flight⟩

theorem locality_step {G : SimpleGraph (NodeId n)} {s : State n}
    (h : EdgeLocality G s) {e} (he : Enabled s e) : EdgeLocality G (next s e) := by
  cases e with
  | request a =>
    refine ⟨h.holder, ?_, h.sent, h.flight⟩
    intro i j hj
    by_cases hi : i = a
    · subst i
      have hx : j ∈ s.queue a ∨ j = a := by simpa [next] using hj
      exact hx.elim (h.queue a j) Or.inl
    · exact h.queue i j (by simpa [next, hi] using hj)
  | receive r =>
    refine ⟨h.holder, ?_, h.sent, h.flight⟩
    intro i j hj
    by_cases hi : i = r.dest
    · subst i
      have hx : j ∈ s.queue r.dest ∨ j = r.sender := by simpa [next] using hj
      rcases hx with hx | rfl
      · exact h.queue r.dest j hx
      · exact Or.inr (h.sent r he.2.1).symm
    · exact h.queue i j (by simpa [next, hi] using hj)
  | deliver a b =>
    refine ⟨?_, h.queue, h.sent, ?_⟩
    · intro i
      by_cases hi : i = b
      · subst i; simp [next]
      · simpa [next, hi] using h.holder i
    · simp [next]
  | leave => exact ⟨h.holder, h.queue, h.sent, h.flight⟩
  | assign a => exact locality_assign h a
  | makeRequest a => exact locality_makeRequest h a
  | idle => exact h

theorem reachable_edge_locality {G : SimpleGraph (NodeId n)} {owner : NodeId n} {route}
    (hr : ∀ i, route i = i ∨ G.Adj i (route i)) {s : State n}
    (hs : Reachable owner route s) : EdgeLocality G s := by
  induction hs with
  | refl => exact locality_initial _ hr
  | tail _ he ih => rcases he with ⟨he, rfl⟩; exact locality_step ih he

/-- Executable finite traces are used only as witnesses and regressions. -/
def execute (s : State n) : List (Event n) → State n
  | [] => s
  | e :: es => execute (next s e) es

def ValidEvents (s : State n) : List (Event n) → Prop
  | [] => True
  | e :: es => Enabled s e ∧ ValidEvents (next s e) es

instance (s : State n) (es : List (Event n)) : Decidable (ValidEvents s es) := by
  induction es generalizing s with
  | nil => exact isTrue trivial
  | cons e es ih => exact instDecidableAnd

theorem execute_reachable {s : State n} {es : List (Event n)} (h : ValidEvents s es) :
    Execution s (execute s es) := by
  have trans : ∀ {s t u : State n}, Execution s t → Execution t u → Execution s u := by
    intro s t u hst htu
    induction htu with
    | refl => exact hst
    | tail _ h ih => exact .tail ih h
  induction es generalizing s with
  | nil => exact .refl _
  | cons e es ih =>
    exact trans (.tail (.refl s) ⟨h.1, rfl⟩) (ih h.2)

def twoNodeInitial : State 2 := initial 0 (fun _ => 0)

def transitTrace : List (Event 2) :=
  [.request 1, .assign 1, .makeRequest 1, .receive ⟨1, 0, 0⟩, .assign 0]

theorem transit_trace_valid : ValidEvents twoNodeInitial transitTrace := by decide

/-- The sender changes HOLDER before delivery; the destination still points back.
Thus raw HOLDER acyclicity is false even for a two-node tree. -/
theorem raw_holder_two_cycle_reachable : ∃ s : State 2,
    Reachable 0 (fun _ => 0) s ∧ s.holder 0 = 1 ∧ s.holder 1 = 0 ∧
      s.flight = some (0, 1) ∧ s.owners = ∅ := by
  refine ⟨execute twoNodeInitial transitTrace, execute_reachable transit_trace_valid, ?_⟩
  decide

/-- A path follows the local HOLDER pointer at each nonterminal vertex. -/
def Follows {G : SimpleGraph (NodeId n)} (f : NodeId n → NodeId n) :
    {i j : NodeId n} → G.Walk i j → Prop
  | _, _, .nil => True
  | i, _, @SimpleGraph.Walk.cons _ _ _ k _ _ p => f i = k ∧ Follows f p

theorem follows_update_end {G : SimpleGraph (NodeId n)} {f : NodeId n → NodeId n}
    {i j : NodeId n} {p : G.Walk i j} (hp : p.IsPath) (hf : Follows f p) (v : NodeId n) :
    Follows (Function.update f j v) p := by
  induction p with
  | nil => trivial
  | @cons i k j h p ih =>
    obtain ⟨ht, hn⟩ := (SimpleGraph.Walk.cons_isPath_iff h p).mp hp
    have hij : i ≠ j := fun he => hn (he ▸ p.end_mem_support)
    exact ⟨by simpa [Follows, hij] using hf.1, ih ht hf.2⟩

theorem follows_takeUntil {G : SimpleGraph (NodeId n)} {f : NodeId n → NodeId n}
    {i j : NodeId n} {p : G.Walk i j} (hf : Follows f p) (v : NodeId n)
    (hv : v ∈ p.support) : Follows f (p.takeUntil v hv) := by
  induction p with
  | @nil u =>
    have he : v = u := by simpa using hv
    subst v; trivial
  | @cons i k j h p ih =>
    by_cases hi : i = v
    · subst v; simp [SimpleGraph.Walk.takeUntil, Follows]
    · have ht : v ∈ p.support := by simpa [SimpleGraph.Walk.support, Ne.symm hi] using hv
      simpa [SimpleGraph.Walk.takeUntil, hi, Follows] using And.intro hf.1 (ih hf.2 ht)

theorem follows_concat {G : SimpleGraph (NodeId n)} {f : NodeId n → NodeId n}
    {i j v : NodeId n} {p : G.Walk i j} (hf : Follows f p)
    (h : G.Adj j v) (he : f j = v) : Follows f (p.concat h) := by
  induction p with
  | nil => exact ⟨he, trivial⟩
  | cons _ _ ih => exact ⟨hf.1, ih hf.2 h he⟩

/-- The outgoing pointer of the root is deliberately not read. During transit
this root is the destination of PRIVILEGE, not a fictitious token owner. -/
def Routes (G : SimpleGraph (NodeId n)) (f : NodeId n → NodeId n) (root : NodeId n) : Prop :=
  ∀ i, ∃ p : G.Walk i root, p.IsPath ∧ Follows f p

theorem routes_update_root {G : SimpleGraph (NodeId n)} {f : NodeId n → NodeId n}
    {root : NodeId n} (hr : Routes G f root) (v : NodeId n) :
    Routes G (Function.update f root v) root := by
  intro i
  obtain ⟨p, hp, hf⟩ := hr i
  exact ⟨p, hp, follows_update_end hp hf v⟩

theorem routes_reroot {G : SimpleGraph (NodeId n)} {f : NodeId n → NodeId n}
    {root v : NodeId n} (hr : Routes G f root) (hadj : G.Adj root v) :
    Routes G (Function.update f root v) v := by
  intro i
  obtain ⟨p, hp, hf⟩ := hr i
  have hu := follows_update_end hp hf v
  by_cases hv : v ∈ p.support
  · exact ⟨p.takeUntil v hv, hp.takeUntil hv, follows_takeUntil hu v hv⟩
  · exact ⟨p.concat hadj, hp.concat hv hadj,
      follows_concat hu hadj (by simp)⟩

def Location (s : State n) (i : NodeId n) : Prop :=
  i ∈ s.owners ∨ ∃ src, s.flight = some (src, i)

theorem location_unique {s : State n} (hs : tokenCount s = 1) {i j}
    (hi : Location s i) (hj : Location s j) : i = j := by
  rcases hi with hi | ⟨a, hi⟩
  · obtain ⟨ho, hf⟩ := owner_singleton hs hi
    rcases hj with hj | ⟨b, hj⟩
    · exact (Finset.mem_singleton.mp (ho ▸ hj)).symm
    · simp [hf] at hj
  · have ho := flight_empty_owners hs hi
    rcases hj with hj | ⟨b, hj⟩
    · simp [ho] at hj
    · rw [hi] at hj
      exact (Prod.mk.inj (Option.some.inj hj)).2

structure Topology (G : SimpleGraph (NodeId n)) (s : State n) : Prop where
  routes : ∃ root, Location s root ∧ Routes G s.holder root
  owner_self : ∀ i ∈ s.owners, s.holder i = i

theorem topology_initial {G : SimpleGraph (NodeId n)} {owner : NodeId n} {route}
    (hr : Routes G route owner) (ho : route owner = owner) :
    Topology G (initial owner route) := by
  refine ⟨⟨owner, Or.inl (by simp [initial]), hr⟩, ?_⟩
  intro i hi
  have he : i = owner := by simpa [initial] using hi
  subst i; exact ho

theorem topology_assign {G : SimpleGraph (NodeId n)} {s : State n}
    (hs : Safety s) (hl : EdgeLocality G s) (ht : Topology G s) (a : NodeId n) :
    Topology G (assignPrivilege s a) := by
  unfold assignPrivilege
  split
  · rename_i ha
    split
    · exact ⟨ht.routes, ht.owner_self⟩
    · rename_i j tail hq
      obtain ⟨ho, _⟩ := owner_singleton hs.conserved ha.1
      obtain ⟨root, hroot, hr⟩ := ht.routes
      have he : root = a := location_unique hs.conserved hroot (Or.inl ha.1)
      subst root
      have hj := hl.queue a j (by simp [hq])
      split
      · rename_i hja
        subst j
        refine ⟨⟨a, Or.inl ha.1, routes_update_root hr a⟩, ?_⟩
        intro i hi
        have hi' : i = a := by simpa [ho] using hi
        subst i; simp
      · rename_i hja
        refine ⟨⟨j, Or.inr ⟨a, rfl⟩, routes_reroot hr (hj.resolve_left hja)⟩, ?_⟩
        simp [ho]
  · exact ⟨ht.routes, ht.owner_self⟩

theorem topology_makeRequest {G : SimpleGraph (NodeId n)} {s : State n}
    (ht : Topology G s) (a : NodeId n) : Topology G (makeRequest s a) := by
  unfold makeRequest
  split <;> exact ⟨ht.routes, ht.owner_self⟩

theorem topology_step {G : SimpleGraph (NodeId n)} {s : State n}
    (hs : Safety s) (hl : EdgeLocality G s) (ht : Topology G s)
    {e} (he : Enabled s e) : Topology G (next s e) := by
  cases e with
  | request => exact ⟨ht.routes, ht.owner_self⟩
  | receive => exact ⟨ht.routes, ht.owner_self⟩
  | leave => exact ⟨ht.routes, ht.owner_self⟩
  | idle => exact ht
  | makeRequest a => exact topology_makeRequest ht a
  | assign a => exact topology_assign hs hl ht a
  | deliver a b =>
    obtain ⟨root, hroot, hr⟩ := ht.routes
    have heq : root = b := location_unique hs.conserved hroot (Or.inr ⟨a, he.2⟩)
    subst root
    have ho := flight_empty_owners hs.conserved he.2
    refine ⟨⟨b, Or.inl (by simp [next]), routes_update_root hr b⟩, ?_⟩
    intro i hi
    have hi' : i = b := by simpa [next, ho] using hi
    subst i; simp [next]

theorem reachable_topology {G : SimpleGraph (NodeId n)} {owner : NodeId n} {route}
    (hr : Routes G route owner) (ho : route owner = owner)
    (he : ∀ i, route i = i ∨ G.Adj i (route i)) {s : State n}
    (hs : Reachable owner route s) : Topology G s := by
  induction hs with
  | refl => exact topology_initial hr ho
  | tail hst htu ih =>
    rcases htu with ⟨hen, rfl⟩
    exact topology_step (reachable_safety hst) (reachable_edge_locality he hst) ih hen

/-- All effective HOLDER paths terminate at the actual owner or packet destination.
No assertion of acyclicity is made about the destination's outgoing raw pointer. -/
theorem holder_graph_acyclicity {G : SimpleGraph (NodeId n)} {owner : NodeId n} {route}
    (hr : Routes G route owner) (ho : route owner = owner)
    (he : ∀ i, route i = i ∨ G.Adj i (route i)) {s : State n}
    (hs : Reachable owner route s) : ∃ root, Location s root ∧ Routes G s.holder root :=
  (reachable_topology hr ho he hs).routes

noncomputable def treePath {G : SimpleGraph (NodeId n)} (hG : G.IsTree)
    (i root : NodeId n) : G.Walk i root := (hG.existsUnique_path i root).choose

theorem treePath_isPath {G : SimpleGraph (NodeId n)} (hG : G.IsTree)
    (i root : NodeId n) : (treePath hG i root).IsPath :=
  (hG.existsUnique_path i root).choose_spec.1

theorem treePath_eq {G : SimpleGraph (NodeId n)} (hG : G.IsTree)
    {i root : NodeId n} {p : G.Walk i root} (hp : p.IsPath) : treePath hG i root = p :=
  ((hG.existsUnique_path i root).choose_spec.2 p hp).symm

noncomputable def treeRoute {G : SimpleGraph (NodeId n)} (hG : G.IsTree)
    (root i : NodeId n) : NodeId n := (treePath hG i root).snd

theorem treeRoute_follows {G : SimpleGraph (NodeId n)} (hG : G.IsTree)
    {i root : NodeId n} {p : G.Walk i root} (hp : p.IsPath) :
    Follows (treeRoute hG root) p := by
  induction p with
  | nil => trivial
  | cons h p ih =>
    refine ⟨?_, ih hp.of_cons⟩
    simp [treeRoute, treePath_eq hG hp]

theorem treeRoute_routes {G : SimpleGraph (NodeId n)} (hG : G.IsTree) (root : NodeId n) :
    Routes G (treeRoute hG root) root := by
  intro i
  exact ⟨treePath hG i root, treePath_isPath hG i root,
    treeRoute_follows hG (treePath_isPath hG i root)⟩

theorem treeRoute_self {G : SimpleGraph (NodeId n)} (hG : G.IsTree) (root : NodeId n) :
    treeRoute hG root root = root := by
  rw [treeRoute, treePath_eq hG (SimpleGraph.Walk.IsPath.nil (u := root))]
  rfl

theorem treeRoute_local {G : SimpleGraph (NodeId n)} (hG : G.IsTree) (root i : NodeId n) :
    treeRoute hG root i = i ∨ G.Adj i (treeRoute hG root i) := by
  unfold treeRoute
  cases treePath hG i root with
  | nil => exact Or.inl rfl
  | cons h p => exact Or.inr (by simpa using h)

theorem tree_initialization_exists {G : SimpleGraph (NodeId n)} (hG : G.IsTree)
    (root : NodeId n) : ∃ route, Routes G route root ∧ route root = root ∧
      ∀ i, route i = i ∨ G.Adj i (route i) :=
  ⟨treeRoute hG root, treeRoute_routes hG root, treeRoute_self hG root, treeRoute_local hG root⟩

theorem follows_iteration {G : SimpleGraph (NodeId n)} {f : NodeId n → NodeId n}
    {i j : NodeId n} {p : G.Walk i j} (hf : Follows f p) : f^[p.length] i = j := by
  induction p with
  | nil => rfl
  | cons _ _ ih =>
    rw [SimpleGraph.Walk.length_cons, Function.iterate_succ_apply, hf.1]
    exact ih hf.2

/-- Suppressing the virtual root's outgoing edge gives a terminating routing
function. The bound counts pointer hops, not network messages or wall time. -/
theorem effective_holder_termination {G : SimpleGraph (NodeId n)} {f : NodeId n → NodeId n}
    {root : NodeId n} (hr : Routes G f root) (i : NodeId n) :
    ∃ k, k < n ∧ (Function.update f root root)^[k] i = root := by
  obtain ⟨p, hp, hf⟩ := hr i
  exact ⟨p.length, by simpa using hp.length_lt, follows_iteration (follows_update_end hp hf root)⟩

theorem tree_path_length_eq_dist {G : SimpleGraph (NodeId n)} (hG : G.IsTree)
    {i j : NodeId n} {p : G.Walk i j} (hp : p.IsPath) : p.length = G.dist i j := by
  obtain ⟨q, hq, hlen⟩ := hG.connected.exists_path_of_dist i j
  have he : p = q := Subtype.mk.inj (hG.isAcyclic.subsingleton_path i j |>.elim ⟨p, hp⟩ ⟨q, hq⟩)
  exact he ▸ hlen

def SelfQueued (s : State n) : Prop :=
  ∀ i, (s.queue i).count i = if s.mode i = .requesting then 1 else 0

theorem selfQueued_initial (owner : NodeId n) (route) : SelfQueued (initial owner route) := by
  intro i; simp [initial]

theorem selfQueued_assign {s : State n} (hs : SelfQueued s) (a : NodeId n) :
    SelfQueued (assignPrivilege s a) := by
  unfold assignPrivilege
  split
  · split
    · exact hs
    · rename_i j tail hq
      split
      · rename_i hja
        subst j
        intro i
        by_cases hi : i = a
        · subst i
          have hc := hs a
          simp only [hq, List.count_cons_self] at hc
          split_ifs at hc; simp_all
        · simpa [hi] using hs i
      · rename_i hja
        intro i
        by_cases hi : i = a
        · subst i
          simpa [hq, hja] using hs a
        · simpa [hi] using hs i
  · exact hs

theorem selfQueued_makeRequest {s : State n} (hs : SelfQueued s) (a : NodeId n) :
    SelfQueued (makeRequest s a) := by
  unfold makeRequest
  split <;> exact hs

theorem selfQueued_step {G : SimpleGraph (NodeId n)} {s : State n}
    (hl : EdgeLocality G s) (hs : SelfQueued s) {e} (he : Enabled s e) :
    SelfQueued (next s e) := by
  cases e with
  | request a =>
    intro i
    by_cases hi : i = a
    · subst i
      have hc : (s.queue a).count a = 0 := by simpa [he.2] using hs a
      simp [next, hc]
    · simpa [next, hi] using hs i
  | receive r =>
    have hn : r.dest ≠ r.sender := (hl.sent r he.2.1).ne.symm
    intro i
    by_cases hi : i = r.dest
    · subst i
      dsimp only [next]
      simp only [Function.update_self, List.count_append]
      have hc : [r.sender].count r.dest = 0 := by simp [Ne.symm hn]
      rw [hc, Nat.add_zero]
      exact hs r.dest
    · change (Function.update s.queue r.dest (s.queue r.dest ++ [r.sender]) i).count i = _
      rw [Function.update_of_ne hi]
      exact hs i
  | deliver => exact hs
  | leave a =>
    intro i
    by_cases hi : i = a
    · subst i; simpa [next, he.2] using hs a
    · simpa [next, hi] using hs i
  | assign a => exact selfQueued_assign hs a
  | makeRequest a => exact selfQueued_makeRequest hs a
  | idle => exact hs

theorem reachable_selfQueued {G : SimpleGraph (NodeId n)} {owner : NodeId n} {route}
    (he : ∀ i, route i = i ∨ G.Adj i (route i)) {s : State n}
    (hs : Reachable owner route s) : SelfQueued s := by
  induction hs with
  | refl => exact selfQueued_initial _ _
  | tail hst htu ih =>
    rcases htu with ⟨hen, rfl⟩
    exact selfQueued_step (reachable_edge_locality he hst) ih hen

structure Run (n : ℕ) where
  owner : NodeId n
  route : NodeId n → NodeId n
  state : ℕ → State n
  event : ℕ → Event n
  start : state 0 = initial owner route
  valid : ∀ k, Step (state k) (event k) (state (k + 1))

theorem Run.reachable (ρ : Run n) (k : ℕ) : Reachable ρ.owner ρ.route (ρ.state k) := by
  induction k with
  | zero => rw [ρ.start]; exact .refl _
  | succ k ih => exact .tail ih (ρ.valid k)

def Internal : Event n → Prop
  | .assign _ | .makeRequest _ => True
  | _ => False

/-- Fairness concerns the actual local handler phases, not eventual service. -/
def WeakFairness (ρ : Run n) : Prop := ∀ e, Internal e → ∀ k,
  (∀ l, k ≤ l → Enabled (ρ.state l) e) → ∃ l, k ≤ l ∧ ρ.event l = e

def ReliableDelivery (ρ : Run n) : Prop :=
  (∀ k r, r ∈ (ρ.state k).sent → ∃ l, k ≤ l ∧ r ∈ (ρ.state l).received) ∧
  (∀ k i j, (ρ.state k).flight = some (i, j) → ∃ l, k ≤ l ∧ ρ.event l = .deliver i j)

def FiniteCS (ρ : Run n) : Prop := ∀ k i, (ρ.state k).mode i = .inCS →
  ∃ l, k ≤ l ∧ ρ.event l = .leave i

theorem fair_persistent_action (ρ : Run n) (hf : WeakFairness ρ) (e : Event n)
    (he : Internal e) (k : ℕ) (hk : Enabled (ρ.state k) e)
    (hp : ∀ l, k ≤ l → Enabled (ρ.state l) e → ρ.event l ≠ e →
      Enabled (ρ.state (l + 1)) e) : ∃ l, k ≤ l ∧ ρ.event l = e := by
  by_contra hn
  push Not at hn
  have hall : ∀ l, k ≤ l → Enabled (ρ.state l) e := by
    intro l hkl
    induction l, hkl using Nat.le_induction with
    | base => exact hk
    | succ l hkl ih => exact hp l hkl ih (hn l hkl)
  obtain ⟨l, hkl, heq⟩ := hf e he k hall
  exact hn l hkl heq

structure MessageHistory (s : State n) : Prop where
  received_sent : s.received ⊆ s.sent
  serial_bound : ∀ r ∈ s.sent, r.serial < s.serial r.sender

theorem history_initial (owner : NodeId n) (route) : MessageHistory (initial owner route) := by
  constructor <;> simp [initial]

theorem history_assign {s : State n} (hs : MessageHistory s) (i : NodeId n) :
    MessageHistory (assignPrivilege s i) := by
  unfold assignPrivilege
  split
  · split
    · exact ⟨hs.received_sent, hs.serial_bound⟩
    · split <;> exact ⟨hs.received_sent, hs.serial_bound⟩
  · exact ⟨hs.received_sent, hs.serial_bound⟩

theorem next_request_fresh {s : State n} (hs : MessageHistory s) (i : NodeId n) :
    (⟨i, s.holder i, s.serial i⟩ : Request n) ∉ s.sent := by
  intro h
  have := hs.serial_bound _ h
  exact (Nat.lt_irrefl _) this

theorem history_makeRequest {s : State n} (hs : MessageHistory s) (a : NodeId n) :
    MessageHistory (makeRequest s a) := by
  unfold makeRequest
  split
  · constructor
    · intro r hr; exact Finset.mem_insert_of_mem (hs.received_sent hr)
    · intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · simp
      · have hb := hs.serial_bound r hr
        by_cases hi : r.sender = a
        · simpa [hi] using Nat.lt_succ_of_lt (hi ▸ hb)
        · simpa [hi] using hb
  · exact ⟨hs.received_sent, hs.serial_bound⟩

theorem history_step {s : State n} (hs : MessageHistory s) {e} (he : Enabled s e) :
    MessageHistory (next s e) := by
  cases e with
  | receive r =>
    refine ⟨?_, hs.serial_bound⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact he.2.1
    · exact hs.received_sent hq
  | assign i => exact history_assign hs i
  | makeRequest i => exact history_makeRequest hs i
  | request => exact ⟨hs.received_sent, hs.serial_bound⟩
  | deliver => exact ⟨hs.received_sent, hs.serial_bound⟩
  | leave => exact ⟨hs.received_sent, hs.serial_bound⟩
  | idle => exact hs

theorem reachable_message_history {owner : NodeId n} {route} {s : State n}
    (hs : Reachable owner route s) : MessageHistory s := by
  induction hs with
  | refl => exact history_initial _ _
  | tail _ he ih => rcases he with ⟨he, rfl⟩; exact history_step ih he

theorem phase_assign (s : State n) (i : NodeId n) :
    (assignPrivilege s i).phase = Function.update s.phase i .makeRequest := by
  unfold assignPrivilege
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

theorem phase_makeRequest (s : State n) (i : NodeId n) :
    (makeRequest s i).phase = Function.update s.phase i .ready := by
  unfold makeRequest
  split <;> rfl

def Event.actor : Event n → Option (NodeId n)
  | .request i | .leave i | .assign i | .makeRequest i => some i
  | .receive r => some r.dest
  | .deliver _ j => some j
  | .idle => none

theorem phase_foreign (s : State n) (e : Event n) (i : NodeId n)
    (hne : e.actor ≠ some i) : (next s e).phase i = s.phase i := by
  cases e <;> simp only [Event.actor, ne_eq, Option.some.injEq] at hne
  all_goals simp [next, phase_assign, phase_makeRequest, Ne.symm hne]

theorem busy_phase_persistent {s : State n} {i : NodeId n} {p : Phase}
    (hp : s.phase i = p) (hn : p ≠ .ready) {e} (he : Enabled s e)
    (ha : e ≠ .assign i) (hm : e ≠ .makeRequest i) : (next s e).phase i = p := by
  by_cases hactor : e.actor = some i
  · cases e with
    | request a =>
      have hi : a = i := Option.some.inj hactor
      subst a; exact False.elim (hn (hp.symm.trans he.1))
    | receive r =>
      have hi : r.dest = i := Option.some.inj hactor
      exact False.elim (hn (hp.symm.trans (hi ▸ he.1)))
    | deliver a b =>
      have hi : b = i := Option.some.inj hactor
      subst b; exact False.elim (hn (hp.symm.trans he.1))
    | leave a =>
      have hi : a = i := Option.some.inj hactor
      subst a; exact False.elim (hn (hp.symm.trans he.1))
    | assign a =>
      have hi : a = i := Option.some.inj hactor
      subst a; exact False.elim (ha rfl)
    | makeRequest a =>
      have hi : a = i := Option.some.inj hactor
      subst a; exact False.elim (hm rfl)
    | idle => cases hactor
  · exact (phase_foreign s e i hactor).trans hp

theorem assign_eventually (ρ : Run n) (hf : WeakFairness ρ) {k i}
    (hp : (ρ.state k).phase i = .assign) : ∃ l, k ≤ l ∧ ρ.event l = .assign i := by
  apply fair_persistent_action ρ hf (.assign i) trivial k hp
  intro l _ hl hne
  rw [(ρ.valid l).2]
  apply busy_phase_persistent hl (by decide) (ρ.valid l).1 hne
  intro heq
  have hm := (ρ.valid l).1
  rw [heq] at hm
  change (ρ.state l).phase i = .makeRequest at hm
  exact Phase.noConfusion (hl.symm.trans hm)

theorem makeRequest_eventually (ρ : Run n) (hf : WeakFairness ρ) {k i}
    (hp : (ρ.state k).phase i = .makeRequest) : ∃ l, k ≤ l ∧ ρ.event l = .makeRequest i := by
  apply fair_persistent_action ρ hf (.makeRequest i) trivial k hp
  intro l _ hl hne
  rw [(ρ.valid l).2]
  refine busy_phase_persistent hl (by decide) (ρ.valid l).1 ?_ hne
  intro heq
  have hm := (ρ.valid l).1
  rw [heq] at hm
  change (ρ.state l).phase i = .assign at hm
  exact Phase.noConfusion (hl.symm.trans hm)

theorem handler_eventually_completes (ρ : Run n) (hf : WeakFairness ρ) (k : ℕ) (i : NodeId n) :
    ∃ l, k ≤ l ∧ (ρ.state l).phase i = .ready := by
  cases hp : (ρ.state k).phase i with
  | ready => exact ⟨k, le_refl _, hp⟩
  | makeRequest =>
    obtain ⟨l, hkl, he⟩ := makeRequest_eventually ρ hf hp
    refine ⟨l + 1, by omega, ?_⟩
    rw [(ρ.valid l).2, he]
    simp [next, phase_makeRequest]
  | assign =>
    obtain ⟨l, hkl, he⟩ := assign_eventually ρ hf hp
    have hm : (ρ.state (l + 1)).phase i = .makeRequest := by
      rw [(ρ.valid l).2, he]; simp [next, phase_assign]
    obtain ⟨m, hlm, he'⟩ := makeRequest_eventually ρ hf hm
    refine ⟨m + 1, by omega, ?_⟩
    rw [(ρ.valid m).2, he']
    simp [next, phase_makeRequest]

open scoped BigOperators

def pending (s : State n) : Finset (Request n) := s.sent \ s.received

def pendingLoad (s : State n) (i : NodeId n) : ℤ :=
  ∑ r ∈ pending s, if r.sender = i then 1 else 0

def queueLoad (q : NodeId n → List (NodeId n)) (i : NodeId n) : ℤ :=
  ∑ j : NodeId n, if j = i then 0 else ((q j).count i : ℤ)

def flightLoad (f : Option (NodeId n × NodeId n)) (i : NodeId n) : ℤ :=
  if f.map Prod.snd = some i then 1 else 0

def credit (s : State n) (i : NodeId n) : ℤ :=
  if i ∈ s.owners then 0 else if s.asked i = true then 1 else 0

/-- One outstanding ASKED credit is represented either by a request packet,
a neighbouring FIFO entry, or a returning PRIVILEGE packet. Local self entries
are accounted separately by SelfQueued. -/
def RequestBalance (s : State n) : Prop := ∀ i,
  pendingLoad s i + queueLoad s.queue i + flightLoad s.flight i = credit s i

theorem pendingLoad_nonneg (s : State n) (i : NodeId n) : 0 ≤ pendingLoad s i := by
  apply Finset.sum_nonneg
  intro r _; split <;> norm_num

theorem queueLoad_nonneg (q : NodeId n → List (NodeId n)) (i : NodeId n) :
    0 ≤ queueLoad q i := by
  apply Finset.sum_nonneg
  intro j _; split
  · exact le_refl _
  · exact Int.natCast_nonneg _

theorem flightLoad_nonneg (f : Option (NodeId n × NodeId n)) (i : NodeId n) :
    0 ≤ flightLoad f i := by
  unfold flightLoad
  split <;> norm_num

theorem queueLoad_update (q : NodeId n → List (NodeId n)) (i a : NodeId n)
    (xs : List (NodeId n)) :
    queueLoad (Function.update q a xs) i = queueLoad q i +
      if a = i then 0 else (xs.count i : ℤ) - ((q a).count i : ℤ) := by
  let f : NodeId n → ℤ := fun j => if j = i then 0 else ((q j).count i : ℤ)
  let g : NodeId n → ℤ := fun j =>
    if j = i then 0 else (((Function.update q a xs) j).count i : ℤ)
  have hsum : ∑ j ∈ Finset.univ.erase a, g j = ∑ j ∈ Finset.univ.erase a, f j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [f, g, (Finset.mem_erase.mp hj).1]
  have h1 := Finset.sum_erase_add Finset.univ f (Finset.mem_univ a)
  have h2 := Finset.sum_erase_add Finset.univ g (Finset.mem_univ a)
  rw [hsum] at h2
  change (∑ j, g j) = (∑ j, f j) + _
  by_cases ha : a = i
  · simp only [f, g, ha, if_true, Function.update_self] at h1 h2 ⊢
    omega
  · simp only [f, g, ha, if_false, Function.update_self] at h1 h2 ⊢
    omega

theorem queueLoad_append (q : NodeId n → List (NodeId n)) (i a b : NodeId n) :
    queueLoad (Function.update q a (q a ++ [b])) i = queueLoad q i +
      if a ≠ i ∧ b = i then 1 else 0 := by
  rw [queueLoad_update]
  by_cases ha : a = i <;> by_cases hb : b = i <;>
    simp [ha, hb, List.count_append]

theorem queueLoad_pop {q : NodeId n → List (NodeId n)} {a b : NodeId n} {tail}
    (hq : q a = b :: tail) (i : NodeId n) :
    queueLoad (Function.update q a tail) i = queueLoad q i -
      if a ≠ i ∧ b = i then 1 else 0 := by
  rw [queueLoad_update]
  by_cases ha : a = i <;> by_cases hb : b = i <;>
    simp [hq, ha, hb]
  omega

theorem pendingLoad_receive {s : State n} {r : Request n}
    (hr : r ∈ s.sent) (hn : r ∉ s.received) (i : NodeId n) :
    pendingLoad (next s (.receive r)) i = pendingLoad s i - if r.sender = i then 1 else 0 := by
  have hp : r ∈ pending s := Finset.mem_sdiff.mpr ⟨hr, hn⟩
  have he := Finset.sum_erase_add (pending s)
    (fun q => (if q.sender = i then 1 else 0 : ℤ)) hp
  unfold pendingLoad
  have hp' : pending (next s (.receive r)) = (pending s).erase r := by
    simp only [pending, next, Finset.sdiff_insert]
  rw [hp']
  omega

theorem pendingLoad_makeRequest {s : State n} (hs : MessageHistory s) {a : NodeId n}
    (ha : s.holder a ≠ a ∧ s.queue a ≠ [] ∧ s.asked a = false) (i : NodeId n) :
    pendingLoad (makeRequest s a) i = pendingLoad s i + if a = i then 1 else 0 := by
  let r : Request n := ⟨a, s.holder a, s.serial a⟩
  have hn : r ∉ s.sent := next_request_fresh hs a
  have hr : r ∉ s.received := fun h => hn (hs.received_sent h)
  have hp : r ∉ pending s := fun h => hn (Finset.mem_sdiff.mp h).1
  have hp' : pending (makeRequest s a) = insert r (pending s) := by
    simp [pending, makeRequest, ha, Finset.insert_sdiff_of_notMem _ hr, r]
  unfold pendingLoad
  rw [hp', Finset.sum_insert hp]
  simp only [r]
  omega

theorem requestBalance_initial (owner : NodeId n) (route) :
    RequestBalance (initial owner route) := by
  intro i
  simp [pendingLoad, pending, queueLoad, flightLoad, credit, initial]

theorem requestBalance_assign {s : State n} (hs : Safety s) (hb : RequestBalance s)
    (a : NodeId n) : RequestBalance (assignPrivilege s a) := by
  unfold assignPrivilege
  split
  · rename_i ha
    split
    · exact hb
    · rename_i j tail hq
      obtain ⟨ho, hf⟩ := owner_singleton hs.conserved ha.1
      split
      · rename_i hja
        subst j
        intro i
        have hi := hb i
        change pendingLoad s i + queueLoad (Function.update s.queue a tail) i +
          flightLoad s.flight i = if i ∈ s.owners then 0 else
            if Function.update s.asked a false i = true then 1 else 0
        rw [queueLoad_pop hq]
        by_cases hia : i = a
        · subst i; simpa [credit, ha.1] using hi
        · simpa [credit, hia, Ne.symm hia] using hi
      · rename_i hja
        intro i
        have hi := hb i
        change pendingLoad s i + queueLoad (Function.update s.queue a tail) i +
          flightLoad (some (a, j)) i = if i ∈ s.owners.erase a then 0 else
            if Function.update s.asked a false i = true then 1 else 0
        rw [queueLoad_pop hq]
        by_cases hia : i = a
        · subst i
          simpa [credit, ho, hf, flightLoad, hja] using hi
        · by_cases hij : j = i
          · subst j
            simp [credit, ho, hf, flightLoad, hia, Ne.symm hia] at hi ⊢
            omega
          · simpa [credit, ho, hf, flightLoad, hia, Ne.symm hia, hij] using hi
  · exact hb

theorem requestBalance_makeRequest {G : SimpleGraph (NodeId n)} {s : State n}
    (ht : Topology G s) (hh : MessageHistory s) (hb : RequestBalance s) (a : NodeId n) :
    RequestBalance (makeRequest s a) := by
  by_cases ha : s.holder a ≠ a ∧ s.queue a ≠ [] ∧ s.asked a = false
  · have ho : a ∉ s.owners := fun h => ha.1 (ht.owner_self a h)
    intro i
    have hi := hb i
    have hp := pendingLoad_makeRequest hh ha i
    have hq : (makeRequest s a).queue = s.queue := by simp [makeRequest, ha]
    have hf : (makeRequest s a).flight = s.flight := by simp [makeRequest, ha]
    change pendingLoad (makeRequest s a) i + queueLoad (makeRequest s a).queue i +
      flightLoad (makeRequest s a).flight i = _
    rw [hp, hq, hf]
    by_cases hia : i = a
    · subst i
      simp [credit, ho, ha.2.2] at hi
      simp [credit, makeRequest, ha, ho]
      omega
    · simpa [credit, makeRequest, ha, hia, Ne.symm hia] using hi
  · unfold makeRequest
    rw [if_neg ha]
    exact hb

theorem requestBalance_step {G : SimpleGraph (NodeId n)} {s : State n}
    (hs : Safety s) (hl : EdgeLocality G s) (ht : Topology G s)
    (hh : MessageHistory s) (hb : RequestBalance s) {e} (he : Enabled s e) :
    RequestBalance (next s e) := by
  cases e with
  | request a =>
    intro i
    change pendingLoad s i + queueLoad (Function.update s.queue a (s.queue a ++ [a])) i +
      flightLoad s.flight i = credit s i
    rw [queueLoad_append]
    have hn : ¬ (a ≠ i ∧ a = i) := fun h => h.1 h.2
    simpa [hn] using hb i
  | receive r =>
    have hn : r.sender ≠ r.dest := (hl.sent r he.2.1).ne
    intro i
    change pendingLoad (next s (.receive r)) i +
      queueLoad (Function.update s.queue r.dest (s.queue r.dest ++ [r.sender])) i +
      flightLoad s.flight i = credit s i
    rw [pendingLoad_receive he.2.1 he.2.2, queueLoad_append]
    have hi := hb i
    by_cases hri : r.sender = i
    · subst i; simp [Ne.symm hn]; omega
    · simpa [hri] using hi
  | deliver a b =>
    have ho := flight_empty_owners hs.conserved he.2
    intro i
    have hi := hb i
    change pendingLoad s i + queueLoad s.queue i + flightLoad none i =
      if i ∈ insert b s.owners then 0 else if s.asked i = true then 1 else 0
    by_cases hib : i = b
    · subst i
      have hp := pendingLoad_nonneg s b
      have hq := queueLoad_nonneg s.queue b
      simp [credit, ho, he.2, flightLoad] at hi
      simp [ho, flightLoad]
      split_ifs at hi <;> omega
    · simpa [credit, ho, he.2, flightLoad, hib, Ne.symm hib] using hi
  | leave => exact hb
  | assign a => exact requestBalance_assign hs hb a
  | makeRequest a => exact requestBalance_makeRequest ht hh hb a
  | idle => exact hb

theorem reachable_requestBalance {G : SimpleGraph (NodeId n)} {owner : NodeId n} {route}
    (hr : Routes G route owner) (ho : route owner = owner)
    (he : ∀ i, route i = i ∨ G.Adj i (route i)) {s : State n}
    (hs : Reachable owner route s) : RequestBalance s := by
  induction hs with
  | refl => exact requestBalance_initial _ _
  | tail hst htu ih =>
    rcases htu with ⟨hen, rfl⟩
    exact requestBalance_step (reachable_safety hst) (reachable_edge_locality he hst)
      (reachable_topology hr ho he hst) (reachable_message_history hst) ih hen

theorem credit_le_one (s : State n) (i : NodeId n) : credit s i ≤ 1 := by
  unfold credit
  split
  · norm_num
  · split <;> norm_num

theorem balanced_queueLoad_le_one {s : State n} (hb : RequestBalance s) (i : NodeId n) :
    queueLoad s.queue i ≤ 1 := by
  have h := hb i
  have hp := pendingLoad_nonneg s i
  have hf := flightLoad_nonneg s.flight i
  have hc := credit_le_one s i
  omega

theorem queue_count_le_load {q : NodeId n → List (NodeId n)} {i j : NodeId n} (hne : j ≠ i) :
    ((q j).count i : ℤ) ≤ queueLoad q i := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun k : NodeId n => if k = i then (0 : ℤ) else ((q k).count i : ℤ))
    (fun k _ => by
      split
      · exact le_refl _
      · exact Int.natCast_nonneg _) (Finset.mem_univ j)
  simpa [queueLoad, hne] using h

theorem balanced_queue_nodup {s : State n} (hb : RequestBalance s) (hq : SelfQueued s)
    (j : NodeId n) : (s.queue j).Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro i
  by_cases hij : i = j
  · subst i
    rw [hq j]
    split <;> omega
  · have h1 := queue_count_le_load (q := s.queue) (Ne.symm hij)
    have h2 := balanced_queueLoad_le_one hb i
    omega

theorem queue_nodup_preservation {G : SimpleGraph (NodeId n)} {owner : NodeId n} {route}
    (hr : Routes G route owner) (ho : route owner = owner)
    (he : ∀ i, route i = i ∨ G.Adj i (route i)) {s : State n}
    (hs : Reachable owner route s) (j : NodeId n) : (s.queue j).Nodup :=
  balanced_queue_nodup (reachable_requestBalance hr ho he hs) (reachable_selfQueued he hs) j

theorem flight_recipient_asked {s : State n} (hs : Safety s) (hb : RequestBalance s)
    {a b : NodeId n} (hf : s.flight = some (a, b)) : s.asked b = true := by
  have ho := flight_empty_owners hs.conserved hf
  have h := hb b
  have hp := pendingLoad_nonneg s b
  have hq := queueLoad_nonneg s.queue b
  simp [credit, ho, hf, flightLoad] at h
  split_ifs at h with ha
  · exact ha
  · omega

/-- A received neighbour request has an outstanding ASKED credit at its origin;
no fabricated queue entry or duplicate outstanding request is assumed away. -/
theorem queued_neighbour_asked {s : State n} (hb : RequestBalance s) {i j : NodeId n}
    (hne : j ≠ i) (hm : i ∈ s.queue j) : s.asked i = true ∧ i ∉ s.owners := by
  have hc : 0 < (s.queue j).count i := List.count_pos_iff.mpr hm
  have hl := queue_count_le_load (q := s.queue) hne
  have hp := pendingLoad_nonneg s i
  have hf := flightLoad_nonneg s.flight i
  have h := hb i
  unfold credit at h
  split_ifs at h with ho ha
  · omega
  · exact ⟨ha, ho⟩
  · omega

theorem pending_count_positive {s : State n} {r : Request n} (hr : r ∈ pending s) :
    1 ≤ pendingLoad s r.sender := by
  have h := Finset.single_le_sum (s := pending s)
    (f := fun q => (if q.sender = r.sender then 1 else 0 : ℤ))
    (fun q _ => by split <;> norm_num) hr
  simpa [pendingLoad] using h

theorem pending_origin_not_owner {s : State n} (hb : RequestBalance s)
    {r : Request n} (hr : r ∈ pending s) : r.sender ∉ s.owners := by
  intro ho
  have h := hb r.sender
  have hp := pending_count_positive hr
  have hq := queueLoad_nonneg s.queue r.sender
  have hf := flightLoad_nonneg s.flight r.sender
  simp [credit, ho] at h
  omega

theorem pending_origin_not_flight {s : State n} (hb : RequestBalance s)
    {r : Request n} (hr : r ∈ pending s) {a b : NodeId n}
    (hf : s.flight = some (a, b)) : r.sender ≠ b := by
  intro he
  subst b
  have h := hb r.sender
  have hp := pending_count_positive hr
  have hq := queueLoad_nonneg s.queue r.sender
  have hc := credit_le_one s r.sender
  simp [flightLoad, hf] at h
  omega

theorem queued_origin_not_flight {s : State n} (hb : RequestBalance s)
    {i j : NodeId n} (hne : j ≠ i) (hm : i ∈ s.queue j) {a b : NodeId n}
    (hf : s.flight = some (a, b)) : i ≠ b := by
  intro he
  subst b
  have h := hb i
  have hp := pendingLoad_nonneg s i
  have hl := queue_count_le_load (q := s.queue) hne
  have hc : 0 < (s.queue j).count i := List.count_pos_iff.mpr hm
  have hh := credit_le_one s i
  simp [flightLoad, hf] at h
  omega

structure CreditRouting (s : State n) : Prop where
  pending_holder : ∀ r ∈ pending s, s.holder r.sender = r.dest
  queue_holder : ∀ i j, i ≠ j → i ∈ s.queue j → s.holder i = j

theorem creditRouting_initial (owner : NodeId n) (route) :
    CreditRouting (initial owner route) := by
  constructor <;> simp [pending, initial]

theorem creditRouting_assign {s : State n} (hb : RequestBalance s)
    (hr : CreditRouting s) (a : NodeId n) : CreditRouting (assignPrivilege s a) := by
  unfold assignPrivilege
  split
  · rename_i ha
    split
    · exact ⟨hr.pending_holder, hr.queue_holder⟩
    · rename_i j tail hq
      have hp : ∀ r ∈ pending s, Function.update s.holder a j r.sender = r.dest := by
        intro r hm
        have hn : r.sender ≠ a := fun he => pending_origin_not_owner hb hm (he ▸ ha.1)
        simpa [hn] using hr.pending_holder r hm
      have hqq : ∀ i k, i ≠ k → i ∈ Function.update s.queue a tail k →
          Function.update s.holder a j i = k := by
        intro i k hik hm
        have hmem : i ∈ s.queue k := by
          by_cases hk : k = a
          · subst k
            have ht : i ∈ tail := by simpa using hm
            simp [hq, ht]
          · simpa [hk] using hm
        have hn : i ≠ a := fun he => (queued_neighbour_asked hb (Ne.symm hik) hmem).2 (he ▸ ha.1)
        simpa [hn] using hr.queue_holder i k hik hmem
      split <;> exact ⟨hp, hqq⟩
  · exact ⟨hr.pending_holder, hr.queue_holder⟩

theorem creditRouting_makeRequest {s : State n} (hr : CreditRouting s)
    (a : NodeId n) : CreditRouting (makeRequest s a) := by
  unfold makeRequest
  split
  · refine ⟨?_, hr.queue_holder⟩
    intro r hm
    have hmem : r ∈ insert ⟨a, s.holder a, s.serial a⟩ s.sent ∧ r ∉ s.received :=
      Finset.mem_sdiff.mp hm
    rcases Finset.mem_insert.mp hmem.1 with rfl | ho
    · rfl
    · exact hr.pending_holder r (Finset.mem_sdiff.mpr ⟨ho, hmem.2⟩)
  · exact ⟨hr.pending_holder, hr.queue_holder⟩

theorem creditRouting_step {s : State n} (hb : RequestBalance s) (hr : CreditRouting s)
    {e} (he : Enabled s e) : CreditRouting (next s e) := by
  cases e with
  | request a =>
    refine ⟨hr.pending_holder, ?_⟩
    intro i j hij hm
    by_cases hj : j = a
    · subst j
      have hx : i ∈ s.queue a ∨ i = a := by simpa [next] using hm
      exact hx.elim (hr.queue_holder i a hij) (fun hi => False.elim (hij hi))
    · exact hr.queue_holder i j hij (by simpa [next, hj] using hm)
  | receive r =>
    refine ⟨?_, ?_⟩
    · intro q hq
      have hmem := Finset.mem_sdiff.mp hq
      apply hr.pending_holder q
      exact Finset.mem_sdiff.mpr ⟨hmem.1, fun h => hmem.2 (Finset.mem_insert_of_mem h)⟩
    · intro i j hij hm
      by_cases hj : j = r.dest
      · subst j
        have hx : i ∈ s.queue r.dest ∨ i = r.sender := by simpa [next] using hm
        rcases hx with hx | rfl
        · exact hr.queue_holder i r.dest hij hx
        · exact hr.pending_holder r (Finset.mem_sdiff.mpr ⟨he.2.1, he.2.2⟩)
      · exact hr.queue_holder i j hij (by simpa [next, hj] using hm)
  | deliver a b =>
    constructor
    · intro r hm
      have hn := pending_origin_not_flight hb hm he.2
      simpa [next, hn] using hr.pending_holder r hm
    · intro i j hij hm
      have hn := queued_origin_not_flight hb (Ne.symm hij) hm he.2
      simpa [next, hn] using hr.queue_holder i j hij hm
  | assign a => exact creditRouting_assign hb hr a
  | makeRequest a => exact creditRouting_makeRequest hr a
  | leave => exact ⟨hr.pending_holder, hr.queue_holder⟩
  | idle => exact hr

theorem reachable_creditRouting {G : SimpleGraph (NodeId n)} {owner : NodeId n} {route}
    (hr : Routes G route owner) (ho : route owner = owner)
    (he : ∀ i, route i = i ∨ G.Adj i (route i)) {s : State n}
    (hs : Reachable owner route s) : CreditRouting s := by
  induction hs with
  | refl => exact creditRouting_initial _ _
  | tail hst htu ih =>
    rcases htu with ⟨hen, rfl⟩
    exact creditRouting_step (reachable_requestBalance hr ho he hst) ih hen

theorem routes_adj_holder {G : SimpleGraph (NodeId n)} (hG : G.IsTree)
    {f : NodeId n → NodeId n} {root j : NodeId n} (hr : Routes G f root)
    (hj : G.Adj j root) : f j = root := by
  obtain ⟨p, hp, hf⟩ := hr j
  have hq : (SimpleGraph.Walk.cons hj .nil).IsPath := by simp [hj.ne]
  have he : p = .cons hj .nil := Subtype.mk.inj
    (hG.isAcyclic.subsingleton_path j root |>.elim ⟨p, hp⟩ ⟨_, hq⟩)
  rw [he] at hf
  exact hf.1

def Backpointer (s : State n) : Prop := ∀ a b,
  s.flight = some (a, b) → s.holder b = a

theorem backpointer_assign {G : SimpleGraph (NodeId n)} (hG : G.IsTree) {s : State n}
    (hs : Safety s) (hl : EdgeLocality G s) (ht : Topology G s) (hb : Backpointer s)
    (a : NodeId n) : Backpointer (assignPrivilege s a) := by
  unfold assignPrivilege
  split
  · rename_i ha
    split
    · exact hb
    · rename_i j tail hq
      obtain ⟨_, hf⟩ := owner_singleton hs.conserved ha.1
      obtain ⟨root, hroot, hr⟩ := ht.routes
      have he : root = a := location_unique hs.conserved hroot (Or.inl ha.1)
      subst root
      split
      · intro i k hik; simp [hf] at hik
      · rename_i hja
        have hj := (hl.queue a j (by simp [hq])).resolve_left hja
        have hp := routes_adj_holder hG hr hj.symm
        intro i k hik
        have heq : a = i ∧ j = k := by simpa using hik
        obtain ⟨rfl, rfl⟩ := heq
        simpa [hja] using hp
  · exact hb

theorem backpointer_step {G : SimpleGraph (NodeId n)} (hG : G.IsTree) {s : State n}
    (hs : Safety s) (hl : EdgeLocality G s) (ht : Topology G s) (hb : Backpointer s)
    (e : Event n) : Backpointer (next s e) := by
  cases e with
  | assign a => exact backpointer_assign hG hs hl ht hb a
  | makeRequest a =>
    change Backpointer (makeRequest s a)
    unfold makeRequest
    split <;> exact hb
  | deliver => intro i j hij; simp [next] at hij
  | request => exact hb
  | receive => exact hb
  | leave => exact hb
  | idle => exact hb

theorem reachable_backpointer {G : SimpleGraph (NodeId n)} (hG : G.IsTree)
    {owner : NodeId n} {route} (hr : Routes G route owner) (ho : route owner = owner)
    (he : ∀ i, route i = i ∨ G.Adj i (route i)) {s : State n}
    (hs : Reachable owner route s) : Backpointer s := by
  induction hs with
  | refl => intro i j hij; simp [initial] at hij
  | tail hst htu ih =>
    rcases htu with ⟨_, rfl⟩
    exact backpointer_step hG (reachable_safety hst) (reachable_edge_locality he hst)
      (reachable_topology hr ho he hst) ih _

theorem routes_self_only_root {G : SimpleGraph (NodeId n)} {f : NodeId n → NodeId n}
    {root i : NodeId n} (hr : Routes G f root) (hi : f i = i) : i = root := by
  obtain ⟨p, _, hf⟩ := hr i
  cases p with
  | nil => rfl
  | cons h p => exact False.elim (h.ne (hi.symm.trans hf.1))

theorem holder_self_iff_owner {G : SimpleGraph (NodeId n)} {s : State n}
    (hl : EdgeLocality G s) (ht : Topology G s) (hb : Backpointer s) (i : NodeId n) :
    s.holder i = i ↔ i ∈ s.owners := by
  refine ⟨?_, ht.owner_self i⟩
  intro hi
  obtain ⟨root, hroot, hr⟩ := ht.routes
  have he : i = root := routes_self_only_root hr hi
  subst root
  rcases hroot with ho | ⟨a, hf⟩
  · exact ho
  · have hp := hb a i hf
    have hn := (hl.flight a i hf).ne
    exact False.elim (hn (hp.symm.trans hi))

def ReadyAsks (s : State n) : Prop := ∀ i,
  s.phase i = .ready → s.queue i ≠ [] → s.holder i ≠ i → s.asked i = true

theorem readyAsks_initial (owner : NodeId n) (route) : ReadyAsks (initial owner route) := by
  intro i _ hq
  exact False.elim (hq rfl)

theorem readyAsks_assign {s : State n} (hr : ReadyAsks s) (a : NodeId n) :
    ReadyAsks (assignPrivilege s a) := by
  unfold assignPrivilege
  split
  · split
    · intro i hp hq hh
      by_cases hi : i = a
      · subst i; simp at hp
      · exact hr i (by simpa [hi] using hp) hq hh
    · split
      all_goals
        intro i hp hq hh
        by_cases hi : i = a
        · subst i; simp at hp
        · have h := hr i (by simpa [hi] using hp)
            (by simpa [hi] using hq) (by simpa [hi] using hh)
          simpa [hi] using h
  · intro i hp hq hh
    by_cases hi : i = a
    · subst i; simp at hp
    · exact hr i (by simpa [hi] using hp) hq hh

theorem readyAsks_makeRequest {s : State n} (hr : ReadyAsks s) (a : NodeId n) :
    ReadyAsks (makeRequest s a) := by
  unfold makeRequest
  split
  · intro i hp hq hh
    by_cases hi : i = a
    · subst i; simp
    · simpa [hi] using hr i (by simpa [hi] using hp) hq hh
  · rename_i ha
    intro i hp hq hh
    by_cases hi : i = a
    · subst i
      cases hb : s.asked a
      · exact False.elim (ha ⟨hh, hq, hb⟩)
      · rfl
    · exact hr i (by simpa [hi] using hp) hq hh

theorem readyAsks_step {s : State n} (hr : ReadyAsks s) (e : Event n) :
    ReadyAsks (next s e) := by
  cases e with
  | assign a => exact readyAsks_assign hr a
  | makeRequest a => exact readyAsks_makeRequest hr a
  | idle => exact hr
  | request a | leave a =>
    intro i hp hq hh
    have hi : i ≠ a := by intro he; subst i; simp [next] at hp
    exact hr i (by simpa [next, hi] using hp) (by simpa [next, hi] using hq) hh
  | receive r =>
    intro i hp hq hh
    have hi : i ≠ r.dest := by intro he; subst i; simp [next] at hp
    exact hr i (by simpa [next, hi] using hp) (by simpa [next, hi] using hq) hh
  | deliver a b =>
    intro i hp hq hh
    have hi : i ≠ b := by intro he; subst i; simp [next] at hp
    exact hr i (by simpa [next, hi] using hp) hq (by simpa [next, hi] using hh)

theorem reachable_readyAsks {owner : NodeId n} {route} {s : State n}
    (hs : Reachable owner route s) : ReadyAsks s := by
  induction hs with
  | refl => exact readyAsks_initial _ _
  | tail _ he ih => rcases he with ⟨_, rfl⟩; exact readyAsks_step ih _

/-- A genuine FIFO removal, as opposed to a no-op ASSIGN_PRIVILEGE phase. -/
def Dequeue (s : State n) (e : Event n) (i : NodeId n) : Prop :=
  e = .assign i ∧ i ∈ s.owners ∧ s.mode i ≠ .inCS ∧ s.queue i ≠ []

def Removed (s : State n) (e : Event n) (i x : NodeId n) : Prop :=
  Dequeue s e i ∧ (s.queue i).head? = some x

theorem queue_change (s : State n) (e : Event n) (i : NodeId n) :
    (Dequeue s e i ∧ (next s e).queue i = (s.queue i).tail) ∨
    (¬ Dequeue s e i ∧ ∃ xs, (next s e).queue i = s.queue i ++ xs) := by
  cases e with
  | request a =>
    right
    refine ⟨by simp [Dequeue], ?_⟩
    by_cases hi : i = a
    · subst i; exact ⟨[a], by simp [next]⟩
    · exact ⟨[], by simp [next, hi]⟩
  | receive r =>
    right
    refine ⟨by simp [Dequeue], ?_⟩
    by_cases hi : i = r.dest
    · subst i; exact ⟨[r.sender], by simp [next]⟩
    · exact ⟨[], by simp [next, hi]⟩
  | deliver => exact Or.inr ⟨by simp [Dequeue], [], by simp [next]⟩
  | leave => exact Or.inr ⟨by simp [Dequeue], [], by simp [next]⟩
  | idle => exact Or.inr ⟨by simp [Dequeue], [], by simp [next]⟩
  | makeRequest a =>
    right
    refine ⟨by simp [Dequeue], [], ?_⟩
    dsimp only [next]
    unfold makeRequest
    split <;> simp
  | assign a =>
    by_cases hi : i = a
    · subst i
      by_cases ha : a ∈ s.owners ∧ s.mode a ≠ .inCS
      · cases hq : s.queue a with
        | nil => exact Or.inr ⟨by simp [Dequeue, hq], [], by simp [next, assignPrivilege, ha, hq]⟩
        | cons j tail =>
          left
          refine ⟨⟨rfl, ha.1, ha.2, by simp [hq]⟩, ?_⟩
          simp only [next, assignPrivilege, if_pos ha, hq]
          split <;> simp
      · exact Or.inr ⟨fun h => ha ⟨h.2.1, h.2.2.1⟩,
          [], by simp [next, assignPrivilege, ha]⟩
    · right
      refine ⟨by simp [Dequeue, Ne.symm hi], [], ?_⟩
      dsimp only [next]
      unfold assignPrivilege
      split
      · split
        · simp
        · split <;> simp [hi]
      · simp

theorem queue_without_removal {s : State n} {e : Event n} {i x : NodeId n}
    (hm : x ∈ s.queue i) (hn : ¬ Removed s e i x) :
    x ∈ (next s e).queue i ∧ ((next s e).queue i).idxOf x ≤ (s.queue i).idxOf x := by
  rcases queue_change s e i with ⟨hp, hq⟩ | ⟨_, xs, hq⟩
  · cases hs : s.queue i with
    | nil => simp [hs] at hm
    | cons y tail =>
      have hy : y ≠ x := by intro he; subst y; exact hn ⟨hp, by simp [hs]⟩
      have ht : x ∈ tail := by simpa [hs, Ne.symm hy] using hm
      rw [hq]
      simp only [hs, List.tail_cons]
      exact ⟨ht, by simp [List.idxOf_cons_ne tail hy]⟩
  · rw [hq]
    exact ⟨List.mem_append_left xs hm, by rw [List.idxOf_append_of_mem hm]⟩

theorem dequeue_strict_index {s : State n} {e : Event n} {i x : NodeId n}
    (hm : x ∈ s.queue i) (hn : ¬ Removed s e i x) (hp : Dequeue s e i) :
    ((next s e).queue i).idxOf x < (s.queue i).idxOf x := by
  rcases queue_change s e i with ⟨_, hq⟩ | ⟨hno, _⟩
  · cases hs : s.queue i with
    | nil => simp [hs] at hm
    | cons y tail =>
      have hy : y ≠ x := by intro he; subst y; exact hn ⟨hp, by simp [hs]⟩
      rw [hq]
      simp [hs, List.idxOf_cons_ne tail hy]
  · exact False.elim (hno hp)

def Recurrent (ρ : Run n) (i : NodeId n) : Prop :=
  ∀ k, ∃ l, k ≤ l ∧ Dequeue (ρ.state l) (ρ.event l) i

theorem queue_persists_without_removal (ρ : Run n) {k i x}
    (hm : x ∈ (ρ.state k).queue i)
    (hn : ∀ l, k ≤ l → ¬ Removed (ρ.state l) (ρ.event l) i x) :
    ∀ l, k ≤ l → x ∈ (ρ.state l).queue i ∧
      ((ρ.state l).queue i).idxOf x ≤ ((ρ.state k).queue i).idxOf x := by
  intro l hkl
  induction l, hkl using Nat.le_induction with
  | base => exact ⟨hm, le_refl _⟩
  | succ l hkl ih =>
    rw [(ρ.valid l).2]
    have h := queue_without_removal ih.1 (hn l hkl)
    exact ⟨h.1, h.2.trans ih.2⟩

/-- The finite position in a local FIFO prevents an entry from being skipped
by infinitely many genuine removals at that node. -/
theorem recurrent_serves_queued (ρ : Run n) {i} (hi : Recurrent ρ i) {k x}
    (hm : x ∈ (ρ.state k).queue i) :
    ∃ l, k ≤ l ∧ Removed (ρ.state l) (ρ.event l) i x := by
  by_contra hn
  push Not at hn
  have hw : ∀ m, ∀ k, x ∈ (ρ.state k).queue i →
      ((ρ.state k).queue i).idxOf x = m →
      (∀ l, k ≤ l → ¬ Removed (ρ.state l) (ρ.event l) i x) → False := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro k hk he hno
      obtain ⟨l, hkl, hp⟩ := hi k
      have hmem := queue_persists_without_removal ρ hk hno l hkl
      have hlt := dequeue_strict_index hmem.1 (hno l hkl) hp
      have hnext := (queue_without_removal hmem.1 (hno l hkl)).1
      rw [← (ρ.valid l).2] at hlt hnext
      apply ih (((ρ.state (l + 1)).queue i).idxOf x) (by omega) (l + 1) hnext rfl
      intro j hj
      exact hno j (by omega)
  exact hw _ k hm rfl hn

/-- A common time after the last removal at every non-recurrent node.
This is a finite-node argument, not an additional scheduling assumption. -/
theorem finite_quiet_cutoff (ρ : Run n) : ∃ K,
    ∀ i, ¬ Recurrent ρ i → ∀ l, K ≤ l → ¬ Dequeue (ρ.state l) (ρ.event l) i := by
  classical
  have h : ∀ i : NodeId n, ∃ k, ¬ Recurrent ρ i →
      ∀ l, k ≤ l → ¬ Dequeue (ρ.state l) (ρ.event l) i := by
    intro i
    by_cases hi : Recurrent ρ i
    · exact ⟨0, fun hn => False.elim (hn hi)⟩
    · simp only [Recurrent, not_forall, not_exists, not_and] at hi
      obtain ⟨k, hk⟩ := hi
      exact ⟨k, fun _ => hk⟩
  choose time ht using h
  refine ⟨Finset.univ.sup time, ?_⟩
  intro i hi l hl
  exact ht i hi l ((Finset.le_sup (f := time) (Finset.mem_univ i)).trans hl)

def IdleOwnerQuiet (s : State n) : Prop := ∀ i, i ∈ s.owners →
  s.mode i ≠ .inCS → s.phase i ≠ .assign → s.queue i = []

theorem quiet_initial (owner : NodeId n) (route) : IdleOwnerQuiet (initial owner route) := by
  intro i _ _ _; rfl

theorem quiet_assign {s : State n} (hq : IdleOwnerQuiet s) (a : NodeId n) :
    IdleOwnerQuiet (assignPrivilege s a) := by
  unfold assignPrivilege
  split
  · rename_i ha
    split
    · rename_i hnil
      intro i ho hm hp
      by_cases hi : i = a
      · subst i; simpa using hnil
      · exact hq i ho hm (by simpa [hi] using hp)
    · split
      · rename_i heq
        intro i ho hm hp
        by_cases hi : i = a
        · subst i; simp at hm
        · simpa [hi] using hq i ho (by simpa [hi] using hm) (by simpa [hi] using hp)
      · intro i ho hm hp
        have hi : i ≠ a := (Finset.mem_erase.mp ho).1
        simpa [hi] using hq i (Finset.mem_erase.mp ho).2 hm (by simpa [hi] using hp)
  · rename_i ha
    intro i ho hm hp
    by_cases hi : i = a
    · subst i; exact False.elim (ha ⟨ho, hm⟩)
    · exact hq i ho hm (by simpa [hi] using hp)

theorem quiet_makeRequest {s : State n} (hq : IdleOwnerQuiet s) {a : NodeId n}
    (hp : s.phase a = .makeRequest) : IdleOwnerQuiet (makeRequest s a) := by
  unfold makeRequest
  split
  all_goals
    intro i ho hm hphase
    apply hq i ho hm
    by_cases hi : i = a
    · subst i; simp [hp]
    · simpa [hi] using hphase

theorem quiet_step {s : State n} (hq : IdleOwnerQuiet s) {e} (he : Enabled s e) :
    IdleOwnerQuiet (next s e) := by
  cases e with
  | assign a => exact quiet_assign hq a
  | makeRequest a => exact quiet_makeRequest hq he
  | idle => exact hq
  | request a | leave a =>
    intro i ho hm hp
    have hi : i ≠ a := by intro hi; subst i; simp [next] at hp
    simpa [next, hi] using hq i ho (by simpa [next, hi] using hm) (by simpa [next, hi] using hp)
  | receive r =>
    intro i ho hm hp
    have hi : i ≠ r.dest := by intro hi; subst i; simp [next] at hp
    simpa [next, hi] using hq i ho hm (by simpa [next, hi] using hp)
  | deliver a b =>
    intro i ho hm hp
    have hi : i ≠ b := by intro hi; subst i; simp [next] at hp
    exact hq i (by simpa [next, hi] using ho) hm (by simpa [next, hi] using hp)

theorem reachable_quiet {owner : NodeId n} {route} {s : State n}
    (hs : Reachable owner route s) : IdleOwnerQuiet s := by
  induction hs with
  | refl => exact quiet_initial _ _
  | tail _ he ih => rcases he with ⟨he, rfl⟩; exact quiet_step ih he

theorem owner_persists_without_dequeue {s : State n} {e} {i : NodeId n}
    (ho : i ∈ s.owners) (hn : ¬ Dequeue s e i) : i ∈ (next s e).owners := by
  cases e with
  | request | receive | leave | idle => exact ho
  | deliver a b => exact Finset.mem_insert_of_mem ho
  | makeRequest a =>
    dsimp only [next]; unfold makeRequest; split <;> exact ho
  | assign a =>
    dsimp only [next]; unfold assignPrivilege
    split
    · rename_i ha
      split
      · exact ho
      · rename_i j tail hq
        split
        · exact ho
        · have hi : i ≠ a := by
            intro hi; subst i
            exact hn ⟨rfl, ha.1, ha.2, by simp [hq]⟩
          exact Finset.mem_erase.mpr ⟨hi, ho⟩
    · exact ho

theorem nonCS_persists_without_dequeue {s : State n} {e} {i : NodeId n}
    (hm : s.mode i ≠ .inCS) (hn : ¬ Dequeue s e i) : (next s e).mode i ≠ .inCS := by
  cases e with
  | request a | leave a =>
    by_cases hi : i = a
    · subst i; simp [next]
    · simpa [next, hi] using hm
  | receive | deliver | idle => exact hm
  | makeRequest a =>
    dsimp only [next]; unfold makeRequest; split <;> exact hm
  | assign a =>
    dsimp only [next]; unfold assignPrivilege
    split
    · rename_i ha
      split
      · exact hm
      · rename_i j tail hq
        split
        · have hi : i ≠ a := by
            intro hi; subst i
            exact hn ⟨rfl, ha.1, ha.2, by simp [hq]⟩
          simpa [hi] using hm
        · exact hm
    · exact hm

def QuietAfter (ρ : Run n) (K : ℕ) (i : NodeId n) : Prop :=
  ∀ l, K ≤ l → ¬ Dequeue (ρ.state l) (ρ.event l) i

theorem queue_growth_quiet (ρ : Run n) {K i} (hq : QuietAfter ρ K i) {k l}
    (hk : K ≤ k) (hkl : k ≤ l) :
    ∃ xs, (ρ.state l).queue i = (ρ.state k).queue i ++ xs := by
  induction l, hkl using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ l hkl ih =>
    obtain ⟨xs, hxs⟩ := ih
    rcases queue_change (ρ.state l) (ρ.event l) i with ⟨h, _⟩ | ⟨_, ys, hy⟩
    · exact False.elim (hq l (hk.trans hkl) h)
    · refine ⟨xs ++ ys, ?_⟩
      rw [(ρ.valid l).2, hy, hxs, List.append_assoc]

theorem quiet_owner_persists (ρ : Run n) {K i} (hq : QuietAfter ρ K i) {k l}
    (hk : K ≤ k) (hkl : k ≤ l) (ho : i ∈ (ρ.state k).owners) : i ∈ (ρ.state l).owners := by
  induction l, hkl using Nat.le_induction with
  | base => exact ho
  | succ l hkl ih =>
    rw [(ρ.valid l).2]
    exact owner_persists_without_dequeue ih (hq l (hk.trans hkl))

theorem quiet_nonCS_persists (ρ : Run n) {K i} (hq : QuietAfter ρ K i) {k l}
    (hk : K ≤ k) (hkl : k ≤ l) (hm : (ρ.state k).mode i ≠ .inCS) :
    (ρ.state l).mode i ≠ .inCS := by
  induction l, hkl using Nat.le_induction with
  | base => exact hm
  | succ l hkl ih =>
    rw [(ρ.valid l).2]
    exact nonCS_persists_without_dequeue ih (hq l (hk.trans hkl))

theorem quiet_queue_nonempty (ρ : Run n) {K i} (hq : QuietAfter ρ K i) {k l}
    (hk : K ≤ k) (hkl : k ≤ l) (hne : (ρ.state k).queue i ≠ []) :
    (ρ.state l).queue i ≠ [] := by
  obtain ⟨xs, hx⟩ := queue_growth_quiet ρ hq hk hkl
  rw [hx]
  exact fun h => hne (List.append_eq_nil_iff.mp h).1

/-- Under the real scheduling contracts, a node cannot keep the privilege and
a nonempty queue forever without performing a FIFO removal. -/
theorem quiet_owner_queue_impossible (ρ : Run n) (hf : WeakFairness ρ) (hc : FiniteCS ρ)
    {K i} (hq : QuietAfter ρ K i) {k} (hk : K ≤ k)
    (ho : i ∈ (ρ.state k).owners) (hne : (ρ.state k).queue i ≠ []) : False := by
  obtain ⟨t, hkt, ht⟩ := handler_eventually_completes ρ hf k i
  have hot := quiet_owner_persists ρ hq hk hkt ho
  have hqt := quiet_queue_nonempty ρ hq hk hkt hne
  have hcs : (ρ.state t).mode i = .inCS := by
    by_contra hm
    exact hqt (reachable_quiet (ρ.reachable t) i hot hm (by simp [ht]))
  obtain ⟨u, htu, hu⟩ := hc t i hcs
  have hphase : (ρ.state (u + 1)).phase i = .assign := by rw [(ρ.valid u).2, hu]; simp [next]
  have hmode : (ρ.state (u + 1)).mode i ≠ .inCS := by rw [(ρ.valid u).2, hu]; simp [next]
  obtain ⟨v, huv, hv⟩ := assign_eventually ρ hf hphase
  have hov := quiet_owner_persists ρ hq hk (show k ≤ v by omega) ho
  have hqv := quiet_queue_nonempty ρ hq hk (show k ≤ v by omega) hne
  have hmv := quiet_nonCS_persists ρ hq (show K ≤ u + 1 by omega) huv hmode
  exact hq v (by omega) ⟨hv, hov, hmv, hqv⟩

/-- Even ownership before the queue becomes nonempty is impossible for a quiet
node: the absence of handoff preserves that ownership until work arrives. -/
theorem quiet_eventual_queue_never_owner (ρ : Run n) (hf : WeakFairness ρ) (hc : FiniteCS ρ)
    {K i} (hq : QuietAfter ρ K i)
    (hw : ∃ k, K ≤ k ∧ (ρ.state k).queue i ≠ []) :
    ∀ t, K ≤ t → i ∉ (ρ.state t).owners := by
  obtain ⟨k, hk, hne⟩ := hw
  intro t ht ho
  have ho' := quiet_owner_persists ρ hq ht (le_max_left t k) ho
  have hq' := quiet_queue_nonempty ρ hq hk (le_max_right t k) hne
  exact quiet_owner_queue_impossible ρ hf hc hq (by omega) ho' hq'

theorem removed_self_enters {s : State n} {e} {i : NodeId n}
    (h : Removed s e i i) : (next s e).mode i = .inCS := by
  rcases h with ⟨⟨rfl, ho, hm, _⟩, hh⟩
  cases hq : s.queue i with
  | nil => simp [hq] at hh
  | cons j tail =>
    have he : j = i := by simpa [hq] using hh
    subst j
    simp [next, assignPrivilege, ho, hm, hq]

theorem removed_neighbour_sends {s : State n} {e} {i j : NodeId n} (hne : j ≠ i)
    (h : Removed s e i j) : (next s e).flight = some (i, j) := by
  rcases h with ⟨⟨rfl, ho, hm, _⟩, hh⟩
  cases hq : s.queue i with
  | nil => simp [hq] at hh
  | cons k tail =>
    have he : k = j := by simpa [hq] using hh
    subst k
    simp [next, assignPrivilege, ho, hm, hq, hne]

theorem flight_eventually_owned (ρ : Run n) (hd : ReliableDelivery ρ) {k a b}
    (hf : (ρ.state k).flight = some (a, b)) : ∃ l, k ≤ l ∧ b ∈ (ρ.state l).owners := by
  obtain ⟨l, hkl, he⟩ := hd.2 k a b hf
  refine ⟨l + 1, by omega, ?_⟩
  rw [(ρ.valid l).2, he]; simp [next]

theorem no_owner_no_flight (ρ : Run n) (hd : ReliableDelivery ρ) {K i}
    (ho : ∀ l, K ≤ l → i ∉ (ρ.state l).owners) {t} (ht : K ≤ t) :
    ((ρ.state t).flight.map Prod.snd) ≠ some i := by
  intro h
  cases hf : (ρ.state t).flight with
  | none => simp [hf] at h
  | some p =>
    have he : p.2 = i := by simpa [hf] using h
    obtain ⟨l, htl, hl⟩ := flight_eventually_owned ρ hd hf
    exact ho l (ht.trans htl) (he ▸ hl)

theorem holder_stable_without_owner {s : State n} {e} {i : NodeId n}
    (ho : i ∉ s.owners) (ho' : i ∉ (next s e).owners) :
    (next s e).holder i = s.holder i := by
  cases e with
  | request | receive | leave | idle => rfl
  | deliver a b =>
    have hi : i ≠ b := by intro he; subst i; exact ho' (by simp [next])
    simp [next, hi]
  | makeRequest a =>
    dsimp only [next]; unfold makeRequest; split <;> rfl
  | assign a =>
    by_cases hi : i = a
    · subst i; simp [next, assignPrivilege, ho]
    · dsimp only [next]; unfold assignPrivilege
      split
      · split
        · rfl
        · split <;> simp [hi]
      · rfl

theorem never_owner_holder_stable (ρ : Run n) {K i}
    (ho : ∀ l, K ≤ l → i ∉ (ρ.state l).owners) {t} (ht : K ≤ t) :
    (ρ.state t).holder i = (ρ.state K).holder i := by
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t hKt ih =>
    rw [(ρ.valid t).2]
    exact (holder_stable_without_owner (ho t hKt)
      (by rw [← (ρ.valid t).2]; exact ho (t + 1) (by omega))).trans ih

theorem newly_received {s : State n} {e} {r : Request n}
    (hn : r ∉ s.received) (hy : r ∈ (next s e).received) : e = .receive r := by
  cases e with
  | receive q =>
    have he : r = q := (Finset.mem_insert.mp hy).resolve_right hn
    subst q; rfl
  | request | deliver | leave | idle => exact False.elim (hn hy)
  | makeRequest a =>
    dsimp only [next] at hy
    unfold makeRequest at hy
    split at hy <;> exact False.elim (hn hy)
  | assign a =>
    dsimp only [next] at hy
    unfold assignPrivilege at hy
    split at hy
    · split at hy
      · exact False.elim (hn hy)
      · split at hy <;> exact False.elim (hn hy)
    · exact False.elim (hn hy)

theorem pending_eventually_received_event (ρ : Run n) (hd : ReliableDelivery ρ) {k r}
    (hr : r ∈ pending (ρ.state k)) : ∃ l, k ≤ l ∧ ρ.event l = .receive r := by
  classical
  obtain ⟨t, hkt, ht⟩ := hd.1 k r (Finset.mem_sdiff.mp hr).1
  have hx : ∃ t, k ≤ t ∧ r ∈ (ρ.state t).received := ⟨t, hkt, ht⟩
  let u := Nat.find hx
  have hu : k ≤ u ∧ r ∈ (ρ.state u).received := Nat.find_spec hx
  have hku : k < u := by
    have hn := (Finset.mem_sdiff.mp hr).2
    by_contra h
    have he : u = k := by omega
    exact hn (he ▸ hu.2)
  have hn : r ∉ (ρ.state (u - 1)).received := by
    intro hn
    exact Nat.find_min hx (show u - 1 < u by omega) ⟨by omega, hn⟩
  refine ⟨u - 1, by omega, newly_received hn ?_⟩
  rw [← (ρ.valid (u - 1)).2, show u - 1 + 1 = u by omega]
  exact hu.2

theorem credit_has_witness {s : State n} (hb : RequestBalance s) {i : NodeId n}
    (ho : i ∉ s.owners) (ha : s.asked i = true)
    (hf : s.flight.map Prod.snd ≠ some i) :
    (∃ r ∈ pending s, r.sender = i) ∨ (∃ j, j ≠ i ∧ i ∈ s.queue j) := by
  classical
  by_contra h
  push Not at h
  have hp : pendingLoad s i = 0 := by
    apply Finset.sum_eq_zero
    intro r hr; simp [h.1 r hr]
  have hq : queueLoad s.queue i = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j = i
    · simp [hj]
    · simp [hj, List.count_eq_zero.mpr (h.2 j hj)]
  have hi := hb i
  simp [hp, hq, credit, ho, ha, flightLoad, hf] at hi

/-- Bundle only the fixed tree and its valid initial orientation. Temporal
progress remains in the separately stated delivery/fairness/CS contracts. -/
structure OnTree (G : SimpleGraph (NodeId n)) (ρ : Run n) : Prop where
  tree : G.IsTree
  routes : Routes G ρ.route ρ.owner
  self : ρ.route ρ.owner = ρ.owner
  edge_local : ∀ i, ρ.route i = i ∨ G.Adj i (ρ.route i)

theorem OnTree.balance {G : SimpleGraph (NodeId n)} {ρ : Run n}
    (h : OnTree G ρ) (k : ℕ) : RequestBalance (ρ.state k) :=
  reachable_requestBalance h.routes h.self h.edge_local (ρ.reachable k)

theorem OnTree.creditRouting {G : SimpleGraph (NodeId n)} {ρ : Run n}
    (h : OnTree G ρ) (k : ℕ) : CreditRouting (ρ.state k) :=
  reachable_creditRouting h.routes h.self h.edge_local (ρ.reachable k)

theorem OnTree.topology {G : SimpleGraph (NodeId n)} {ρ : Run n}
    (h : OnTree G ρ) (k : ℕ) : Topology G (ρ.state k) :=
  reachable_topology h.routes h.self h.edge_local (ρ.reachable k)

theorem OnTree.holder_owner {G : SimpleGraph (NodeId n)} {ρ : Run n}
    (h : OnTree G ρ) (k : ℕ) (i : NodeId n) :
    (ρ.state k).holder i = i ↔ i ∈ (ρ.state k).owners :=
  holder_self_iff_owner (reachable_edge_locality h.edge_local (ρ.reachable k)) (h.topology k)
    (reachable_backpointer h.tree h.routes h.self h.edge_local (ρ.reachable k)) i

/-- A nonempty queue at a node that stops serving must eventually appear as a
request in its holder's queue. Delivery, rather than FIFO channels, is used. -/
theorem quiet_request_reaches_holder {G : SimpleGraph (NodeId n)} {ρ : Run n}
    (hT : OnTree G ρ) (hd : ReliableDelivery ρ) (hf : WeakFairness ρ) (hc : FiniteCS ρ)
    {K i} (hq : QuietAfter ρ K i) (hw : ∃ k, K ≤ k ∧ (ρ.state k).queue i ≠ []) :
    ∃ t, K ≤ t ∧ i ∈ (ρ.state t).queue ((ρ.state K).holder i) := by
  have hno := quiet_eventual_queue_never_owner ρ hf hc hq hw
  obtain ⟨k, hk, hnon⟩ := hw
  obtain ⟨t, hkt, ht⟩ := handler_eventually_completes ρ hf k i
  have hKt : K ≤ t := hk.trans hkt
  have hqt := quiet_queue_nonempty ρ hq hk hkt hnon
  have hht : (ρ.state t).holder i ≠ i := fun h => hno t hKt ((hT.holder_owner t i).mp h)
  have ha := reachable_readyAsks (ρ.reachable t) i ht hqt hht
  have hflight := no_owner_no_flight ρ hd hno hKt
  rcases credit_has_witness (hT.balance t) (hno t hKt) ha hflight with
    ⟨r, hr, hri⟩ | ⟨j, hji, hij⟩
  · have hp := (hT.creditRouting t).pending_holder r hr
    rw [hri, never_owner_holder_stable ρ hno hKt] at hp
    obtain ⟨l, htl, he⟩ := pending_eventually_received_event ρ hd hr
    refine ⟨l + 1, by omega, ?_⟩
    rw [(ρ.valid l).2, he, hp]
    simp [next, hri]
  · have hp := (hT.creditRouting t).queue_holder i j (Ne.symm hji) hij
    rw [never_owner_holder_stable ρ hno hKt] at hp
    exact ⟨t, hKt, hp ▸ hij⟩

theorem follows_closed {G : SimpleGraph (NodeId n)} {f : NodeId n → NodeId n}
    {P : NodeId n → Prop} (hP : ∀ i, P i → P (f i)) {i j} {p : G.Walk i j}
    (hf : Follows f p) (hi : P i) : P j := by
  induction p with
  | nil => exact hi
  | cons _ _ ih => exact ih hf.2 (hf.1 ▸ hP _ hi)

/-- Every actual local request eventually enters its critical section.
The proof combines finite FIFO position with the finite holder path. It does not
assume global FIFO channels, strong fairness, or eventual token service. -/
theorem starvation_freedom_under_liveness {G : SimpleGraph (NodeId n)} (ρ : Run n)
    (hT : OnTree G ρ) (hd : ReliableDelivery ρ) (hf : WeakFairness ρ) (hc : FiniteCS ρ)
    {k i} (hw : (ρ.state k).mode i = .requesting) :
    ∃ l, k ≤ l ∧ (ρ.state l).mode i = .inCS := by
  classical
  by_contra hno
  push Not at hno
  have hmem : i ∈ (ρ.state k).queue i := by
    have h := reachable_selfQueued hT.edge_local (ρ.reachable k) i
    rw [hw, if_pos rfl] at h
    exact List.count_pos_iff.mp (by omega)
  have hnotremoved : ∀ l, k ≤ l → ¬ Removed (ρ.state l) (ρ.event l) i i := by
    intro l hkl hr
    have he := removed_self_enters hr
    rw [← (ρ.valid l).2] at he
    exact hno (l + 1) (by omega) he
  have hnotrec : ¬ Recurrent ρ i := by
    intro hi
    obtain ⟨l, hkl, hr⟩ := recurrent_serves_queued ρ hi hmem
    exact hnotremoved l hkl hr
  obtain ⟨K₀, hK₀⟩ := finite_quiet_cutoff ρ
  let K := max K₀ k
  have hquiet : ∀ j, ¬ Recurrent ρ j → QuietAfter ρ K j := by
    intro j hj l hl
    exact hK₀ j hj l ((le_max_left K₀ k).trans hl)
  let Stuck : NodeId n → Prop := fun j => ¬ Recurrent ρ j ∧
    ∃ t, K ≤ t ∧ (ρ.state t).queue j ≠ []
  have hi : Stuck i := by
    refine ⟨hnotrec, K, le_refl _, ?_⟩
    have hm := (queue_persists_without_removal ρ hmem hnotremoved K (le_max_right K₀ k)).1
    exact List.ne_nil_of_mem hm
  have hclosed : ∀ j, Stuck j → Stuck ((ρ.state K).holder j) := by
    intro j hj
    have hq := hquiet j hj.1
    have hn := quiet_eventual_queue_never_owner ρ hf hc hq hj.2
    have hne : j ≠ (ρ.state K).holder j := by
      intro he
      exact hn K (le_refl _) ((hT.holder_owner K j).mp he.symm)
    obtain ⟨t, hKt, ht⟩ := quiet_request_reaches_holder hT hd hf hc hq hj.2
    refine ⟨?_, t, hKt, List.ne_nil_of_mem ht⟩
    intro hrec
    obtain ⟨l, htl, hr⟩ := recurrent_serves_queued ρ hrec ht
    have hfl := removed_neighbour_sends hne hr
    rw [← (ρ.valid l).2] at hfl
    obtain ⟨u, hlu, hu⟩ := flight_eventually_owned ρ hd hfl
    exact hn u (by omega) hu
  obtain ⟨root, hroot, hr⟩ := (hT.topology K).routes
  obtain ⟨p, _, hp⟩ := hr i
  have hrootStuck : Stuck root := follows_closed hclosed hp hi
  have hn := quiet_eventual_queue_never_owner ρ hf hc
    (hquiet root hrootStuck.1) hrootStuck.2
  rcases hroot with ho | ⟨a, hfl⟩
  · exact hn K (le_refl _) ho
  · obtain ⟨l, hKl, hl⟩ := flight_eventually_owned ρ hd hfl
    exact hn l hKl hl

def AskedNonempty (s : State n) : Prop := ∀ i, s.asked i = true → s.queue i ≠ []

theorem askedNonempty_assign {s : State n} (h : AskedNonempty s) (a : NodeId n) :
    AskedNonempty (assignPrivilege s a) := by
  unfold assignPrivilege
  split
  · split
    · exact h
    · split
      all_goals
        intro i hi
        have hn : i ≠ a := by intro he; subst i; simp at hi
        simpa [hn] using h i (by simpa [hn] using hi)
  · exact h

theorem askedNonempty_makeRequest {s : State n} (h : AskedNonempty s) (a : NodeId n) :
    AskedNonempty (makeRequest s a) := by
  unfold makeRequest
  split
  · rename_i ha
    intro i hi
    by_cases hn : i = a
    · subst i; exact ha.2.1
    · exact h i (by simpa [hn] using hi)
  · exact h

theorem askedNonempty_step {s : State n} (h : AskedNonempty s) (e : Event n) :
    AskedNonempty (next s e) := by
  cases e with
  | assign a => exact askedNonempty_assign h a
  | makeRequest a => exact askedNonempty_makeRequest h a
  | request a =>
    intro i hi
    by_cases hn : i = a
    · subst i; simp [next]
    · simpa [next, hn] using h i hi
  | receive r =>
    intro i hi
    by_cases hn : i = r.dest
    · subst i; simp [next]
    · simpa [next, hn] using h i hi
  | deliver | leave | idle => exact h

theorem reachable_askedNonempty {owner : NodeId n} {route} {s : State n}
    (hs : Reachable owner route s) : AskedNonempty s := by
  induction hs with
  | refl => intro i hi; simp [initial] at hi
  | tail _ he ih => rcases he with ⟨_, rfl⟩; exact askedNonempty_step ih _

theorem routes_parent_distance {G : SimpleGraph (NodeId n)} (hG : G.IsTree)
    {f : NodeId n → NodeId n} {root i : NodeId n} (hr : Routes G f root) (hi : i ≠ root) :
    G.dist i root = G.dist (f i) root + 1 := by
  obtain ⟨p, hp, hf⟩ := hr i
  cases p with
  | nil => exact False.elim (hi rfl)
  | cons h p =>
    have hlen := tree_path_length_eq_dist hG hp
    have ht := tree_path_length_eq_dist hG hp.of_cons
    simp only [SimpleGraph.Walk.length_cons] at hlen
    rw [hf.1]
    omega

def Descends {G : SimpleGraph (NodeId n)} (d : NodeId n → ℕ) :
    {i j : NodeId n} → G.Walk i j → Prop
  | _, _, .nil => True
  | i, _, @SimpleGraph.Walk.cons _ _ _ k _ _ p => d i = d k + 1 ∧ Descends d p

theorem follows_effective_descends {G : SimpleGraph (NodeId n)} (hG : G.IsTree)
    {f : NodeId n → NodeId n} {root : NodeId n} (hr : Routes G f root)
    {i j} {p : G.Walk i j} (hf : Follows (Function.update f root root) p) :
    Descends (fun v => G.dist v root) p := by
  induction p with
  | nil => trivial
  | @cons i k j h p ih =>
    have hi : i ≠ root := by
      intro he; subst i
      have hk : root = k := by simpa using hf.1
      exact h.ne hk
    have he : f i = k := by simpa [hi] using hf.1
    exact ⟨by simpa [he] using routes_parent_distance hG hr hi, ih hf.2⟩

theorem descends_support_le {G : SimpleGraph (NodeId n)} {d : NodeId n → ℕ}
    {i j} {p : G.Walk i j} (hd : Descends d p) {v} (hv : v ∈ p.support) : d v ≤ d i := by
  induction p with
  | @nil w =>
    have he : v = w := by simpa using hv
    subst v; exact le_refl _
  | cons _ _ ih =>
    rcases List.mem_cons.mp hv with rfl | hv
    · exact le_refl _
    · have ht := ih hd.2 hv
      have hs := hd.1
      omega

theorem descends_isPath {G : SimpleGraph (NodeId n)} {d : NodeId n → ℕ}
    {i j} {p : G.Walk i j} (hd : Descends d p) : p.IsPath := by
  induction p with
  | nil => exact .nil
  | @cons i k j h p ih =>
    apply (ih hd.2).cons
    intro hm
    have hl := descends_support_le hd.2 hm
    have hs := hd.1
    omega

/-- Trace a queued demand backwards to a real local invocation. The recursive
measure is the remaining height of the finite holder tree. -/
theorem nonempty_queue_has_source {G : SimpleGraph (NodeId n)} (hG : G.IsTree)
    {s : State n} {root : NodeId n} (hloc : Location s root) (hr : Routes G s.holder root)
    (hl : EdgeLocality G s) (hb : RequestBalance s) (hc : CreditRouting s)
    (ha : AskedNonempty s) (hq : SelfQueued s) (j : NodeId n) (hne : s.queue j ≠ []) :
    ∃ u, s.mode u = .requesting ∧ ∃ p : G.Walk u j,
      Follows (Function.update s.holder root root) p := by
  have hall : ∀ m, ∀ j : NodeId n, n - G.dist j root = m → s.queue j ≠ [] →
      ∃ u, s.mode u = .requesting ∧ ∃ p : G.Walk u j,
        Follows (Function.update s.holder root root) p := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro v hm hnon
      cases hlist : s.queue v with
      | nil => exact False.elim (hnon hlist)
      | cons x tail =>
        have hx : x ∈ s.queue v := by simp [hlist]
        by_cases hxv : x = v
        · subst x
          have hs := hq v
          have hpos : 0 < (s.queue v).count v := List.count_pos_iff.mpr hx
          have hmode : s.mode v = .requesting := by
            split_ifs at hs with h
            · exact h
            · omega
          exact ⟨v, hmode, .nil, trivial⟩
        · have hcredit := queued_neighbour_asked hb (Ne.symm hxv) hx
          have hxroot : x ≠ root := by
            intro he; subst root
            rcases hloc with ho | ⟨a, hf⟩
            · exact hcredit.2 ho
            · exact queued_origin_not_flight hb (Ne.symm hxv) hx hf rfl
          have hp := hc.queue_holder x v hxv hx
          have hd := routes_parent_distance hG hr hxroot
          rw [hp] at hd
          obtain ⟨p, hpath, _⟩ := hr x
          have hlen := tree_path_length_eq_dist hG hpath
          have hbound : G.dist x root < n := by simpa [hlen] using hpath.length_lt
          obtain ⟨u, hu, p, hfp⟩ := ih (n - G.dist x root) (by omega) x rfl (ha x hcredit.1)
          have hadj := (hl.queue v x hx).resolve_left hxv
          refine ⟨u, hu, p.concat hadj.symm, follows_concat hfp hadj.symm ?_⟩
          simpa [hxroot] using hp
  exact hall _ j rfl hne

def OnlyRequester (s : State n) (u : NodeId n) : Prop :=
  ∀ i, s.mode i = .requesting → i = u

/-- With a single local requester, every queued neighbour lies one step closer
to that requester. This will make the token-distance potential exact. -/
theorem isolated_queue_distance {G : SimpleGraph (NodeId n)} (hG : G.IsTree)
    {s : State n} {root u a b : NodeId n}
    (hloc : Location s root) (hr : Routes G s.holder root)
    (hl : EdgeLocality G s) (hb : RequestBalance s) (hc : CreditRouting s)
    (ha : AskedNonempty s) (hq : SelfQueued s) (hu : OnlyRequester s u)
    (hne : b ≠ a) (hm : b ∈ s.queue a) : G.dist u a = G.dist u b + 1 := by
  have hdemand := queued_neighbour_asked hb (Ne.symm hne) hm
  obtain ⟨v, hv, p, hp⟩ := nonempty_queue_has_source hG hloc hr hl hb hc ha hq b
    (ha b hdemand.1)
  have he := hu v hv
  subst v
  have hbroot : b ≠ root := by
    intro he; subst root
    rcases hloc with ho | ⟨src, hf⟩
    · exact hdemand.2 ho
    · exact queued_origin_not_flight hb (Ne.symm hne) hm hf rfl
  have hadj := (hl.queue a b hm).resolve_left hne
  have hholder := hc.queue_holder b a hne hm
  have hp' := follows_concat hp hadj.symm (by simpa [hbroot] using hholder)
  have hl1 := tree_path_length_eq_dist hG (descends_isPath (follows_effective_descends hG hr hp))
  have hl2 := tree_path_length_eq_dist hG (descends_isPath (follows_effective_descends hG hr hp'))
  simp only [SimpleGraph.Walk.length_concat] at hl2
  omega

def workLoad (s : State n) : ℤ := ∑ i : NodeId n, (pendingLoad s i + queueLoad s.queue i)

def TrafficBalance (s : State n) : Prop :=
  (s.requestSends : ℤ) = (s.privilegeSends : ℤ) + workLoad s

theorem workLoad_request (s : State n) (a : NodeId n) :
    workLoad (next s (.request a)) = workLoad s := by
  apply Finset.sum_congr rfl
  intro i _
  change pendingLoad s i + queueLoad (Function.update s.queue a (s.queue a ++ [a])) i = _
  rw [queueLoad_append]
  have hn : ¬ (a ≠ i ∧ a = i) := fun h => h.1 h.2
  simp [hn]

theorem workLoad_receive {s : State n} {r : Request n}
    (hr : r ∈ s.sent) (hn : r ∉ s.received) (hne : r.sender ≠ r.dest) :
    workLoad (next s (.receive r)) = workLoad s := by
  apply Finset.sum_congr rfl
  intro i _
  change pendingLoad (next s (.receive r)) i +
    queueLoad (Function.update s.queue r.dest (s.queue r.dest ++ [r.sender])) i = _
  rw [pendingLoad_receive hr hn, queueLoad_append]
  by_cases hi : r.sender = i
  · subst i; simp [Ne.symm hne]
  · simp [hi]

theorem workLoad_makeRequest {s : State n} (hh : MessageHistory s) {a : NodeId n}
    (ha : s.holder a ≠ a ∧ s.queue a ≠ [] ∧ s.asked a = false) :
    workLoad (makeRequest s a) = workLoad s + 1 := by
  calc
    _ = ∑ i : NodeId n, ((pendingLoad s i + queueLoad s.queue i) +
        (if i = a then (1 : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      have hq : (makeRequest s a).queue = s.queue := by simp [makeRequest, ha]
      rw [pendingLoad_makeRequest hh ha, hq]
      by_cases hi : i = a
      · subst i; omega
      · simp only [if_neg hi, if_neg (Ne.symm hi)]; omega
    _ = _ := by rw [Finset.sum_add_distrib]; simp [workLoad]

theorem workLoad_pop {s : State n} {a b : NodeId n} {tail : List (NodeId n)}
    (hq : s.queue a = b :: tail) :
    workLoad {s with queue := Function.update s.queue a tail} =
      workLoad s - if b = a then 0 else 1 := by
  calc
    _ = ∑ i : NodeId n, ((pendingLoad s i + queueLoad s.queue i) -
        (if a ≠ i ∧ b = i then (1 : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      change pendingLoad s i + queueLoad (Function.update s.queue a tail) i = _
      rw [queueLoad_pop hq]
      omega
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      by_cases hba : b = a
      · subst b
        simp [workLoad]
      · have hi : ∀ i : NodeId n, (if a ≠ i ∧ b = i then (1 : ℤ) else 0) =
            if i = b then 1 else 0 := by
          intro i
          by_cases hib : i = b
          · subst i; simp [Ne.symm hba]
          · simp [hib, Ne.symm hib]
        simp [hi, hba, workLoad]

theorem traffic_assign {s : State n} (ht : TrafficBalance s) (a : NodeId n) :
    TrafficBalance (assignPrivilege s a) := by
  unfold assignPrivilege
  split
  · split
    · exact ht
    · rename_i j tail hq
      have hwork := workLoad_pop hq
      split
      · rename_i he
        subst j
        change (s.requestSends : ℤ) = (s.privilegeSends : ℤ) +
          workLoad {s with queue := Function.update s.queue a tail}
        simpa [TrafficBalance, hwork] using ht
      · rename_i he
        change (s.requestSends : ℤ) = ((s.privilegeSends + 1 : ℕ) : ℤ) +
          workLoad {s with queue := Function.update s.queue a tail}
        rw [hwork, if_neg he]
        unfold TrafficBalance at ht
        push_cast
        omega
  · exact ht

theorem traffic_step {G : SimpleGraph (NodeId n)} {s : State n}
    (hl : EdgeLocality G s) (hh : MessageHistory s) (ht : TrafficBalance s)
    {e} (he : Enabled s e) : TrafficBalance (next s e) := by
  cases e with
  | assign a => exact traffic_assign ht a
  | request a =>
    change (s.requestSends : ℤ) = (s.privilegeSends : ℤ) + workLoad (next s (.request a))
    rw [workLoad_request]; exact ht
  | receive r =>
    change (s.requestSends : ℤ) = (s.privilegeSends : ℤ) + workLoad (next s (.receive r))
    rw [workLoad_receive he.2.1 he.2.2 (hl.sent r he.2.1).ne]; exact ht
  | makeRequest a =>
    by_cases ha : s.holder a ≠ a ∧ s.queue a ≠ [] ∧ s.asked a = false
    · have hw := workLoad_makeRequest hh ha
      change ((makeRequest s a).requestSends : ℤ) =
        ((makeRequest s a).privilegeSends : ℤ) + workLoad (makeRequest s a)
      rw [hw]
      have hc : (makeRequest s a).requestSends = s.requestSends + 1 := by simp [makeRequest, ha]
      have hp : (makeRequest s a).privilegeSends = s.privilegeSends := by simp [makeRequest, ha]
      rw [hc, hp]
      unfold TrafficBalance at ht
      push_cast
      omega
    · dsimp only [next]; unfold makeRequest; rw [if_neg ha]; exact ht
  | deliver | leave | idle => exact ht

theorem reachable_traffic {G : SimpleGraph (NodeId n)} {owner : NodeId n} {route}
    (he : ∀ i, route i = i ∨ G.Adj i (route i)) {s : State n}
    (hs : Reachable owner route s) : TrafficBalance s := by
  induction hs with
  | refl => simp [TrafficBalance, initial, workLoad, pendingLoad, pending, queueLoad]
  | tail hst htu ih =>
    rcases htu with ⟨hen, rfl⟩
    exact traffic_step (reachable_edge_locality he hst) (reachable_message_history hst) ih hen

def OnlyClientEvent (u : NodeId n) (e : Event n) : Prop := ∀ i, e = .request i → i = u

theorem onlyRequester_step {s : State n} {u : NodeId n} (hu : OnlyRequester s u)
    {e} (he : OnlyClientEvent u e) : OnlyRequester (next s e) u := by
  cases e with
  | request a =>
    intro i hi
    by_cases ha : i = a
    · subst i; exact he a rfl
    · exact hu i (by simpa [next, ha] using hi)
  | leave a =>
    intro i hi
    by_cases ha : i = a
    · subst i; simp [next] at hi
    · exact hu i (by simpa [next, ha] using hi)
  | receive | deliver | idle => exact hu
  | makeRequest a =>
    dsimp only [next]; unfold makeRequest; split <;> exact hu
  | assign a =>
    dsimp only [next]; unfold assignPrivilege
    split
    · split
      · exact hu
      · split
        · intro i hi
          by_cases ha : i = a
          · subst i; simp at hi
          · exact hu i (by simpa [ha] using hi)
        · exact hu
    · exact hu

/-- Arbitrary legal interleavings with one application client. Initialization is
quiescent; message delivery is not serialized and idle steps are permitted.
The client may even enter repeatedly: after its first isolated entry no extra
network traffic is needed. -/
inductive IsolatedExecution (u owner : NodeId n) (route : NodeId n → NodeId n) :
    State n → Prop where
  | initial : IsolatedExecution u owner route (initial owner route)
  | step {s t e} : IsolatedExecution u owner route s → Step s e t → OnlyClientEvent u e →
      IsolatedExecution u owner route t

theorem IsolatedExecution.reachable {u owner : NodeId n} {route} {s : State n}
    (h : IsolatedExecution u owner route s) : Reachable owner route s := by
  induction h with
  | initial => exact .refl _
  | step _ hs _ ih => exact .tail ih hs

theorem IsolatedExecution.onlyRequester {u owner : NodeId n} {route} {s : State n}
    (h : IsolatedExecution u owner route s) : OnlyRequester s u := by
  induction h with
  | initial => intro i hi; simp [DistributedRaymondTreeMutex.initial] at hi
  | step _ hs he ih => rcases hs with ⟨_, rfl⟩; exact onlyRequester_step ih he

def TokenPotential (G : SimpleGraph (NodeId n)) (u : NodeId n) (s : State n) (d : ℕ) : Prop :=
  ∀ root, Location s root → s.privilegeSends + G.dist u root = d

theorem potential_initial (G : SimpleGraph (NodeId n)) (u owner : NodeId n) (route) :
    TokenPotential G u (initial owner route) (G.dist u owner) := by
  intro root hroot
  have he : root = owner := by simpa [Location, initial] using hroot
  subst root; simp [initial]

theorem potential_assign {G : SimpleGraph (NodeId n)} (hG : G.IsTree)
    {s : State n} {u : NodeId n} {d : ℕ}
    (hs : Safety s) (hl : EdgeLocality G s) (ht : Topology G s)
    (hb : RequestBalance s) (hc : CreditRouting s) (ha : AskedNonempty s) (hq : SelfQueued s)
    (hu : OnlyRequester s u) (hp : TokenPotential G u s d) (a : NodeId n) :
    TokenPotential G u (assignPrivilege s a) d := by
  unfold assignPrivilege
  split
  · rename_i hactive
    split
    · exact hp
    · rename_i j tail hlist
      split
      · exact hp
      · rename_i hja
        obtain ⟨ho, _⟩ := owner_singleton hs.conserved hactive.1
        obtain ⟨root, hroot, hr⟩ := ht.routes
        have he : root = a := location_unique hs.conserved hroot (Or.inl hactive.1)
        subst root
        have hdist := isolated_queue_distance hG (Or.inl hactive.1) hr hl hb hc ha hq hu hja
          (by simp [hlist])
        have hpotential := hp a (Or.inl hactive.1)
        intro root hroot
        have he : root = j := by
          rcases hroot with hown | ⟨src, hfl⟩
          · simp [ho] at hown
          · have heq : a = src ∧ j = root := by simpa using hfl
            exact heq.2.symm
        subst root
        change s.privilegeSends + 1 + G.dist u j = d
        omega
  · exact hp

theorem potential_step {G : SimpleGraph (NodeId n)} (hG : G.IsTree)
    {s : State n} {u : NodeId n} {d : ℕ}
    (hs : Safety s) (hl : EdgeLocality G s) (ht : Topology G s)
    (hb : RequestBalance s) (hc : CreditRouting s) (ha : AskedNonempty s) (hq : SelfQueued s)
    (hu : OnlyRequester s u) (hp : TokenPotential G u s d) {e} (he : Enabled s e) :
    TokenPotential G u (next s e) d := by
  cases e with
  | request | receive | leave | idle => exact hp
  | makeRequest a =>
    dsimp only [next]; unfold makeRequest; split <;> exact hp
  | assign a => exact potential_assign hG hs hl ht hb hc ha hq hu hp a
  | deliver a b =>
    have ho := flight_empty_owners hs.conserved he.2
    intro root hroot
    have hroot' : root = b := by simpa [Location, next, ho] using hroot
    subst root
    exact hp b (Or.inr ⟨a, he.2⟩)

theorem isolated_token_potential {G : SimpleGraph (NodeId n)} (hG : G.IsTree)
    {u owner : NodeId n} {route} (hr : Routes G route owner) (ho : route owner = owner)
    (he : ∀ i, route i = i ∨ G.Adj i (route i)) {s : State n}
    (h : IsolatedExecution u owner route s) : TokenPotential G u s (G.dist u owner) := by
  induction h with
  | initial => exact potential_initial G u owner route
  | @step s t e hst hstep _ ih =>
    rcases hstep with ⟨hen, rfl⟩
    have hs := hst.reachable
    exact potential_step hG (reachable_safety hs) (reachable_edge_locality he hs)
      (reachable_topology hr ho he hs) (reachable_requestBalance hr ho he hs)
      (reachable_creditRouting hr ho he hs) (reachable_askedNonempty hs)
      (reachable_selfQueued he hs) hst.onlyRequester ih hen

theorem no_local_requests_no_work {G : SimpleGraph (NodeId n)} (hG : G.IsTree)
    {s : State n} (ht : Topology G s) (hl : EdgeLocality G s) (hb : RequestBalance s)
    (hc : CreditRouting s) (ha : AskedNonempty s) (hq : SelfQueued s)
    (hn : ∀ i, s.mode i ≠ .requesting) : workLoad s = 0 := by
  obtain ⟨root, hloc, hr⟩ := ht.routes
  have hqueue : ∀ i, s.queue i = [] := by
    intro i
    by_contra he
    obtain ⟨u, hu, _⟩ := nonempty_queue_has_source hG hloc hr hl hb hc ha hq i he
    exact hn u hu
  have hasked : ∀ i, s.asked i ≠ true := by
    intro i hi; exact ha i hi (hqueue i)
  have hp : ∀ i, pendingLoad s i = 0 := by
    intro i
    have h := hb i
    have hn := pendingLoad_nonneg s i
    have hfl := flightLoad_nonneg s.flight i
    have hc0 : credit s i = 0 := by simp [credit, hasked i]
    simp [hc0, queueLoad, hqueue] at h
    omega
  simp [workLoad, hp, queueLoad, hqueue]

/-- Exact traffic for every completed isolated execution, including arbitrary
message delays/interleavings and the zero-distance retained-token case. -/
theorem isolated_request_message_bound {G : SimpleGraph (NodeId n)} (hG : G.IsTree)
    {u owner : NodeId n} {route} (hr : Routes G route owner) (ho : route owner = owner)
    (he : ∀ i, route i = i ∨ G.Adj i (route i)) {s : State n}
    (h : IsolatedExecution u owner route s) (hcs : s.mode u = .inCS) :
    s.requestSends = G.dist u owner ∧ s.privilegeSends = G.dist u owner ∧
      s.requestSends + s.privilegeSends = 2 * G.dist u owner := by
  have hs := h.reachable
  have hsafe := reachable_safety hs
  have hpotential := isolated_token_potential hG hr ho he h u (Or.inl (hsafe.cs_owner u hcs))
  have hpriv : s.privilegeSends = G.dist u owner := by simpa using hpotential
  have hn : ∀ i, s.mode i ≠ .requesting := by
    intro i hi
    have he := h.onlyRequester i hi
    subst i; rw [hcs] at hi; cases hi
  have hw := no_local_requests_no_work hG (reachable_topology hr ho he hs)
    (reachable_edge_locality he hs) (reachable_requestBalance hr ho he hs)
    (reachable_creditRouting hr ho he hs) (reachable_askedNonempty hs)
    (reachable_selfQueued he hs) hn
  have ht := reachable_traffic he hs
  unfold TrafficBalance at ht
  rw [hw] at ht
  exact ⟨by omega, hpriv, by omega⟩

/-- The reviewed contract preserves arbitrary finite trees and explicit liveness hypotheses. -/
structure DistributedRaymondTreeSuite : Prop where
  conservation : ∀ n (owner : NodeId n) route s,
    Reachable owner route s → tokenCount s = 1
  exclusion : ∀ n (owner : NodeId n) route s, Reachable owner route s →
    ∀ i j, i ≠ j → s.mode i = .inCS → s.mode j = .inCS → False
  initialization : ∀ n (G : SimpleGraph (NodeId n)), G.IsTree → ∀ root,
    ∃ route, Routes G route root ∧ route root = root ∧
      ∀ i, route i = i ∨ G.Adj i (route i)
  routing : ∀ n (G : SimpleGraph (NodeId n)) owner route,
    Routes G route owner → route owner = owner →
    (∀ i, route i = i ∨ G.Adj i (route i)) → ∀ s, Reachable owner route s →
      ∃ root, Location s root ∧ Routes G s.holder root
  queue : ∀ n (G : SimpleGraph (NodeId n)) owner route,
    Routes G route owner → route owner = owner →
    (∀ i, route i = i ∨ G.Adj i (route i)) → ∀ s, Reachable owner route s →
      ∀ i, (s.queue i).Nodup
  progress : ∀ n (G : SimpleGraph (NodeId n)) (ρ : Run n), OnTree G ρ →
    ReliableDelivery ρ → WeakFairness ρ → FiniteCS ρ → ∀ k i,
      (ρ.state k).mode i = .requesting → ∃ l, k ≤ l ∧ (ρ.state l).mode i = .inCS
  traffic : ∀ n (G : SimpleGraph (NodeId n)), G.IsTree → ∀ u owner route,
    Routes G route owner → route owner = owner →
    (∀ i, route i = i ∨ G.Adj i (route i)) → ∀ s,
      IsolatedExecution u owner route s → s.mode u = .inCS →
      s.requestSends = G.dist u owner ∧ s.privilegeSends = G.dist u owner ∧
        s.requestSends + s.privilegeSends = 2 * G.dist u owner
  raw_transit_cycle : ∃ s : State 2, Reachable 0 (fun _ => 0) s ∧ s.holder 0 = 1 ∧
    s.holder 1 = 0 ∧ s.flight = some (0, 1) ∧ s.owners = ∅

theorem distributed_raymond_tree_master_suite : DistributedRaymondTreeSuite where
  conservation := fun _ _ _ _ => privilege_conservation_invariant
  exclusion := fun _ _ _ _ h _ _ => mutual_exclusion_safety h
  initialization := fun _ _ hG => tree_initialization_exists hG
  routing := fun _ _ _ _ hr ho he _ => holder_graph_acyclicity hr ho he
  queue := fun _ _ _ _ hr ho he _ => queue_nodup_preservation hr ho he
  progress := fun _ _ ρ hT hd hf hc _ _ =>
    starvation_freedom_under_liveness ρ hT hd hf hc
  traffic := fun _ _ hG _ _ _ hr ho he _ => isolated_request_message_bound hG hr ho he
  raw_transit_cycle := raw_holder_two_cycle_reachable

end DistributedRaymondTreeMutex
