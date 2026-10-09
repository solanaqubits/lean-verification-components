/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedRaymondTreeMutex
import Mathlib.Data.Int.LeastGreatest
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Topological costs count network sends of a completed isolated request.
Existence of a completing execution is established separately from the cost identity. -/
noncomputable section
open scoped BigOperators
namespace DistributedRaymondTreeMessageComplexity
open DistributedRaymondTreeMutex

variable {V : Type*}

def treeHeight [Fintype V] (G : SimpleGraph V) (root : V) : ℕ :=
  Finset.univ.sup (G.dist root)

def treeDiameter [Fintype V] (G : SimpleGraph V) : ℕ :=
  Finset.univ.sup (treeHeight G)

def messages (G : SimpleGraph V) (u t : V) : ℕ := 2 * G.dist u t

def maximumMessages [Fintype V] (G : SimpleGraph V) : ℕ := 2 * treeDiameter G

theorem distance_le_height [Fintype V] (G : SimpleGraph V) (root v : V) :
    G.dist root v ≤ treeHeight G root := Finset.le_sup (Finset.mem_univ v)

theorem distance_le_diameter [Fintype V] (G : SimpleGraph V) (u v : V) :
    G.dist u v ≤ treeDiameter G :=
  (distance_le_height G u v).trans (Finset.le_sup (Finset.mem_univ u))

theorem diameter_attained [Fintype V] (G : SimpleGraph V) [Nonempty V] :
    ∃ u v, G.dist u v = treeDiameter G := by
  obtain ⟨u, _, hu⟩ := Finset.sup_mem_of_nonempty (f := treeHeight G)
    (Finset.univ_nonempty : (Finset.univ : Finset V).Nonempty)
  obtain ⟨v, _, hv⟩ := Finset.sup_mem_of_nonempty (f := G.dist u)
    (Finset.univ_nonempty : (Finset.univ : Finset V).Nonempty)
  exact ⟨u, v, hv.trans hu⟩

theorem diameter_le_twice_height [Fintype V] (G : SimpleGraph V) (hG : G.Connected) (root : V) :
    treeDiameter G ≤ 2 * treeHeight G root := by
  apply Finset.sup_le
  intro u _
  apply Finset.sup_le
  intro v _
  have h := hG.dist_triangle (u := u) (v := root) (w := v)
  have hu := distance_le_height G root u
  have hv := distance_le_height G root v
  rw [G.dist_comm (u := u) (v := root)] at h
  omega

theorem raymond_bound_diameter {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G.IsTree)
    {u owner : Fin n} {route} (hr : Routes G route owner) (ho : route owner = owner)
    (he : ∀ i, route i = i ∨ G.Adj i (route i)) {s : State n}
    (hs : IsolatedExecution u owner route s) (hcs : s.mode u = .inCS) :
    s.requestSends + s.privilegeSends ≤ 2 * treeDiameter G := by
  rw [(isolated_request_message_bound hG hr ho he hs hcs).2.2]
  exact Nat.mul_le_mul_left 2 (distance_le_diameter G u owner)

theorem raymond_bound_height {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G.IsTree)
    {u owner : Fin n} {route} (hr : Routes G route owner) (ho : route owner = owner)
    (he : ∀ i, route i = i ∨ G.Adj i (route i)) {s : State n}
    (hs : IsolatedExecution u owner route s) (hcs : s.mode u = .inCS) (root : Fin n) :
    treeDiameter G ≤ 2 * treeHeight G root ∧
      s.requestSends + s.privilegeSends ≤ 4 * treeHeight G root := by
  have hd := diameter_le_twice_height G hG.connected root
  have hm := raymond_bound_diameter hG hr ho he hs hcs
  omega

/-- The geodesic-through-root premise is explicit. -/
theorem raymond_height_tightness [Fintype V] (G : SimpleGraph V) (hG : G.Connected)
    (root u v : V) (hu : G.dist root u = treeHeight G root)
    (hv : G.dist root v = treeHeight G root)
    (hpath : G.dist u v = G.dist u root + G.dist root v) :
    G.dist u v = 2 * treeHeight G root ∧ treeDiameter G = 2 * treeHeight G root := by
  have he : G.dist u v = 2 * treeHeight G root := by
    rw [hpath, G.dist_comm (u := u) (v := root), hu, hv]; omega
  have hd := distance_le_diameter G u v
  have hb := diameter_le_twice_height G hG root
  omega

theorem reg_token_holder (G : SimpleGraph V) (u : V) : messages G u u = 0 := by
  simp [messages]

/-- Local phase rank increases through ASSIGN then MAKE_REQUEST. -/
def phaseRank : Phase → ℤ
  | .assign => 0
  | .makeRequest => 1
  | .ready => 2

def serviceRank {n : ℕ} (s : State n) : ℤ :=
  3 * (s.received.card : ℤ) + 3 * (s.privilegeSends : ℤ) -
    3 * (s.flight.toList.length : ℤ) + ∑ i, phaseRank (s.phase i)

/-- No new application calls, releases or idle steps in the selected finite service trace. -/
def ServiceEvent {n : ℕ} : Event n → Prop
  | .receive _ | .deliver _ _ | .assign _ | .makeRequest _ => True
  | _ => False

theorem phase_rank_update {n : ℕ} (f : Fin n → Phase) (i : Fin n) (p : Phase) :
    (∑ j, phaseRank (Function.update f i p j)) =
      (∑ j, phaseRank (f j)) - phaseRank (f i) + phaseRank p := by
  classical
  have h : (fun j => phaseRank (Function.update f i p j)) =
      Function.update (fun j => phaseRank (f j)) i (phaseRank p) := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [h, Finset.sum_update_of_mem (Finset.mem_univ i)]
  have he := Finset.sum_sdiff (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))
    (f := fun j => phaseRank (f j))
  simp only [Finset.sum_singleton] at he
  omega


theorem service_rank_step {n : ℕ} {s : State n} (hs : Safety s) {e : Event n}
    (he : ServiceEvent e) (hen : Enabled s e) : serviceRank (next s e) = serviceRank s + 1 := by
  cases e with
  | request | leave | idle => contradiction
  | receive r =>
    simp only [Enabled] at hen
    dsimp only [next, serviceRank]
    rw [phase_rank_update, hen.1, Finset.card_insert_of_notMem hen.2.2]
    simp only [Nat.cast_add, Nat.cast_one, phaseRank]
    ring
  | deliver i j =>
    simp only [Enabled] at hen
    dsimp only [next, serviceRank]
    rw [phase_rank_update, hen.1, hen.2]
    norm_num [phaseRank]
    ring
  | makeRequest i =>
    change s.phase i = .makeRequest at hen
    dsimp only [next]
    unfold makeRequest
    split <;> dsimp only [serviceRank] <;>
      rw [phase_rank_update, hen] <;> norm_num [phaseRank] <;> ring
  | assign i =>
    change s.phase i = .assign at hen
    dsimp only [next]
    unfold assignPrivilege
    split
    · rename_i hactive
      have hf := (owner_singleton hs.conserved hactive.1).2
      split
      · dsimp only [serviceRank]
        rw [phase_rank_update, hen]
        norm_num [phaseRank]
        ring
      · split <;> dsimp only [serviceRank] <;>
          rw [phase_rank_update, hen] <;> norm_num [phaseRank, hf] <;> ring
    · dsimp only [serviceRank]
      rw [phase_rank_update, hen]
      norm_num [phaseRank]
      ring

theorem sent_card_eq {n : ℕ} {owner : Fin n} {route} {s : State n}
    (hs : Reachable owner route s) : s.sent.card = s.requestSends := by
  induction hs with
  | refl => rfl
  | @tail t s e ht hstep ih =>
    rcases hstep with ⟨hen, rfl⟩
    have hh := reachable_message_history ht
    cases e with
    | request | receive | deliver | leave | idle => exact ih
    | assign i =>
      dsimp only [next]; unfold assignPrivilege
      split
      · split
        · exact ih
        · split <;> exact ih
      · exact ih
    | makeRequest i =>
      dsimp only [next]; unfold makeRequest
      split
      · simp [Finset.card_insert_of_notMem (next_request_fresh hh i), ih]
      · exact ih

theorem work_load_le_nodes {n : ℕ} {s : State n} (hb : RequestBalance s) :
    workLoad s ≤ n := by
  calc
    workLoad s ≤ ∑ _i : Fin n, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro i _
      have h := hb i
      have hn := flightLoad_nonneg s.flight i
      have hc := credit_le_one s i
      omega
    _ = n := by simp

theorem service_rank_bounded {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G.IsTree)
    {u owner : Fin n} {route} (hr : Routes G route owner) (ho : route owner = owner)
    (he : ∀ i, route i = i ∨ G.Adj i (route i)) {s : State n}
    (hs : IsolatedExecution u owner route s) : serviceRank s ≤ 6 * G.dist u owner + 5 * n := by
  have hreach := hs.reachable
  obtain ⟨root, hroot, _⟩ := (reachable_topology hr ho he hreach).routes
  have hp := isolated_token_potential hG hr ho he hs root hroot
  have ht := reachable_traffic he hreach
  have hw := work_load_le_nodes (reachable_requestBalance hr ho he hreach)
  have hc := Finset.card_le_card (reachable_message_history hreach).received_sent
  rw [sent_card_eq hreach] at hc
  have hsum : (∑ i, phaseRank (s.phase i)) ≤ (2 * n : ℤ) := by
    calc
      _ ≤ ∑ _i : Fin n, (2 : ℤ) := by
        apply Finset.sum_le_sum
        intro i _
        cases s.phase i <;> norm_num [phaseRank]
      _ = _ := by simp; ring
  dsimp only [serviceRank, TrafficBalance] at *
  have hc' : (s.received.card : ℤ) ≤ s.requestSends := by exact_mod_cast hc
  have hp' : (s.privilegeSends : ℤ) ≤ G.dist u owner := by
    exact_mod_cast (show s.privilegeSends ≤ G.dist u owner by omega)
  have hf : (0 : ℤ) ≤ s.flight.toList.length := Int.natCast_nonneg _
  omega


theorem service_mode_change {n : ℕ} {s : State n} (hq : SelfQueued s)
    {e : Event n} (he : ServiceEvent e) (i : Fin n) :
    (next s e).mode i = s.mode i ∨
      (s.mode i = .requesting ∧ (next s e).mode i = .inCS) := by
  cases e with
  | request | leave | idle => contradiction
  | receive | deliver => exact Or.inl rfl
  | makeRequest a => dsimp only [next]; unfold makeRequest; split <;> exact Or.inl rfl
  | assign a =>
    dsimp only [next]; unfold assignPrivilege
    split
    · split
      · exact Or.inl rfl
      · rename_i j tail hlist
        split
        · rename_i hja
          subst j
          by_cases hi : i = a
          · subst i
            have hm : s.mode a = .requesting := by
              have hh := hq a
              by_contra hn
              simp [hn, hlist] at hh
            exact Or.inr ⟨hm, by simp⟩
          · exact Or.inl (by simp [hi])
        · exact Or.inl rfl
    · exact Or.inl rfl

def ActiveClient {n : ℕ} (s : State n) (u : Fin n) : Prop :=
  s.mode u ≠ .idle ∧ ∀ i, i ≠ u → s.mode i = .idle

theorem active_service {n : ℕ} {s : State n} (hq : SelfQueued s) {u : Fin n}
    (ha : ActiveClient s u) {e : Event n} (he : ServiceEvent e) :
    ActiveClient (next s e) u := by
  constructor
  · rcases service_mode_change hq he u with h | ⟨_, h⟩
    · rw [h]; exact ha.1
    · simp [h]
  · intro i hi
    rcases service_mode_change hq he i with h | ⟨h, _⟩
    · exact h.trans (ha.2 i hi)
    · rw [ha.2 i hi] at h
      cases h

theorem requesting_has_service {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G.IsTree)
    {u owner : Fin n} {route} (hr : Routes G route owner) (ho : route owner = owner)
    (he : ∀ i, route i = i ∨ G.Adj i (route i)) {s : State n}
    (hs : IsolatedExecution u owner route s) (ha : ActiveClient s u)
    (hcs : s.mode u ≠ .inCS) : ∃ e, ServiceEvent e ∧ Enabled s e := by
  classical
  by_contra hn
  push Not at hn
  have hready : ∀ i, s.phase i = .ready := by
    intro i
    cases hp : s.phase i with
    | ready => rfl
    | assign => exact False.elim (hn (.assign i) trivial hp)
    | makeRequest => exact False.elim (hn (.makeRequest i) trivial hp)
  have hfl : s.flight = none := by
    cases hf : s.flight with
    | none => rfl
    | some p => exact False.elim (hn (.deliver p.1 p.2) trivial ⟨hready _, hf⟩)
  have hpend : ∀ r, r ∉ pending s := by
    intro r hm
    exact hn (.receive r) trivial ⟨hready _, (Finset.mem_sdiff.mp hm).1,
      (Finset.mem_sdiff.mp hm).2⟩
  have hreach := hs.reachable
  have ht := reachable_topology hr ho he hreach
  have hl := reachable_edge_locality he hreach
  have hb := reachable_requestBalance hr ho he hreach
  have hc := reachable_creditRouting hr ho he hreach
  have hback := reachable_backpointer hG hr ho he hreach
  have hnoCS : ∀ i, s.mode i ≠ .inCS := by
    intro i
    by_cases hi : i = u
    · simpa [hi] using hcs
    · simp [ha.2 i hi]
  have hquiet := reachable_quiet hreach
  have hclosed : ∀ i, s.queue i ≠ [] → s.queue (s.holder i) ≠ [] := by
    intro i hi
    have howner : i ∉ s.owners := by
      intro hown
      exact hi (hquiet i hown (hnoCS i) (by simp [hready i]))
    have hself : s.holder i ≠ i := fun h => howner ((holder_self_iff_owner hl ht hback i).mp h)
    have hasked := reachable_readyAsks hreach i (hready i) hi hself
    rcases credit_has_witness hb howner hasked (by simp [hfl]) with
      ⟨r, hm, _⟩ | ⟨j, hji, hm⟩
    · exact False.elim (hpend r hm)
    · have heq := hc.queue_holder i j (Ne.symm hji) hm
      rw [heq]
      exact List.ne_nil_of_mem hm
  have hu : s.mode u = .requesting := by
    cases hm : s.mode u with
    | idle => exact False.elim (ha.1 hm)
    | requesting => rfl
    | inCS => exact False.elim (hcs hm)
  have hqu : s.queue u ≠ [] := by
    have hh := reachable_selfQueued he hreach u
    simp only [hu, if_true] at hh
    intro hn
    simp [hn] at hh
  obtain ⟨root, hroot, hroute⟩ := ht.routes
  have hown : root ∈ s.owners := by simpa [Location, hfl] using hroot
  obtain ⟨p, _, hp⟩ := hroute u
  exact follows_closed hclosed hp hqu (hquiet root hown (hnoCS root) (by simp [hready root]))

/-- A finite legal completion exists; no fairness premise is assumed for this witness. -/
theorem isolated_completion_exists {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G.IsTree)
    (u owner : Fin n) {route} (hr : Routes G route owner) (ho : route owner = owner)
    (he : ∀ i, route i = i ∨ G.Adj i (route i)) :
    ∃ s, IsolatedExecution u owner route s ∧ s.mode u = .inCS := by
  classical
  let P : ℤ → Prop := fun z => ∃ s, IsolatedExecution u owner route s ∧
    ActiveClient s u ∧ serviceRank s = z
  have hbounded : ∃ b, ∀ z, P z → z ≤ b := by
    refine ⟨6 * G.dist u owner + 5 * n, ?_⟩
    rintro z ⟨s, hs, _, rfl⟩
    exact service_rank_bounded hG hr ho he hs
  have hex : ∃ z, P z := by
    let s := next (initial owner route) (.request u)
    refine ⟨serviceRank s, s, ?_, ?_, rfl⟩
    · exact .step .initial ⟨by simp [Enabled, initial], rfl⟩
        (by intro i hi; cases hi; rfl)
    · constructor
      · simp [s, next, initial]
      · intro i hi; simp [s, next, initial, hi]
  obtain ⟨z, ⟨s, hs, ha, hz⟩, hmax⟩ := Int.exists_greatest_of_bdd hbounded hex
  refine ⟨s, hs, ?_⟩
  by_contra hcs
  obtain ⟨e, hservice, hen⟩ := requesting_has_service hG hr ho he hs ha hcs
  have hnext : IsolatedExecution u owner route (next s e) := by
    apply hs.step ⟨hen, rfl⟩
    intro i hi
    subst e
    contradiction
  have hanext := active_service (reachable_selfQueued he hs.reachable) ha hservice
  have hm := hmax (serviceRank (next s e)) ⟨_, hnext, hanext, rfl⟩
  rw [service_rank_step (reachable_safety hs.reachable) hservice hen, hz] at hm
  omega

theorem raymond_diameter_tightness {n : ℕ} (hn : 2 ≤ n) {G : SimpleGraph (Fin n)}
    (hG : G.IsTree) : ∃ u owner route s,
      Routes G route owner ∧ route owner = owner ∧
      (∀ i, route i = i ∨ G.Adj i (route i)) ∧
      IsolatedExecution u owner route s ∧ s.mode u = .inCS ∧
      s.requestSends + s.privilegeSends = 2 * treeDiameter G := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨u, owner, hd⟩ := diameter_attained G
  obtain ⟨route, hr, ho, he⟩ := tree_initialization_exists hG owner
  obtain ⟨s, hs, hcs⟩ := isolated_completion_exists hG u owner hr ho he
  refine ⟨u, owner, route, s, hr, ho, he, hs, hcs, ?_⟩
  rw [(isolated_request_message_bound hG hr ho he hs hcs).2.2, hd]


/-- A parent map whose natural depth decreases exactly once along each parent edge. -/
structure RootedShape (V : Type*) where
  root : V
  parent : V → V
  depth : V → ℕ
  root_depth : depth root = 0
  descend : ∀ v, v ≠ root → depth v = depth (parent v) + 1

namespace RootedShape
variable (S : RootedShape V)

def graph : SimpleGraph V where
  Adj u v := (u ≠ S.root ∧ S.parent u = v) ∨ (v ≠ S.root ∧ S.parent v = u)
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := ⟨by
    intro u h
    rcases h with h | h <;> have hd := S.descend u h.1 <;> rw [h.2] at hd <;> omega⟩

theorem parent_ne {v : V} (hv : v ≠ S.root) : S.parent v ≠ v := by
  have h := S.descend v hv
  intro he
  rw [he] at h
  omega

theorem walk_to_root (v : V) : ∃ p : S.graph.Walk v S.root, p.length = S.depth v := by
  have hall : ∀ d v, S.depth v = d → ∃ p : S.graph.Walk v S.root, p.length = d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro v hv
      by_cases he : v = S.root
      · subst v
        exact ⟨.nil, by simpa [S.root_depth] using hv⟩
      · have hd := S.descend v he
        obtain ⟨p, hp⟩ := ih (S.depth (S.parent v)) (by omega) (S.parent v) rfl
        have hadj : S.graph.Adj v (S.parent v) := Or.inl ⟨he, rfl⟩
        exact ⟨.cons hadj p, by simp only [SimpleGraph.Walk.length_cons, hp]; omega⟩
  exact hall (S.depth v) v rfl

theorem connected : S.graph.Connected := by
  have : Nonempty V := ⟨S.root⟩
  refine ⟨?_⟩
  intro u v
  obtain ⟨p, _⟩ := S.walk_to_root u
  obtain ⟨q, _⟩ := S.walk_to_root v
  exact ⟨p.append q.reverse⟩

theorem edge_finset [Fintype V] [DecidableEq V] [DecidableRel S.graph.Adj] :
    S.graph.edgeFinset = (Finset.univ.erase S.root).image (fun v => s(v, S.parent v)) := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    change ((u ≠ S.root ∧ S.parent u = v) ∨ (v ≠ S.root ∧ S.parent v = u)) ↔ _
    constructor
    · rintro (⟨hu, rfl⟩ | ⟨hv, rfl⟩)
      · exact Finset.mem_image.mpr ⟨u, by simp [hu], rfl⟩
      · exact Finset.mem_image.mpr ⟨v, by simp [hv], Sym2.eq_swap⟩
    · rintro h
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp h
      have hne := (Finset.mem_erase.mp hw).1
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨hne, rfl⟩
      · exact Or.inr ⟨hne, rfl⟩

theorem isTree [Finite V] : S.graph.IsTree := by
  classical
  let _ := Fintype.ofFinite V
  have hinj : Set.InjOn (fun v => s(v, S.parent v)) (↑(Finset.univ.erase S.root) : Set V) := by
    intro u hu v hv he
    rcases Sym2.eq_iff.mp he with h | h
    · exact h.1
    · have hd1 := S.descend u (Finset.mem_erase.mp hu).1
      have hd2 := S.descend v (Finset.mem_erase.mp hv).1
      rw [h.2] at hd1
      rw [← h.1] at hd2
      omega
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨S.connected, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, S.edge_finset,
    Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem (Finset.mem_univ S.root)]
  rw [Finset.card_univ, Nat.card_eq_fintype_card]
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨S.root⟩
  omega

theorem depth_walk_le {u v : V} (p : S.graph.Walk u v) :
    S.depth u ≤ S.depth v + p.length := by
  induction p with
  | nil => simp
  | @cons u w v he p ih =>
    have h : S.depth u ≤ S.depth w + 1 := by
      rcases he with ⟨hu, hp⟩ | ⟨hw, hp⟩
      · have hd := S.descend u hu; rw [hp] at hd; omega
      · have hd := S.descend w hw; rw [hp] at hd; omega
    simp only [SimpleGraph.Walk.length_cons]
    omega

theorem distance_root (v : V) : S.graph.dist v S.root = S.depth v := by
  obtain ⟨p, hp⟩ := S.walk_to_root v
  have hupper := SimpleGraph.dist_le p
  obtain ⟨q, hq⟩ := S.connected.exists_walk_length_eq_dist v S.root
  have hlower := S.depth_walk_le q
  rw [S.root_depth, hq] at hlower
  omega

end RootedShape

theorem potential_walk_bound {G : SimpleGraph V} (f : V → ℤ)
    (hf : ∀ u v, G.Adj u v → f u ≤ f v + 1) {u v : V} (p : G.Walk u v) :
    f u - f v ≤ p.length := by
  induction p with
  | nil => simp
  | cons he p ih =>
    have h := hf _ _ he
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    omega

theorem potential_distance_bound (G : SimpleGraph V) (hG : G.Connected) (f : V → ℤ)
    (hf : ∀ u v, G.Adj u v → f u ≤ f v + 1) (u v : V) :
    f u - f v ≤ G.dist u v := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
  simpa [hp] using potential_walk_bound f hf p


/-- All words up to a fixed length, including the empty root. -/
def KaryNode (k h : ℕ) := {w : List (Fin k) // w.length ≤ h}

def karyNodeEquiv (k h : ℕ) : KaryNode k h ≃ (Σ d : Fin (h + 1), List.Vector (Fin k) d.val) where
  toFun w := ⟨⟨w.val.length, by have := w.prop; omega⟩, ⟨w.val, rfl⟩⟩
  invFun w := ⟨w.2.val, by rw [w.2.prop]; exact Nat.le_of_lt_succ w.1.isLt⟩
  left_inv _ := rfl
  right_inv := by rintro ⟨⟨d, hd⟩, ⟨w, hw⟩⟩; cases hw; rfl

instance (k h : ℕ) : Fintype (KaryNode k h) :=
  Fintype.ofEquiv (Σ d : Fin (h + 1), List.Vector (Fin k) d.val) (karyNodeEquiv k h).symm

def karyShape (k h : ℕ) : RootedShape (KaryNode k h) where
  root := ⟨[], by simp⟩
  parent w := ⟨w.val.dropLast, by have := w.prop; simp only [List.length_dropLast]; omega⟩
  depth w := w.val.length
  root_depth := rfl
  descend := by
    intro w hw
    have hn : w.val ≠ [] := fun he => hw (Subtype.ext he)
    have hp : 0 < w.val.length := List.length_pos_iff.mpr hn
    simp only [List.length_dropLast]
    omega

abbrev karyGraph (k h : ℕ) : SimpleGraph (KaryNode k h) := (karyShape k h).graph

def karyNodeCount (k h : ℕ) : ℕ := ∑ j ∈ Finset.range (h + 1), k ^ j

theorem kary_card (k h : ℕ) : Fintype.card (KaryNode k h) = karyNodeCount k h := by
  rw [Fintype.card_congr (karyNodeEquiv k h)]
  simp [karyNodeCount, Fintype.card_sigma, Fin.sum_univ_eq_sum_range]

def constantLeaf {k h : ℕ} (a : Fin k) : KaryNode k h :=
  ⟨List.replicate h a, by simp⟩

theorem kary_height {k h : ℕ} (hk : 1 ≤ k) :
    treeHeight (karyGraph k h) (karyShape k h).root = h := by
  apply le_antisymm
  · apply Finset.sup_le
    intro v _
    rw [SimpleGraph.dist_comm, (karyShape k h).distance_root]
    exact v.prop
  · have hb := distance_le_height (karyGraph k h) (karyShape k h).root
      (constantLeaf (h := h) ⟨0, by omega⟩)
    rw [SimpleGraph.dist_comm, (karyShape k h).distance_root] at hb
    simpa [karyShape, constantLeaf] using hb

/-- The two root branches have opposite signed depths. -/
def branchPotential {k h : ℕ} (v : KaryNode k h) : ℤ :=
  if v.val.head?.map Fin.val = some 0 then v.val.length else -(v.val.length : ℤ)

theorem branch_parent_difference {k h : ℕ} (v : KaryNode k h) :
    branchPotential v ≤ branchPotential ((karyShape k h).parent v) + 1 ∧
      branchPotential ((karyShape k h).parent v) ≤ branchPotential v + 1 := by
  rcases v with ⟨w, hw⟩
  cases w with
  | nil => norm_num [branchPotential, karyShape]
  | cons a w =>
    cases w with
    | nil =>
      by_cases ha : a.val = 0 <;> simp [branchPotential, karyShape, ha]
    | cons b w =>
      by_cases ha : a.val = 0
      · simp [branchPotential, karyShape, List.dropLast_cons_cons, ha]; omega
      · simp [branchPotential, karyShape, List.dropLast_cons_cons, ha]

theorem kary_diameter {k h : ℕ} (hk : 2 ≤ k) (hh : 1 ≤ h) :
    treeDiameter (karyGraph k h) = 2 * h := by
  have hu := diameter_le_twice_height (karyGraph k h) (karyShape k h).connected
    (karyShape k h).root
  rw [kary_height (by omega : 1 ≤ k)] at hu
  let a : KaryNode k h := constantLeaf ⟨0, by omega⟩
  let b : KaryNode k h := constantLeaf ⟨1, by omega⟩
  have hpotential : ∀ u v, (karyGraph k h).Adj u v →
      branchPotential u ≤ branchPotential v + 1 := by
    intro u v hadj
    rcases hadj with ⟨_, hp⟩ | ⟨_, hp⟩
    · rw [← hp]; exact (branch_parent_difference u).1
    · rw [← hp]; exact (branch_parent_difference v).2
  have hl := potential_distance_bound (karyGraph k h) (karyShape k h).connected
    branchPotential hpotential a b
  have ha : branchPotential a = h := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
    simp [a, constantLeaf, branchPotential, List.replicate_succ]
  have hb : branchPotential b = -(h : ℤ) := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
    simp [b, constantLeaf, branchPotential, List.replicate_succ]
  rw [ha, hb] at hl
  have hd := distance_le_diameter (karyGraph k h) a b
  omega

@[simp] theorem kary_count_zero (k : ℕ) : karyNodeCount k 0 = 1 := by
  simp [karyNodeCount]

theorem kary_count_succ (k h : ℕ) :
    karyNodeCount k (h + 1) = karyNodeCount k h + k ^ (h + 1) := by
  exact Finset.sum_range_succ _ _

theorem kary_count_bounds {k : ℕ} (hk : 2 ≤ k) (h : ℕ) :
    k ^ h ≤ karyNodeCount k h ∧ karyNodeCount k h < k ^ (h + 1) := by
  induction h with
  | zero => simpa using (show 1 < k by omega)
  | succ h ih =>
    rw [kary_count_succ]
    constructor
    · omega
    · rw [pow_succ k (h + 1)]
      nlinarith [pow_pos (by omega : 0 < k) (h + 1)]

theorem kary_count_geometric {k : ℕ} (hk : 2 ≤ k) (h : ℕ) :
    (k - 1) * karyNodeCount k h + 1 = k ^ (h + 1) := by
  have hk' : k - 1 + 1 = k := by omega
  induction h with
  | zero => simp; omega
  | succ h ih =>
    rw [kary_count_succ, Nat.mul_add, Nat.add_right_comm, ih]
    rw [pow_succ k (h + 1)]
    calc
      _ = k ^ (h + 1) * (k - 1 + 1) := by ring
      _ = _ := by rw [hk']

theorem kary_count_quotient {k : ℕ} (hk : 2 ≤ k) (h : ℕ) :
    karyNodeCount k h = (k ^ (h + 1) - 1) / (k - 1) := by
  have he := kary_count_geometric hk h
  have he' : k ^ (h + 1) - 1 = (k - 1) * karyNodeCount k h := by omega
  rw [he', Nat.mul_div_right _ (by omega : 0 < k - 1)]

theorem kary_height_log {k : ℕ} (hk : 2 ≤ k) (h : ℕ) :
    h = Nat.log k (karyNodeCount k h) := by
  exact (Nat.log_eq_of_pow_le_of_lt_pow (kary_count_bounds hk h).1
    (kary_count_bounds hk h).2).symm

theorem complete_kary_tree_metrics {k h : ℕ} (hk : 2 ≤ k) (hh : 1 ≤ h) :
    (karyGraph k h).IsTree ∧
    Fintype.card (KaryNode k h) = karyNodeCount k h ∧
    karyNodeCount k h = (k ^ (h + 1) - 1) / (k - 1) ∧
    treeHeight (karyGraph k h) (karyShape k h).root = h ∧
    treeDiameter (karyGraph k h) = 2 * h ∧
    maximumMessages (karyGraph k h) = 4 * h ∧
    h = Nat.log k (karyNodeCount k h) ∧
    maximumMessages (karyGraph k h) = 4 * Nat.log k (karyNodeCount k h) := by
  have hd := kary_diameter hk hh
  have hl := kary_height_log hk h
  refine ⟨(karyShape k h).isTree, kary_card k h, kary_count_quotient hk h,
    kary_height (by omega), hd, ?_, hl, ?_⟩ <;>
    (simp only [maximumMessages, hd, ← hl]; omega)

/-- Relabelling preserves graph distance, hence the operational worst case. -/
theorem iso_distance {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : G.Connected) (u v : V) : H.dist (e u) (e v) = G.dist u v := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
  have hup := H.dist_le (p.map e.toHom)
  rw [SimpleGraph.Walk.length_map, hp] at hup
  have hH := e.connected_iff.mp hG
  obtain ⟨p', hp'⟩ := hH.exists_walk_length_eq_dist (e u) (e v)
  have hdown := G.dist_le (p'.map e.symm.toHom)
  rw [SimpleGraph.Walk.length_map, hp'] at hdown
  exact le_antisymm hup (by simpa using hdown)

theorem iso_diameter {W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (hG : G.Connected) :
    treeDiameter H = treeDiameter G := by
  apply le_antisymm
  · apply Finset.sup_le
    intro u _
    apply Finset.sup_le
    intro v _
    obtain ⟨u, rfl⟩ := e.surjective u
    obtain ⟨v, rfl⟩ := e.surjective v
    rw [iso_distance e hG]
    exact distance_le_diameter G u v
  · apply Finset.sup_le
    intro u _
    apply Finset.sup_le
    intro v _
    rw [← iso_distance e hG]
    exact distance_le_diameter H (e u) (e v)

/-- This assertion contains actual finite enabled protocol executions, not just a cost function. -/
def AttainedOnFin [Fintype V] (G : SimpleGraph V) (cost : ℕ) : Prop :=
  ∃ u owner route s, Routes (G.overFin rfl) route owner ∧ route owner = owner ∧
    (∀ i, route i = i ∨ (G.overFin rfl).Adj i (route i)) ∧
    IsolatedExecution u owner route s ∧ s.mode u = .inCS ∧
    s.requestSends + s.privilegeSends = cost

theorem finite_tree_operational_attainment [Fintype V] (G : SimpleGraph V)
    (hG : G.IsTree) (hn : 2 ≤ Fintype.card V) : AttainedOnFin G (maximumMessages G) := by
  have ht := (G.overFinIso rfl).isTree_iff.mp hG
  have hex := raymond_diameter_tightness hn ht
  rw [iso_diameter (G.overFinIso rfl) hG.connected] at hex
  exact hex

theorem kary_operational_attainment {k h : ℕ} (hk : 2 ≤ k) (hh : 1 ≤ h) :
    AttainedOnFin (karyGraph k h) (4 * h) := by
  have hn : 2 ≤ Fintype.card (KaryNode k h) := by
    rw [kary_card]
    have hb := (kary_count_bounds hk h).1
    have hp : k ≤ k ^ h := Nat.le_pow (by omega)
    omega
  have hex := finite_tree_operational_attainment (karyGraph k h) (karyShape k h).isTree hn
  simpa only [maximumMessages, kary_diameter hk hh, ← Nat.mul_assoc] using hex

/-- Every shortest simple path uses at most all vertices once. -/
theorem diameter_le_card_sub_one [Fintype V] (G : SimpleGraph V) (hG : G.Connected) :
    treeDiameter G ≤ Fintype.card V - 1 := by
  apply Finset.sup_le
  intro u _
  apply Finset.sup_le
  intro v _
  obtain ⟨p, hp, hl⟩ := hG.exists_path_of_dist u v
  have hb := hp.length_lt
  omega

def lineShape (N : ℕ) (hN : 1 ≤ N) : RootedShape (Fin N) where
  root := ⟨0, by omega⟩
  parent v := ⟨v.val - 1, by have := v.isLt; omega⟩
  depth := Fin.val
  root_depth := rfl
  descend := by intro v hv; have : v.val ≠ 0 := fun he => hv (Fin.ext he); simp; omega

abbrev lineGraph (N : ℕ) (hN : 1 ≤ N) := (lineShape N hN).graph

theorem reg_line_graph {N : ℕ} (hN : 1 ≤ N) :
    (lineGraph N hN).IsTree ∧ treeDiameter (lineGraph N hN) = N - 1 ∧
      maximumMessages (lineGraph N hN) = 2 * (N - 1) := by
  have hb := diameter_le_card_sub_one (lineGraph N hN) (lineShape N hN).connected
  have hl := distance_le_diameter (lineGraph N hN)
    (⟨N - 1, by omega⟩ : Fin N) (lineShape N hN).root
  rw [(lineShape N hN).distance_root] at hl
  simp only [Fintype.card_fin] at hb
  have hd : treeDiameter (lineGraph N hN) = N - 1 := by exact le_antisymm hb hl
  exact ⟨(lineShape N hN).isTree, hd, congrArg (2 * ·) hd⟩

def starShape (N : ℕ) (hN : 1 ≤ N) : RootedShape (Fin N) where
  root := ⟨0, by omega⟩
  parent _ := ⟨0, by omega⟩
  depth v := if v.val = 0 then 0 else 1
  root_depth := by simp
  descend := by
    intro v hv
    have hv' : v.val ≠ 0 := fun he => hv (Fin.ext he)
    simp [hv']

abbrev starGraph (N : ℕ) (hN : 1 ≤ N) := (starShape N hN).graph

theorem star_height {N : ℕ} (hN : 2 ≤ N) :
    treeHeight (starGraph N (by omega)) (starShape N (by omega)).root = 1 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro v _
    rw [SimpleGraph.dist_comm, (starShape N (by omega)).distance_root]
    simp only [starShape]; split <;> omega
  · have hb := distance_le_height (starGraph N (by omega))
      (starShape N (by omega)).root ⟨1, by omega⟩
    rw [SimpleGraph.dist_comm, (starShape N (by omega)).distance_root] at hb
    simpa [starShape] using hb

theorem reg_star_graph {N : ℕ} (hN : 3 ≤ N) :
    (starGraph N (by omega)).IsTree ∧
    treeHeight (starGraph N (by omega)) (starShape N (by omega)).root = 1 ∧
    treeDiameter (starGraph N (by omega)) = 2 ∧
    maximumMessages (starGraph N (by omega)) = 4 := by
  have hc := (starShape N (by omega)).connected
  have hu := diameter_le_twice_height (starGraph N (by omega)) hc
    (starShape N (by omega)).root
  rw [star_height (by omega : 2 ≤ N)] at hu
  have hn : (⟨1, by omega⟩ : Fin N) ≠ ⟨2, by omega⟩ := by
    intro he; have := congrArg Fin.val he; simp at this
  have ha : ¬(starGraph N (by omega)).Adj ⟨1, by omega⟩ ⟨2, by omega⟩ := by
    simp [RootedShape.graph, starShape, Fin.ext_iff]
  have hl := hc.one_lt_dist_of_ne_of_not_adj hn ha
  have hd := distance_le_diameter (starGraph N (by omega))
    ⟨1, by omega⟩ ⟨2, by omega⟩
  have he : treeDiameter (starGraph N (by omega)) = 2 := by
    change 1 < (starGraph N (by omega)).dist ⟨1, by omega⟩ ⟨2, by omega⟩ at hl
    omega
  exact ⟨(starShape N (by omega)).isTree, star_height (by omega), he,
    by simp [maximumMessages, he]⟩

theorem reg_binary_tree_h3 :
    Fintype.card (KaryNode 2 3) = 15 ∧ treeDiameter (karyGraph 2 3) = 6 ∧
    maximumMessages (karyGraph 2 3) = 12 ∧ maximumMessages (karyGraph 2 3) ≠ 8 ∧
    AttainedOnFin (karyGraph 2 3) 12 := by
  have hd := kary_diameter (k := 2) (h := 3) (by decide) (by decide)
  have ha := kary_operational_attainment (k := 2) (h := 3) (by decide) (by decide)
  refine ⟨?_, hd, ?_, ?_, ha⟩
  · rw [kary_card]; norm_num [karyNodeCount, Finset.sum_range_succ]
  · change 2 * treeDiameter (karyGraph 2 3) = 12; rw [hd]
  · change 2 * treeDiameter (karyGraph 2 3) ≠ 8; rw [hd]; decide

theorem line_operational_attainment {N : ℕ} (hN : 2 ≤ N) :
    AttainedOnFin (lineGraph N (by omega)) (2 * (N - 1)) := by
  have h := finite_tree_operational_attainment (lineGraph N (by omega))
    (lineShape N (by omega)).isTree (by simpa using hN)
  rwa [(reg_line_graph (by omega : 1 ≤ N)).2.2] at h

theorem star_operational_attainment {N : ℕ} (hN : 3 ≤ N) :
    AttainedOnFin (starGraph N (by omega)) 4 := by
  have h := finite_tree_operational_attainment (starGraph N (by omega))
    (starShape N (by omega)).isTree (by simpa using (show 2 ≤ N by omega))
  rwa [(reg_star_graph hN).2.2.2] at h

/-- For each fixed branching factor, the family cost is logarithmic in its actual vertex count. -/
theorem kary_cost_isBigO {k : ℕ} (hk : 2 ≤ k) :
    Asymptotics.IsBigO Filter.atTop
      (fun h : ℕ => (maximumMessages (karyGraph k h) : ℝ))
      (fun h : ℕ => (Nat.log k (Fintype.card (KaryNode k h)) : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨4, Filter.eventually_atTop.mpr ⟨1, ?_⟩⟩
  intro h hh
  have hm := (complete_kary_tree_metrics hk hh).2.2.2.2.2.2.2
  rw [kary_card, hm]
  simp

structure DistributedRaymondTreeMessageComplexitySuite : Prop where
  completed_cost_bound : ∀ {n : ℕ} {G : SimpleGraph (Fin n)}, G.IsTree →
    ∀ {u owner : Fin n} {route}, Routes G route owner → route owner = owner →
    (∀ i, route i = i ∨ G.Adj i (route i)) → ∀ {s : State n},
    IsolatedExecution u owner route s → s.mode u = .inCS →
    s.requestSends + s.privilegeSends ≤ 2 * treeDiameter G
  finite_completion : ∀ {n : ℕ} {G : SimpleGraph (Fin n)}, G.IsTree →
    ∀ (u owner : Fin n) {route}, Routes G route owner → route owner = owner →
    (∀ i, route i = i ∨ G.Adj i (route i)) →
    ∃ s, IsolatedExecution u owner route s ∧ s.mode u = .inCS
  attained_diameter : ∀ {n : ℕ}, 2 ≤ n → ∀ {G : SimpleGraph (Fin n)}, G.IsTree →
    ∃ u owner route s, Routes G route owner ∧ route owner = owner ∧
      (∀ i, route i = i ∨ G.Adj i (route i)) ∧
      IsolatedExecution u owner route s ∧ s.mode u = .inCS ∧
      s.requestSends + s.privilegeSends = 2 * treeDiameter G
  height_bound : ∀ {n : ℕ} {G : SimpleGraph (Fin n)}, G.IsTree →
    ∀ {u owner : Fin n} {route}, Routes G route owner → route owner = owner →
    (∀ i, route i = i ∨ G.Adj i (route i)) → ∀ {s : State n},
    IsolatedExecution u owner route s → s.mode u = .inCS → ∀ root,
    treeDiameter G ≤ 2 * treeHeight G root ∧
      s.requestSends + s.privilegeSends ≤ 4 * treeHeight G root
  root_path_equality : ∀ {n : ℕ} (G : SimpleGraph (Fin n)), G.Connected →
    ∀ root u v, G.dist root u = treeHeight G root → G.dist root v = treeHeight G root →
    G.dist u v = G.dist u root + G.dist root v →
    G.dist u v = 2 * treeHeight G root ∧ treeDiameter G = 2 * treeHeight G root
  kary_metrics : ∀ {k h : ℕ}, 2 ≤ k → 1 ≤ h →
    (karyGraph k h).IsTree ∧ Fintype.card (KaryNode k h) = karyNodeCount k h ∧
    karyNodeCount k h = (k ^ (h + 1) - 1) / (k - 1) ∧
    treeHeight (karyGraph k h) (karyShape k h).root = h ∧
    treeDiameter (karyGraph k h) = 2 * h ∧ maximumMessages (karyGraph k h) = 4 * h ∧
    h = Nat.log k (karyNodeCount k h) ∧
    maximumMessages (karyGraph k h) = 4 * Nat.log k (karyNodeCount k h)
  kary_attainment : ∀ {k h : ℕ}, 2 ≤ k → 1 ≤ h → AttainedOnFin (karyGraph k h) (4 * h)
  logarithmic_cost : ∀ {k : ℕ}, 2 ≤ k → Asymptotics.IsBigO Filter.atTop
    (fun h : ℕ => (maximumMessages (karyGraph k h) : ℝ))
    (fun h : ℕ => (Nat.log k (Fintype.card (KaryNode k h)) : ℝ))
  local_token : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) u, messages G u u = 0
  line_metrics : ∀ {N : ℕ} (hN : 1 ≤ N),
    (lineGraph N hN).IsTree ∧ treeDiameter (lineGraph N hN) = N - 1 ∧
      maximumMessages (lineGraph N hN) = 2 * (N - 1)
  star_metrics : ∀ {N : ℕ} (hN : 3 ≤ N),
    (starGraph N (by omega)).IsTree ∧
    treeHeight (starGraph N (by omega)) (starShape N (by omega)).root = 1 ∧
    treeDiameter (starGraph N (by omega)) = 2 ∧
    maximumMessages (starGraph N (by omega)) = 4
  binary_regression : Fintype.card (KaryNode 2 3) = 15 ∧
    treeDiameter (karyGraph 2 3) = 6 ∧ maximumMessages (karyGraph 2 3) = 12 ∧
    maximumMessages (karyGraph 2 3) ≠ 8 ∧ AttainedOnFin (karyGraph 2 3) 12

theorem distributed_raymond_tree_message_complexity_master_suite :
    DistributedRaymondTreeMessageComplexitySuite where
  completed_cost_bound := raymond_bound_diameter
  finite_completion := isolated_completion_exists
  attained_diameter := raymond_diameter_tightness
  height_bound := raymond_bound_height
  root_path_equality := raymond_height_tightness
  kary_metrics := complete_kary_tree_metrics
  kary_attainment := kary_operational_attainment
  logarithmic_cost := kary_cost_isBigO
  local_token := reg_token_holder
  line_metrics := reg_line_graph
  star_metrics := reg_star_graph
  binary_regression := reg_binary_tree_h3

end DistributedRaymondTreeMessageComplexity
