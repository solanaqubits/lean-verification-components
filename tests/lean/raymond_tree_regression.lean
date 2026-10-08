/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedRaymondTreeMutex
import Mathlib.Tactic.FinCases

-- Kernel reduction of the complete competing-request trace exceeds the default depth.
set_option maxRecDepth 4096

namespace RaymondTreeRegression
open DistributedRaymondTreeMutex

def handler (e : Event n) (i : NodeId n) : List (Event n) :=
  [e, .assign i, .makeRequest i]

def enterNeighbour : List (Event 2) :=
  handler (.request 1) 1 ++ handler (.receive ⟨1, 0, 0⟩) 0 ++ handler (.deliver 0 1) 1

example : ValidEvents twoNodeInitial enterNeighbour := by decide
example : (execute twoNodeInitial enterNeighbour).mode 1 = .inCS := by decide
example : (execute twoNodeInitial enterNeighbour).requestSends = 1 ∧
    (execute twoNodeInitial enterNeighbour).privilegeSends = 1 := by decide
example : ¬ Enabled (execute twoNodeInitial enterNeighbour) (.deliver 0 1) := by decide
example : ¬ Enabled (execute twoNodeInitial enterNeighbour) (.receive ⟨1, 0, 0⟩) := by decide
example : ¬ Enabled twoNodeInitial (.receive ⟨1, 0, 0⟩) := by decide
example : ¬ Enabled twoNodeInitial (.deliver 0 1) := by decide
example : ¬ Enabled (next twoNodeInitial (.request 1)) (.request 1) := by decide
example : ¬ Enabled (next twoNodeInitial (.request 1)) (.receive ⟨0, 1, 0⟩) := by decide

example : ∃ s : State 2, Reachable 0 (fun _ => 0) s ∧ s.holder 0 = 1 ∧
    s.holder 1 = 0 ∧ s.flight = some (0, 1) ∧ s.owners = ∅ :=
  raw_holder_two_cycle_reachable

def retained : List (Event 2) := handler (.request 0) 0 ++ handler (.leave 0) 0 ++
  handler (.request 0) 0
example : ValidEvents twoNodeInitial retained := by decide
example : (execute twoNodeInitial retained).mode 0 = .inCS := by decide
example : (execute twoNodeInitial retained).requestSends = 0 ∧
    (execute twoNodeInitial retained).privilegeSends = 0 := by decide

def starInitial : State 3 := initial 0 (fun _ => 0)
def starRequests : List (Event 3) := handler (.request 0) 0 ++
  handler (.request 1) 1 ++ handler (.request 2) 2 ++
  handler (.receive ⟨1, 0, 0⟩) 0 ++ handler (.receive ⟨2, 0, 0⟩) 0
example : ValidEvents starInitial starRequests := by decide
example : (execute starInitial starRequests).queue 0 = [1, 2] := by decide
example : (execute starInitial starRequests).owners = {0} := by decide

def starHandoff := starRequests ++ handler (.leave 0) 0
example : ValidEvents starInitial starHandoff := by decide
example : (execute starInitial starHandoff).flight = some (0, 1) := by decide
example : (⟨0, 1, 0⟩ : Request 3) ∈ (execute starInitial starHandoff).sent := by decide

-- The return REQUEST overtakes PRIVILEGE on the same edge. No FIFO assumption.
def reordered := starHandoff ++ handler (.receive ⟨0, 1, 0⟩) 1
example : ValidEvents starInitial reordered := by decide
example : (execute starInitial reordered).queue 1 = [1, 0] := by decide
example : (execute starInitial reordered).asked 1 = true := by decide
example : (execute starInitial reordered).requestSends = 3 := by decide

def starFirst := reordered ++ handler (.deliver 0 1) 1
example : ValidEvents starInitial starFirst := by decide
example : (execute starInitial starFirst).mode 1 = .inCS ∧
    (execute starInitial starFirst).mode 2 = .requesting := by decide

def starBoth := starFirst ++ handler (.leave 1) 1 ++ handler (.deliver 1 0) 0 ++
  handler (.deliver 0 2) 2
example : ValidEvents starInitial starBoth := by decide
example : (execute starInitial starBoth).mode 2 = .inCS ∧
    (execute starInitial starBoth).mode 1 = .idle := by decide
example : (execute starInitial starBoth).requestSends = 3 ∧
    (execute starInitial starBoth).privilegeSends = 3 := by decide

def chainInitial : State 5 := initial 0 (fun i => ⟨i.val - 1, by omega⟩)
def chainEntry : List (Event 5) := handler (.request 4) 4 ++
  handler (.receive ⟨4, 3, 0⟩) 3 ++ handler (.receive ⟨3, 2, 0⟩) 2 ++
  handler (.receive ⟨2, 1, 0⟩) 1 ++ handler (.receive ⟨1, 0, 0⟩) 0 ++
  handler (.deliver 0 1) 1 ++ handler (.deliver 1 2) 2 ++
  handler (.deliver 2 3) 3 ++ handler (.deliver 3 4) 4
example : ValidEvents chainInitial chainEntry := by decide
example : (execute chainInitial chainEntry).mode 4 = .inCS := by decide
example : (execute chainInitial chainEntry).requestSends = 4 ∧
    (execute chainInitial chainEntry).privilegeSends = 4 := by decide

-- Generic invariants retain arbitrary node count and initialization hypotheses.
example {n : ℕ} {owner : NodeId n} {route} {s : State n}
    (h : Reachable owner route s) : tokenCount s = 1 := privilege_conservation_invariant h
example {n : ℕ} {owner : NodeId n} {route} {s : State n}
    (h : Reachable owner route s) {i j} (hne : i ≠ j) (hi : s.mode i = .inCS) :
    s.mode j ≠ .inCS := fun hj => mutual_exclusion_safety h hne hi hj
example {n : ℕ} {G : SimpleGraph (NodeId n)} (hG : G.IsTree) (root : NodeId n) :
    ∃ route, Routes G route root ∧ route root = root ∧
      ∀ i, route i = i ∨ G.Adj i (route i) := tree_initialization_exists hG root
example {n : ℕ} {G : SimpleGraph (NodeId n)} (hG : G.IsTree) (root : NodeId n)
    {s : State n} (hs : Reachable root (treeRoute hG root) s) (i : NodeId n) :
    (s.queue i).Nodup := queue_nodup_preservation (treeRoute_routes hG root)
      (treeRoute_self hG root) (treeRoute_local hG root) hs i
example {n : ℕ} (ρ : Run n) (hf : WeakFairness ρ) (k : ℕ) (i : NodeId n) :
    ∃ l, k ≤ l ∧ (ρ.state l).phase i = .ready := handler_eventually_completes ρ hf k i

theorem pairTree : (⊤ : SimpleGraph (Fin 2)).IsTree :=
  ⟨SimpleGraph.connected_top, SimpleGraph.IsAcyclic.of_card_le_two (by simp)⟩

theorem pairRoutes : Routes (⊤ : SimpleGraph (Fin 2)) (fun _ => 0) 0 := by
  intro i
  fin_cases i
  · exact ⟨.nil, .nil, trivial⟩
  · refine ⟨.cons (by decide) .nil, by simp, ?_⟩
    exact And.intro rfl trivial

example : Topology (⊤ : SimpleGraph (Fin 2)) (execute twoNodeInitial transitTrace) :=
  reachable_topology pairRoutes rfl (by intro i; fin_cases i <;> decide)
    (execute_reachable transit_trace_valid)

example {n : ℕ} {G : SimpleGraph (NodeId n)} (hG : G.IsTree) (root : NodeId n)
    {s : State n} (hs : Reachable root (treeRoute hG root) s) : Backpointer s :=
  reachable_backpointer hG (treeRoute_routes hG root) (treeRoute_self hG root)
    (treeRoute_local hG root) hs

-- Liveness cannot be invoked by substituting an eventual-service assumption.
example {n : ℕ} {G : SimpleGraph (NodeId n)} (ρ : Run n) (hT : OnTree G ρ)
    (hd : ReliableDelivery ρ) (hf : WeakFairness ρ) (hc : FiniteCS ρ)
    {k i} (hw : (ρ.state k).mode i = .requesting) :
    ∃ l, k ≤ l ∧ (ρ.state l).mode i = .inCS :=
  starvation_freedom_under_liveness ρ hT hd hf hc hw

-- Exact message counts for arbitrary isolated executions, not a selected schedule.
example {n : ℕ} {G : SimpleGraph (NodeId n)} (hG : G.IsTree)
    {u owner : NodeId n} {s : State n}
    (h : IsolatedExecution u owner (treeRoute hG owner) s) (hcs : s.mode u = .inCS) :
    s.requestSends = G.dist u owner ∧ s.privilegeSends = G.dist u owner ∧
      s.requestSends + s.privilegeSends = 2 * G.dist u owner :=
  isolated_request_message_bound hG (treeRoute_routes hG owner) (treeRoute_self hG owner)
    (treeRoute_local hG owner) h hcs

example : DistributedRaymondTreeSuite := distributed_raymond_tree_master_suite

end RaymondTreeRegression
