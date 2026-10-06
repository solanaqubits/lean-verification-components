import Mathlib.Tactic.FinCases
import Verification.DistributedChandyMisraHaasDeadlock

open DistributedChandyMisraHaasDeadlock

namespace CMHRegression

def back : State 2 := enqueue { waiting with queue := [] } (outgoing twoCycle 0 1)
def done : State 2 := { back with queue := [], detected := {0} }

theorem two_cycle_trace : Reachable twoCycle done := by
  apply Execution.cons (Step.initiate initial 0 ⟨1, by decide⟩)
  apply Execution.cons (Step.forward waiting ⟨0,0,1⟩ [] [] (by decide) (by decide) ⟨0, by decide⟩)
  apply Execution.cons (Step.detect back ⟨0,1,0⟩ [] [] (by decide) rfl ⟨1, by decide⟩)
  exact .nil _

example : WaitCycle twoCycle 0 := cycle_detection_soundness two_cycle_trace (by decide)

def branch : WFG 3 := ⟨{(0,1), (0,2)}⟩
def branching : State 3 := enqueue initial (outgoing branch 0 0)
def absorbed : State 3 := { branching with queue := [] }

theorem branch_trace : Reachable branch absorbed := by
  apply Execution.cons (Step.initiate initial 0 ⟨1, by decide⟩)
  apply Execution.cons (Step.absorb branching ⟨0,0,1⟩ [] [⟨0,0,2⟩] (by decide) (by unfold Blocked; decide))
  apply Execution.cons (Step.absorb _ ⟨0,0,2⟩ [] [] (by decide) (by unfold Blocked; decide))
  exact .nil _

example : absorbed.detected = ∅ := by decide
example : branching.queue.length = 2 := by decide

-- Three edges, with the initiator belonging to a genuine fixed cycle.
def triangle : WFG 3 := ⟨{(0,1), (1,2), (2,0)}⟩
example : ∃ t, Execution triangle initial t ∧ (0 : Fin 3) ∈ t.detected := by
  apply cycle_detection_path_exists
  exact ⟨2, .cons (q := (1 : Fin 3)) (by decide)
    (.cons (q := (2 : Fin 3)) (by decide) (.cons (by decide) (.nil _)))⟩

-- Duplicate initiation is permitted, but creates no false reports.
def duplicated : State 2 := enqueue waiting (outgoing twoCycle 0 0)
example : Reachable twoCycle duplicated := by
  exact .cons (.initiate _ _ ⟨1, by decide⟩) (.cons (.initiate _ _ ⟨1, by decide⟩) (.nil _))
example : duplicated.queue = [⟨0,0,1⟩, ⟨0,0,1⟩] := by decide

def selfLoop : WFG 1 := ⟨{(0,0)}⟩
example : WaitCycle selfLoop 0 := ⟨0, .cons (by decide) (.nil _)⟩
example (g : WFG 0) : Acyclic g := fun i => Fin.elim0 i
example (g : WFG 0) (s) (h : Reachable g s) : s.detected = ∅ :=
  phantom_deadlock_absence (fun i => Fin.elim0 i) h

-- No forged delivery is possible from an empty queue.
example (g : WFG n) (m : Probe n) (t) : ¬Step g initial (.deliver m) t := by
  intro h
  cases h <;> simp [initial] at *

-- Explicit reset invalidates all prior queued work; subsequent results use new graph.
example : EpochReachable branch initial := .reset (.initial triangle) branch
example {s : State 3} (h : EpochReachable branch s) : s.detected = ∅ := by
  apply phantom_deadlock_absence (acyclic_of_rank Fin.val ?_) (epoch_reachable_static h)
  intro p q he
  fin_cases p <;> fin_cases q <;> simp_all [WFG.waitsFor, branch]

-- These are kernel proofs of the dynamic and scheduling limitations, not expected failures.
example := dynamic_send_checks_insufficient
example := unfair_execution_counterexample
example {g : WFG n} (r : Run g) (hf : DeliveryFair r) {i t}
    (hc : WaitCycle g i) (hi : r.events t = .initiate i) :
    ∃ u, t ≤ u ∧ i ∈ (r.states u).detected := cycle_eventually_detected r hf hc hi

end CMHRegression
