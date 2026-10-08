import Verification.DistributedSuzukiKasamiMutex

open DistributedSuzukiKasamiMutex

namespace SuzukiKasamiRegression

-- Generic theorems retain arbitrary finite membership and every requesting node.
example (owner : Fin n) (s : State n) (h : Reachable owner s) : tokenCount s = 1 :=
  token_uniqueness_invariant h
example (owner : Fin n) (s : State n) (h : Reachable owner s) (i j : Fin n)
    (hne : i ≠ j) : ¬ (s.mode i = .inCS ∧ s.mode j = .inCS) := by
  rintro ⟨hi, hj⟩
  exact mutual_exclusion_safety h hne hi hj
example (ρ : Run n) (hd : ReliableDelivery ρ) (hf : WeakFairness ρ)
    (hc : FiniteCS ρ) (k : ℕ) (j : Fin n) (hj : (ρ.state k).mode j = .requesting) :
    ∃ l, k ≤ l ∧ (ρ.state l).mode j = .inCS :=
  starvation_freedom_under_liveness ρ hd hf hc hj
example (owner : Fin n) (s : State n) (h : Reachable owner s) (i j : Fin n) :
    s.rn i j ≤ s.rn j j ∧ s.token.ln j ≤ s.rn j j :=
  ⟨(reachable_counters h).rn_bound i j, (reachable_counters h).ln_bound j⟩

-- FIFO handoff for concurrent requests, transit ownership and two completions.
def waiting : State 3 := runTrace (initial 0)
  [.request 1, .request 2, .receive ⟨1,1,0⟩, .receive ⟨2,1,0⟩]
example : waiting.token.queue = [1,2] := by decide
example : ¬ Enabled waiting (.request 0) := by decide
example : (next waiting (.send 0 1)).owners = ∅ ∧
    (next waiting (.send 0 1)).flight = some 1 ∧
    (next waiting (.send 0 1)).token.queue = [2] := by decide
example : ¬ Enabled (next waiting (.send 0 1)) (.enter 1) := by decide
example : ¬ Enabled waiting (.deliver 1) := by decide

example : Reachable 0 staleHolder := holder_rn_can_lag_ln.1
example : staleHolder.token.ln 1 > staleHolder.rn 2 1 := by decide
example : ¬ Enabled staleHolder (.deliver 2) := by decide

def completed : State 3 := runTrace (initial 0)
  (staleHolderTrace ++ [.enter 2, .leave 2])
example : ValidTrace (initial 0) (staleHolderTrace ++ [.enter 2, .leave 2]) := by decide
example : completed.token.ln 1 = 1 ∧ completed.token.ln 2 = 1 ∧
    completed.token.queue = [] ∧ 2 ∈ completed.owners := by decide
-- Two late requests have already been served; max updates cannot create phantom demand.
example : (runTrace completed [.receive ⟨1,1,2⟩, .receive ⟨2,1,1⟩]).token.queue = [] := by decide
example : ValidTrace completed [.receive ⟨1,1,2⟩, .receive ⟨2,1,1⟩] := by decide
example : ¬ Enabled (next completed (.receive ⟨1,1,2⟩)) (.receive ⟨1,1,2⟩) := by decide
example : ¬ Enabled completed (.receive ⟨1,7,2⟩) := by decide
example : ¬ Enabled completed (.send 0 1) := by decide

-- A fresh request increments only the sender's own number and can recur.
def fresh : State 3 := next completed (.request 1)
example : Enabled completed (.request 1) ∧ fresh.rn 1 1 = 2 := by decide
example : ¬ Enabled fresh (.request 1) := by decide
-- At node 2, receive newer request before the older one: RN stays at two.
example : ValidTrace fresh [.receive ⟨1,2,2⟩, .receive ⟨1,1,2⟩] := by decide
example : (runTrace fresh [.receive ⟨1,2,2⟩, .receive ⟨1,1,2⟩]).rn 2 1 = 2 ∧
    (runTrace fresh [.receive ⟨1,2,2⟩, .receive ⟨1,1,2⟩]).token.queue = [1] := by decide

-- Reusing a retained token neither broadcasts nor increments the network sequence.
def localTwice : List (Event 2) :=
  [.request 0, .enter 0, .leave 0, .request 0, .enter 0, .leave 0]
example : ValidTrace (initial 0) localTwice := by decide
example : (runTrace (initial 0) localTwice).rn 0 0 = 0 ∧
    (runTrace (initial 0) localTwice).sent = ∅ := by decide
example : (next (initial (0 : Fin 2)) (.request 0)).token.queue = [] := by decide

-- Critical-section ownership cannot be shipped away; waiting requests append on release.
def busy : State 2 := runTrace (initial 0) [.request 0, .enter 0, .request 1, .receive ⟨1,1,0⟩]
example : ValidTrace (initial (0 : Fin 2)) [.request 0, .enter 0, .request 1, .receive ⟨1,1,0⟩] := by decide
example : ¬ Enabled busy (.send 0 1) ∧ busy.token.queue = [] := by decide
example : (next busy (.leave 0)).token.queue = [1] := by decide

example : ¬ ReliableDelivery withheldRun := reliable_delivery_is_necessary.2.2
example : ∀ k, (withheldRun.state k).mode 1 ≠ .inCS := reliable_delivery_is_necessary.2.1

end SuzukiKasamiRegression
