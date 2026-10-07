/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedRicartAgrawalaMutex
import Mathlib.Tactic.FinCases

namespace RicartAgrawalaRegression
open DistributedRicartAgrawalaMutex

def a : Request 2 := ⟨1, 0⟩
def b : Request 2 := ⟨1, 1⟩

def simultaneous : List (Event 2) := [.request 0, .request 1]
def deferred : List (Event 2) := simultaneous ++ [.receive b 0, .receive a 1]
def firstEntry : List (Event 2) := deferred ++ [.reply a 1, .deliver a 1, .enter 0 1]
def bothComplete : List (Event 2) := firstEntry ++
  [.leave 0 1, .reply b 0, .deliver b 0, .enter 1 1, .leave 1 1]

example : ValidTrace initial simultaneous := by decide +kernel
example : ValidTrace initial deferred := by decide +kernel
example : Deferred (runTrace initial deferred) b 0 := by decide +kernel
example : ¬ Enabled (runTrace initial deferred) (.reply b 0) := by decide +kernel
example : Enabled (runTrace initial deferred) (.reply a 1) := by decide +kernel
example : ValidTrace initial firstEntry := by decide +kernel
example : (runTrace initial firstEntry).mode 0 = .held 1 := by decide +kernel
example : (runTrace initial firstEntry).mode 1 = .wanted 1 := by decide +kernel
example : ¬ Enabled (runTrace initial firstEntry) (.deliver a 1) := by decide +kernel
example : ValidTrace initial bothComplete := by decide +kernel
example : (runTrace initial bothComplete).mode 0 = .released ∧
    (runTrace initial bothComplete).mode 1 = .released := by decide +kernel

-- A fresh timestamp cannot consume the old request's permission.
def retry := bothComplete ++ [.request 0]
example : ValidTrace initial retry := by decide +kernel
example : (runTrace initial retry).mode 0 = .wanted 3 := by decide +kernel
example : ¬ Enabled (runTrace initial retry) (.enter 0 3) := by decide +kernel
example : ¬ Enabled (initial : State 2) (.reply a 1) := by decide +kernel
example : ¬ Enabled (initial : State 2) (.deliver a 1) := by decide +kernel

-- A reply was issued before the responder made its own request. The clock
-- update makes the new request later, despite the responder's lower node ID.
def priorReply : List (Event 2) :=
  [.request 1, .receive b 0, .reply b 0, .request 0, .deliver b 0, .enter 1 1]
example : ValidTrace initial priorReply := by decide +kernel
example : (runTrace initial priorReply).mode 0 = .wanted 3 ∧
    (runTrace initial priorReply).mode 1 = .held 1 := by decide +kernel
example : Earlier b (⟨3, 0⟩ : Request 2) := by decide +kernel

-- Three nodes: out-of-order reply receipt and a nonzero initiator.
def c : Request 3 := ⟨1, 2⟩
def three : List (Event 3) := [.request 2, .receive c 0, .receive c 1,
  .reply c 0, .reply c 1, .deliver c 1, .deliver c 0, .enter 2 1, .leave 2 1]
example : ValidTrace initial three := by decide +kernel
example : (runTrace initial three).mode 2 = .released := by decide +kernel

-- General theorems are exercised without fixing the number of nodes.
example {n : ℕ} (ρ : Run n) (hd : ReliableDelivery ρ) (hf : WeakFairness ρ)
    (hc : FiniteCS ρ) (r : Request n) (k : ℕ)
    (hw : (ρ.state k).mode r.owner = .wanted r.ts) :
    ∃ l, k ≤ l ∧ (ρ.state l).mode r.owner = .held r.ts :=
  request_eventually_enters ρ hd hf hc r k hw

example {n : ℕ} {s : State n} (h : Reachable s) {i j t u}
    (hne : i ≠ j) (hi : s.mode i = .held t) : s.mode j ≠ .held u :=
  fun hj => mutual_exclusion_safety h hne hi hj

example : ¬ ReliableDelivery withheldRun := delivery_contract_necessary.2.2
example : Reachable (runTrace initial bothComplete) :=
  valid_trace_reachable (by decide +kernel)

-- The withholding counterexample satisfies the other two progress contracts.
example : FiniteCS withheldRun := by
  intro k i t hh
  cases k <;> fin_cases i <;> simp [withheldRun, next, initial] at hh

example : WeakFairness withheldRun := by
  intro e he k henabled
  have hh := henabled (k + 1) (Nat.le_succ k)
  cases e with
  | reply r j =>
    have hm := hh.1
    simp [withheldRun, next, initial] at hm
  | enter i t =>
    fin_cases i
    · have hm := hh.2 1 (by decide)
      simp [withheldRun, next, initial] at hm
    · have hm := hh.1
      simp [withheldRun, next, initial] at hm
  | request => cases he
  | receive => cases he
  | deliver => cases he
  | leave => cases he
  | idle => cases he

end RicartAgrawalaRegression
