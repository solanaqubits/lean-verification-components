import Verification.DistributedTendermintUnbondingPeriodContract
import Mathlib.Data.Fin.VecNotation

open Finset DistributedTendermintCoreSafety DistributedTendermintAccountableSafety
open DistributedTendermintSlashingPenaltyContract
open DistributedTendermintSlashingReplayProtection (CertificateRequest)
open DistributedTendermintUnbondingPeriodContract
namespace TendermintUnbondingRegression
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048

def window : Window := ⟨10, by decide⟩
def cfg (h : ℕ) : Config 3 := ⟨![8, 6, 4], univ, h⟩
def votes : Finset (Vote 3) := {⟨0, 0, .prevote, some 0⟩, ⟨0, 0, .prevote, some 1⟩}
def view (h : ℕ) : EvidenceView 3 := ⟨votes.image (fun v => ⟨h, v⟩), ∅⟩
def certificate (h : ℕ) : CertificateRequest 3 := ⟨cfg h, some votes, view h⟩
def initialState : UnbondingState (Fin 3) := ⟨17, .admission, ![8, 6, 4], [], 5, ![0, 0, 0], ∅⟩
def requested := request_unbonding initialState 0 8
def deadline := { requested with now := 27 }
def step (h : ℕ) (α : ℚ) (s : UnbondingState (Fin 3)) :=
  slash_unbonding window (cfg h) (some votes) (view h) α s
def half := step 17 (1/2) deadline
def full := step 17 1 deadline
def paid := processSlot window (1/2) deadline [certificate 17]
def honest := processSlot window (1/2) deadline []
def wrongOrder := step 17 (1/2) (finalize_unbonding window (close_admission deadline))
def mixed := { deadline with
  active := ![2, 6, 4]
  queue := [⟨0, 8, 17⟩, ⟨0, 6, 15⟩, ⟨1, 4, 17⟩] }
def mixedAfter := step 17 (1/2) mixed

def observed (s : UnbondingState (Fin 3)) :=
  (s.now, s.phase, s.active 0, s.queue.map Withdrawal.amount,
   s.confiscated, s.completed 0, s.processed)

example : attribute_evidence (cfg 17) (some votes) (view 17) = .ok {0} := by decide +kernel
example : is_timely window 17 27 := by decide
example : ¬ is_timely window 18 17 := by decide
example : ¬ is_timely window 17 28 := by decide
example : observed requested = (17, .admission, 0, [8], 5, 0, ∅) := by decide +kernel
example : requested.queue = [⟨0, 8, 17⟩] := by decide +kernel
example : totalValue requested = 23 := by decide +kernel
example : observed (request_unbonding initialState 0 9) = observed initialState := by decide +kernel
example : observed (request_unbonding initialState 0 0) = observed initialState := by decide +kernel
example : observed (request_unbonding initialState 0 (-1)) = observed initialState := by decide +kernel
example : finalize_unbonding window deadline = deadline := admission_finalize_noop _ _ rfl
example : observed (finalize_unbonding window (close_admission requested)) =
    (17, .withdrawal, 0, [8], 5, 0, ∅) := by decide +kernel
example : step 18 (1/2) requested = requested := no_future_evidence_accepted _ _ _ _ _ _ (by decide)
example : step 17 (1/2) {deadline with now := 28} = {deadline with now := 28} :=
  expired_evidence_rejected _ _ _ _ _ _ (by decide)
example : observed half = (27, .admission, 0, [4], 9, 0, {(17, 0)}) := by decide +kernel
example : observed paid = (28, .admission, 0, [], 9, 4, {(17, 0)}) := by decide +kernel
example : observed full = (27, .admission, 0, [0], 13, 0, {(17, 0)}) := by decide +kernel
example : (processSlot window 1 deadline [certificate 17]).completed 0 = 0 := by decide +kernel
example : step 17 (1/2) half = half := replay_idempotence _ _ _ _ _ _
example : observed (step 17 1 half) = observed half := by decide +kernel
example : (step 18 (1/2) deadline).queue = deadline.queue := by decide +kernel
example : (step 18 (1/2) deadline).confiscated = 5 := by decide +kernel
example : (step 18 (1/2) deadline).processed = {(18, 0)} := by decide +kernel
example : observed honest = (28, .admission, 0, [], 5, 8, ∅) := by decide +kernel
-- Mutation witness: closing admission and withdrawing first loses the intended debit.
example : wrongOrder.completed 0 = 8 ∧ wrongOrder.confiscated = 5 := by decide +kernel
example : paid.completed 0 ≠ wrongOrder.completed 0 := by decide +kernel
example : totalValue paid = totalValue deadline := total_value_conservation _ _ _ _
example : observed mixedAfter = (27, .admission, 1, [4, 6, 4], 10, 0, {(17, 0)}) := by decide +kernel
example : available mixed 17 0 = 10 := by decide +kernel
example : totalValue mixedAfter = totalValue mixed := checked_conservation _ _ _ _ _ _
example : (finalize_unbonding window (close_admission mixedAfter)).completed 0 = 10 := by decide +kernel
example : (finalize_unbonding window (close_admission mixedAfter)).completed 1 = 4 := by decide +kernel
example : slash_unbonding window (cfg 17) none (view 17) (1/2) deadline = deadline :=
  invalid_certificate_noop _ _ _ _ _ _ .insufficientEvidence rfl
example : observed (step 17 0 deadline) = observed deadline := by decide +kernel
example : observed (step 17 2 deadline) = observed deadline := by decide +kernel
example : observed (step 17 (-1) deadline) = observed deadline := by decide +kernel
example : (step 16 (1/2) {half with now := 26}).confiscated = 11 := by decide +kernel
example : toLedger half 17 =
    DistributedTendermintSlashingReplayProtection.applyCertifiedSet (toLedger deadline 17) 17 {0} (1/2) := by
  change toLedger (slash_unbonding window (cfg 17) (some votes) (view 17) (1/2) deadline) 17 = _
  rw [accepted_certificate window (cfg 17) (some votes) (view 17) (1/2) deadline {0}
    (by decide +kernel) (by decide +kernel)]
  exact ledger_refinement _ _ _ _
example : WellFormed initialState := ⟨by decide +kernel, by simp [initialState], by decide +kernel⟩
example : WellFormed paid := slot_wellFormed _ _ _ _
  ⟨by decide +kernel, by simp [deadline, requested, request_unbonding, initialState], by decide +kernel⟩
example : deadline.confiscated < half.confiscated := by decide +kernel
example : (⟨0, 8, 17⟩ : Withdrawal (Fin 3)).maturity window = 27 := by decide
example : (⟨0, 8, 18⟩ : Withdrawal (Fin 3)).maturity window > 27 := by decide
-- The stronger assertion about offences AFTER the request is false.
example : is_timely window 26 28 ∧ (⟨0, 8, 17⟩ : Withdrawal (Fin 3)).maturity window < 28 := by decide
example : advance_time requested = requested := by rfl
example : (advance_time (close_admission requested)).now = 18 := by rfl
example : (processSlot window (1/2) deadline [certificate 17, certificate 17]).completed 0 = 4 := by decide +kernel
example : (processSlot window (1/2) deadline [certificate 17, certificate 17]).confiscated = 9 := by decide +kernel
-- A real reachable protocol history supplies the two conflicting votes.
def actions : List (Action 3) :=
  [.faulty ⟨0, 0, .prevote, some 0⟩, .faulty ⟨0, 0, .prevote, some 1⟩]
def reached := (run (cfg 17) initial actions).getD initial
theorem execution : run (cfg 17) initial actions = some reached := by decide +kernel
theorem reachable : Reachable (cfg 17) reached := run_reachable _ _ Reachable.init execution
example : reached.votes = votes := by decide +kernel
example : attribute_evidence (cfg 17) (some reached.votes) (view 17) = .ok {0} := by decide +kernel

example : (finalize_unbonding window (close_admission half)).completed 0 = 4 := by
  have he := checked_deadline_precedence window (cfg 17) (some votes) (view 17) (1/2)
    deadline (⟨0, 8, 17⟩ : Withdrawal (Fin 3)) {0}
    (by decide +kernel) rfl (by norm_num) rfl (by decide) (by decide +kernel)
    (by decide) rfl rfl
  change (finalize_unbonding window (close_admission half)).completed 0 =
    (0 : ℚ) + (1 - 1/2) * 8 at he
  norm_num at he
  exact he
example {n : ℕ} w (c : Config n) ref e α (s : UnbondingState (Fin n)) B v
    (hc : attribute_evidence c ref e = .ok B)
    (hg : s.phase = .admission ∧ is_timely w c.height s.now ∧ 0 < α ∧ α ≤ 1)
    (hw : WellFormed s) (hb : v ∈ B) (hf : (c.height, v) ∉ s.processed)
    (hp : 0 < available s c.height v) :
    s.confiscated < (slash_unbonding w c ref e α s).confiscated :=
  timely_slashing_guarantee w c ref e α s B v hc hg hw hb hf hp
example {n : ℕ} (c : Config n) {history : State n} (hr : Reachable c history) e qs
    (hh : ∀ q ∈ qs, q.validator ∉ c.byzantine) :
    QueueSafe qs ⟨c, some history.votes, e⟩ := honest_queue_safe c hr e qs hh
example : honest.completed 0 = 8 := by
  have he := honest_withdrawal_liveness window (1/2) deadline [] ⟨0, 8, 17⟩ rfl
    (by decide +kernel) (by simp)
  change honest.completed 0 = (0 : ℚ) + 8 at he
  norm_num at he
  exact he
example : 27 ≤ (⟨0, 8, 18⟩ : Withdrawal (Fin 3)).maturity window :=
  no_escape_theorem window _ 17 27 (by decide) (by decide)
example : ¬ (⟨0, 8, 17⟩ : Withdrawal (Fin 3)).maturity window ≤ 26 :=
  no_prior_finalization window _ 17 27 26 (by decide) (by decide) (by decide)

#eval [("request", decide (requested.active 0 = 0 ∧ queueValue requested.queue = 8)),
  ("no early payout", decide ((finalize_unbonding window (close_admission requested)).completed 0 = 0)),
  ("future", decide (observed (step 18 (1/2) requested) = observed requested)),
  ("deadline half", decide (paid.completed 0 = 4 ∧ paid.confiscated = 9)),
  ("deadline full", decide (full.confiscated = 13)),
  ("expired", decide ((step 17 (1/2) {deadline with now := 28}).confiscated = 5)),
  ("replay", decide (observed (step 17 (1/2) half) = observed half)),
  ("late offence", decide ((step 18 (1/2) deadline).queue = deadline.queue)),
  ("honest", decide (honest.completed 0 = 8)),
  ("priority mutation", decide (wrongOrder.completed 0 = 8 ∧ paid.completed 0 = 4)),
  ("invalid evidence", decide ((slash_unbonding window (cfg 17) none (view 17) (1/2) deadline).confiscated = 5)),
  ("invalid rate", decide ((step 17 2 deadline).confiscated = 5)),
  ("mixed queue", decide (mixedAfter.queue.map Withdrawal.amount = [4, 6, 4])),
  ("slot time", decide (paid.now = 28)),
  ("conservation", decide (totalValue paid = 23)),
  ("fresh positive", decide (half.confiscated > deadline.confiscated)),
  ("old key", decide ((step 17 1 half).confiscated = 9)),
  ("request overdraw", decide (observed (request_unbonding initialState 0 9) = observed initialState)),
  ("new height", decide ((step 16 (1/2) {half with now := 26}).confiscated = 11)),
  ("reachable", (run (cfg 17) initial actions).isSome)]
end TendermintUnbondingRegression
