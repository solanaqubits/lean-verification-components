import Verification.DistributedTwoPhaseCommitTimeout

namespace TwoPhaseCommitTimeoutRegression

open DistributedTwoPhaseCommitTimeout

/-- Both participants receive a genuine coordinator commit. -/
def fullCommitHistory : List Event :=
  [.prepare false, .prepare true, .receiveYes false, .receiveYes true,
   .chooseCommit, .sendDecision false .commit, .sendDecision true .commit,
   .receiveDecision false .commit, .receiveDecision true .commit]

def fullCommitEnd : Network :=
  ⟨⟨.committed, .committed, true, true, some .commit, true⟩, []⟩

example : Execution initial fullCommitHistory fullCommitEnd := run_sound (by decide)
example : Reachable fullCommitEnd := ⟨fullCommitHistory, run_sound (by decide)⟩
example : Agreement fullCommitEnd :=
  reachable_agreement ⟨fullCommitHistory, run_sound (by decide)⟩

/-- A chosen commit cannot be reversed by the coordinator abort rule. -/
example : runEvent fullCommitEnd .chooseAbort = none := by decide
example : runEvent fullCommitEnd (.sendDecision false .abort) = none := by decide

/-- A duplicate authentic decision is harmless even after terminal application. -/
example : Execution fullCommitEnd
    [.sendDecision false .commit, .receiveDecision false .commit] fullCommitEnd :=
  run_sound (by decide)

/-- Packet presence matters even when the local commit-receive guard permits delivery. -/
example : coreNext fullCommitEnd.core (.receiveDecision false .commit) =
    some fullCommitEnd.core := by decide
example : runEvent fullCommitEnd (.receiveDecision false .commit) = none := by decide
example : runEvent initial (.receiveYes false) = none := by decide

def earlyAbortEnd : Network :=
  ⟨⟨.aborted, .init, false, false, none, true⟩, [.no false]⟩

example : Execution initial [.preVoteAbort false] earlyAbortEnd := run_sound (by decide)
example : runEvent earlyAbortEnd (.prepare false) = none := by decide
example : runEvent earlyAbortEnd (.receiveYes false) = none := by decide
example : runEvent earlyAbortEnd .chooseCommit = none := by decide

example (es : List Event) (s : Network) (h : Execution earlyAbortEnd es s) :
    s.core.decision ≠ some .commit := by
  have hp := aborted_preserved_execution h false (by rfl)
  have hr : Reachable earlyAbortEnd := ⟨[.preVoteAbort false], run_sound (by decide)⟩
  exact (reachable_invariant (hr.after h)).1.2.1 false hp

/-- Receiving P1's one vote consumes it, and cannot count as P2's vote. -/
def oneVoteEnd : Network :=
  ⟨⟨.prepared, .init, true, false, none, true⟩, []⟩

example : Execution initial [.prepare false, .receiveYes false] oneVoteEnd :=
  run_sound (by decide)
example : runEvent oneVoteEnd (.receiveYes false) = none := by decide
example : runEvent oneVoteEnd .chooseCommit = none := by decide
example : votedYes (recordYes oneVoteEnd.core false) true = false := by decide

/-- Running coordinator is essential to the relative blocking characterization. -/
def livePreparedEnd : Network :=
  ⟨⟨.prepared, .prepared, false, false, none, true⟩, [.yes false, .yes true]⟩

def liveAbortEnd : Network :=
  ⟨⟨.aborted, .prepared, false, false, some .abort, true⟩, [.yes false, .yes true]⟩

example : Execution initial [.prepare false, .prepare true] livePreparedEnd :=
  run_sound (by decide)
example : BothPrepared livePreparedEnd.core ∧ NoDecision livePreparedEnd.packets := by decide

example : ¬ Blocked livePreparedEnd := by
  intro h
  have he : Execution livePreparedEnd
      [.chooseAbort, .sendDecision false .abort, .receiveDecision false .abort]
      liveAbortEnd := run_sound (by decide)
  exact h _ _ he ⟨false, Or.inr rfl⟩

/-- Abort delivery, like commit delivery, can happen after coordinator failure. -/
def abortInFlightEnd : Network :=
  ⟨⟨.prepared, .prepared, false, false, some .abort, false⟩,
    [.yes false, .yes true, .decision false .abort]⟩

def abortDeliveredEnd : Network :=
  ⟨⟨.aborted, .prepared, false, false, some .abort, false⟩, [.yes false, .yes true]⟩

example : Execution initial
    [.prepare false, .prepare true, .chooseAbort, .sendDecision false .abort, .crash]
    abortInFlightEnd := run_sound (by decide)
example : Execution abortInFlightEnd [.receiveDecision false .abort] abortDeliveredEnd :=
  run_sound (by decide)
example : runEvent abortInFlightEnd (.sendDecision true .abort) = none := by decide

/-- Complete observations coincide, while opposite peers have genuinely terminated. -/
example : Obs false Examples.abortHistory = Obs false Examples.commitHistory := by decide
example : view false Examples.abortHistory Examples.abortEnd =
    view false Examples.commitHistory Examples.commitEnd := by decide
example : Reachable Examples.abortEnd ∧ Reachable Examples.commitEnd :=
  ⟨Examples.abort_reachable, Examples.commit_reachable⟩
example : ¬ Agreement (unsafeDecision Examples.abortEnd false .commit) :=
  unilateral_commit_breaks_agreement
example : ¬ Agreement (unsafeDecision Examples.commitEnd false .abort) :=
  unilateral_abort_breaks_agreement

example : Reachable Examples.blockedEnd ∧ Blocked Examples.blockedEnd :=
  ⟨Examples.blocked_reachable, Examples.blocked_end_blocked⟩
example : Reachable Examples.inFlightEnd ∧ ¬ Blocked Examples.inFlightEnd :=
  ⟨Examples.in_flight_reachable, Examples.in_flight_not_blocked⟩

/-- Losing the only already-sent decision can remove the available escape. -/
def droppedEnd : Network := { Examples.inFlightEnd with packets := [] }

example : Execution Examples.inFlightEnd [.drop (.decision false .commit)] droppedEnd :=
  run_sound (by decide)
example : Blocked droppedEnd :=
  (blocking_condition_characterization (by decide) (by rfl)).2 (by decide)

example : Execution Examples.blockedEnd
    [.timeout false, .drop (.yes false), .timeout true, .drop (.yes true)]
    { Examples.blockedEnd with packets := [] } := run_sound (by decide)

end TwoPhaseCommitTimeoutRegression
