/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedRaftStateMachine

/-!
# Reachable old-term majority counterexample

A five-server execution of the existing small-step model follows the mechanism
of Raft Figure 8: an old-term entry obtains a majority in a later term without
being committed, and a legitimately elected leader subsequently replaces it.
No crash/recovery implementation or application transition is assumed here.
-/

namespace DistributedRaftCommitApplicationExample

open DistributedRaftLeaderCompleteness
open DistributedRaftStateMachine


abbrev cluster : Cluster := ⟨5, by decide⟩
abbrev Node := NodeId cluster

local instance (p : ServerState cluster) (c : Node) (li lt : ℕ) :
    Decidable (mayVote p c li lt) := by
  unfold mayVote upToDateFields
  infer_instance

local instance (Q : Finset Node) : Decidable (majority cluster Q) :=
  inferInstanceAs (Decidable (5 < 2 * Q.card))

def oldEntry : LogEntry := ⟨1, 1, 10⟩
def replacementEntry : LogEntry := ⟨1, 2, 20⟩

def state00 : GlobalState cluster := initState cluster


def state01 : GlobalState cluster := startElection state00 (0 : Node)

theorem step01 : Step state00 state01 := by
  exact Step.timeout _ _ (by decide)


def state02 : GlobalState cluster := observeTerm state01 (1 : Node) 1

theorem step02 : Step state01 state02 := by
  exact Step.observe (m := ⟨(1 : Node), .requestVote 1 (0 : Node) 0 0⟩) (by decide) (by decide)


def state03 : GlobalState cluster := grantVote state02 (1 : Node) (0 : Node) (state02.network.take
  0) (state02.network.drop 1)

theorem step03 : Step state02 state03 := by
  exact Step.vote (t := 1) (li := 0) (lt := 0) (by decide) (by decide) (by decide)


def state04 : GlobalState cluster := receiveVote state03 (1 : Node) (0 : Node) 1
  (state03.network.take 3) (state03.network.drop 4)

theorem step04 : Step state03 state04 := by
  exact Step.voteReply (by decide) (by decide) (by decide)


def state05 : GlobalState cluster := observeTerm state04 (2 : Node) 1

theorem step05 : Step state04 state05 := by
  exact Step.observe (m := ⟨(2 : Node), .requestVote 1 (0 : Node) 0 0⟩) (by decide) (by decide)


def state06 : GlobalState cluster := grantVote state05 (2 : Node) (0 : Node) (state05.network.take
  0) (state05.network.drop 1)

theorem step06 : Step state05 state06 := by
  exact Step.vote (t := 1) (li := 0) (lt := 0) (by decide) (by decide) (by decide)


def state07 : GlobalState cluster := receiveVote state06 (2 : Node) (0 : Node) 1
  (state06.network.take 2) (state06.network.drop 3)

theorem step07 : Step state06 state07 := by
  exact Step.voteReply (by decide) (by decide) (by decide)


def state08 : GlobalState cluster := becomeLeader state07 (0 : Node)

theorem step08 : Step state07 state08 := by
  exact Step.elect (by decide) (by decide)


def state09 : GlobalState cluster := leaderAppend state08 (0 : Node) 10

theorem step09 : Step state08 state09 := by
  exact Step.append 10 (by decide)


def state10 : GlobalState cluster := observeTerm state09 (4 : Node) 1

theorem step10 : Step state09 state10 := by
  exact Step.observe (m := ⟨(4 : Node), .requestVote 1 (0 : Node) 0 0⟩) (by decide) (by decide)


def state11 : GlobalState cluster := startElection state10 (4 : Node)

theorem step11 : Step state10 state11 := by
  exact Step.timeout _ _ (by decide)


def state12 : GlobalState cluster := observeTerm state11 (3 : Node) 2

theorem step12 : Step state11 state12 := by
  exact Step.observe (m := ⟨(3 : Node), .requestVote 2 (4 : Node) 0 0⟩) (by decide) (by decide)


def state13 : GlobalState cluster := grantVote state12 (3 : Node) (4 : Node) (state12.network.take
  9) (state12.network.drop 10)

theorem step13 : Step state12 state13 := by
  exact Step.vote (t := 2) (li := 0) (lt := 0) (by decide) (by decide) (by decide)


def state14 : GlobalState cluster := receiveVote state13 (3 : Node) (4 : Node) 2
  (state13.network.take 9) (state13.network.drop 10)

theorem step14 : Step state13 state14 := by
  exact Step.voteReply (by decide) (by decide) (by decide)


def state15 : GlobalState cluster := observeTerm state14 (2 : Node) 2

theorem step15 : Step state14 state15 := by
  exact Step.observe (m := ⟨(2 : Node), .requestVote 2 (4 : Node) 0 0⟩) (by decide) (by decide)


def state16 : GlobalState cluster := grantVote state15 (2 : Node) (4 : Node) (state15.network.take
  8) (state15.network.drop 9)

theorem step16 : Step state15 state16 := by
  exact Step.vote (t := 2) (li := 0) (lt := 0) (by decide) (by decide) (by decide)


def state17 : GlobalState cluster := receiveVote state16 (2 : Node) (4 : Node) 2
  (state16.network.take 8) (state16.network.drop 9)

theorem step17 : Step state16 state17 := by
  exact Step.voteReply (by decide) (by decide) (by decide)


def state18 : GlobalState cluster := becomeLeader state17 (4 : Node)

theorem step18 : Step state17 state18 := by
  exact Step.elect (by decide) (by decide)


def state19 : GlobalState cluster := leaderAppend state18 (4 : Node) 20

theorem step19 : Step state18 state19 := by
  exact Step.append 20 (by decide)


def state20 : GlobalState cluster := observeTerm state19 (0 : Node) 2

theorem step20 : Step state19 state20 := by
  exact Step.observe (m := ⟨(0 : Node), .requestVote 2 (4 : Node) 0 0⟩) (by decide) (by decide)


def state21 : GlobalState cluster := startElection state20 (0 : Node)

theorem step21 : Step state20 state21 := by
  exact Step.timeout _ _ (by decide)


def state22 : GlobalState cluster := observeTerm state21 (1 : Node) 3

theorem step22 : Step state21 state22 := by
  exact Step.observe (m := ⟨(1 : Node), .requestVote 3 (0 : Node) 1 1⟩) (by decide) (by decide)


def state23 : GlobalState cluster := grantVote state22 (1 : Node) (0 : Node) (state22.network.take
  12) (state22.network.drop 13)

theorem step23 : Step state22 state23 := by
  exact Step.vote (t := 3) (li := 1) (lt := 1) (by decide) (by decide) (by decide)


def state24 : GlobalState cluster := receiveVote state23 (1 : Node) (0 : Node) 3
  (state23.network.take 15) (state23.network.drop 16)

theorem step24 : Step state23 state24 := by
  exact Step.voteReply (by decide) (by decide) (by decide)


def state25 : GlobalState cluster := observeTerm state24 (2 : Node) 3

theorem step25 : Step state24 state25 := by
  exact Step.observe (m := ⟨(2 : Node), .requestVote 3 (0 : Node) 1 1⟩) (by decide) (by decide)


def state26 : GlobalState cluster := grantVote state25 (2 : Node) (0 : Node) (state25.network.take
  12) (state25.network.drop 13)

theorem step26 : Step state25 state26 := by
  exact Step.vote (t := 3) (li := 1) (lt := 1) (by decide) (by decide) (by decide)


def state27 : GlobalState cluster := receiveVote state26 (2 : Node) (0 : Node) 3
  (state26.network.take 14) (state26.network.drop 15)

theorem step27 : Step state26 state27 := by
  exact Step.voteReply (by decide) (by decide) (by decide)


def state28 : GlobalState cluster := becomeLeader state27 (0 : Node)

theorem step28 : Step state27 state28 := by
  exact Step.elect (by decide) (by decide)


def state29 : GlobalState cluster := { state28 with network := state28.network ++ [⟨(1 : Node),
  .appendEntries 3 (0 : Node) 0 0 [oldEntry] 0⟩] }

theorem step29 : Step state28 state29 := by
  exact Step.replicate (s := state28) (n := (0 : Node)) (v := (1 : Node)) 0 1 (by decide) (by
    decide) (by decide)


def state30 : GlobalState cluster := handleAppend state29 (1 : Node) (0 : Node) 0 [oldEntry] 0
  (state29.network.take 14) (state29.network.drop 15)

theorem step30 : Step state29 state30 := by
  exact Step.appendEntries (t := 3) (pt := 0) (by decide) (by decide) (by decide)


def state31 : GlobalState cluster := receiveAppendReply state30 (0 : Node) (1 : Node) 1
  (state30.network.take 14) (state30.network.drop 15)

theorem step31 : Step state30 state31 := by
  exact Step.appendReply (t := 3) (by decide) (by decide) (by decide)


def state32 : GlobalState cluster := { state31 with network := state31.network ++ [⟨(2 : Node),
  .appendEntries 3 (0 : Node) 0 0 [oldEntry] 0⟩] }

theorem step32 : Step state31 state32 := by
  exact Step.replicate (s := state31) (n := (0 : Node)) (v := (2 : Node)) 0 1 (by decide) (by
    decide) (by decide)


def state33 : GlobalState cluster := handleAppend state32 (2 : Node) (0 : Node) 0 [oldEntry] 0
  (state32.network.take 14) (state32.network.drop 15)

theorem step33 : Step state32 state33 := by
  exact Step.appendEntries (t := 3) (pt := 0) (by decide) (by decide) (by decide)


def state34 : GlobalState cluster := receiveAppendReply state33 (0 : Node) (2 : Node) 1
  (state33.network.take 14) (state33.network.drop 15)

theorem step34 : Step state33 state34 := by
  exact Step.appendReply (t := 3) (by decide) (by decide) (by decide)


def state35 : GlobalState cluster := observeTerm state34 (4 : Node) 3

theorem step35 : Step state34 state35 := by
  exact Step.observe (m := ⟨(4 : Node), .requestVote 3 (0 : Node) 1 1⟩) (by decide) (by decide)


def state36 : GlobalState cluster := startElection state35 (4 : Node)

theorem step36 : Step state35 state36 := by
  exact Step.timeout _ _ (by decide)


def state37 : GlobalState cluster := observeTerm state36 (3 : Node) 4

theorem step37 : Step state36 state37 := by
  exact Step.observe (m := ⟨(3 : Node), .requestVote 4 (4 : Node) 1 2⟩) (by decide) (by decide)


def state38 : GlobalState cluster := grantVote state37 (3 : Node) (4 : Node) (state37.network.take
  17) (state37.network.drop 18)

theorem step38 : Step state37 state38 := by
  exact Step.vote (t := 4) (li := 1) (lt := 2) (by decide) (by decide) (by decide)


def state39 : GlobalState cluster := receiveVote state38 (3 : Node) (4 : Node) 4
  (state38.network.take 17) (state38.network.drop 18)

theorem step39 : Step state38 state39 := by
  exact Step.voteReply (by decide) (by decide) (by decide)


def state40 : GlobalState cluster := observeTerm state39 (2 : Node) 4

theorem step40 : Step state39 state40 := by
  exact Step.observe (m := ⟨(2 : Node), .requestVote 4 (4 : Node) 1 2⟩) (by decide) (by decide)


def state41 : GlobalState cluster := grantVote state40 (2 : Node) (4 : Node) (state40.network.take
  16) (state40.network.drop 17)

theorem step41 : Step state40 state41 := by
  exact Step.vote (t := 4) (li := 1) (lt := 2) (by decide) (by decide) (by decide)


def state42 : GlobalState cluster := receiveVote state41 (2 : Node) (4 : Node) 4
  (state41.network.take 16) (state41.network.drop 17)

theorem step42 : Step state41 state42 := by
  exact Step.voteReply (by decide) (by decide) (by decide)


def state43 : GlobalState cluster := becomeLeader state42 (4 : Node)

theorem step43 : Step state42 state43 := by
  exact Step.elect (by decide) (by decide)


def state44 : GlobalState cluster := { state43 with network := state43.network ++ [⟨(2 : Node),
  .appendEntries 4 (4 : Node) 0 0 [replacementEntry] 0⟩] }

theorem step44 : Step state43 state44 := by
  exact Step.replicate (s := state43) (n := (4 : Node)) (v := (2 : Node)) 0 1 (by decide) (by
    decide) (by decide)


def state45 : GlobalState cluster := handleAppend state44 (2 : Node) (4 : Node) 0
  [replacementEntry] 0 (state44.network.take 16) (state44.network.drop 17)

theorem step45 : Step state44 state45 := by
  exact Step.appendEntries (t := 4) (pt := 0) (by decide) (by decide) (by decide)


/-- The old-term majority snapshot, before the new election. -/
def majorityState := state34


/-- A later state after a valid conflicting AppendEntries delivery. -/
def overwrittenState := state45


theorem majorityState_reachable : Reachable majorityState := by
  apply Reachable.step ?_ step34
  apply Reachable.step ?_ step33
  apply Reachable.step ?_ step32
  apply Reachable.step ?_ step31
  apply Reachable.step ?_ step30
  apply Reachable.step ?_ step29
  apply Reachable.step ?_ step28
  apply Reachable.step ?_ step27
  apply Reachable.step ?_ step26
  apply Reachable.step ?_ step25
  apply Reachable.step ?_ step24
  apply Reachable.step ?_ step23
  apply Reachable.step ?_ step22
  apply Reachable.step ?_ step21
  apply Reachable.step ?_ step20
  apply Reachable.step ?_ step19
  apply Reachable.step ?_ step18
  apply Reachable.step ?_ step17
  apply Reachable.step ?_ step16
  apply Reachable.step ?_ step15
  apply Reachable.step ?_ step14
  apply Reachable.step ?_ step13
  apply Reachable.step ?_ step12
  apply Reachable.step ?_ step11
  apply Reachable.step ?_ step10
  apply Reachable.step ?_ step09
  apply Reachable.step ?_ step08
  apply Reachable.step ?_ step07
  apply Reachable.step ?_ step06
  apply Reachable.step ?_ step05
  apply Reachable.step ?_ step04
  apply Reachable.step ?_ step03
  apply Reachable.step ?_ step02
  apply Reachable.step ?_ step01
  exact Reachable.init


theorem overwrittenState_reachable : Reachable overwrittenState := by
  apply Reachable.step ?_ step45
  apply Reachable.step ?_ step44
  apply Reachable.step ?_ step43
  apply Reachable.step ?_ step42
  apply Reachable.step ?_ step41
  apply Reachable.step ?_ step40
  apply Reachable.step ?_ step39
  apply Reachable.step ?_ step38
  apply Reachable.step ?_ step37
  apply Reachable.step ?_ step36
  apply Reachable.step ?_ step35
  exact majorityState_reachable


/-- The overwriting state extends the very same majority execution. -/
theorem majority_to_overwrite :
    Relation.ReflTransGen Step majorityState overwrittenState := by
  apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single step35)
  apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single step36)
  apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single step37)
  apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single step38)
  apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single step39)
  apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single step40)
  apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single step41)
  apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single step42)
  apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single step43)
  apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single step44)
  apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single step45)
  exact Relation.ReflTransGen.refl


/-- Three of five servers contain the same old-term entry. -/
theorem old_term_majority :
    majority cluster ({0, 1, 2} : Finset Node) ∧
      ∀ n ∈ ({0, 1, 2} : Finset Node),
        (majorityState.servers n).log = [oldEntry] := by decide

/-- Actual successful replies establish the operational replication quorum. -/
theorem acknowledged_old_term_majority :
    majority cluster (replicationQuorum majorityState 0 1) ∧
    1 ≤ (majorityState.servers 0).log.length := by decide

/-- The elected leader is in term 3, so the term-1 entry fails the commit guard. -/
theorem current_term_commit_guard_fails :
    (majorityState.servers 0).role = .leader ∧
    (majorityState.servers 0).currentTerm = 3 ∧
    termAt (majorityState.servers 0).log 1 ≠
      (majorityState.servers 0).currentTerm := by decide

/-- Every commit counter is zero at both displayed execution endpoints. -/
theorem no_operational_commit :
    (∀ n, (majorityState.servers n).commitIndex = 0) ∧
    (∀ n, (overwrittenState.servers n).commitIndex = 0) := by decide

/-- Both later leaders were promoted using actual received-majority evidence. -/
theorem legitimate_later_leaders :
    (3, (0 : Node)) ∈ majorityState.elected ∧
    (4, (4 : Node)) ∈ overwrittenState.elected := by decide

/-- A majority member's previously replicated command is actually replaced. -/
theorem old_term_entry_overwritten :
    (majorityState.servers 2).log = [oldEntry] ∧
    (overwrittenState.servers 2).log = [replacementEntry] ∧
    oldEntry.index = replacementEntry.index ∧
    oldEntry.term ≠ replacementEntry.term ∧
    oldEntry.cmd ≠ replacementEntry.cmd := by decide

/-- Hypothetically applying the first replicated command before an operational
commit is unsafe: a deterministic last-command fold changes after replacement.
This evaluates two log prefixes; it does not add a premature application step. -/
theorem premature_prefix_application_changes :
    (((majorityState.servers 2).log.take 1).map LogEntry.cmd).foldl
        (fun (_ : ℕ) cmd => cmd) 0 = 10 ∧
    (((overwrittenState.servers 2).log.take 1).map LogEntry.cmd).foldl
        (fun (_ : ℕ) cmd => cmd) 0 = 20 := by decide

/-- A majority of actual acknowledgments for an old-term entry does not justify
applying it. The later conflicting leader is elected within the same execution. -/
theorem uncommitted_overwriting_counterexample :
    Reachable majorityState ∧
    Relation.ReflTransGen Step majorityState overwrittenState ∧
    Reachable overwrittenState ∧
    majority cluster (replicationQuorum majorityState 0 1) ∧
    (majorityState.servers 0).role = .leader ∧
    1 ≤ (majorityState.servers 0).log.length ∧
    termAt (majorityState.servers 0).log 1 ≠
      (majorityState.servers 0).currentTerm ∧
    (majorityState.servers 2).commitIndex = 0 ∧
    (overwrittenState.servers 2).commitIndex = 0 ∧
    (majorityState.servers 2).log = [oldEntry] ∧
    (overwrittenState.servers 2).log = [replacementEntry] ∧
    oldEntry.cmd ≠ replacementEntry.cmd := by
  exact ⟨majorityState_reachable, majority_to_overwrite,
    overwrittenState_reachable, acknowledged_old_term_majority.1,
    current_term_commit_guard_fails.1, acknowledged_old_term_majority.2,
    current_term_commit_guard_fails.2.2,
    no_operational_commit.1 2, no_operational_commit.2 2,
    old_term_entry_overwritten.1, old_term_entry_overwritten.2.1,
    old_term_entry_overwritten.2.2.2.2⟩

end DistributedRaftCommitApplicationExample
