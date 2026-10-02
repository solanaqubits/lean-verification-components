import Verification.DistributedRaftCompleteBridge
import Mathlib.Tactic.IntervalCases

namespace RaftCompleteBridgeRegression
open DistributedRaftLeaderCompleteness (majority)
open DistributedRaftStateMachine
open DistributedRaftStateMachine.Examples
open DistributedRaftEventHistory
open DistributedRaftCompleteBridge

def campaign2 := startElection committed n1

def request2 (v : DistributedRaftLeaderCompleteness.NodeId cluster) : Envelope cluster :=
  ⟨v, .requestVote 2 n1 1 1⟩

def prepared2 := observeTerm campaign2 n0 2

def granted2 := grantVote prepared2 n0 n1 [voteRequest n2, appendRequest n2] [request2 n2]

def received2 := receiveVote granted2 n0 n1 2 [voteRequest n2, appendRequest n2, request2 n2] []

def leader2 := becomeLeader received2 n1

def states : ℕ → GlobalState cluster
  | 0 => initial
  | 1 => campaigning
  | 2 => prepared
  | 3 => granted
  | 4 => received
  | 5 => elected
  | 6 => appended
  | 7 => replicated
  | 8 => acknowledged
  | 9 => committed
  | 10 => campaign2
  | 11 => prepared2
  | 12 => granted2
  | 13 => received2
  | _ => leader2

theorem transitions (i : ℕ) (hi : i < 14) : Step (states i) (states (i + 1)) := by
  interval_cases i
  · exact Step.timeout initial n0 (by decide)
  · apply Step.observe (m := voteRequest n1) <;> decide
  · apply Step.vote (t := 1) (li := 0) (lt := 0)
    · decide
    · decide
    · constructor
      · left; decide
      · right; constructor <;> decide
  · apply Step.voteReply <;> decide
  · apply Step.elect
    · decide
    · change 3 < 2 * (votesFor received.received (received.servers n0).currentTerm n0).card
      decide
  · exact Step.append 7 (by decide)
  · apply Step.appendEntries (t := 1) (pt := 0)
    · decide
    · decide
    · constructor <;> decide
  · apply Step.appendReply (t := 1) <;> decide
  · apply Step.commit
    · decide
    · decide
    · decide
    · change 3 < 2 * (replicationQuorum acknowledged n0 1).card
      decide
  · exact Step.timeout committed n1 (by decide)
  · apply Step.observe (m := request2 n0) <;> decide
  · apply Step.vote (t := 2) (li := 1) (lt := 1)
    · decide
    · decide
    · constructor
      · left; decide
      · right; constructor <;> decide
  · apply Step.voteReply <;> decide
  · apply Step.elect
    · decide
    · change 3 < 2 * (votesFor received2.received (received2.servers n1).currentTerm n1).card
      decide

def execution : Execution cluster := ⟨14, states, rfl, transitions⟩

example : Reachable leader2 := execution.reachable 14 le_rfl

example : (leader2.servers n1).role = .leader ∧
    (leader2.servers n1).currentTerm = 2 ∧
    (leader2.servers n1).log = [⟨1, 1, 7⟩] := by decide

theorem actual_commit : CommitEvent execution 8 n0 1 := by
  constructor
  · decide
  · decide
  · decide
  · decide
  · change 3 < 2 * (replicationQuorum acknowledged n0 1).card
    decide
  · rfl

theorem historical_commit : committedInTerm leader2 ⟨1, 1, 7⟩ 1 := by
  exact ⟨execution, 8, n0, 1, rfl, actual_commit, rfl, by decide⟩

/-- The general theorem applies to a real two-term execution, not an assumed safe history. -/
example : (⟨1, 1, 7⟩ : DistributedRaftLeaderCompleteness.LogEntry) ∈
    (leader2.servers n1).log := by
  exact reachable_leader_completeness leader2 (execution.reachable 14 le_rfl)
    ⟨1, 1, 7⟩ 1 2 n1 (by decide) historical_commit (by decide) (by decide)

example : ([⟨1, 1, 7⟩] : List DistributedRaftLeaderCompleteness.LogEntry).IsPrefix
    (leader2.servers n1).log := by
  exact committed_prefix_preserved execution 8 n0 1 actual_commit 9 14
    (by decide) (by decide) n1 (by exact List.prefix_rfl)

end RaftCompleteBridgeRegression
