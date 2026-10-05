import Verification.DistributedRaftCommitApplication
import Mathlib.Tactic.IntervalCases

/-! Compiler regressions for actual commit propagation and application. -/
namespace RaftCommitApplicationRegression

open DistributedRaftLeaderCompleteness (Cluster NodeId LogEntry)
open DistributedRaftStateMachine
open DistributedRaftStateMachine.Examples
open DistributedRaftEventHistory
open DistributedRaftCompleteBridge
open DistributedRaftCommitIndexInvariant
open DistributedRaftCommitApplication

/-- A real heartbeat sent after the leader's commit propagates its count. -/
def commitHeartbeat : Envelope cluster := ⟨n1, .appendEntries 1 n0 1 1 [] 1⟩
def sentCommit : GlobalState cluster :=
  { committed with network := committed.network ++ [commitHeartbeat] }
def followerCommitted : GlobalState cluster :=
  handleAppend sentCommit n1 n0 1 [] 1 committed.network []

def state (k : ℕ) : GlobalState cluster :=
  match k with
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
  | 10 => sentCommit
  | _ => followerCommitted

theorem transitions (i : ℕ) (hi : i < 11) : Step (state i) (state (i + 1)) := by
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
  · exact Step.replicate (s := committed) (n := n0) (v := n1) 1 0
      (by decide) (by decide) (by decide)
  · apply Step.appendEntries (t := 1) (pt := 1)
    · decide
    · decide
    · constructor <;> decide

def run : Execution cluster := ⟨11, state, rfl, transitions⟩

example : ((run.state 9).servers n0).commitIndex = 1 := by decide
example : ((run.state 9).servers n1).commitIndex = 0 := by decide
example : ((run.state 11).servers n1).commitIndex = 1 := by decide
example : ((run.state 11).servers n1).log = [⟨1, 1, 7⟩] := by decide

example : ((run.state 11).servers n1).commitIndex ≤
    ((run.state 11).servers n1).log.length := execution_commitIndex_bound run 11 (by decide) n1

example : (((run.state 9).servers n0).log.take 1).IsPrefix
    ((run.state 11).servers n0).log :=
  execution_commit_prefix_stable run 9 11 (by decide) (by decide) n0

example : IsCommittedAt run 11 0 ⟨1, 1, 7⟩ :=
  below_commit_is_committed run 11 (by decide) n1 0 ⟨1, 1, 7⟩ (by decide) (by decide)

/-- Network-only evolution leaves arbitrary application data unchanged. -/
example {C : Cluster} {σ : Type*} (r : Execution C) (step : σ → ℕ → σ)
    (a : ApplicationState C σ) (ht : a.time < r.length) :
    ApplicationStep r step a { a with time := a.time + 1 } ∧
      ({ a with time := a.time + 1 } : ApplicationState C σ).value = a.value :=
  ⟨ApplicationStep.network a ht, rfl⟩

def atTime (t : ℕ) : ApplicationState cluster ℕ :=
  { initialApplication 0 with time := t }

theorem atTime_reachable (t : ℕ) (ht : t ≤ 11) :
    ApplicationReachable run (· + ·) 0 (atTime t) := by
  induction t with
  | zero => exact .init
  | succ t ih =>
    exact .next (ih (by omega)) (ApplicationStep.network (atTime t) (by
      change t < 11
      omega))

def leaderApplied : ApplicationState cluster ℕ :=
  applyNext (· + ·) (atTime 9) n0 ⟨1, 1, 7⟩

theorem leaderApplied_reachable : ApplicationReachable run (· + ·) 0 leaderApplied :=
  .next (atTime_reachable 9 (by decide))
    (ApplicationStep.apply (atTime 9) n0 ⟨1, 1, 7⟩ (by decide) (by decide) (by decide))

def networkTen : ApplicationState cluster ℕ := { leaderApplied with time := 10 }
def networkEleven : ApplicationState cluster ℕ := { leaderApplied with time := 11 }

theorem networkTen_reachable : ApplicationReachable run (· + ·) 0 networkTen :=
  .next leaderApplied_reachable (ApplicationStep.network leaderApplied (by decide))

theorem networkEleven_reachable : ApplicationReachable run (· + ·) 0 networkEleven :=
  .next networkTen_reachable (ApplicationStep.network networkTen (by decide))

def bothApplied : ApplicationState cluster ℕ :=
  applyNext (· + ·) networkEleven n1 ⟨1, 1, 7⟩

theorem bothApplied_reachable : ApplicationReachable run (· + ·) 0 bothApplied :=
  .next networkEleven_reachable
    (ApplicationStep.apply networkEleven n1 ⟨1, 1, 7⟩ (by decide) (by decide) (by decide))

example : bothApplied.value n0 = 7 ∧ bothApplied.value n1 = 7 ∧
    bothApplied.lastApplied n0 = 1 ∧ bothApplied.lastApplied n1 = 1 := by decide

example : ApplicationInvariant run (· + ·) 0 bothApplied :=
  application_invariant run (· + ·) 0 bothApplied_reachable

example : bothApplied.value n1 =
    applyCommitPrefix (· + ·) 0 ((run.state 11).servers n1).log 1 :=
  application_replay run (· + ·) 0 bothApplied_reachable n1

example : IsCommittedAt run 11 0 ⟨1, 1, 7⟩ :=
  applied_has_commit run (· + ·) 0 bothApplied_reachable n1 0 ⟨1, 1, 7⟩ (by decide)

/-- Even a majority-replicated entry cannot be applied before the actual commit. -/
example : ¬ ApplicationReachable run (· + ·) 0
    (applyNext (· + ·) (atTime 8) n0 ⟨1, 1, 7⟩) := by
  intro h
  have hb := (application_invariant run (· + ·) 0 h).bound n0
  change 1 ≤ 0 at hb
  omega

/-- A follower with the entry but no propagated commit count cannot apply it. -/
example : ¬ ApplicationReachable run (· + ·) 0
    (applyNext (· + ·) (atTime 9) n1 ⟨1, 1, 7⟩) := by
  intro h
  have hb := (application_invariant run (· + ·) 0 h).bound n1
  change 1 ≤ 0 at hb
  omega

example {σ : Type*} (step : σ → ℕ → σ) (s₀ : σ)
    (a b : List LogEntry) (c d : ℕ) (hd : d ≤ c)
    (h : ∀ i, i < c → a[i]? = b[i]?) :
    applyCommitPrefix step s₀ a d = applyCommitPrefix step s₀ b d :=
  state_machine_prefix_consistency step s₀ a b c d h hd

example {σ : Type*} (step : σ → ℕ → σ) (s₀ : σ) (log : List LogEntry)
    (a b : ℕ) (hab : a ≤ b) :
    applyCommitPrefix step s₀ log b =
      (((log.drop a).take (b-a)).map LogEntry.cmd).foldl step
        (applyCommitPrefix step s₀ log a) :=
  applyCommitPrefix_advance step s₀ log a b hab

example :
    DistributedRaftLogAppend.LogsMatchUpTo
      ([⟨1, 1, 7⟩].map toConsensus) ([⟨1, 1, 9⟩].map toConsensus) 1 ∧
    applyCommitPrefix (· + ·) 0 [⟨1, 1, 7⟩] 1 ≠
      applyCommitPrefix (· + ·) 0 [⟨1, 1, 9⟩] 1 :=
  metadata_matching_insufficient

/-- A second application of the same sole committed entry is not reachable. -/
example : ¬ ApplicationReachable run (· + ·) 0
    (applyNext (· + ·) bothApplied n1 ⟨1, 1, 7⟩) := by
  intro h
  have hb := (application_invariant run (· + ·) 0 h).bound n1
  change 2 ≤ 1 at hb
  omega

/-- Matching metadata cannot substitute a different command during application. -/
example : ¬ ApplicationReachable run (· + ·) 0
    (applyNext (· + ·) networkEleven n1 ⟨1, 1, 9⟩) := by
  intro h
  have hp := (application_invariant run (· + ·) 0 h).log_prefix n1
  change [⟨1, 1, 9⟩] = ([⟨1, 1, 7⟩] : List LogEntry) at hp
  exact (by decide : ([⟨1, 1, 9⟩] : List LogEntry) ≠ [⟨1, 1, 7⟩]) hp

example : applyCommitPrefix (fun (s cmd : ℕ) => 10 * s + cmd) 0
    [⟨1, 1, 7⟩, ⟨2, 1, 9⟩] 2 = 79 := by decide

/-- The old-term majority counterexample is an actual reachable network trace. -/
example : Reachable DistributedRaftCommitApplicationExample.majorityState ∧
    Relation.ReflTransGen Step DistributedRaftCommitApplicationExample.majorityState
      DistributedRaftCommitApplicationExample.overwrittenState :=
  ⟨DistributedRaftCommitApplicationExample.uncommitted_overwriting_counterexample.1,
    DistributedRaftCommitApplicationExample.uncommitted_overwriting_counterexample.2.1⟩

example :
    applyCommitPrefix (fun (_ cmd : ℕ) => cmd) 0
      (DistributedRaftCommitApplicationExample.majorityState.servers 2).log 1 = 10 ∧
    applyCommitPrefix (fun (_ cmd : ℕ) => cmd) 0
      (DistributedRaftCommitApplicationExample.overwrittenState.servers 2).log 1 = 20 :=
  DistributedRaftCommitApplicationExample.premature_prefix_application_changes

end RaftCommitApplicationRegression
