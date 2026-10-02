import Verification.DistributedRaftNetworkInduction

namespace RaftNetworkRegression

open DistributedRaftLeaderCompleteness (LogEntry)
open DistributedRaftStateMachine
open DistributedRaftNetworkInduction

/-- The global theorem applies to the existing nonempty committed execution. -/
example : GlobalLogMatching Examples.committed :=
  reachable_global_log_matching _ Examples.committed_reachable

example :
    (Examples.committed.servers Examples.n0).log.take 1 =
    (Examples.committed.servers Examples.n1).log.take 1 := by
  exact (reachable_global_log_matching _ Examples.committed_reachable)
    Examples.n0 Examples.n1 0 ⟨1, 1, 7⟩ ⟨1, 1, 7⟩ (by decide) (by decide) rfl

/-- Duplication and loss exercise the original queue transitions. -/
def duplicated : GlobalState Examples.cluster :=
  { Examples.appended with
    network := Examples.appendRequest Examples.n2 :: Examples.appended.network }

theorem duplicated_reachable : Reachable duplicated :=
  Examples.appended_reachable.step (Step.duplicate (by decide))

example : GlobalLogMatching duplicated :=
  reachable_global_log_matching _ duplicated_reachable

example : NetworkLogConsistency duplicated :=
  reachable_network_log_consistency duplicated_reachable

example : Generated duplicated 0 ⟨1, 1, 7⟩ := by
  apply reachable_network_entry_origin duplicated_reachable
    (dst := Examples.n2) (leader := Examples.n0) (t := 1)
    (prev := 0) (pt := 0) (lc := 0) (entries := [⟨1, 1, 7⟩]) (offset := 0)
  · decide
  · rfl

def dropped : GlobalState Examples.cluster :=
  consume duplicated [] Examples.appended.network

theorem dropped_reachable : Reachable dropped :=
  duplicated_reachable.step
    (Step.drop (m := Examples.appendRequest Examples.n2)
      (before := []) (after := Examples.appended.network) rfl)

example : GlobalLogMatching dropped :=
  reachable_global_log_matching _ dropped_reachable

example : (dropped.servers Examples.n0).log = [⟨1, 1, 7⟩] := by decide

/-- Equal index/term alone does not constrain arbitrary, non-reachable input logs. -/
theorem conflicting_commands_do_not_match :
    ¬ LogMatching [⟨1, 1, 7⟩] [⟨1, 1, 8⟩] := by
  intro matching
  have impossible := matching 0 ⟨1, 1, 7⟩ ⟨1, 1, 8⟩ rfl rfl rfl
  contradiction

end RaftNetworkRegression
