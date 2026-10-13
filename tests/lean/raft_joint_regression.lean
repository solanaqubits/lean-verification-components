import Verification.DistributedRaftJointConsensusReconfig

open DistributedRaftJointConsensusReconfig

-- Quorum arithmetic does not assert old/new intersection.
example : is_stable_quorum {0} {0} ∧ is_stable_quorum {1} {1} ∧
    ({0} ∩ {1} : Finset NodeId) = ∅ := counterexample_direct_switch_disjoint
example : is_joint_quorum {0, 1} {0} {1} := by decide
example : ¬ is_joint_quorum {0} {0} {1} := by decide
example : ¬ is_joint_quorum {1} {0} {1} := by decide

-- A reachable, complete handover between disjoint singleton configurations.
example : Reachable Examples.s₁₂ := Examples.reach₁₂
example : (Examples.s₁₂.servers 0).role = .follower ∧
    (Examples.s₁₂.servers 0).commitIndex = 2 := by decide
example : active (Examples.s₄.servers 0) = Examples.disjoint.jointConfig ∧
    (Examples.s₄.servers 0).commitIndex = 0 := Examples.local_uncommitted_activation
example : ¬ mayAppend (Examples.s₄.servers 0) (.config Examples.disjoint.finalConfig) :=
  Examples.new_before_joint_commit_rejected

-- A different leader replaces an uncommitted joint entry in a later term.
example : Reachable RollbackExample.r₁₇ := RollbackExample.reach₁₇
example : (RollbackExample.r₁₇.servers 1).role = .leader ∧
    (RollbackExample.r₁₇.servers 1).currentTerm = 2 ∧
    active (RollbackExample.r₁₇.servers 0) = RollbackExample.cfg.initial := by decide

-- The operational proof is stronger than uniqueness of the local Option field.
example {C : Transition} {s : GlobalState C} (h : Reachable s) (t v a b : ℕ)
    (ha : (t, v, a) ∈ s.cast) (hb : (t, v, b) ∈ s.cast) : a = b :=
  single_vote_preserved h t v a b ha hb
example {C : Transition} {s : GlobalState C} (h : Reachable s) {t a b : ℕ}
    (ha : (t, a, C.initial) ∈ s.elected) (hb : (t, b, C.jointConfig) ∈ s.elected) : a = b :=
  old_joint_election_safety h ha hb
example {C : Transition} {s : GlobalState C} (h : Reachable s) {t a b : ℕ}
    (ha : (t, a, C.jointConfig) ∈ s.elected) (hb : (t, b, C.finalConfig) ∈ s.elected) : a = b :=
  joint_new_election_safety h ha hb

-- Scope guard: no global dynamic safety theorem is exported by this draft.
-- Local exact bridge to the existing fixed-cluster conflict-sensitive merge.
example (a b : List DistributedRaftLeaderCompleteness.LogEntry) (prev : ℕ) :
    appendEntriesLog (a.map ofFixedEntry) prev (b.map ofFixedEntry) =
    (DistributedRaftStateMachine.appendEntriesLog a prev b).map ofFixedEntry :=
  fixed_cluster_append_entries_bridge a b prev

#print axioms old_joint_election_safety
#print axioms joint_new_election_safety
#print axioms Examples.disjoint_transition_and_retirement
#print axioms RollbackExample.leader_change_rolls_back_uncommitted_joint

-- The destination configuration can elect its own leader after the handover.
example : Reachable Examples.s₁₄ := Examples.reach₁₄
example : (Examples.s₁₄.servers 1).role = .leader ∧
    (Examples.s₁₄.servers 1).currentTerm = 2 := by decide

-- Every reachable state admits a finite history with proved lower-layer origins.
example {C : Transition} {s : GlobalState C} (hr : Reachable s) :
    ∃ run : Execution C, run.state run.length = s ∧
      ProvenHistoryInvariant run run.length := by
  obtain ⟨run, hs⟩ := reachable_execution hr
  exact ⟨run, hs, proven_history_invariant run run.length le_rfl⟩

-- The new-only candidate in this real disjoint handover has a strictly earlier commit.
example : ∃ run : Execution Examples.disjoint,
    run.state run.length = Examples.s₁₃ ∧
    ∃ j owner a committer bound, a < j ∧ j < run.length ∧
      CommitEvent run a committer bound ∧
      ((run.state a).servers committer).currentTerm < 2 ∧
      active ((run.state j).servers owner) = Examples.disjoint.jointConfig := by
  obtain ⟨run, hs⟩ := reachable_execution Examples.reach₁₃
  refine ⟨run, hs, ?_⟩
  have hc : ((run.state run.length).servers 1).role = .candidate := by rw [hs]; decide
  have ha : active ((run.state run.length).servers 1) = Examples.disjoint.finalConfig := by
    rw [hs]; decide
  have h := new_candidate_has_earlier_commit run run.length le_rfl 1 hc ha (by decide)
  simpa only [hs, show (Examples.s₁₃.servers 1).currentTerm = 2 from rfl] using h

-- Freshness is attached to the candidate's retained campaign log and a real voter snapshot.
example {C : Transition} (run : Execution C) (k candidate voter : ℕ) (hk : k ≤ run.length)
    (hc : ((run.state k).servers candidate).role = .candidate)
    (hv : (((run.state k).servers candidate).currentTerm, voter, candidate) ∈
      (run.state k).cast) :
    ∃ j, j < k ∧ upToDateFields ((run.state j).servers voter)
      (lastIndex ((run.state k).servers candidate).log)
      (lastTerm ((run.state k).servers candidate).log) :=
  candidate_vote_historical_freshness run k hk candidate voter hc hv

#print axioms proven_history_invariant
#print axioms new_candidate_has_earlier_commit
#print axioms candidate_vote_historical_freshness

-- Historical quorum witnesses include the ordering of receipt and later vote.
#check candidate_vote_timed_freshness
#check ack_precedes_later_vote
#check joint_commit_election_common_voter
#print axioms joint_commit_election_common_voter

-- The base case is now exported by the module rather than reproved in the harness.
example {C : Transition} {s : GlobalState C} (hr : Reachable s)
    {a b : NodeId} {cfgA cfgB : Config}
    (ha : (1, a, cfgA) ∈ s.elected) (hb : (1, b, cfgB) ∈ s.elected) : a = b :=
  first_term_election_safety hr ha hb

-- Election tenure is not a valid invariant after removing the leader.
example : (1, 0, Examples.disjoint.initial) ∈ Examples.s₁₂.elected ∧
    (Examples.s₁₂.servers 0).currentTerm = 1 ∧
    (Examples.s₁₂.servers 0).role = .follower := by decide

-- Freshness alone cannot justify committed-prefix inclusion.
example : logUpToDate [⟨1, 2, .command 9⟩] [⟨1, 1, .command 7⟩] ∧
    ¬ ([⟨1, 1, .command 7⟩] : List LogEntry).IsPrefix [⟨1, 2, .command 9⟩] := by
  unfold logUpToDate
  decide

-- A short compatible batch retains the already present suffix.
example : appendEntriesLog [⟨1, 1, .command 7⟩, ⟨2, 1, .command 8⟩] 0
    [⟨1, 1, .command 7⟩] = [⟨1, 1, .command 7⟩, ⟨2, 1, .command 8⟩] := by decide

#print axioms first_term_election_safety
#print axioms elected_not_candidate_reachable
#print axioms log_matching_of_prior_election_safety
#print axioms commit_quorum_replica
#print axioms joint_commit_prefix_in_later_leader_aux
#print axioms joint_prefix_in_candidate_aux
#print axioms joint_commit_blocks_old_candidate_aux

-- The final interfaces require reachability, never an auxiliary safety assumption.
example {C : Transition} {s : GlobalState C} (hr : Reachable s)
    (t a b : ℕ) (cfgA cfgB : Config)
    (ha : (t, a, cfgA) ∈ s.elected) (hb : (t, b, cfgB) ∈ s.elected) : a = b :=
  raft_reconfig_election_safety hr t a b cfgA cfgB ha hb

example {C : Transition} (run : Execution C) (time node position : ℕ)
    (ht : time ≤ run.length) (hp : position < ((run.state time).servers node).commitIndex) :
    ∃ e, ((run.state time).servers node).log[position]? = some e ∧
      HistoricallyCommitted run time position e :=
  commit_index_soundness run time ht node position hp

-- This interface also covers identical old and new memberships: no distinctness premise.
example {C : Transition} (run : Execution C) (time node : ℕ) (ht : time ≤ run.length)
    (guard : mayAppend ((run.state time).servers node) (.config C.finalConfig)) :
    JointBarrierBefore run time ((run.state time).servers node).currentTerm :=
  joint_committed_before_new_created run time ht node guard

-- Removed leaders remain covered by the unconditional state invariants.
example : ElectionHistorySafe Examples.s₁₂ ∧ GlobalLogMatching Examples.s₁₂ :=
  ⟨raft_reconfig_election_safety Examples.reach₁₂, raft_reconfig_log_matching Examples.reach₁₂⟩

-- Actual rollback and disjoint handover are covered, not merely static quorum sets.
example : ElectionHistorySafe RollbackExample.r₁₇ ∧ GlobalLogMatching RollbackExample.r₁₇ :=
  ⟨raft_reconfig_election_safety RollbackExample.reach₁₇,
    raft_reconfig_log_matching RollbackExample.reach₁₇⟩

example : DistributedRaftJointConsensusReconfigSuite := distributed_raft_joint_consensus_master_suite

#print axioms raft_reconfig_election_safety
#print axioms raft_reconfig_log_matching
#print axioms raft_reconfig_leader_completeness
#print axioms commit_index_soundness
#print axioms committed_prefix_preserved_at_election
#print axioms joint_committed_before_new_created
#print axioms distributed_raft_joint_consensus_master_suite
