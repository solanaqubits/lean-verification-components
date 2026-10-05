/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedRaftCommitIndexInvariant
import Verification.DistributedRaftCommitApplicationExample
import Verification.DistributedRaftLogAppend
import Verification.DistributedRaftLogReplication

/-! # Commitment and deterministic application

Majority replication in one snapshot is distinct from a real current-term commit.
The operational entry type is reused; explicit adapters connect the older list APIs.
-/
namespace DistributedRaftCommitApplication

open DistributedRaftLeaderCompleteness (Cluster NodeId LogEntry majority quorum_intersection)
open DistributedRaftStateMachine
open DistributedRaftEventHistory
open DistributedRaftCompleteBridge
open DistributedRaftCommitIndexInvariant

variable {C : Cluster} {σ : Type*}

/-- Snapshot replication, not operational commitment. Positions are zero-based. -/
def MajorityReplicatedAt (logs : NodeId C → List LogEntry) (idx t : ℕ) : Prop :=
  ∃ Q : Finset (NodeId C), majority C Q ∧
    ∀ n ∈ Q, ∃ e, (logs n)[idx]? = some e ∧ e.term = t

/-- Two majority claims about the same immutable snapshot agree, with no leader axiom. -/
theorem quorum_intersection_committed_uniqueness
    (logs : NodeId C → List LogEntry) (idx t₁ t₂ : ℕ)
    (h₁ : MajorityReplicatedAt logs idx t₁) (h₂ : MajorityReplicatedAt logs idx t₂) :
    t₁ = t₂ := by
  obtain ⟨Q₁, hQ₁, h₁⟩ := h₁
  obtain ⟨Q₂, hQ₂, h₂⟩ := h₂
  obtain ⟨v, hv⟩ := quorum_intersection C Q₁ Q₂ hQ₁ hQ₂
  obtain ⟨a, ha, hat⟩ := h₁ v (Finset.mem_inter.mp hv).1
  obtain ⟨b, hb, hbt⟩ := h₂ v (Finset.mem_inter.mp hv).2
  have : a = b := Option.some.inj (ha.symm.trans hb)
  subst b
  exact hat.symm.trans hbt

/-- Entry occurrence in the prefix of an actual commit event of this execution. -/
def IsCommittedAt (run : Execution C) (time idx : ℕ) (e : LogEntry) : Prop :=
  ∃ k leader c, k < time ∧ CommitEvent run k leader c ∧ idx < c ∧
    (((run.state k).servers leader).log)[idx]? = some e

/-- The command type in the existing models is Nat; the application state is arbitrary. -/
def applyCommitPrefix (step : σ → ℕ → σ) (s₀ : σ)
    (log : List LogEntry) (commitIdx : ℕ) : σ :=
  ((log.take commitIdx).map LogEntry.cmd).foldl step s₀

theorem commit_prefix_take_monotonic (log : List LogEntry) (c₁ c₂ : ℕ) (h : c₁ ≤ c₂) :
    (log.take c₁).IsPrefix (log.take c₂) := List.take_prefix_take_left h

/-- Adapter to the legacy consensus/list-append API, not a new entry type. -/
def toConsensus (e : LogEntry) : DistributedRaftConsensus.LogEntry :=
  ⟨e.index, e.term⟩

/-- Adapter to the independently declared legacy replication API. -/
def toReplication (e : LogEntry) : DistributedRaftLogReplication.LogEntry :=
  ⟨e.index, e.term, e.cmd⟩

theorem applyCommitPrefix_legacy (step : σ → ℕ → σ) (s₀ : σ)
    (log : List LogEntry) (c : ℕ) :
    applyCommitPrefix step s₀ log c =
      (DistributedRaftLogReplication.applyEntries (log.map toReplication) c).foldl step s₀ := by
  simp [applyCommitPrefix, DistributedRaftLogReplication.applyEntries, List.map_take,
    List.map_map, Function.comp_def, toReplication]

/-- Full-entry agreement is essential: the old consensus predicate omits commands. -/
theorem state_machine_prefix_consistency (step : σ → ℕ → σ) (s₀ : σ)
    (log₁ log₂ : List LogEntry) (c c' : ℕ)
    (hm : ∀ i, i < c → log₁[i]? = log₂[i]?) (hc : c' ≤ c) :
    applyCommitPrefix step s₀ log₁ c' = applyCommitPrefix step s₀ log₂ c' := by
  have he : log₁.take c' = log₂.take c' := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < c'
    · rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi]
      exact hm i (by omega)
    · simp [hi]
  simp [applyCommitPrefix, he]

theorem applyCommitPrefix_succ (step : σ → ℕ → σ) (s₀ : σ)
    (log : List LogEntry) (i : ℕ) (e : LogEntry) (he : log[i]? = some e) :
    applyCommitPrefix step s₀ log (i + 1) = step (applyCommitPrefix step s₀ log i) e.cmd := by
  simp [applyCommitPrefix, List.take_add_one, he, List.map_append, List.foldl_append]

/-- Advancing a prefix applies exactly the new slice, in order, without replaying old commands. -/
theorem applyCommitPrefix_advance (step : σ → ℕ → σ) (s₀ : σ)
    (log : List LogEntry) (a b : ℕ) (hab : a ≤ b) :
    applyCommitPrefix step s₀ log b =
      (((log.drop a).take (b-a)).map LogEntry.cmd).foldl step
        (applyCommitPrefix step s₀ log a) := by
  have hb : b = a + (b-a) := by omega
  conv_lhs => rw [hb]
  simp [applyCommitPrefix, List.take_add, List.map_append, List.foldl_append]

/-- The old two-field log predicate cannot guarantee agreement of applied commands. -/
theorem metadata_matching_insufficient :
    let a : List LogEntry := [⟨1, 1, 7⟩]
    let b : List LogEntry := [⟨1, 1, 9⟩]
    DistributedRaftLogAppend.LogsMatchUpTo (a.map toConsensus) (b.map toConsensus) 1 ∧
      applyCommitPrefix (· + ·) 0 a 1 ≠ applyCommitPrefix (· + ·) 0 b 1 := by
  constructor
  · intro i _
    rfl
  · decide

/-- Advancing network time may not alter a prefix already known committed locally. -/
theorem take_eq_of_prefix {p l : List LogEntry} (hp : p.IsPrefix l) (i : ℕ)
    (hi : i ≤ p.length) : l.take i = p.take i := by
  obtain ⟨tail, rfl⟩ := hp
  simp [List.take_append, Nat.sub_eq_zero_of_le hi]

/-- Application metadata is a conservative overlay: it never changes Raft state or RPC guards. -/
structure ApplicationState (C : Cluster) (σ : Type*) where
  time : ℕ
  lastApplied : NodeId C → ℕ
  applied : NodeId C → List LogEntry
  value : NodeId C → σ

def initialApplication (s₀ : σ) : ApplicationState C σ :=
  ⟨0, fun _ => 0, fun _ => [], fun _ => s₀⟩

def applyNext (step : σ → ℕ → σ) (a : ApplicationState C σ)
    (v : NodeId C) (e : LogEntry) : ApplicationState C σ :=
  { a with
    lastApplied := Function.update a.lastApplied v (a.lastApplied v + 1)
    applied := Function.update a.applied v (a.applied v ++ [e])
    value := Function.update a.value v (step (a.value v) e.cmd) }

/-- Network moves advance an existing execution. Apply reads the next real log entry.
The guards do not assume that the entry has a commit witness or that prefixes are safe. -/
inductive ApplicationStep (run : Execution C) (step : σ → ℕ → σ) :
    ApplicationState C σ → ApplicationState C σ → Prop where
  | network (a) : a.time < run.length →
      ApplicationStep run step a { a with time := a.time + 1 }
  | apply (a) (v : NodeId C) (e : LogEntry) : a.time ≤ run.length →
      a.lastApplied v < ((run.state a.time).servers v).commitIndex →
      (((run.state a.time).servers v).log)[a.lastApplied v]? = some e →
      ApplicationStep run step a (applyNext step a v e)

inductive ApplicationReachable (run : Execution C) (step : σ → ℕ → σ) (s₀ : σ) :
    ApplicationState C σ → Prop where
  | init : ApplicationReachable run step s₀ (initialApplication s₀)
  | next {a b} : ApplicationReachable run step s₀ a → ApplicationStep run step a b →
      ApplicationReachable run step s₀ b

structure ApplicationInvariant (run : Execution C) (step : σ → ℕ → σ) (s₀ : σ)
    (a : ApplicationState C σ) : Prop where
  within : a.time ≤ run.length
  bound : ∀ v, a.lastApplied v ≤ ((run.state a.time).servers v).commitIndex
  log_prefix : ∀ v, a.applied v = ((run.state a.time).servers v).log.take (a.lastApplied v)
  fold : ∀ v, a.value v = ((a.applied v).map LogEntry.cmd).foldl step s₀

theorem application_initial (run : Execution C) (step : σ → ℕ → σ) (s₀ : σ) :
    ApplicationInvariant run step s₀ (initialApplication s₀) := by
  constructor
  · exact Nat.zero_le _
  · intro v; exact Nat.zero_le _
  · intro v; simp [initialApplication]
  · intro v; simp [initialApplication]

theorem application_invariant_step (run : Execution C) (step : σ → ℕ → σ) (s₀ : σ)
    {a b : ApplicationState C σ} (ha : ApplicationInvariant run step s₀ a)
    (st : ApplicationStep run step a b) : ApplicationInvariant run step s₀ b := by
  cases st with
  | network ht =>
    constructor
    · dsimp; omega
    · intro v
      exact (ha.bound v).trans (commitIndex_step_monotone (run.transition a.time ht) v)
    · intro v
      have hp := execution_commit_prefix_stable run a.time (a.time + 1)
        (by omega) (by omega) v
      have hlen := execution_commitIndex_bound run a.time ha.within v
      have he := take_eq_of_prefix hp (a.lastApplied v) (by
        simp only [List.length_take]; have := ha.bound v; omega)
      simp only [List.take_take, Nat.min_eq_left (ha.bound v)] at he
      exact (ha.log_prefix v).trans he.symm
    · exact ha.fold
  | apply v e ht hg he =>
    constructor
    · exact ht
    · intro w
      by_cases hw : w = v
      · subst w; simpa [applyNext] using (Nat.succ_le_of_lt hg)
      · simpa [applyNext, Function.update_of_ne hw] using ha.bound w
    · intro w
      by_cases hw : w = v
      · subst w
        simp only [applyNext, Function.update_self]
        rw [ha.log_prefix, List.take_add_one, he]
        rfl
      · simpa [applyNext, Function.update_of_ne hw] using ha.log_prefix w
    · intro w
      by_cases hw : w = v
      · subst w
        simp [applyNext, ha.fold v, List.map_append, List.foldl_append]
      · simpa [applyNext, Function.update_of_ne hw] using ha.fold w

theorem application_invariant (run : Execution C) (step : σ → ℕ → σ) (s₀ : σ)
    {a : ApplicationState C σ} (hr : ApplicationReachable run step s₀ a) :
    ApplicationInvariant run step s₀ a := by
  induction hr with
  | init => exact application_initial run step s₀
  | next _ st ih => exact application_invariant_step run step s₀ ih st

/-- Actual application agrees with deterministic replay of precisely the applied prefix. -/
theorem application_replay (run : Execution C) (step : σ → ℕ → σ) (s₀ : σ)
    {a : ApplicationState C σ} (hr : ApplicationReachable run step s₀ a) (v : NodeId C) :
    a.value v = applyCommitPrefix step s₀ ((run.state a.time).servers v).log (a.lastApplied v) := by
  have h := application_invariant run step s₀ hr
  simpa [applyCommitPrefix, h.log_prefix v] using h.fold v

/-- Both network and application moves preserve monotone application indices. -/
theorem lastApplied_step_monotone (run : Execution C) (step : σ → ℕ → σ)
    {a b : ApplicationState C σ} (st : ApplicationStep run step a b) (v : NodeId C) :
    a.lastApplied v ≤ b.lastApplied v := by
  cases st with
  | network => exact le_rfl
  | apply w e _ _ _ =>
    by_cases hv : v = w
    · subst v; simp [applyNext]
    · simp [applyNext, Function.update_of_ne hv]

/-- Every entry eligible for application has a real earlier current-term commit event.
This is derived from commitIndex provenance, not an application transition premise. -/
theorem below_commit_is_committed (run : Execution C) (time : ℕ) (ht : time ≤ run.length)
    (v : NodeId C) (idx : ℕ) (e : LogEntry)
    (hi : idx < ((run.state time).servers v).commitIndex)
    (he : (((run.state time).servers v).log)[idx]? = some e) :
    IsCommittedAt run time idx e := by
  obtain ⟨k, leader, c, hk, hc, hp⟩ :=
    execution_commit_provenance run time ht v (by omega)
  have hlen := execution_commitIndex_bound run time ht v
  have hci : ((run.state time).servers v).commitIndex ≤ c := by
    have := hp.length_le
    simp only [List.length_take] at this
    omega
  refine ⟨k, leader, c, hk, hc, by omega, ?_⟩
  have hx : ((((run.state time).servers v).log).take
      ((run.state time).servers v).commitIndex)[idx]? = some e := by
    rw [List.getElem?_take_of_lt hi]; exact he
  obtain ⟨tail, htail⟩ := hp
  have hit : idx < (((run.state time).servers v).log.take
      ((run.state time).servers v).commitIndex).length := by
    simp only [List.length_take]; omega
  have hy : ((((run.state k).servers leader).log).take c)[idx]? = some e := by
    rw [← htail, List.getElem?_append_left hit]; exact hx
  rwa [List.getElem?_take_of_lt (by omega : idx < c)] at hy

/-- Previously applied entries remain justified even while network time advances. -/
theorem applied_has_commit (run : Execution C) (step : σ → ℕ → σ) (s₀ : σ)
    {a : ApplicationState C σ} (hr : ApplicationReachable run step s₀ a)
    (v : NodeId C) (idx : ℕ) (e : LogEntry) (he : (a.applied v)[idx]? = some e) :
    IsCommittedAt run a.time idx e := by
  have h := application_invariant run step s₀ hr
  have hidx : idx < a.lastApplied v := by
    have hi := List.getElem?_eq_some_iff.mp he
    obtain ⟨hi, _⟩ := hi
    rw [h.log_prefix] at hi
    simp only [List.length_take] at hi
    omega
  apply below_commit_is_committed run a.time h.within v idx e
    (lt_of_lt_of_le hidx (h.bound v))
  rw [h.log_prefix, List.getElem?_take_of_lt hidx] at he
  exact he

/-- The next entry is available whenever the application guard holds.
This is local enabledness, not fairness or eventual application. -/
theorem application_enabled (run : Execution C) (step : σ → ℕ → σ) (s₀ : σ)
    {a : ApplicationState C σ} (hr : ApplicationReachable run step s₀ a)
    (v : NodeId C) (hg : a.lastApplied v < ((run.state a.time).servers v).commitIndex) :
    ∃ e, ApplicationReachable run step s₀ (applyNext step a v e) := by
  have h := application_invariant run step s₀ hr
  have hi := lt_of_lt_of_le hg (execution_commitIndex_bound run a.time h.within v)
  exact ⟨_, hr.next (.apply a v _ h.within hg (List.getElem?_eq_getElem hi))⟩

theorem applied_history_step_prefix (run : Execution C) (step : σ → ℕ → σ)
    {a b : ApplicationState C σ} (st : ApplicationStep run step a b) (v : NodeId C) :
    (a.applied v).IsPrefix (b.applied v) := by
  cases st with
  | network => exact List.prefix_refl _
  | apply w e _ _ _ =>
    by_cases hv : v = w
    · subst v; simp [applyNext]
    · simp [applyNext, Function.update_of_ne hv]

open DistributedRaftCommitApplicationExample
  (majorityState overwrittenState oldEntry replacementEntry)

/-- A reachable Figure-8-style counterexample, not arbitrary fabricated snapshots. -/
theorem uncommitted_overwriting_counterexample :
    Reachable majorityState ∧ Relation.ReflTransGen Step majorityState overwrittenState ∧
    MajorityReplicatedAt (fun v => (majorityState.servers v).log) 0 oldEntry.term ∧
    (majorityState.servers 2).commitIndex = 0 ∧
    applyCommitPrefix (fun (_ : ℕ) cmd => cmd) 0 (majorityState.servers 2).log 1 ≠
      applyCommitPrefix (fun (_ : ℕ) cmd => cmd) 0 (overwrittenState.servers 2).log 1 := by
  refine ⟨DistributedRaftCommitApplicationExample.majorityState_reachable,
    DistributedRaftCommitApplicationExample.majority_to_overwrite, ?_, ?_, ?_⟩
  · refine ⟨{0, 1, 2}, DistributedRaftCommitApplicationExample.old_term_majority.1, ?_⟩
    intro v hv
    refine ⟨oldEntry, ?_, rfl⟩
    dsimp only
    rw [DistributedRaftCommitApplicationExample.old_term_majority.2 v hv]
    rfl
  · exact DistributedRaftCommitApplicationExample.no_operational_commit.1 2
  · decide

structure DistributedRaftCommitApplicationSuite : Prop where
  quorum_unique : ∀ (C : Cluster) (logs : NodeId C → List LogEntry) idx t₁ t₂,
    MajorityReplicatedAt logs idx t₁ → MajorityReplicatedAt logs idx t₂ → t₁ = t₂
  prefix_monotone : ∀ (log : List LogEntry) a b, a ≤ b →
    (log.take a).IsPrefix (log.take b)
  bounded_commit : ∀ (C : Cluster) (run : Execution C) k, k ≤ run.length →
    ∀ v, ((run.state k).servers v).commitIndex ≤ ((run.state k).servers v).log.length
  monotone_commit : ∀ (C : Cluster) (run : Execution C) a b, a ≤ b → b ≤ run.length →
    ∀ v, ((run.state a).servers v).commitIndex ≤ ((run.state b).servers v).commitIndex
  stable_commit : ∀ (C : Cluster) (run : Execution C) a b, a ≤ b → b ≤ run.length →
    ∀ v, (((run.state a).servers v).log.take ((run.state a).servers v).commitIndex).IsPrefix
      ((run.state b).servers v).log
  consistent_fold : ∀ (σ : Type) (step : σ → ℕ → σ) (s₀ : σ) log₁ log₂ c c',
    (∀ i, i < c → log₁[i]? = log₂[i]?) → c' ≤ c →
    applyCommitPrefix step s₀ log₁ c' = applyCommitPrefix step s₀ log₂ c'
  application_invariant : ∀ (C : Cluster) (σ : Type) (run : Execution C)
    (step : σ → ℕ → σ) s₀ a, ApplicationReachable run step s₀ a →
    ApplicationInvariant run step s₀ a
  application_commit : ∀ (C : Cluster) (σ : Type) (run : Execution C)
    (step : σ → ℕ → σ) s₀ a, ApplicationReachable run step s₀ a →
    ∀ v i e, (a.applied v)[i]? = some e → IsCommittedAt run a.time i e
  counterexample : Reachable majorityState ∧
    Relation.ReflTransGen Step majorityState overwrittenState ∧
    MajorityReplicatedAt (fun v => (majorityState.servers v).log) 0 oldEntry.term ∧
    (majorityState.servers 2).commitIndex = 0 ∧
    applyCommitPrefix (fun (_ : ℕ) cmd => cmd) 0 (majorityState.servers 2).log 1 ≠
      applyCommitPrefix (fun (_ : ℕ) cmd => cmd) 0 (overwrittenState.servers 2).log 1

theorem distributed_raft_commit_application_master_suite :
    DistributedRaftCommitApplicationSuite := {
  quorum_unique := fun _ => quorum_intersection_committed_uniqueness
  prefix_monotone := commit_prefix_take_monotonic
  bounded_commit := fun _ => execution_commitIndex_bound
  monotone_commit := fun _ => execution_commitIndex_monotone
  stable_commit := fun _ => execution_commit_prefix_stable
  consistent_fold := fun _ => state_machine_prefix_consistency
  application_invariant := fun _ _ run step s₀ _ => application_invariant run step s₀
  application_commit := fun _ _ run step s₀ _ => applied_has_commit run step s₀
  counterexample := uncommitted_overwriting_counterexample
}

end DistributedRaftCommitApplication
