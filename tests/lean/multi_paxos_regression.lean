import Verification.DistributedMultiPaxosConsensus
open DistributedMultiPaxosConsensus

example : DistributedMultiPaxosConsensusSuite := distributed_multi_paxos_consensus_master_suite
example {α : Type} {n : ℕ} {c : Config α n} (h : Reachable c)
    {s b d v w} (hv : Chosen c s b v) (hw : Chosen c s d w) : v = w :=
  multi_paxos_slot_agreement h hv hw
example {α : Type} {n : ℕ} {c : Config α n} (h : Reachable c)
    {s b d v w} (hv : Chosen c s b v) (hbd : b < d) (hw : Proposed c d s w) : v = w :=
  inter_ballot_value_preservation h hv hbd hw
example {α : Type} {n : ℕ} {S : System α n} (h : SystemReachable S) (p q : Fin n) :
    (S.logs p).IsPrefix (S.logs q) ∨ (S.logs q).IsPrefix (S.logs p) :=
  reachable_replica_prefixes h p q
example (v : ℕ) : ∃ S : System ℕ 1, SystemReachable S ∧ S.logs 0 = [v] :=
  singleton_execution v
example : NetworkReachable ⟨Regression.c13, Regression.c13.history⟩ :=
  core_network_realization Regression.reach_c13
example : Executed Regression.c13 [7,8,9] := Regression.pipeline_executes
example : Regression.c13.history.count (.prepare Regression.b0) = 1 :=
  single_phase_one_pipeline
example : Chosen Regression.d7 0 Regression.b0 7 ∧ Chosen Regression.d7 0 Regression.b1 7 :=
  Regression.leader_change.2
example : ∀ L, ¬ ExecuteStep Regression.gap3 [] L := Regression.gap_blocks_prefix.2
example : ¬ Reachable Regression.wrongMax3 := by
  intro h
  -- Check the concrete faulty witness independently of the existential theorem.
  have a : Chosen Regression.wrongMax3 0 Regression.b0 7 := by
    refine ⟨{0,1}, by decide, ?_⟩
    simp only [Regression.wrongMax3, Regression.wrongMax2, Regression.wrongMax1,
      acceptStep, proposeStep, Voted]
    trace_simp
  have b : Chosen Regression.wrongMax3 0 Regression.b1 9 := by
    refine ⟨{1,2}, by decide, ?_⟩
    simp [Regression.wrongMax3, Regression.wrongMax2, Regression.wrongMax1,
      acceptStep, proposeStep, Voted]
  have impossible := multi_paxos_slot_agreement h a b
  omega
example {α : Type} [DecidableEq α] {n : ℕ} {c : Config α n} (h : Reachable c) (p : Fin n) :
    ExactSnapshot (c.nodes p) (serialize c p) := serialize_exact h p
example {α : Type} {n : ℕ} (hn : 0 < n) {c : Config α n} (h : Reachable c)
    (s : Slot) (encode : α → ℕ) :
    DistributedPaxos.SingleVote (legacyAccepted hn c s encode) := derived_single_vote hn h s encode
