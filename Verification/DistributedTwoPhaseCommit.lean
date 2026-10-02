import Mathlib.Data.Nat.Basic

set_option linter.style.header false

namespace DistributedTwoPhaseCommit

/-- Supplied participant vote; no prepare-state transition is modeled. -/
inductive Vote where
  | yes
  | no
  deriving DecidableEq, Repr

inductive Decision where
  | commit
  | abort
  deriving DecidableEq, Repr

/-- Decision table for two already-collected votes. -/
def coordinatorDecision (v1 v2 : Vote) : Decision :=
  match v1, v2 with
  | Vote.yes, Vote.yes => Decision.commit
  | _, _ => Decision.abort

/-- Identity on a supplied decision, without delivery or participant state. -/
def applyDecision (d : Decision) : Decision := d

theorem commit_iff_all_yes (v1 v2 : Vote) :
    coordinatorDecision v1 v2 = Decision.commit ↔ v1 = Vote.yes ∧ v2 = Vote.yes := by
  cases v1 <;> cases v2 <;> simp [coordinatorDecision]

theorem abort_iff_any_no (v1 v2 : Vote) :
    coordinatorDecision v1 v2 = Decision.abort ↔ v1 = Vote.no ∨ v2 = Vote.no := by
  cases v1 <;> cases v2 <;> simp [coordinatorDecision]

theorem abort_on_v1_no (v2 : Vote) :
    coordinatorDecision Vote.no v2 = Decision.abort := by
  cases v2 <;> rfl

theorem abort_on_v2_no (v1 : Vote) :
    coordinatorDecision v1 Vote.no = Decision.abort := by
  cases v1 <;> rfl

/-- Reflexivity for the same supplied decision; not distributed agreement. -/
theorem global_agreement_invariant (v1 v2 : Vote) :
    let global_dec := coordinatorDecision v1 v2
    applyDecision global_dec = applyDecision global_dec := by
  rfl

namespace Responses

inductive Vote where
  | voteCommit | voteAbort
  deriving DecidableEq, Repr
inductive CohortResponse where
  | vote (v : Vote)
  | timeout
  deriving DecidableEq, Repr
inductive GlobalDecision where
  | globalCommit | globalAbort
  deriving DecidableEq, Repr
inductive LocalState where
  | committed | aborted
  deriving DecidableEq, Repr

def resolveResponse (r : CohortResponse) : Vote :=
  match r with
  | .vote v => v
  | .timeout => .voteAbort

def coordinatorDecision (r1 r2 : CohortResponse) : GlobalDecision :=
  match resolveResponse r1, resolveResponse r2 with
  | .voteCommit, .voteCommit => .globalCommit
  | _, _ => .globalAbort

def applyDecision (d : GlobalDecision) : LocalState :=
  match d with
  | .globalCommit => .committed
  | .globalAbort => .aborted

theorem resolve_timeout : resolveResponse .timeout = .voteAbort := rfl

theorem two_pc_commit_iff_both_commit (r1 r2 : CohortResponse) :
    coordinatorDecision r1 r2 = .globalCommit ↔
    resolveResponse r1 = .voteCommit ∧ resolveResponse r2 = .voteCommit := by
  unfold coordinatorDecision
  cases resolveResponse r1 <;> cases resolveResponse r2 <;> simp

theorem two_pc_abort_on_cohort1_failure (r1 r2 : CohortResponse)
    (h1 : resolveResponse r1 = .voteAbort) : coordinatorDecision r1 r2 = .globalAbort := by
  simp [coordinatorDecision, h1]

theorem two_pc_abort_on_cohort2_failure (r1 r2 : CohortResponse)
    (h2 : resolveResponse r2 = .voteAbort) : coordinatorDecision r1 r2 = .globalAbort := by
  unfold coordinatorDecision
  rw [h2]
  cases resolveResponse r1 <;> rfl

/-- Both expressions use the same decision; no delivery or independent local states. -/
theorem two_pc_agreement (r1 r2 : CohortResponse) :
    applyDecision (coordinatorDecision r1 r2) = applyDecision (coordinatorDecision r1 r2) := rfl

theorem two_pc_atomicity (r1 r2 : CohortResponse) :
    (applyDecision (coordinatorDecision r1 r2) = .committed ∧
     applyDecision (coordinatorDecision r1 r2) = .committed) ∨
    (applyDecision (coordinatorDecision r1 r2) = .aborted ∧
     applyDecision (coordinatorDecision r1 r2) = .aborted) := by
  cases coordinatorDecision r1 r2 <;> simp [applyDecision]

theorem two_pc_commit_safety (r1 r2 : CohortResponse) :
    applyDecision (coordinatorDecision r1 r2) = .committed →
    resolveResponse r1 = .voteCommit ∧ resolveResponse r2 = .voteCommit := by
  intro h
  have hd : coordinatorDecision r1 r2 = .globalCommit := by
    cases he : coordinatorDecision r1 r2 <;> simp_all [applyDecision]
  exact (two_pc_commit_iff_both_commit r1 r2).mp hd

structure ResponseFormalSuite : Prop where
  h_timeout : resolveResponse .timeout = .voteAbort
  h_commit_iff : ∀ r1 r2, coordinatorDecision r1 r2 = .globalCommit ↔
    resolveResponse r1 = .voteCommit ∧ resolveResponse r2 = .voteCommit
  h_abort_c1 : ∀ r1 r2, resolveResponse r1 = .voteAbort →
    coordinatorDecision r1 r2 = .globalAbort
  h_abort_c2 : ∀ r1 r2, resolveResponse r2 = .voteAbort →
    coordinatorDecision r1 r2 = .globalAbort
  h_agreement : ∀ r1 r2,
    applyDecision (coordinatorDecision r1 r2) = applyDecision (coordinatorDecision r1 r2)
  h_atomicity : ∀ r1 r2,
    (applyDecision (coordinatorDecision r1 r2) = .committed ∧
     applyDecision (coordinatorDecision r1 r2) = .committed) ∨
    (applyDecision (coordinatorDecision r1 r2) = .aborted ∧
     applyDecision (coordinatorDecision r1 r2) = .aborted)
  h_safety : ∀ r1 r2, applyDecision (coordinatorDecision r1 r2) = .committed →
    resolveResponse r1 = .voteCommit ∧ resolveResponse r2 = .voteCommit

theorem response_master_suite : ResponseFormalSuite := {
  h_timeout := resolve_timeout
  h_commit_iff := two_pc_commit_iff_both_commit
  h_abort_c1 := two_pc_abort_on_cohort1_failure
  h_abort_c2 := two_pc_abort_on_cohort2_failure
  h_agreement := two_pc_agreement
  h_atomicity := two_pc_atomicity
  h_safety := two_pc_commit_safety
}

end Responses

structure DistributedTwoPhaseCommitFormalSuite : Prop where
  h_commit_iff : ∀ v1 v2 : Vote,
    coordinatorDecision v1 v2 = Decision.commit ↔ v1 = Vote.yes ∧ v2 = Vote.yes
  h_abort_iff : ∀ v1 v2 : Vote,
    coordinatorDecision v1 v2 = Decision.abort ↔ v1 = Vote.no ∨ v2 = Vote.no
  h_abort_v1 : ∀ v2 : Vote, coordinatorDecision Vote.no v2 = Decision.abort
  h_abort_v2 : ∀ v1 : Vote, coordinatorDecision v1 Vote.no = Decision.abort
  h_agreement : ∀ v1 v2 : Vote,
    let d := coordinatorDecision v1 v2
    applyDecision d = applyDecision d

  h_responses : Responses.ResponseFormalSuite

/-- Registry of the decision-table properties and the stated reflexive equality. -/
theorem distributed_two_phase_commit_master_verification_suite :
    DistributedTwoPhaseCommitFormalSuite := {
  h_responses := Responses.response_master_suite
  h_commit_iff := commit_iff_all_yes
  h_abort_iff := abort_iff_any_no
  h_abort_v1 := abort_on_v1_no
  h_abort_v2 := abort_on_v2_no
  h_agreement := global_agreement_invariant
}

theorem distributed_two_phase_commit_master_suite : DistributedTwoPhaseCommitFormalSuite :=
  distributed_two_phase_commit_master_verification_suite

end DistributedTwoPhaseCommit
