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

/-- Registry of the decision-table properties and the stated reflexive equality. -/
theorem distributed_two_phase_commit_master_verification_suite :
    DistributedTwoPhaseCommitFormalSuite := {
  h_commit_iff := commit_iff_all_yes
  h_abort_iff := abort_iff_any_no
  h_abort_v1 := abort_on_v1_no
  h_abort_v2 := abort_on_v2_no
  h_agreement := global_agreement_invariant
}

end DistributedTwoPhaseCommit
