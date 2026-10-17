import Verification.DistributedTendermintSlashingPenaltyContract
import Mathlib.Data.Fin.VecNotation

open Finset DistributedTendermintCoreSafety DistributedTendermintAccountableSafety
open DistributedTendermintSlashingPenaltyContract
namespace TendermintSlashingRegression

def weights : Fin 3 → ℚ := ![3, 1, 1]
def smallFault : Fin 3 → ℚ := ![1, 2, 2]
def zeroFault : Fin 3 → ℚ := ![0, 1, 1]
def B : Finset (Fin 3) := {0}
def cfg : Config 3 := ⟨![3, 1, 1], {0}, 17⟩

def voteAction (i : Fin 3) (r : ℕ) (p : Phase) (v : ℕ) : Action 3 :=
  if i ∈ cfg.byzantine then .faulty ⟨i, r, p, some v⟩ else .honest i p (some v)

def roundActions (ids : List (Fin 3)) (r v : ℕ) : List (Action 3) :=
  (if r = 0 then [] else ids.map fun i => .advance i r) ++
  ids.map (fun i => .propose i ⟨r, v, none⟩) ++
  ids.map (fun i => voteAction i r .prevote v) ++
  ids.flatMap (fun i => ids.map fun j => .deliver i ⟨j, r, .prevote, some v⟩) ++
  ids.map (fun i => voteAction i r .precommit v)

def trace := roundActions [0, 1] 0 7 ++ roundActions [0, 2] 1 8
def reached := (run cfg initial trace).getD initial

theorem execution : run cfg initial trace = some reached := by decide +kernel
theorem reachable : Reachable cfg reached := run_reachable cfg trace Reachable.init execution

def view := completeView cfg reached.votes

def unavailable : EvidenceView 3 := completeView cfg (reached.votes.filter (fun m => m.phase = .precommit))
def wrongHeight : EvidenceView 3 := completeView { cfg with height := 18 } reached.votes

example : (∀ v, 0 ≤ weights v) ∧ totalStake weights = 5 := by decide +kernel
example : stakeMass weights B = 3 ∧ honestWeight weights B = 2 := by decide +kernel
example : stakeSlashing weights B (1/2) 0 = 3/2 := by decide +kernel
example : stakeSlashing weights B (1/2) 1 = 1 := by decide +kernel
example : stakeSlashing weights B (1/2) 2 = 1 := by decide +kernel
example : confiscated weights B (1/2) = 3/2 := by decide +kernel
example : totalStake (stakeSlashing weights B (1/2)) = 7/2 := by decide +kernel
example : totalStake (stakeSlashing weights B (1/2)) + confiscated weights B (1/2) = 5 := by decide +kernel
example : (1/2 : ℚ) * (totalStake weights / 3) < confiscated weights B (1/2) :=
  slashing_lower_bound weights B (1/2) (by norm_num) (by decide +kernel)
example : stakeMass (stakeSlashing weights B (1/2)) B < stakeMass weights B :=
  faulty_mass_strict_decrease weights B (1/2) (by norm_num) (by decide +kernel)
example : honestWeight weights B / totalStake weights = 2/5 := by decide +kernel
example : honestWeight (stakeSlashing weights B (1/2)) B / totalStake (stakeSlashing weights B (1/2)) = 4/7 := by decide +kernel
example : honestWeight weights B / totalStake weights <
    honestWeight (stakeSlashing weights B (1/2)) B / totalStake (stakeSlashing weights B (1/2)) :=
  relative_honest_dominance_increase weights B (1/2) (by decide +kernel)
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
example : (∀ v, 0 ≤ stakeSlashing weights B (1/2) v) :=
  slashing_nonnegative weights B (1/2) (by decide +kernel) (by norm_num)
example : stakeSlashing weights B 1 0 = 0 := full_confiscation weights B 0 (by decide)
example : confiscated weights B 1 = 3 ∧ totalStake (stakeSlashing weights B 1) = 2 := by decide +kernel
example : honestWeight (stakeSlashing weights B 1) B / totalStake (stakeSlashing weights B 1) = 1 := by decide +kernel
example : (∀ v, 0 ≤ stakeSlashing weights B 1 v) :=
  slashing_nonnegative weights B 1 (by decide +kernel) (by norm_num)
example : stakeSlashing weights ∅ (1/2) = weights := empty_slashing weights (1/2)
example : confiscated weights ∅ (1/2) = 0 := by decide +kernel
example : stakeSlashing weights B 0 = weights := zero_slashing weights B
example : stakeSlashing weights (B ∪ B) (1/2) = stakeSlashing weights B (1/2) :=
  duplicate_set_same_penalty weights B (1/2)
-- Exactly one third gives equality, not the strict accountable bound.
example : confiscated (fun _ : Fin 3 => (1 : ℚ)) B (1/2) =
    (1/2 : ℚ) * (totalStake (fun _ : Fin 3 => (1 : ℚ)) / 3) := by decide +kernel
example : ¬ (1/2 : ℚ) * (totalStake (fun _ : Fin 3 => (1 : ℚ)) / 3) <
    confiscated (fun _ : Fin 3 => (1 : ℚ)) B (1/2) := by decide +kernel
-- Nonempty blame alone does not give a strict decrease.
example : B ≠ ∅ ∧ confiscated zeroFault B (1/2) = 0 := by decide +kernel
example : ¬ stakeMass (stakeSlashing zeroFault B (1/2)) B < stakeMass zeroFault B := by decide +kernel
-- Honest supermajority is a separate, compatible scenario with small culprit mass.
example : 2 * totalStake smallFault < 3 * honestWeight smallFault B := by decide +kernel
example : honestWeight (stakeSlashing smallFault B (1/2)) B / totalStake (stakeSlashing smallFault B (1/2)) = 8/9 := by decide +kernel
example : 2 * totalStake (stakeSlashing smallFault B (1/2)) <
    3 * honestWeight (stakeSlashing smallFault B (1/2)) B :=
  honest_quorum_preserved smallFault B (1/2) (by decide +kernel) (by norm_num) (by decide +kernel)
example : ¬ 2 * totalStake weights < 3 * honestWeight weights B :=
  threshold_and_honest_quorum_incompatible weights B (by decide +kernel)
-- Invalid rate and empty honest mass counterexamples guard the hypotheses.
example : stakeSlashing weights B 2 0 < 0 := by decide +kernel
example : weights 0 < stakeSlashing weights B (-1) 0 := by decide +kernel
example : totalStake (stakeSlashing weights univ 1) = 0 := by decide +kernel
example : ¬ honestWeight weights univ / totalStake weights <
    honestWeight (stakeSlashing weights univ 1) univ / totalStake (stakeSlashing weights univ 1) := by decide +kernel
-- A replay ledger is a separate obligation: applying a partial penalty twice charges twice.
example : stakeSlashing (stakeSlashing weights B (1/2)) B (1/2) 0 = 3/4 := by decide +kernel
example : stakeSlashing (stakeSlashing weights B (1/2)) B (1/2) 0 ≠ stakeSlashing weights B (1/2) 0 := by decide +kernel
-- Non-vacuous bridge: an executable reachable trace, checked blame and two conflicting commits.
example : commit cfg reached.votes 0 7 ∧ commit cfg reached.votes 1 8 := by decide +kernel
example : attribute_evidence cfg (some reached.votes) view = .ok B := by decide +kernel
example : (1/2 : ℚ) * ((cfg.total : ℚ) / 3) < confiscated (stakeOfConfig cfg) B (1/2) :=
  checked_slashing_lower_bound cfg reached.votes view B (by decide +kernel)
    (r := 0) (r' := 1) (u := 7) (v := 8) (by decide +kernel) (by decide +kernel)
    (by decide) (1/2) (by norm_num)
example : stakeSlashing (stakeOfConfig cfg) B (1/2) 1 = stakeOfConfig cfg 1 :=
  certified_honest_stake_invariant cfg reachable view B (by decide +kernel) (1/2) 1 (by decide)
example : stakeMass (stakeOfConfig cfg) cfg.byzantineᶜ / totalStake (stakeOfConfig cfg) <
    stakeMass (stakeSlashing (stakeOfConfig cfg) B (1/2)) cfg.byzantineᶜ /
      totalStake (stakeSlashing (stakeOfConfig cfg) B (1/2)) :=
  certified_honest_share_increase cfg reachable view B (by decide +kernel) (1/2)
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
example : slashEvidence cfg (some reached.votes) view (1/2) =
    .ok (stakeSlashing (stakeOfConfig cfg) B (1/2)) :=
  checked_slashing_result cfg (some reached.votes) view B (1/2) (by decide +kernel)
example : slashEvidence cfg none view (1/2) = .error .insufficientEvidence := rfl
example : slashEvidence cfg (some reached.votes) unavailable (1/2) = .error .insufficientEvidence := by decide +kernel
example : slashEvidence cfg (some reached.votes) wrongHeight (1/2) = .error .invalidEvidence := by decide +kernel
example : DistributedTendermintSlashingPenaltyContractSuite := verification_suite

def scenarios : List (String × Bool) :=
  [("partial confiscation", decide (confiscated weights B (1/2) = 3/2)),
   ("remaining total", decide (totalStake (stakeSlashing weights B (1/2)) = 7/2)),
   ("full confiscation", decide (confiscated weights B 1 = 3)),
   ("empty blame", decide (confiscated weights ∅ (1/2) = 0)),
   ("nonnegative remainder", decide (∀ v, 0 ≤ stakeSlashing weights B 1 v)),
   ("strict lower bound", decide ((1/2 : ℚ) * (5/3) < confiscated weights B (1/2))),
   ("honest fraction", decide (honestWeight (stakeSlashing weights B (1/2)) B / totalStake (stakeSlashing weights B (1/2)) = 4/7)),
   ("honest supermajority", decide (honestWeight (stakeSlashing smallFault B (1/2)) B / totalStake (stakeSlashing smallFault B (1/2)) = 8/9)),
   ("zero culprit weight", decide (confiscated zeroFault B (1/2) = 0)),
   ("rate above one rejected by invariant", decide (stakeSlashing weights B 2 0 < 0)),
   ("reachable execution", (run cfg initial trace).isSome),
   ("checked culprit", decide (attribute_evidence cfg (some reached.votes) view = .ok B)),
   ("missing reference", decide (attribute_evidence cfg none view = .error .insufficientEvidence)),
   ("incomplete view", decide (attribute_evidence cfg (some reached.votes) unavailable = .error .insufficientEvidence))]

#eval scenarios
end TendermintSlashingRegression
