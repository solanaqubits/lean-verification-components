import Verification.DistributedTendermintAccountableSafety
import Mathlib.Data.Fin.VecNotation

open Finset DistributedTendermintCoreSafety DistributedTendermintAccountableSafety
namespace TendermintAccountabilityRegression

def good : Config 4 := ⟨fun _ => 1, {3}, 17⟩
def bad : Config 4 := ⟨fun _ => 1, {0, 1}, 17⟩
def weighted : Config 3 := ⟨![3, 1, 1], ∅, 17⟩
def boundary : Config 3 := ⟨![2, 1, 0], ∅, 17⟩

def voteAction (c : Config n) (i : Fin n) (r : ℕ) (p : Phase) (v : ℕ) : Action n :=
  if i ∈ c.byzantine then .faulty ⟨i, r, p, some v⟩ else .honest i p (some v)

def roundActions (c : Config n) (ids : List (Fin n)) (r v : ℕ) : List (Action n) :=
  (if r = 0 then [] else ids.map fun i => .advance i r) ++
  ids.map (fun i => .propose i ⟨r, v, none⟩) ++
  ids.map (fun i => voteAction c i r .prevote v) ++
  ids.flatMap (fun i => ids.map fun j => .deliver i ⟨j, r, .prevote, some v⟩) ++
  ids.map (fun i => voteAction c i r .precommit v)

def goodTrace := roundActions good [0, 1, 2] 0 7
def goodState := (run good initial goodTrace).getD initial

def badTrace := roundActions bad [0, 1, 2] 0 7 ++ roundActions bad [0, 1, 3] 1 8
def badState := (run bad initial badTrace).getD initial

/-- Validator 2 is honestly locked at round 0; the round-1 polka permits its round-2 switch. -/
def legalTrace := badTrace ++ [.advance 2 2,
  .deliver 2 ⟨0, 1, .prevote, some 8⟩, .deliver 2 ⟨1, 1, .prevote, some 8⟩,
  .deliver 2 ⟨3, 1, .prevote, some 8⟩, .propose 2 ⟨2, 8, some 1⟩,
  .honest 2 .prevote (some 8)]
def legalState := (run bad initial legalTrace).getD initial

theorem good_execution : run good initial goodTrace = some goodState := by decide +kernel
theorem bad_execution : run bad initial badTrace = some badState := by decide +kernel
theorem legal_execution : run bad initial legalTrace = some legalState := by decide +kernel

theorem good_reachable : Reachable good goodState :=
  run_reachable good goodTrace Reachable.init good_execution

theorem bad_reachable : Reachable bad badState :=
  run_reachable bad badTrace Reachable.init bad_execution

theorem legal_reachable : Reachable bad legalState :=
  run_reachable bad legalTrace Reachable.init legal_execution

def quorumVotes (ids : Finset (Fin n)) (r v : ℕ) : Finset (Vote n) :=
  ids.image (fun i => ⟨i, r, .prevote, some v⟩) ∪
    ids.image (fun i => ⟨i, r, .precommit, some v⟩)

def sameRound := quorumVotes ({0, 1, 2} : Finset (Fin 4)) 0 7 ∪ quorumVotes {1, 2, 3} 0 8
def unequal := quorumVotes ({0, 1} : Finset (Fin 3)) 0 7 ∪ quorumVotes {0, 2} 0 8

def partialVotes := goodState.votes.filter (fun m => m.phase = .precommit)
def partialView := completeView good partialVotes

def prevoteOnly := completeView good (goodState.votes.filter (fun m => m.phase = .prevote))

def forgedCertificate : JustificationEvidence 4 := ⟨17, 0, 8, {0, 1, 2}⟩
def forgedView : EvidenceView 4 :=
  { completeView good goodState.votes with justifications := {forgedCertificate} }
def validCertificate : JustificationEvidence 4 := canonicalJustification bad legalState.votes 1 8
def justifiedView : EvidenceView 4 :=
  { completeView bad legalState.votes with justifications := {validCertificate} }
def wrongHeight : EvidenceView 4 := completeView { good with height := 18 } goodState.votes

def fakeVotes : Finset (Vote 4) := insert ⟨3, 99, .prevote, some 42⟩ goodState.votes

def uncertified : Finset (Vote 4) := {⟨0, 4, .precommit, some 7⟩}
def staleOnly := quorumVotes ({0, 1, 2} : Finset (Fin 4)) 0 7 ∪ {⟨0, 1, .precommit, some 7⟩}
def nilPair : Finset (Vote 4) := {⟨0, 0, .prevote, none⟩, ⟨0, 0, .prevote, some 7⟩}
def differentPhases : Finset (Vote 4) := {⟨0, 0, .prevote, some 7⟩, ⟨0, 0, .precommit, none⟩}
def oneSwitch : Finset (Vote 3) := {⟨1, 0, .precommit, some 7⟩, ⟨1, 1, .prevote, some 8⟩}

def check (c : Config n) (votes : Finset (Vote n)) :=
  attribute_evidence c (some votes) (completeView c votes)

example : check good goodState.votes = .ok ∅ := by decide +kernel
example : commit bad badState.votes 0 7 ∧ commit bad badState.votes 1 8 := by decide +kernel
example : check bad badState.votes = .ok {0, 1} := by decide +kernel
example : bad.total < 3 * bad.mass (culprits bad badState.votes) :=
  accountable_safety_attribution bad badState.votes (r := 0) (r' := 1) (u := 7) (v := 8)
    (by decide +kernel) (by decide +kernel) (by decide)
example : check good sameRound = .ok {1, 2} := by decide +kernel
example : commit good sameRound 0 7 ∧ commit good sameRound 0 8 := by decide +kernel
example : check weighted unequal = .ok {0} := by decide +kernel
example : weighted.mass (culprits weighted unequal) = 3 ∧ weighted.total = 5 := by decide +kernel
example : ¬ boundary.quorum {0} ∧ boundary.quorum {0, 1} ∧ boundary.weight 2 = 0 := by decide +kernel
example : attribute_evidence good (some goodState.votes) partialView =
    .error .insufficientEvidence := by decide +kernel
-- Without the coverage gate, missing prevotes would frame three honest precommitters.
example : attribute_evidence good (some goodState.votes) prevoteOnly = .ok ∅ := by decide +kernel
example : culprits good partialVotes = {0, 1, 2} := by decide +kernel
example : attribute_evidence good none (completeView good goodState.votes) =
    .error .insufficientEvidence := rfl
example : attribute_evidence good (some goodState.votes) forgedView =
    .error .invalidEvidence := by decide +kernel
example : attribute_evidence good (some goodState.votes) wrongHeight =
    .error .invalidEvidence := by decide +kernel
example : attribute_evidence good (some goodState.votes) (completeView good fakeVotes) =
    .error .invalidEvidence := by decide +kernel
example : check good uncertified = .ok {0} := by decide +kernel
example : InvalidPrecommit good staleOnly 0 := by decide +kernel
example : ¬ Equivocation differentPhases 0 := by decide +kernel
example : Equivocation nilPair 0 := by decide +kernel
example : LockViolation weighted oneSwitch 1 ∧
    ¬ weighted.total < 3 * weighted.mass (culprits weighted oneSwitch) := by decide +kernel
example : ValidJustification bad legalState.votes validCertificate := by decide +kernel
example : attribute_evidence bad (some legalState.votes) justifiedView = .ok {0, 1} := by decide +kernel
example : HasJustification bad legalState.votes 0 2 8 := by decide +kernel
example : ¬ LockViolation bad legalState.votes 2 := by decide +kernel
example : 2 ∉ culprits bad (completeView bad legalState.votes).votes :=
  reachable_honest_never_accused bad legal_reachable _
    (complete_view_sufficient bad legalState.votes) 2 (by decide)
example : (⟨2, 2, .prevote, some 8⟩ : Vote 4) ∈ legalState.votes := by decide +kernel
example : (.unjustifiedSwitch ⟨0, 0, .precommit, some 7⟩ ⟨0, 1, .prevote, some 8⟩) ∈
    accusations bad badState.votes := by decide +kernel
example : (.doubleVote ⟨1, 0, .prevote, some 7⟩ ⟨1, 0, .prevote, some 8⟩) ∈
    accusations good sameRound := by decide +kernel
example : (.uncertifiedPrecommit ⟨0, 4, .precommit, some 7⟩) ∈
    accusations good uncertified := by decide +kernel
example : culprits good sameRound = (accusations good sameRound).image Accusation.offender :=
  culprits_eq_accusation_senders good sameRound
example : good.mass ((culprits good sameRound) ∪ (culprits good sameRound)) = 2 := by decide +kernel
example : check { bad with byzantine := ∅ } badState.votes = check bad badState.votes := rfl
example : culprits good (sameRound ∪ sameRound) = culprits good sameRound :=
  duplicate_messages_idempotent good sameRound
example : DistributedTendermintAccountableSafetySuite := verification_suite

/-- Exact compiled scenarios; the Python harness requires every named result to be true. -/
def scenarios : List (String × Bool) :=
  [("honest empty blame", decide (check good goodState.votes = .ok ∅)),
   ("reachable cross round", decide (check bad badState.votes = .ok {0, 1})),
   ("same round", decide (check good sameRound = .ok {1, 2})),
   ("unequal weights", decide (check weighted unequal = .ok {0})),
   ("strict quorum boundary", decide (¬ boundary.quorum {0})),
   ("positive quorum", decide (boundary.quorum {0, 1})),
   ("partial view rejected", decide (attribute_evidence good (some goodState.votes) partialView =
     .error .insufficientEvidence)),
   ("unsafe raw partial blame", decide (culprits good partialVotes = {0, 1, 2})),
   ("no reference", decide (attribute_evidence good none partialView = .error .insufficientEvidence)),
   ("forged certificate", decide (attribute_evidence good (some goodState.votes) forgedView =
     .error .invalidEvidence)),
   ("wrong height", decide (attribute_evidence good (some goodState.votes) wrongHeight =
     .error .invalidEvidence)),
   ("unauthenticated message", decide (attribute_evidence good (some goodState.votes)
     (completeView good fakeVotes) = .error .invalidEvidence)),
   ("invalid precommit", decide (check good uncertified = .ok {0})),
   ("stale polka insufficient", decide (InvalidPrecommit good staleOnly 0)),
   ("nil block equivocation", decide (Equivocation nilPair 0)),
   ("different phases", decide (¬ Equivocation differentPhases 0)),
   ("legal unlock execution", (run bad initial legalTrace).isSome),
   ("legal unlock not blamed", decide (¬ LockViolation bad legalState.votes 2)),
   ("valid certificate", decide (ValidJustification bad legalState.votes validCertificate)),
   ("justified view", decide (attribute_evidence bad (some legalState.votes) justifiedView = .ok {0, 1})),
   ("single fault below threshold", decide
     (¬ weighted.total < 3 * weighted.mass (culprits weighted oneSwitch))),
   ("duplicate blame weight", decide (good.mass ({1, 2} ∪ {1, 2}) = 2)),
   ("fault oracle unused", decide (check { bad with byzantine := ∅ } badState.votes = .ok {0, 1})),
   ("precommit omission allowed", decide
     (attribute_evidence good (some goodState.votes) prevoteOnly = .ok ∅))]

#eval scenarios
end TendermintAccountabilityRegression
