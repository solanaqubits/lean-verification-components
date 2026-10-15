import Verification.DistributedTendermintCoreSafety
import Mathlib.Data.Fin.VecNotation

open DistributedTendermintCoreSafety

namespace TendermintRegression

def good : Config 4 := ⟨fun _ => 1, {3}, 17⟩
def weighted : Config 4 := ⟨![2, 1, 1, 0], {1}, 17⟩
def boundary : Config 3 := ⟨fun _ => 1, {2}, 17⟩
def bad : Config 4 := ⟨fun _ => 1, {0, 1}, 17⟩

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
def secondTrace := goodTrace ++ roundActions good [2, 0, 1] 1 7
def secondState := (run good initial secondTrace).getD initial

def badTrace := roundActions bad [0, 1, 2] 0 7 ++ roundActions bad [0, 1, 3] 1 8
def badState := (run bad initial badTrace).getD initial

def weightedTrace := roundActions weighted [0, 2] 0 5
def weightedState := (run weighted initial weightedTrace).getD initial

def nilTrace : List (Action 4) := [.honest 0 .prevote none, .honest 0 .precommit none]
def nilState := (run good initial nilTrace).getD initial

def cert (r v : ℕ) : Finset (Vote 4) :=
  {⟨0, r, .prevote, some v⟩, ⟨1, r, .prevote, some v⟩, ⟨2, r, .prevote, some v⟩}

def locked (vr v : ℕ) : LocalState 4 :=
  { round := 3, lock := some (2, 7), valid := some (2, 7),
    inbox := cert vr v, proposals := {⟨3, v, some vr⟩} }

def equivTrace := goodTrace ++ [.faulty ⟨3, 0, .prevote, some 8⟩,
  .faulty ⟨3, 0, .prevote, some 7⟩, .faulty ⟨3, 0, .precommit, some 8⟩]
def equivState := (run good initial equivTrace).getD initial

theorem good_execution : run good initial goodTrace = some goodState := by decide +kernel
theorem second_execution : run good initial secondTrace = some secondState := by decide +kernel
theorem bad_execution : run bad initial badTrace = some badState := by decide +kernel
theorem weighted_execution : run weighted initial weightedTrace = some weightedState := by
  decide +kernel

theorem good_reachable : Reachable good goodState :=
  run_reachable good goodTrace Reachable.init good_execution

theorem second_reachable : Reachable good secondState :=
  run_reachable good secondTrace Reachable.init second_execution

theorem bad_reachable : Reachable bad badState :=
  run_reachable bad badTrace Reachable.init bad_execution

example : good.total = 4 ∧ 3 * good.mass good.byzantine < good.total := by decide +kernel
example : weighted.total = 4 ∧ weighted.weight 3 = 0 := by decide +kernel
example : weighted.quorum {0, 2} ∧ ¬ weighted.quorum {1, 2, 3} := by decide +kernel
example : 3 * boundary.mass boundary.byzantine = boundary.total := by decide +kernel
example : ¬ boundary.quorum {0, 1} ∧ boundary.quorum {0, 1, 2} := by decide +kernel
example : bad.quorum {0, 1, 2} ∧ bad.quorum {0, 1, 3} := by decide +kernel
example : 3 * bad.mass bad.byzantine > bad.total := by decide +kernel
example : commit good goodState.votes 0 7 := by decide +kernel
example : commit good secondState.votes 0 7 ∧ commit good secondState.votes 1 7 := by
  decide +kernel
example : commit bad badState.votes 0 7 ∧ commit bad badState.votes 1 8 := by decide +kernel
example : commit weighted weightedState.votes 0 5 := by decide +kernel
example : run good initial nilTrace = some nilState := by decide +kernel
example : ¬ commit good nilState.votes 0 7 := by decide +kernel
example : execute good goodState (.honest 0 .prevote (some 8)) = none := by decide +kernel
example : execute good initial (.honest 0 .precommit (some 7)) = none := by decide +kernel
example : execute good initial (.honest 0 .prevote (some 7)) = none := by decide +kernel
example : execute good initial (.deliver 0 ⟨1, 0, .prevote, some 7⟩) = none := by decide +kernel
example : execute good initial (.faulty ⟨0, 0, .prevote, some 7⟩) = none := by decide +kernel
example : execute good goodState (.advance 0 0) = none := by decide +kernel
example : executeAtHeight good 18 initial (.propose 0 ⟨0, 7, none⟩) = none := by decide +kernel
example : ¬ proposalValid good (locked 1 8) ⟨3, 8, some 1⟩ := by decide +kernel
example : proposalValid good (locked 2 8) ⟨3, 8, some 2⟩ := by decide +kernel
example : ¬ proposalValid good (locked 3 8) ⟨3, 8, some 3⟩ := by decide +kernel
example : proposalValid good (locked 1 7) ⟨3, 7, some 1⟩ := by decide +kernel
example : ¬ proposalValid good { locked 2 8 with inbox := ∅ } ⟨3, 8, some 2⟩ := by
  decide +kernel
example : run good initial equivTrace = some equivState := by decide +kernel
example : commit good equivState.votes 0 7 ∧ ¬ commit good equivState.votes 0 8 := by
  decide +kernel
example : (goodState.nodes 0).lock = some (0, 7) := by decide +kernel
example : (secondState.nodes 0).lock = some (1, 7) := by decide +kernel
example : (secondState.nodes 0).valid = some (1, 7) := by decide +kernel
example : ∀ r v, commit good secondState.votes r v → v = 7 := by
  intro r v hv
  exact tendermint_core_safety good second_reachable (by decide +kernel) hv
    (show commit good secondState.votes 0 7 by decide +kernel)
example : ∀ s, Reachable boundary s → ∀ r r' u v,
    commit boundary s.votes r u → commit boundary s.votes r' v → u = v := by
  intro s hs r r' u v hu hv
  exact tendermint_core_safety boundary hs (by decide +kernel) hu hv
example : bad.total < 3 * bad.mass bad.byzantine :=
  accountable_safety_contrapositive bad bad_reachable
    (show commit bad badState.votes 0 7 by decide +kernel)
    (show commit bad badState.votes 1 8 by decide +kernel) (by decide +kernel)
example : ∀ votes msg p r v, good.mass (signers (insert msg (insert msg votes)) p r v) =
    good.mass (signers (insert msg votes) p r v) := duplicate_vote_idempotent good

-- A concrete reordered delivery trace still reaches a certified commit.
def reversedTrace := roundActions good [2, 1, 0] 0 7
def reversedState := (run good initial reversedTrace).getD initial
example : run good initial reversedTrace = some reversedState := by decide +kernel
example : commit good reversedState.votes 0 7 := by decide +kernel
example : goodState.votes = reversedState.votes := by decide +kernel

-- A bare conflicting proposal in a later round cannot make a locked voter vote.
def attemptTrace := goodTrace ++ [.advance 0 1, .propose 0 ⟨1, 8, none⟩,
  .honest 0 .prevote (some 8)]
example : run good initial attemptTrace = none := by decide +kernel

def nilAfterLock := goodTrace ++ [.advance 0 1, .honest 0 .prevote none,
  .honest 0 .precommit none]
def nilAfterState := (run good initial nilAfterLock).getD initial
example : run good initial nilAfterLock = some nilAfterState := by decide +kernel
example : (nilAfterState.nodes 0).lock = some (0, 7) := by decide +kernel
example : (nilAfterState.nodes 0).valid = some (0, 7) := by decide +kernel
example : execute good goodState (.deliver 0 ⟨1, 0, .prevote, some 7⟩) = some goodState := by
  apply duplicate_delivery <;> decide +kernel

private def checks : List (String × Bool) :=
  [("honest trace", (run good initial goodTrace).isSome),
   ("two rounds", (run good initial secondTrace).isSome),
   ("threshold breach trace", (run bad initial badTrace).isSome),
   ("honest commit", decide (commit good goodState.votes 0 7)),
   ("later commit", decide (commit good secondState.votes 1 7)),
   ("breach first commit", decide (commit bad badState.votes 0 7)),
   ("breach conflict", decide (commit bad badState.votes 1 8)),
   ("weighted execution", (run weighted initial weightedTrace).isSome),
   ("weighted commit", decide (commit weighted weightedState.votes 0 5)),
   ("zero weight", decide (weighted.weight 3 = 0)),
   ("strict quorum boundary", decide (¬ boundary.quorum {0, 1})),
   ("nil execution", (run good initial nilTrace).isSome),
   ("nil no block", decide (¬ commit good nilState.votes 0 7)),
   ("duplicate honest vote", (execute good goodState (.honest 0 .prevote (some 8))).isNone),
   ("no proposal", (execute good initial (.honest 0 .prevote (some 7))).isNone),
   ("no certificate", (execute good initial (.honest 0 .precommit (some 7))).isNone),
   ("forged sender", (execute good initial (.faulty ⟨0, 0, .prevote, some 7⟩)).isNone),
   ("stale certificate", decide (¬ proposalValid good (locked 1 8) ⟨3, 8, some 1⟩)),
   ("valid unlock", decide (proposalValid good (locked 2 8) ⟨3, 8, some 2⟩)),
   ("future certificate", decide (¬ proposalValid good (locked 3 8) ⟨3, 8, some 3⟩)),
   ("same value old certificate", decide (proposalValid good (locked 1 7) ⟨3, 7, some 1⟩)),
   ("wrong height", (executeAtHeight good 18 initial (.propose 0 ⟨0, 7, none⟩)).isNone),
   ("byzantine equivocation", (run good initial equivTrace).isSome),
   ("equivocation no fork", decide (¬ commit good equivState.votes 0 8)),
   ("reordered delivery", (run good initial reversedTrace).isSome),
   ("conflicting proposal rejected", (run good initial attemptTrace).isNone),
   ("nil after lock", (run good initial nilAfterLock).isSome),
   ("nil preserves lock", decide ((nilAfterState.nodes 0).lock = some (0, 7))),
   ("duplicate delivery", decide
     (execute good goodState (.deliver 0 ⟨1, 0, .prevote, some 7⟩) = some goodState))]

def main : IO Unit := do
  for (name, ok) in checks do
    unless ok do throw (IO.userError name)
  IO.println s!"TENDERMINT_EXEC_OK: {checks.length} cases"

#eval main

end TendermintRegression
