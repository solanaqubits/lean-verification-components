import Verification.DistributedThreePhaseCommit
open DistributedThreePhaseCommit

def normal_commitEvents : List Nat := [0, 1, 2, 4, 6, 7, 8, 9, 10, 0, 1, 2, 4, 6, 7, 8, 9, 10, 0, 1, 2, 4]
def normal_commitFinal : Core := ⟨3, 3, 3, 7, 3, 0, 0, 4, 2, 2, 0, 0⟩
example : runEvents initial normal_commitEvents = some normal_commitFinal := by decide
example : AllTerminal normal_commitFinal := by decide
example : Agreement normal_commitFinal := by decide

def normal_abortEvents : List Nat := [0, 1, 3, 5, 6, 7, 8, 9, 10]
def normal_abortFinal : Core := ⟨4, 4, 0, 7, 3, 0, 0, 5, 0, 0, 0, 0⟩
example : runEvents initial normal_abortEvents = some normal_abortFinal := by decide
example : AllTerminal normal_abortFinal := by decide
example : Agreement normal_abortFinal := by decide

def before_precommitEvents : List Nat := [0, 1, 2, 4, 11, 14, 0, 1, 2, 4, 6, 7, 8, 9, 10, 0, 1, 2, 4, 6, 7, 8, 9, 10, 0, 1, 2, 4]
def before_precommitFinal : Core := ⟨4, 4, 3, 6, 3, 1, 1, 5, 2, 2, 0, 0⟩
example : runEvents initial before_precommitEvents = some before_precommitFinal := by decide
example : AllTerminal before_precommitFinal := by decide
example : Agreement before_precommitFinal := by decide

def partial_precommitEvents : List Nat := [0, 1, 2, 4, 6, 7, 8, 9, 10, 0, 2, 11, 14, 0, 1, 2, 4, 6, 7, 8, 9, 10, 0, 1, 2, 4, 6, 7, 8, 9, 10, 0, 1, 2, 4]
def partial_precommitFinal : Core := ⟨3, 3, 3, 6, 3, 1, 1, 4, 2, 2, 0, 0⟩
example : runEvents initial partial_precommitEvents = some partial_precommitFinal := by decide
example : AllTerminal partial_precommitFinal := by decide
example : Agreement partial_precommitFinal := by decide

def ack_barrierEvents : List Nat := [0, 1, 2, 4, 6, 7, 8, 9, 10, 0, 1, 2, 4, 6, 7, 8, 9, 11, 14, 0, 1, 2, 4, 6, 7, 8, 9, 10, 0, 1, 2, 4, 6, 7, 8, 9, 10, 0, 1, 2, 4]
def ack_barrierFinal : Core := ⟨3, 3, 3, 6, 3, 1, 1, 4, 2, 2, 0, 0⟩
example : runEvents initial ack_barrierEvents = some ack_barrierFinal := by decide
example : AllTerminal ack_barrierFinal := by decide
example : Agreement ack_barrierFinal := by decide

def partial_commitEvents : List Nat := [0, 1, 2, 4, 6, 7, 8, 9, 10, 0, 1, 2, 4, 6, 7, 8, 9, 10, 0, 2, 11, 14, 0, 1, 2, 4, 6, 7, 8, 9, 10, 0, 1, 2, 4, 6, 7, 8, 9, 10, 0, 1, 2, 4]
def partial_commitFinal : Core := ⟨3, 3, 3, 6, 3, 1, 1, 4, 2, 2, 0, 0⟩
example : runEvents initial partial_commitEvents = some partial_commitFinal := by decide
example : AllTerminal partial_commitFinal := by decide
example : Agreement partial_commitFinal := by decide

def participant_stopEvents : List Nat := [0, 1, 2, 4, 6, 7, 8, 9, 10, 0, 2, 12, 14, 1, 4, 7, 9, 10, 1, 4, 7, 9, 10, 1, 4]
def participant_stopFinal : Core := ⟨2, 4, 3, 5, 2, 2, 1, 5, 0, 2, 0, 0⟩
example : runEvents initial participant_stopEvents = some participant_stopFinal := by decide
example : AllTerminal participant_stopFinal := by decide
example : Agreement participant_stopFinal := by decide

def single_survivorEvents : List Nat := [0, 1, 2, 4, 11, 12, 14, 1, 4, 7, 9, 10, 1, 4, 7, 9, 10, 1, 4]
def single_survivorFinal : Core := ⟨1, 4, 3, 4, 2, 2, 1, 5, 0, 2, 0, 0⟩
example : runEvents initial single_survivorEvents = some single_survivorFinal := by decide
example : AllTerminal single_survivorFinal := by decide
example : Agreement single_survivorFinal := by decide

def partialState : Core := ⟨2, 1, 3, 7, 3, 0, 0, 2, 2, 0, 0, 0⟩
example : runEvents initial [0, 1, 2, 4, 6, 7, 8, 9, 10, 0, 2] = some partialState := by decide
example : ¬Agreement { partialState with left := 3, right := 4 } := by decide
example : participantState participant_stopFinal false = .preCommit ∧
    participantState participant_stopFinal true = .aborted := by decide
example : ¬alive participant_stopFinal false := by decide
example : deliverPacket partialState false { request partialState false with epoch := 100 } = none := by
  apply stale_epoch_rejected
  decide
example : coreStep ack_barrierFinal 8 = none := by decide
example : ∀ s, Reachable s → Agreement s := fun _ => reachable_agreement
example (r : Run) (h : ProgressAssumptions r) : ∃ n, AllTerminal (r.states n) := by
  obtain ⟨n, _, hn⟩ := completion_under_progress_assumptions r h
  exact ⟨n, hn⟩

def replacementView : Core := ⟨2, 1, 3, 6, 3, 1, 1, 1, 0, 0, 0, 0⟩
example : runEvents partialState [11, 14] = some replacementView := by decide
example : deliverPacket replacementView false (request partialState false) = none := by decide
example : deliverPacket partialState false
    { request partialState false with recipient := 9 } = none := by decide
example : deliverPacket partialState false
    { request partialState false with transaction := 1 } = none := by decide

def acknowledgedView : Core := ⟨2, 2, 3, 7, 3, 0, 0, 2, 4, 4, 2, 2⟩
example : coreStep acknowledgedView 8 = none := by decide
example : coreStep acknowledgedView 9 = none := by decide
example : coreStep acknowledgedView 10 = some
    ⟨2, 2, 3, 7, 3, 0, 0, 4, 0, 0, 0, 0⟩ := by decide
example (s : Core) (hs : Reachable s) (alive : s.live / 2 % 4 ≠ 0) :
    ∃ es t, Execution s es t ∧ AllTerminal t := completion_path_after_detection hs alive
example : ¬WeaklyFair (idleRun initial) := by
  intro hf
  have he : ∀ m, 0 ≤ m → ∃ t, coreStep ((idleRun initial).states m) 0 = some t ∧
      t ≠ (idleRun initial).states m := by
    intro m _
    change ∃ t, coreStep initial 0 = some t ∧ t ≠ initial
    exact ⟨⟨0, 0, 0, 7, 3, 0, 0, 0, 1, 0, 0, 0⟩, by decide, by decide⟩
  obtain ⟨m, _, hm⟩ := hf 0 0 (by decide) he
  change 15 = 0 at hm
  omega
