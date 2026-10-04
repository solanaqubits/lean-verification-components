import Verification.DistributedChandyLamportSnapshot

open DistributedChandyLamportSnapshot

def p0 : Packet := ⟨0, 7, false⟩
def p1 : Packet := ⟨1, 7, false⟩
def p2 : Packet := ⟨2, 9, true⟩
def s1 := sendLeft initState 7
def s2 := (initiateLeft s1.mirror).mirror
def s3 := sendLeft s2 7
def s4 := (firstMarkerRight s3.mirror []).mirror
def s5 := sendLeft s4 9
def s6 := receiveRight s5 p0 [.app p1, .marker, .app p2]
def s7 := receiveRight s6 p1 [.marker, .app p2]
def s8 := laterMarkerRight s7 [.app p2]
def s9 := receiveRight s8 p2 []

theorem h1 : Reachable s1 := .step .init (.send _ 7)
theorem h2 : Reachable s2 := .step h1 (Step.mirror (Step.initiate s1.mirror (by decide +kernel)))
theorem h3 : Reachable s3 := .step h2 (.send _ 7)
theorem h4 : Reachable s4 := .step h3
  (Step.mirror (Step.firstMarker s3.mirror [] (by decide +kernel) (by decide +kernel)))
theorem h5 : Reachable s5 := .step h4 (.send _ 9)
theorem h6 : Reachable s6 := .step h5 (.receive _ _ _ (by decide +kernel))
theorem h7 : Reachable s7 := .step h6 (.receive _ _ _ (by decide +kernel))
theorem h8 : Reachable s8 := .step h7 (.laterMarker _ _ (by decide +kernel) (by decide +kernel))
theorem h9 : Reachable s9 := .step h8 (.receive _ _ _ (by decide +kernel))

-- Marker is FIFO behind both earlier sends and in front of the later send.
example : s5.lr.queue = [.app p0, .app p1, .marker, .app p2] := by decide +kernel
-- Equal payloads are distinct occurrences and both must be recorded.
example : s8.lr.transit.map Packet.val = [7, 7] := by decide +kernel
example : s8.lr.transit.map Packet.id = [0, 1] := by decide +kernel
example : p0 ≠ p1 := by decide +kernel
-- Before marker completion, partial recording is not the full channel cut.
example : s6.lr.transit = [p0] ∧ s6.lr.closed = false := by decide +kernel
example : s8.lr.closed = true ∧ s8.rl.closed = true := by decide +kernel
-- First-marker receiver records an empty incoming channel.
example : s4.rl.transit = [] := by decide +kernel
-- Subsequent application traffic changes neither the saved snapshot nor transit.
example : s9.lr.transit = [p0, p1] := by decide +kernel
example : s9.right.value = 23 ∧ s9.right.events = 3 := by decide +kernel
example : s9.right.snapshot = some ⟨0, 0, [], []⟩ := by decide +kernel
example : s9.left.snapshot = some ⟨0, 2, [p0, p1], []⟩ := by decide +kernel
example : ConsistentCut s9 := chandy_lamport_cut_consistency h9
example : s9.lr.transit = [p0, p1].filter (fun m => !([] : List Packet).contains m) :=
  transit_channel_soundness h9 ⟨0, 2, [p0, p1], []⟩ ⟨0, 0, [], []⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : Reachable s9.mirror := reachable_mirror h9

-- A nonempty receive cut also retains its paired send in the sender's saved cut.
def t1 := receiveRight s1 p0 []
def t2 := initiateLeft t1
def t3 := firstMarkerRight t2 []
theorem ht1 : Reachable t1 := .step h1 (.receive _ _ _ (by decide +kernel))
theorem ht2 : Reachable t2 := .step ht1 (.initiate _ (by decide +kernel))
theorem ht3 : Reachable t3 := .step ht2 (.firstMarker _ _ (by decide +kernel) (by decide +kernel))
example : t3.right.snapshot = some ⟨7, 1, [], [p0]⟩ := by decide +kernel
example : ConsistentCut t3 := chandy_lamport_cut_consistency ht3

-- A receive transition has no hidden cut-consistency premise.
-- It can execute on an invalid state; reachability is what excludes that state.
def forged : NetworkState :=
  { left := ({} : Node).capture [] []
    lr := { queue := [.app p2, .marker], sent := [p2] } }
example : Step forged (receiveRight forged p2 [.marker]) := .receive _ _ _ rfl
example : ¬Reachable forged := by
  intro h
  have hf := no_future_messages_in_snapshot h p2 [.marker] rfl rfl
  contradiction
