/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup

/-!
# Operational two-process Chandy--Lamport snapshot

Each directed FIFO channel has a send ledger and a receive ledger. Packet IDs
are channel-local send ordinals; phase stamps are ghost observations of the
local snapshot flag at the event. The receive rule does not inspect these stamps.
One snapshot, no losses, duplication, failures, fairness or termination claim.
-/
namespace DistributedChandyLamportSnapshot

structure Packet where
  id : ℕ
  val : ℕ
  afterSend : Bool
  deriving DecidableEq, Repr

inductive Message where
  | app (packet : Packet)
  | marker
  deriving DecidableEq, Repr

structure Receipt where
  packet : Packet
  afterReceive : Bool
  deriving DecidableEq, Repr

structure LocalSnapshot where
  value : ℕ
  events : ℕ
  sentCut : List Packet
  receivedCut : List Packet
  deriving DecidableEq, Repr

structure Node where
  value : ℕ := 0
  events : ℕ := 0
  snapshot : Option LocalSnapshot := none
  deriving DecidableEq, Repr

def Node.started (n : Node) : Bool := n.snapshot.isSome

def Node.capture (n : Node) (sent received : List Packet) : Node :=
  { n with snapshot := some ⟨n.value, n.events, sent, received⟩ }

def Node.tick (n : Node) (increment : ℕ) : Node :=
  { n with value := n.value + increment, events := n.events + 1 }

@[simp] theorem started_capture (n : Node) (sent received : List Packet) :
    (n.capture sent received).started = true := rfl
@[simp] theorem started_tick (n : Node) (k : ℕ) : (n.tick k).started = n.started := rfl

structure Channel where
  queue : List Message := []
  sent : List Packet := []
  received : List Receipt := []
  closed : Bool := false
  transit : List Packet := []
  deriving DecidableEq, Repr

/-- Recording is local state, not a condition on a message's ghost stamp. -/
def recording (receiver : Node) (c : Channel) : Bool := receiver.started && !c.closed

def appPackets (q : List Message) : List Packet := q.filterMap fun
  | .app m => some m
  | .marker => none

@[simp] theorem appPackets_append (a b : List Message) :
    appPackets (a ++ b) = appPackets a ++ appPackets b := List.filterMap_append

@[simp] theorem appPackets_apps (a : List Packet) : appPackets (a.map Message.app) = a := by
  simp [appPackets, List.filterMap_map]

/-- Ghost definition of received messages crossing the cut in the allowed direction. -/
def crossing (rs : List Receipt) : List Packet :=
  (rs.filter fun r => r.afterReceive && !r.packet.afterSend).map Receipt.packet

def sendChannel (c : Channel) (started : Bool) (v : ℕ) : Channel :=
  let m : Packet := ⟨c.sent.length, v, started⟩
  { c with queue := c.queue ++ [.app m], sent := c.sent ++ [m] }

def startChannel (c : Channel) : Channel := { c with queue := c.queue ++ [.marker] }

def receiveApp (c : Channel) (receiverStarted : Bool) (m : Packet)
    (tail : List Message) : Channel :=
  { c with
    queue := tail
    received := c.received ++ [⟨m, receiverStarted⟩]
    transit := if receiverStarted && !c.closed then c.transit ++ [m] else c.transit }

def receiveMarker (c : Channel) (tail : List Message) : Channel :=
  { c with queue := tail, closed := true }

/-- A marker separates all pre-snapshot packets from all post-snapshot packets. -/
inductive WirePhase : Bool → Bool → List Message → Prop where
  | before (xs : List Packet) (hx : ∀ m ∈ xs, m.afterSend = false) :
      WirePhase false false (xs.map Message.app)
  | marked (xs ys : List Packet) (hx : ∀ m ∈ xs, m.afterSend = false)
      (hy : ∀ m ∈ ys, m.afterSend = true) :
      WirePhase true false (xs.map Message.app ++ .marker :: ys.map Message.app)
  | closed (ys : List Packet) (hy : ∀ m ∈ ys, m.afterSend = true) :
      WirePhase true true (ys.map Message.app)

theorem phase_send {s c : Bool} {q : List Message} (h : WirePhase s c q)
    (m : Packet) (hm : m.afterSend = s) : WirePhase s c (q ++ [.app m]) := by
  cases h with
  | before xs hx =>
    simpa using WirePhase.before (xs ++ [m]) (by
      intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact hx a ha
      · exact hm)
  | marked xs ys hx hy =>
    simpa [List.append_assoc] using WirePhase.marked xs (ys ++ [m]) hx (by
      intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact hy a ha
      · exact hm)
  | closed ys hy =>
    simpa using WirePhase.closed (ys ++ [m]) (by
      intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact hy a ha
      · exact hm)

theorem phase_start {c : Bool} {q : List Message} (h : WirePhase false c q) :
    WirePhase true c (q ++ [.marker]) := by
  cases h with
  | before xs hx => simpa using WirePhase.marked xs [] hx (by simp)

/-- At the head of a valid FIFO, a packet is post-snapshot exactly when the marker passed. -/
theorem phase_app {s c : Bool} {q : List Message} (h : WirePhase s c q)
    {m : Packet} {tail : List Message} (hq : q = .app m :: tail) :
    m.afterSend = c ∧ WirePhase s c tail := by
  cases h with
  | before xs hx =>
    cases xs with
    | nil => simp at hq
    | cons a xs =>
      simp only [List.map_cons, List.cons.injEq, Message.app.injEq] at hq
      rcases hq with ⟨rfl, rfl⟩
      exact ⟨hx _ (by simp), WirePhase.before _ (by intro b hb; exact hx b (by simp [hb]))⟩
  | marked xs ys hx hy =>
    cases xs with
    | nil => simp at hq
    | cons a xs =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq, Message.app.injEq] at hq
      rcases hq with ⟨rfl, rfl⟩
      exact ⟨hx _ (by simp), WirePhase.marked _ _ (by intro b hb; exact hx b (by simp [hb])) hy⟩
  | closed ys hy =>
    cases ys with
    | nil => simp at hq
    | cons a ys =>
      simp only [List.map_cons, List.cons.injEq, Message.app.injEq] at hq
      rcases hq with ⟨rfl, rfl⟩
      exact ⟨hy _ (by simp), WirePhase.closed _ (by intro b hb; exact hy b (by simp [hb]))⟩

theorem phase_marker {s c : Bool} {q : List Message} (h : WirePhase s c q)
    {tail : List Message} (hq : q = .marker :: tail) :
    s = true ∧ c = false ∧ WirePhase s true tail := by
  cases h with
  | before xs hx => cases xs <;> simp at hq
  | marked xs ys hx hy =>
    cases xs with
    | nil =>
      simp only [List.map_nil, List.nil_append, List.cons.injEq, true_and] at hq
      subst tail
      exact ⟨rfl, rfl, WirePhase.closed ys hy⟩
    | cons a xs => simp at hq
  | closed ys hy => cases ys <;> simp at hq

structure ChannelInvariant (sender receiver : Bool) (c : Channel) : Prop where
  phase : WirePhase sender c.closed c.queue
  closed_receiver : c.closed = true → receiver = true
  ledger : c.sent = c.received.map Receipt.packet ++ appPackets c.queue
  recorded : c.transit = crossing c.received
  safe : ∀ r ∈ c.received, r.afterReceive = false → r.packet.afterSend = false
  pending : receiver = false → ∀ r ∈ c.received, r.afterReceive = false
  ids : c.sent.map Packet.id = List.range c.sent.length
  unsent : sender = false → ∀ m ∈ c.sent, m.afterSend = false

theorem invariant_send {s r : Bool} {c : Channel} (h : ChannelInvariant s r c) (v : ℕ) :
    ChannelInvariant s r (sendChannel c s v) := by
  refine ⟨phase_send h.phase _ rfl, h.closed_receiver, ?_, h.recorded, h.safe, h.pending, ?_, ?_⟩
  · simp [sendChannel, appPackets, h.ledger, List.append_assoc]
  · simp [sendChannel, h.ids, List.range_succ]
  · intro hs m hm
    simp only [sendChannel, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact h.unsent hs m hm
    · exact hs

theorem invariant_start_sender {r : Bool} {c : Channel} (h : ChannelInvariant false r c) :
    ChannelInvariant true r (startChannel c) := by
  refine ⟨phase_start h.phase, h.closed_receiver, ?_, h.recorded, h.safe, h.pending, h.ids, by simp⟩
  simpa [startChannel, appPackets] using h.ledger

theorem invariant_start_receiver {s : Bool} {c : Channel} (h : ChannelInvariant s false c) :
    ChannelInvariant s true c :=
  ⟨h.phase, fun _ => rfl, h.ledger, h.recorded, h.safe, by simp, h.ids, h.unsent⟩

theorem invariant_receive_app {s r : Bool} {c : Channel} (h : ChannelInvariant s r c)
    (m : Packet) (tail : List Message) (hq : c.queue = .app m :: tail) :
    ChannelInvariant s r (receiveApp c r m tail) := by
  have hp := phase_app h.phase hq
  have hf : r = false → m.afterSend = false := by
    intro hr
    have hc : c.closed = false := by
      cases he : c.closed
      · rfl
      · have := h.closed_receiver he; simp_all
    exact hp.1.trans hc
  refine ⟨hp.2, h.closed_receiver, ?_, ?_, ?_, ?_, h.ids, h.unsent⟩
  · simpa [receiveApp, hq, appPackets, List.append_assoc] using h.ledger
  · change (if r && !c.closed then c.transit ++ [m] else c.transit) =
      crossing (c.received ++ [⟨m, r⟩])
    rw [h.recorded]
    cases r <;> cases hc : c.closed <;>
      simp [crossing, List.filter_append, hp.1, hc]
  · intro a ha haR
    simp only [receiveApp, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl
    · exact h.safe a ha haR
    · exact hf haR
  · intro hr a ha
    simp only [receiveApp, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl
    · exact h.pending hr a ha
    · exact hr

theorem invariant_receive_marker {s r : Bool} {c : Channel} (h : ChannelInvariant s r c)
    (tail : List Message) (hq : c.queue = .marker :: tail) :
    ChannelInvariant s true (receiveMarker c tail) := by
  refine ⟨(phase_marker h.phase hq).2.2, fun _ => rfl, ?_,
    h.recorded, h.safe, by simp, h.ids, h.unsent⟩
  simpa [receiveMarker, hq, appPackets] using h.ledger

structure NetworkState where
  left : Node := {}
  right : Node := {}
  lr : Channel := {}
  rl : Channel := {}
  deriving DecidableEq, Repr

def NetworkState.mirror (s : NetworkState) : NetworkState := ⟨s.right, s.left, s.rl, s.lr⟩
@[simp] theorem mirror_mirror (s : NetworkState) : s.mirror.mirror = s := rfl

def initState : NetworkState := {}

def sendLeft (s : NetworkState) (v : ℕ) : NetworkState :=
  { s with left := s.left.tick 0, lr := sendChannel s.lr s.left.started v }

def receiveRight (s : NetworkState) (m : Packet) (tail : List Message) : NetworkState :=
  { s with right := s.right.tick m.val, lr := receiveApp s.lr s.right.started m tail }

def initiateLeft (s : NetworkState) : NetworkState :=
  { s with
    left := s.left.capture s.lr.sent (s.rl.received.map Receipt.packet)
    lr := startChannel s.lr }

def firstMarkerRight (s : NetworkState) (tail : List Message) : NetworkState :=
  { s with
    right := s.right.capture s.rl.sent (s.lr.received.map Receipt.packet)
    lr := receiveMarker s.lr tail
    rl := startChannel s.rl }

def laterMarkerRight (s : NetworkState) (tail : List Message) : NetworkState :=
  { s with lr := receiveMarker s.lr tail }

/-- Operational guards check only local snapshot status and the FIFO head. -/
inductive Step : NetworkState → NetworkState → Prop where
  | send (s : NetworkState) (v : ℕ) : Step s (sendLeft s v)
  | receive (s : NetworkState) (m : Packet) (tail : List Message)
      (head : s.lr.queue = .app m :: tail) : Step s (receiveRight s m tail)
  | initiate (s : NetworkState) (fresh : s.left.started = false) : Step s (initiateLeft s)
  | firstMarker (s : NetworkState) (tail : List Message)
      (head : s.lr.queue = .marker :: tail) (fresh : s.right.started = false) :
      Step s (firstMarkerRight s tail)
  | laterMarker (s : NetworkState) (tail : List Message)
      (head : s.lr.queue = .marker :: tail) (recorded : s.right.started = true) :
      Step s (laterMarkerRight s tail)
  | mirror {s t : NetworkState} : Step s t → Step s.mirror t.mirror

inductive Reachable : NetworkState → Prop where
  | init : Reachable initState
  | step {s t : NetworkState} : Reachable s → Step s t → Reachable t

def NetworkInvariant (s : NetworkState) : Prop :=
  ChannelInvariant s.left.started s.right.started s.lr ∧
  ChannelInvariant s.right.started s.left.started s.rl

theorem invariant_mirror {s : NetworkState} (h : NetworkInvariant s) :
    NetworkInvariant s.mirror := ⟨h.2, h.1⟩

theorem invariant_init : NetworkInvariant initState := by
  constructor <;> exact ⟨WirePhase.before [] (by simp), by decide, rfl, rfl,
    by simp [initState], by simp [initState], rfl, by simp [initState]⟩

theorem invariant_step {s t : NetworkState} (hstep : Step s t) :
    NetworkInvariant s → NetworkInvariant t := by
  induction hstep with
  | send s v =>
    intro h
    exact ⟨invariant_send h.1 v, h.2⟩
  | receive s m tail hq =>
    intro h
    exact ⟨invariant_receive_app h.1 m tail hq, h.2⟩
  | initiate s hf =>
    intro h
    exact ⟨invariant_start_sender (hf ▸ h.1), invariant_start_receiver (hf ▸ h.2)⟩
  | firstMarker s tail hq hf =>
    intro h
    exact ⟨invariant_receive_marker h.1 tail hq, invariant_start_sender (hf ▸ h.2)⟩
  | laterMarker s tail hq hr =>
    intro h
    exact ⟨hr ▸ invariant_receive_marker h.1 tail hq, h.2⟩
  | mirror hstep ih =>
    intro h
    exact invariant_mirror (ih (invariant_mirror h))

theorem reachable_invariant {s : NetworkState} (h : Reachable s) : NetworkInvariant s := by
  induction h with
  | init => exact invariant_init
  | step hr hs ih => exact invariant_step hs ih

/-- Actual event lists on the pre-snapshot side of each local cut. -/
def sentBefore (c : Channel) : List Packet := c.sent.filter fun m => !m.afterSend

def receivedBefore (c : Channel) : List Packet :=
  (c.received.filter fun r => !r.afterReceive).map Receipt.packet

def SavedCut (n : Node) (outgoing incoming : Channel) : Prop :=
  ∀ snap, n.snapshot = some snap →
    snap.sentCut = sentBefore outgoing ∧ snap.receivedCut = receivedBefore incoming

def SavedCuts (s : NetworkState) : Prop :=
  SavedCut s.left s.lr s.rl ∧ SavedCut s.right s.rl s.lr

theorem before_sent_unstarted {r : Bool} {c : Channel} (h : ChannelInvariant false r c) :
    sentBefore c = c.sent := by
  apply List.filter_eq_self.mpr
  intro m hm
  simp [h.unsent rfl m hm]

theorem before_received_unstarted {s : Bool} {c : Channel} (h : ChannelInvariant s false c) :
    receivedBefore c = c.received.map Receipt.packet := by
  unfold receivedBefore
  congr 1
  apply List.filter_eq_self.mpr
  intro m hm
  simp [h.pending rfl m hm]

theorem saved_send {n : Node} {outgoing incoming : Channel}
    (h : SavedCut n outgoing incoming) (v : ℕ) :
    SavedCut (n.tick 0) (sendChannel outgoing n.started v) incoming := by
  intro snap hs
  have he : n.snapshot = some snap := hs
  have hn : n.started = true := by simp [Node.started, he]
  simpa [sentBefore, sendChannel, hn] using h snap he

theorem saved_receive {n : Node} {outgoing incoming : Channel}
    (h : SavedCut n outgoing incoming) (m : Packet) (tail : List Message) :
    SavedCut (n.tick m.val) outgoing (receiveApp incoming n.started m tail) := by
  intro snap hs
  have he : n.snapshot = some snap := hs
  have hn : n.started = true := by simp [Node.started, he]
  simpa [receivedBefore, receiveApp, List.filter_append, hn] using h snap he

theorem saved_capture {n : Node} {outgoing incoming : Channel} {other : Bool}
    (ho : ChannelInvariant false other outgoing) (hi : ChannelInvariant other false incoming) :
    SavedCut (n.capture outgoing.sent (incoming.received.map Receipt.packet))
      outgoing incoming := by
  intro snap hs
  cases Option.some.inj hs
  exact ⟨(before_sent_unstarted ho).symm, (before_received_unstarted hi).symm⟩

theorem saved_mirror {s : NetworkState} (h : SavedCuts s) : SavedCuts s.mirror := ⟨h.2, h.1⟩

theorem saved_step {s t : NetworkState} (hs : Step s t) :
    NetworkInvariant s → SavedCuts s → SavedCuts t := by
  induction hs with
  | send s v =>
    intro h hc
    exact ⟨saved_send hc.1 v, hc.2⟩
  | receive s m tail hq =>
    intro h hc
    exact ⟨hc.1, saved_receive hc.2 m tail⟩
  | initiate s hf =>
    intro h hc
    exact ⟨saved_capture (hf ▸ h.1) (hf ▸ h.2), hc.2⟩
  | firstMarker s tail hq hf =>
    intro h hc
    exact ⟨hc.1, saved_capture (hf ▸ h.2) (hf ▸ h.1)⟩
  | laterMarker s tail hq hr =>
    intro h hc
    exact hc
  | mirror hs ih =>
    intro h hc
    exact saved_mirror (ih (invariant_mirror h) (saved_mirror hc))

theorem reachable_saved_cuts {s : NetworkState} (h : Reachable s) : SavedCuts s := by
  induction h with
  | init => constructor <;> intro snap hs <;> cases hs
  | step hr hs ih => exact saved_step hs (reachable_invariant hr) ih

/-- Delivery preserves identity and order: the receive ledger is a prefix of sends. -/
theorem received_origin {s r : Bool} {c : Channel} (h : ChannelInvariant s r c)
    (a : Receipt) (ha : a ∈ c.received) : a.packet ∈ c.sent := by
  rw [h.ledger]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩)

theorem received_packets_nodup {s r : Bool} {c : Channel} (h : ChannelInvariant s r c) :
    (c.received.map Receipt.packet).Nodup := by
  have hs : c.sent.Nodup := List.Nodup.of_map Packet.id (h.ids.symm ▸ List.nodup_range)
  rw [h.ledger] at hs
  exact (List.nodup_append.mp hs).1

theorem before_receive_subset_before_send {s r : Bool} {c : Channel}
    (h : ChannelInvariant s r c) : ∀ m ∈ receivedBefore c, m ∈ sentBefore c := by
  intro m hm
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
  have har := List.mem_filter.mp ha
  have hp : a.afterReceive = false := by simpa using har.2
  exact List.mem_filter.mpr ⟨received_origin h a har.1, by simp [h.safe a har.1 hp]⟩

theorem phase_closed {s : Bool} {q : List Message} (h : WirePhase s true q) :
    ∀ m ∈ appPackets q, m.afterSend = true := by
  cases h with
  | closed ys hy => simpa using hy

theorem closed_pending_after {s r : Bool} {c : Channel} (h : ChannelInvariant s r c)
    (hc : c.closed = true) : ∀ m ∈ appPackets c.queue, m.afterSend = true :=
  phase_closed (hc ▸ h.phase)

/-- Once the marker is received, no pre-snapshot send is still in flight. -/
theorem closed_before_delivered {s r : Bool} {c : Channel} (h : ChannelInvariant s r c)
    (hc : c.closed = true) :
    sentBefore c = (c.received.map Receipt.packet).filter (fun m => !m.afterSend) := by
  have he : (appPackets c.queue).filter (fun m => !m.afterSend) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro m hm
    simp [closed_pending_after h hc m hm]
  simp [sentBefore, h.ledger, List.filter_append, he]

/-- Unique packet identities make cut subtraction unambiguous, even for equal payloads. -/
theorem received_before_membership {s r : Bool} {c : Channel} (h : ChannelInvariant s r c)
    (a : Receipt) (ha : a ∈ c.received) :
    a.packet ∈ receivedBefore c ↔ a.afterReceive = false := by
  constructor
  · intro hm
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
    obtain ⟨hbr, hbp⟩ := List.mem_filter.mp hb
    have hba := List.inj_on_of_nodup_map (received_packets_nodup h) hbr ha he
    subst b
    simpa using hbp
  · intro hr
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha, by simp [hr]⟩, rfl⟩

/-- Exact ordered channel state: saved sends minus saved receives, after the marker. -/
theorem closed_transit_exact {s r : Bool} {c : Channel} (h : ChannelInvariant s r c)
    (hc : c.closed = true) :
    c.transit = (sentBefore c).filter (fun m => !(receivedBefore c).contains m) := by
  rw [h.recorded, closed_before_delivered h hc]
  simp only [crossing, List.filter_filter, List.filter_map]
  congr 1
  apply List.filter_congr
  intro a ha
  have he : (receivedBefore c).contains a.packet = !a.afterReceive := by
    apply Bool.eq_iff_iff.mpr
    simpa using received_before_membership h a ha
  change (a.afterReceive && !a.packet.afterSend) =
    (!(receivedBefore c).contains a.packet && !a.packet.afterSend)
  rw [he]
  simp only [Bool.not_not]

/-- The protocol never overwrites a saved local value, counter, or event cut. -/
theorem snapshots_preserved {s t : NetworkState} (hs : Step s t) :
    (∀ snap, s.left.snapshot = some snap → t.left.snapshot = some snap) ∧
    (∀ snap, s.right.snapshot = some snap → t.right.snapshot = some snap) := by
  induction hs with
  | send s v => exact ⟨fun _ h => h, fun _ h => h⟩
  | receive s m tail hq => exact ⟨fun _ h => h, fun _ h => h⟩
  | initiate s hf =>
    refine ⟨?_, fun _ h => h⟩
    intro snap hs
    simp [Node.started, hs] at hf
  | firstMarker s tail hq hf =>
    refine ⟨fun _ h => h, ?_⟩
    intro snap hs
    simp [Node.started, hs] at hf
  | laterMarker s tail hq hr => exact ⟨fun _ h => h, fun _ h => h⟩
  | mirror hs ih => exact ⟨ih.2, ih.1⟩

/-- Recording never changes again once the corresponding marker has been consumed. -/
theorem closed_transit_preserved {s t : NetworkState} (hs : Step s t) :
    (s.lr.closed = true → t.lr.transit = s.lr.transit) ∧
    (s.rl.closed = true → t.rl.transit = s.rl.transit) := by
  induction hs with
  | send s v => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | receive s m tail hq =>
    refine ⟨?_, fun _ => rfl⟩
    intro hc
    simp [receiveRight, receiveApp, hc]
  | initiate s hf => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | firstMarker s tail hq hf => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | laterMarker s tail hq hr => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | mirror hs ih => exact ⟨ih.2, ih.1⟩

/-- Both directed queues satisfy the explicit marker-separation shape. -/
theorem fifo_marker_ordering {s : NetworkState} (h : Reachable s) :
    WirePhase s.left.started s.lr.closed s.lr.queue ∧
    WirePhase s.right.started s.rl.closed s.rl.queue :=
  ⟨(reachable_invariant h).1.phase, (reachable_invariant h).2.phase⟩

/-- Even the next delivery of a post-snapshot send requires an already recorded receiver. -/
theorem no_future_messages_in_snapshot {s : NetworkState} (h : Reachable s)
    (m : Packet) (tail : List Message) (hq : s.lr.queue = .app m :: tail)
    (hm : m.afterSend = true) : s.right.started = true := by
  have hi := (reachable_invariant h).1
  exact hi.closed_receiver ((phase_app hi.phase hq).1.symm.trans hm)

def ConsistentCut (s : NetworkState) : Prop :=
  ∀ l r, s.left.snapshot = some l → s.right.snapshot = some r →
    (∀ m ∈ r.receivedCut, m ∈ l.sentCut) ∧
    (∀ m ∈ l.receivedCut, m ∈ r.sentCut)

/-- Consistency refers to the actual saved event cuts, not assumed causal closure. -/
theorem chandy_lamport_cut_consistency {s : NetworkState} (h : Reachable s) :
    ConsistentCut s := by
  intro l r hl hr
  have hi := reachable_invariant h
  have hc := reachable_saved_cuts h
  obtain ⟨hls, hlr⟩ := hc.1 l hl
  obtain ⟨hrs, hrr⟩ := hc.2 r hr
  rw [hls, hlr, hrs, hrr]
  exact ⟨before_receive_subset_before_send hi.1, before_receive_subset_before_send hi.2⟩

/-- This channel is complete when its marker was received; no termination assumption is hidden. -/
theorem transit_channel_soundness {s : NetworkState} (h : Reachable s)
    (l r : LocalSnapshot) (hl : s.left.snapshot = some l) (hr : s.right.snapshot = some r)
    (hc : s.lr.closed = true) :
    s.lr.transit = l.sentCut.filter (fun m => !r.receivedCut.contains m) := by
  have hs := reachable_saved_cuts h
  rw [(hs.1 l hl).1, (hs.2 r hr).2]
  exact closed_transit_exact (reachable_invariant h).1 hc

/-- Partial recording has exact received-so-far semantics before the channel closes. -/
theorem transit_partial_soundness {s : NetworkState} (h : Reachable s) :
    s.lr.transit = crossing s.lr.received ∧ s.rl.transit = crossing s.rl.received :=
  ⟨(reachable_invariant h).1.recorded, (reachable_invariant h).2.recorded⟩

/-- First-marker handling records an empty incoming channel, derived from its unsnapped receiver. -/
theorem first_marker_empty {s : NetworkState} (h : Reachable s)
    (hf : s.right.started = false) (tail : List Message) :
    (firstMarkerRight s tail).lr.transit = [] := by
  have hi := (reachable_invariant h).1
  change s.lr.transit = []
  rw [hi.recorded]
  have he : s.lr.received.filter (fun r => r.afterReceive && !r.packet.afterSend) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    simp [hi.pending hf a ha]
  simp [crossing, he]

/-- Mirroring a reachable execution supplies every theorem for the reverse channel. -/
theorem reachable_mirror {s : NetworkState} (h : Reachable s) : Reachable s.mirror := by
  induction h with
  | init => exact Reachable.init
  | step hr hs ih => exact Reachable.step ih (Step.mirror hs)

structure ChandyLamportFormalSuite : Prop where
  operational_invariant : ∀ s, Reachable s → NetworkInvariant s
  saved_cuts : ∀ s, Reachable s → SavedCuts s
  no_future : ∀ s, Reachable s → ∀ m tail, s.lr.queue = .app m :: tail →
    m.afterSend = true → s.right.started = true
  consistent : ∀ s, Reachable s → ConsistentCut s
  transit_exact : ∀ s, Reachable s → ∀ l r, s.left.snapshot = some l →
    s.right.snapshot = some r → s.lr.closed = true →
    s.lr.transit = l.sentCut.filter (fun m => !r.receivedCut.contains m)
  reverse_execution : ∀ s, Reachable s → Reachable s.mirror

theorem chandy_lamport_master_suite : ChandyLamportFormalSuite := {
  operational_invariant := fun _ h => reachable_invariant h
  saved_cuts := fun _ h => reachable_saved_cuts h
  no_future := fun _ h => no_future_messages_in_snapshot h
  consistent := fun _ h => chandy_lamport_cut_consistency h
  transit_exact := fun _ h => transit_channel_soundness h
  reverse_execution := fun _ h => reachable_mirror h
}

end DistributedChandyLamportSnapshot
