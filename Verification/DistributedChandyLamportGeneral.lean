/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedChandyLamportSnapshot
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Lattice.Fold

/-! One snapshot on a finite directed graph. Packet identities and cut-phase stamps
are ghost event observations; the receive rule never tests these stamps.
Channel lemmas generalize the established two-process FIFO proof to arbitrary payloads. -/
namespace DistributedChandyLamportGeneral

structure Packet (M : Type) where
  id : ℕ
  val : M
  afterSend : Bool
  deriving DecidableEq, Repr

inductive ChanItem (M : Type) where
  | app (packet : Packet M)
  | marker
  deriving DecidableEq, Repr

structure Receipt (M : Type) where
  packet : Packet M
  afterReceive : Bool
  deriving DecidableEq, Repr

structure Channel (M : Type) where
  queue : List (ChanItem M) := []
  sent : List (Packet M) := []
  received : List (Receipt M) := []
  closed : Bool := false
  transit : List (Packet M) := []
  deriving DecidableEq, Repr

variable {M : Type}

def appPackets (q : List (ChanItem M)) : List (Packet M) := q.filterMap fun
  | .app m => some m
  | .marker => none

@[simp] theorem appPackets_append (a b : List (ChanItem M)) :
    appPackets (a ++ b) = appPackets a ++ appPackets b := List.filterMap_append

@[simp] theorem appPackets_apps (a : List (Packet M)) : appPackets (a.map ChanItem.app) = a := by
  simp [appPackets, List.filterMap_map]

/-- Ghost definition of received messages crossing the cut in the allowed direction. -/
def crossing (rs : List (Receipt M)) : List (Packet M) :=
  (rs.filter fun r => r.afterReceive && !r.packet.afterSend).map Receipt.packet

def sendChannel (c : (Channel M)) (started : Bool) (v : M) : (Channel M) :=
  let m : (Packet M) := ⟨c.sent.length, v, started⟩
  { c with queue := c.queue ++ [.app m], sent := c.sent ++ [m] }

def startChannel (c : (Channel M)) : (Channel M) := { c with queue := c.queue ++ [.marker] }

def receiveApp (c : (Channel M)) (receiverStarted : Bool) (m : (Packet M))
    (tail : List (ChanItem M)) : (Channel M) :=
  { c with
    queue := tail
    received := c.received ++ [⟨m, receiverStarted⟩]
    transit := if receiverStarted && !c.closed then c.transit ++ [m] else c.transit }

def receiveMarker (c : (Channel M)) (tail : List (ChanItem M)) : (Channel M) :=
  { c with queue := tail, closed := true }

/-- A marker separates all pre-snapshot packets from all post-snapshot packets. -/
inductive WirePhase : Bool → Bool → List (ChanItem M) → Prop where
  | before (xs : List (Packet M)) (hx : ∀ m ∈ xs, m.afterSend = false) :
      WirePhase false false (xs.map ChanItem.app)
  | marked (xs ys : List (Packet M)) (hx : ∀ m ∈ xs, m.afterSend = false)
      (hy : ∀ m ∈ ys, m.afterSend = true) :
      WirePhase true false (xs.map ChanItem.app ++ .marker :: ys.map ChanItem.app)
  | closed (ys : List (Packet M)) (hy : ∀ m ∈ ys, m.afterSend = true) :
      WirePhase true true (ys.map ChanItem.app)

theorem phase_send {s c : Bool} {q : List (ChanItem M)} (h : WirePhase s c q)
    (m : (Packet M)) (hm : m.afterSend = s) : WirePhase s c (q ++ [.app m]) := by
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

theorem phase_start {c : Bool} {q : List (ChanItem M)} (h : WirePhase false c q) :
    WirePhase true c (q ++ [.marker]) := by
  cases h with
  | before xs hx => simpa using WirePhase.marked xs [] hx (by simp)

/-- At the head of a valid FIFO, a packet is post-snapshot exactly when the marker passed. -/
theorem phase_app {s c : Bool} {q : List (ChanItem M)} (h : WirePhase s c q)
    {m : (Packet M)} {tail : List (ChanItem M)} (hq : q = .app m :: tail) :
    m.afterSend = c ∧ WirePhase s c tail := by
  cases h with
  | before xs hx =>
    cases xs with
    | nil => simp at hq
    | cons a xs =>
      simp only [List.map_cons, List.cons.injEq, ChanItem.app.injEq] at hq
      rcases hq with ⟨rfl, rfl⟩
      exact ⟨hx _ (by simp), WirePhase.before _ (by intro b hb; exact hx b (by simp [hb]))⟩
  | marked xs ys hx hy =>
    cases xs with
    | nil => simp at hq
    | cons a xs =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq, ChanItem.app.injEq] at hq
      rcases hq with ⟨rfl, rfl⟩
      exact ⟨hx _ (by simp), WirePhase.marked _ _ (by intro b hb; exact hx b (by simp [hb])) hy⟩
  | closed ys hy =>
    cases ys with
    | nil => simp at hq
    | cons a ys =>
      simp only [List.map_cons, List.cons.injEq, ChanItem.app.injEq] at hq
      rcases hq with ⟨rfl, rfl⟩
      exact ⟨hy _ (by simp), WirePhase.closed _ (by intro b hb; exact hy b (by simp [hb]))⟩

theorem phase_marker {s c : Bool} {q : List (ChanItem M)} (h : WirePhase s c q)
    {tail : List (ChanItem M)} (hq : q = .marker :: tail) :
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

structure ChannelInvariant (sender receiver : Bool) (c : (Channel M)) : Prop where
  phase : WirePhase sender c.closed c.queue
  closed_receiver : c.closed = true → receiver = true
  ledger : c.sent = c.received.map Receipt.packet ++ appPackets c.queue
  recorded : c.transit = crossing c.received
  safe : ∀ r ∈ c.received, r.afterReceive = false → r.packet.afterSend = false
  pending : receiver = false → ∀ r ∈ c.received, r.afterReceive = false
  ids : c.sent.map Packet.id = List.range c.sent.length
  unsent : sender = false → ∀ m ∈ c.sent, m.afterSend = false

theorem invariant_send {s r : Bool} {c : (Channel M)} (h : ChannelInvariant s r c) (v : M) :
    ChannelInvariant s r (sendChannel c s v) := by
  refine ⟨phase_send h.phase _ rfl, h.closed_receiver, ?_, h.recorded, h.safe, h.pending, ?_, ?_⟩
  · simp [sendChannel, appPackets, h.ledger, List.append_assoc]
  · simp [sendChannel, h.ids, List.range_succ]
  · intro hs m hm
    simp only [sendChannel, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact h.unsent hs m hm
    · exact hs

theorem invariant_start_sender {r : Bool} {c : (Channel M)} (h : ChannelInvariant false r c) :
    ChannelInvariant true r (startChannel c) := by
  refine ⟨phase_start h.phase, h.closed_receiver, ?_, h.recorded, h.safe, h.pending, h.ids, by simp⟩
  simpa [startChannel, appPackets] using h.ledger

theorem invariant_start_receiver {s : Bool} {c : (Channel M)} (h : ChannelInvariant s false c) :
    ChannelInvariant s true c :=
  ⟨h.phase, fun _ => rfl, h.ledger, h.recorded, h.safe, by simp, h.ids, h.unsent⟩

theorem invariant_receive_app {s r : Bool} {c : (Channel M)} (h : ChannelInvariant s r c)
    (m : (Packet M)) (tail : List (ChanItem M)) (hq : c.queue = .app m :: tail) :
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

theorem invariant_receive_marker {s r : Bool} {c : (Channel M)} (h : ChannelInvariant s r c)
    (tail : List (ChanItem M)) (hq : c.queue = .marker :: tail) :
    ChannelInvariant s true (receiveMarker c tail) := by
  refine ⟨(phase_marker h.phase hq).2.2, fun _ => rfl, ?_,
    h.recorded, h.safe, by simp, h.ids, h.unsent⟩
  simpa [receiveMarker, hq, appPackets] using h.ledger


def sentBefore (c : (Channel M)) : List (Packet M) := c.sent.filter fun m => !m.afterSend

def receivedBefore (c : (Channel M)) : List (Packet M) :=
  (c.received.filter fun r => !r.afterReceive).map Receipt.packet


theorem before_sent_unstarted {r : Bool} {c : (Channel M)} (h : ChannelInvariant false r c) :
    sentBefore c = c.sent := by
  apply List.filter_eq_self.mpr
  intro m hm
  simp [h.unsent rfl m hm]

theorem before_received_unstarted {s : Bool} {c : (Channel M)} (h : ChannelInvariant s false c) :
    receivedBefore c = c.received.map Receipt.packet := by
  unfold receivedBefore
  congr 1
  apply List.filter_eq_self.mpr
  intro m hm
  simp [h.pending rfl m hm]


/-- Delivery preserves identity and order: the receive ledger is a prefix of sends. -/
theorem received_origin {s r : Bool} {c : (Channel M)} (h : ChannelInvariant s r c)
    (a : (Receipt M)) (ha : a ∈ c.received) : a.packet ∈ c.sent := by
  rw [h.ledger]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩)

theorem received_packets_nodup {s r : Bool} {c : (Channel M)} (h : ChannelInvariant s r c) :
    (c.received.map Receipt.packet).Nodup := by
  have hs : c.sent.Nodup := List.Nodup.of_map Packet.id (h.ids.symm ▸ List.nodup_range)
  rw [h.ledger] at hs
  exact (List.nodup_append.mp hs).1

theorem before_receive_subset_before_send {s r : Bool} {c : (Channel M)}
    (h : ChannelInvariant s r c) : ∀ m ∈ receivedBefore c, m ∈ sentBefore c := by
  intro m hm
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
  have har := List.mem_filter.mp ha
  have hp : a.afterReceive = false := by simpa using har.2
  exact List.mem_filter.mpr ⟨received_origin h a har.1, by simp [h.safe a har.1 hp]⟩

theorem phase_closed {s : Bool} {q : List (ChanItem M)} (h : WirePhase s true q) :
    ∀ m ∈ appPackets q, m.afterSend = true := by
  cases h with
  | closed ys hy => simpa using hy

theorem closed_pending_after {s r : Bool} {c : (Channel M)} (h : ChannelInvariant s r c)
    (hc : c.closed = true) : ∀ m ∈ appPackets c.queue, m.afterSend = true :=
  phase_closed (hc ▸ h.phase)

/-- Once the marker is received, no pre-snapshot send is still in flight. -/
theorem closed_before_delivered {s r : Bool} {c : (Channel M)} (h : ChannelInvariant s r c)
    (hc : c.closed = true) :
    sentBefore c = (c.received.map Receipt.packet).filter (fun m => !m.afterSend) := by
  have he : (appPackets c.queue).filter (fun m => !m.afterSend) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro m hm
    simp [closed_pending_after h hc m hm]
  simp [sentBefore, h.ledger, List.filter_append, he]

/-- Unique packet identities make cut subtraction unambiguous, even for equal payloads. -/
theorem received_before_membership {s r : Bool} {c : (Channel M)} (h : ChannelInvariant s r c)
    (a : (Receipt M)) (ha : a ∈ c.received) :
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
theorem closed_transit_exact [DecidableEq M] {s r : Bool} {c : (Channel M)}
    (h : ChannelInvariant s r c)
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


/-- An edge carries its proof of membership; no fictitious non-edge channels. -/
abbrev Edge {n : ℕ} (edge : Fin n → Fin n → Prop) :=
  {p : Fin n × Fin n // edge p.1 p.2}

structure Node (D : Type) where
  value : D
  events : ℕ := 0
  localSnap : Option (D × ℕ) := none
  deriving DecidableEq, Repr

def Node.started (a : Node D) : Bool := a.localSnap.isSome

def Node.capture (a : Node D) : Node D :=
  { a with localSnap := some (a.value, a.events) }

def Node.tick (a : Node D) (value : D) : Node D :=
  { a with value := value, events := a.events + 1 }

@[simp] theorem started_capture (a : Node D) : a.capture.started = true := rfl
@[simp] theorem started_tick (a : Node D) (d : D) : (a.tick d).started = a.started := rfl

structure State {n : ℕ} (edge : Fin n → Fin n → Prop) (M D : Type) where
  node : Fin n → Node D
  chan : Edge edge → Channel M
  ready : Edge edge → Bool

variable {n : ℕ} {edge : Fin n → Fin n → Prop} {D : Type}

/-- Application data is abstract; each application transition supplies its next local value. -/
def initState (edge : Fin n → Fin n → Prop) (data : Fin n → D) : State edge M D :=
  ⟨fun i => ⟨data i, 0, none⟩, fun _ => {}, fun _ => false⟩

def capture (s : State edge M D) (u : Fin n) : State edge M D :=
  { s with
    node := fun i => if i = u then (s.node i).capture else s.node i
    chan := fun e => if e.val.1 = u then startChannel (s.chan e) else s.chan e }

def sendApp (s : State edge M D) (e : Edge edge) (msg : M) (next : D) : State edge M D :=
  { s with
    node := fun i => if i = e.val.1 then (s.node i).tick next else s.node i
    chan := Function.update s.chan e (sendChannel (s.chan e) (s.node e.val.1).started msg) }

def deliverApp (s : State edge M D) (e : Edge edge) (m : Packet M)
    (tail : List (ChanItem M)) (next : D) : State edge M D :=
  { s with
    node := fun i => if i = e.val.2 then (s.node i).tick next else s.node i
    chan := Function.update s.chan e (receiveApp (s.chan e) (s.node e.val.2).started m tail)
    ready := Function.update s.ready e false }

def closeMarker (s : State edge M D) (e : Edge edge) (tail : List (ChanItem M)) : State edge M D :=
  { s with chan := Function.update s.chan e (receiveMarker (s.chan e) tail)
           ready := Function.update s.ready e false }

def offer (s : State edge M D) (e : Edge edge) : State edge M D :=
  { s with ready := Function.update s.ready e true }

/-- The only spontaneous snapshot initiation is at root. Marker handling and broadcast
are one local atomic action, before subsequent application sends. -/
inductive Step (root : Fin n) : State edge M D → State edge M D → Prop where
  | idle (s) : Step root s s
  | initiate (s) (fresh : (s.node root).started = false) : Step root s (capture s root)
  | send (s) (e) (m : M) (next : D) : Step root s (sendApp s e m next)
  | offer (s) (e) (nonempty : (s.chan e).queue ≠ []) : Step root s (offer s e)
  | app (s) (e) (m) (tail) (next : D) (ready : s.ready e = true)
      (head : (s.chan e).queue = .app m :: tail) : Step root s (deliverApp s e m tail next)
  | firstMarker (s) (e) (tail) (ready : s.ready e = true)
      (head : (s.chan e).queue = .marker :: tail) (fresh : (s.node e.val.2).started = false) :
      Step root s (closeMarker (capture s e.val.2) e tail)
  | laterMarker (s) (e) (tail) (ready : s.ready e = true)
      (head : (s.chan e).queue = .marker :: tail) (started : (s.node e.val.2).started = true) :
      Step root s (closeMarker s e tail)

inductive Reachable (root : Fin n) (data : Fin n → D) : State edge M D → Prop where
  | init : Reachable root data (initState edge data)
  | step {s t} : Reachable root data s → Step root s t → Reachable root data t

def NetworkInvariant (s : State edge M D) : Prop :=
  ∀ e, ChannelInvariant (s.node e.val.1).started (s.node e.val.2).started (s.chan e)

@[simp] theorem send_started (s : State edge M D) (e) (m) (next) (i) :
    ((sendApp s e m next).node i).started = (s.node i).started := by
  simp [sendApp, apply_ite]

@[simp] theorem app_started (s : State edge M D) (e) (m) (tail) (next) (i) :
    ((deliverApp s e m tail next).node i).started = (s.node i).started := by
  simp [deliverApp, apply_ite]

@[simp] theorem capture_started (s : State edge M D) (u i) :
    ((capture s u).node i).started = if i = u then true else (s.node i).started := by
  simp [capture, apply_ite]

theorem invariant_init (data : Fin n → D) :
    NetworkInvariant (initState (M := M) edge data) := by
  intro e
  exact ⟨WirePhase.before [] (by simp), by simp [initState], rfl, rfl,
    by simp [initState], by simp [initState], rfl, by simp [initState]⟩

theorem invariant_capture {s : State edge M D} (h : NetworkInvariant s) (u : Fin n)
    (fresh : (s.node u).started = false) : NetworkInvariant (capture s u) := by
  intro e
  have he := h e
  by_cases hs : e.val.1 = u <;> by_cases hr : e.val.2 = u
  · have hboth : ChannelInvariant false false (s.chan e) := by simpa [hs, hr, fresh] using he
    simpa [capture, hs, hr, apply_ite] using
      invariant_start_receiver (invariant_start_sender hboth)
  · have hsrc : ChannelInvariant false (s.node e.val.2).started (s.chan e) := by
      simpa [hs, fresh] using he
    simpa [capture, hs, hr, apply_ite] using invariant_start_sender hsrc
  · have hdst : ChannelInvariant (s.node e.val.1).started false (s.chan e) := by
      simpa [hr, fresh] using he
    simpa [capture, hs, hr, apply_ite] using invariant_start_receiver hdst
  · simpa [capture, hs, hr, apply_ite] using he

theorem invariant_close {s : State edge M D} (h : NetworkInvariant s) (e : Edge edge)
    (tail) (head : (s.chan e).queue = .marker :: tail)
    (started : (s.node e.val.2).started = true) : NetworkInvariant (closeMarker s e tail) := by
  intro a
  by_cases he : a = e
  · subst a
    simpa [closeMarker, started] using invariant_receive_marker (h e) tail head
  · simpa [closeMarker, Function.update_apply, he] using h a

theorem invariant_step {root : Fin n} {s t : State edge M D} (hs : Step root s t)
    (h : NetworkInvariant s) : NetworkInvariant t := by
  cases hs with
  | idle => exact h
  | initiate hf => exact invariant_capture h _ hf
  | offer => exact h
  | send e m next =>
    intro a
    by_cases he : a = e
    · subst a
      simpa [sendApp, apply_ite] using invariant_send (h e) m
    · simpa [sendApp, apply_ite, Function.update_apply, he] using h a
  | app e m tail next ready head =>
    intro a
    by_cases he : a = e
    · subst a
      simpa [deliverApp, apply_ite] using invariant_receive_app (h e) m tail head
    · simpa [deliverApp, apply_ite, Function.update_apply, he] using h a
  | firstMarker e tail ready head fresh =>
    have src : (s.node e.val.1).started = true := (phase_marker (h e).phase head).1
    have hne : e.val.1 ≠ e.val.2 := by intro he; rw [he, fresh] at src; cases src
    apply invariant_close (invariant_capture h _ fresh) e tail
    · simpa [capture, hne] using head
    · simp
  | laterMarker e tail ready head started => exact invariant_close h e tail head started

theorem reachable_invariant {root : Fin n} {data : Fin n → D} {s : State edge M D}
    (h : Reachable root data s) : NetworkInvariant s := by
  induction h with
  | init => exact invariant_init data
  | step hr hs ih => exact invariant_step hs ih

/-- Phase stamps record the local flag at actual send/receive transitions. -/
theorem consistent_cut_safety {root : Fin n} {data : Fin n → D} {s : State edge M D}
    (h : Reachable root data s) (e : Edge edge) (r : Receipt M)
    (hr : r ∈ (s.chan e).received) (before : r.afterReceive = false) :
    r.packet.afterSend = false ∧ r.packet ∈ (s.chan e).sent :=
  ⟨(reachable_invariant h e).safe r hr before,
    received_origin (reachable_invariant h e) r hr⟩

/-- Ordered equality, retaining message identity even when payloads repeat. -/
theorem channel_recording_soundness [DecidableEq M] {root : Fin n}
    {data : Fin n → D} {s : State edge M D}
    (h : Reachable root data s) (e : Edge edge) (closed : (s.chan e).closed = true) :
    (s.chan e).transit = crossing (s.chan e).received ∧
    (s.chan e).transit = (sentBefore (s.chan e)).filter
      (fun m => !(receivedBefore (s.chan e)).contains m) :=
  ⟨(reachable_invariant h e).recorded, closed_transit_exact (reachable_invariant h e) closed⟩

/-- Receiver-local views of the recording flag and payload log. -/
def recording (s : State edge M D) (e : Edge edge) : Bool :=
  (s.node e.val.2).started && !(s.chan e).closed

def recordedChan (s : State edge M D) (e : Edge edge) : List M :=
  (s.chan e).transit.map Packet.val

theorem snapshot_single_assignment {root : Fin n} {s t : State edge M D}
    (hs : Step root s t) (i : Fin n) (snap : D × ℕ) (hi : (s.node i).localSnap = some snap) :
    (t.node i).localSnap = some snap := by
  have cap : ∀ u, (s.node u).started = false → ((capture s u).node i).localSnap = some snap := by
    intro u hf
    by_cases he : i = u
    · subst i
      simp [Node.started, hi] at hf
    · simpa [capture, he] using hi
  cases hs with
  | idle => exact hi
  | initiate hf => exact cap _ hf
  | offer => exact hi
  | send => simpa [sendApp, Node.tick, apply_ite] using hi
  | app => simpa [deliverApp, Node.tick, apply_ite] using hi
  | firstMarker e tail ready head fresh => exact cap _ fresh
  | laterMarker => exact hi

theorem started_step {root : Fin n} {s t : State edge M D} (hs : Step root s t)
    (i : Fin n) (hi : (s.node i).started = true) : (t.node i).started = true := by
  cases hs <;> simp_all [closeMarker, offer, capture_started]

@[simp] theorem capture_closed (s : State edge M D) (u) (e) :
    ((capture s u).chan e).closed = (s.chan e).closed := by
  simp [capture, apply_ite, startChannel]

@[simp] theorem send_closed (s : State edge M D) (a) (m) (next) (e) :
    ((sendApp s a m next).chan e).closed = (s.chan e).closed := by
  by_cases h : e = a <;> simp [sendApp, h, sendChannel]

@[simp] theorem app_closed (s : State edge M D) (a) (m) (tail) (next) (e) :
    ((deliverApp s a m tail next).chan e).closed = (s.chan e).closed := by
  by_cases h : e = a <;> simp [deliverApp, h, receiveApp]

@[simp] theorem close_closed (s : State edge M D) (a) (tail) (e) :
    ((closeMarker s a tail).chan e).closed = if e = a then true else (s.chan e).closed := by
  by_cases h : e = a <;> simp [closeMarker, h, receiveMarker]

theorem closed_step {root : Fin n} {s t : State edge M D} (hs : Step root s t)
    (e : Edge edge) (he : (s.chan e).closed = true) : (t.chan e).closed = true := by
  cases hs <;> simp [he, offer]

def MarkerEnabled (s : State edge M D) (e : Edge edge) : Prop :=
  s.ready e = true ∧ ∃ tail, (s.chan e).queue = .marker :: tail

theorem capture_enabled {s : State edge M D} {e : Edge edge} (h : MarkerEnabled s e)
    (u : Fin n) : MarkerEnabled (capture s u) e := by
  obtain ⟨hr, tail, ht⟩ := h
  refine ⟨hr, ?_⟩
  by_cases he : e.val.1 = u
  · exact ⟨tail ++ [.marker], by simp [capture, he, startChannel, ht]⟩
  · exact ⟨tail, by simpa [capture, he] using ht⟩

theorem close_enabled {s : State edge M D} {e : Edge edge} (h : MarkerEnabled s e)
    (a : Edge edge) (tail : List (ChanItem M)) :
    ((closeMarker s a tail).chan e).closed = true ∨ MarkerEnabled (closeMarker s a tail) e := by
  by_cases he : e = a
  · subst e; left; simp [closeMarker, receiveMarker]
  · right; simpa [MarkerEnabled, closeMarker, Function.update_apply, he] using h

theorem marker_enabled_step {root : Fin n} {s t : State edge M D} (hs : Step root s t)
    (e : Edge edge) (h : MarkerEnabled s e) :
    (t.chan e).closed = true ∨ MarkerEnabled t e := by
  cases hs with
  | idle => exact Or.inr h
  | initiate hf => exact Or.inr (capture_enabled h _)
  | offer a nonempty =>
    right
    by_cases he : e = a
    · subst a; exact ⟨by simp [offer], h.2⟩
    · simpa [MarkerEnabled, offer, Function.update_apply, he] using h
  | send a msg next =>
    right
    refine ⟨h.1, ?_⟩
    obtain ⟨tail, ht⟩ := h.2
    by_cases he : e = a
    · subst a
      exact ⟨tail ++ [.app ⟨(s.chan e).sent.length, msg, (s.node e.val.1).started⟩], by
        simp [sendApp, sendChannel, ht]⟩
    · exact ⟨tail, by simpa [sendApp, Function.update_apply, he] using ht⟩
  | app a msg tail next ready head =>
    by_cases he : e = a
    · subst a
      obtain ⟨xs, hx⟩ := h.2
      simp [head] at hx
    · right
      simpa [MarkerEnabled, deliverApp, Function.update_apply, he] using h
  | firstMarker a tail ready head fresh => exact close_enabled (capture_enabled h _) a tail
  | laterMarker a tail ready head started => exact close_enabled h a tail

structure Execution (root : Fin n) (data : Fin n → D) where
  state : ℕ → State edge M D
  initial : state 0 = initState edge data
  step : ∀ t, Step root (state t) (state (t + 1))

theorem phase_has_marker {q : List (ChanItem M)} (h : WirePhase true false q) :
    ChanItem.marker ∈ q := by
  cases h with
  | marked xs ys hx hy => simp

namespace Execution
variable {root : Fin n} {data : Fin n → D} (tr : Execution (M := M) (edge := edge) root data)

theorem reachable (t : ℕ) : Reachable root data (tr.state t) := by
  induction t with
  | zero => rw [tr.initial]; exact Reachable.init
  | succ t ih => exact Reachable.step ih (tr.step t)

theorem started_mono {t u : ℕ} (htu : t ≤ u) (i : Fin n)
    (hi : ((tr.state t).node i).started = true) : ((tr.state u).node i).started = true := by
  induction u, htu using Nat.le_induction with
  | base => exact hi
  | succ u hu ih => exact started_step (tr.step u) i ih

theorem closed_mono {t u : ℕ} (htu : t ≤ u) (e : Edge edge)
    (he : ((tr.state t).chan e).closed = true) : ((tr.state u).chan e).closed = true := by
  induction u, htu using Nat.le_induction with
  | base => exact he
  | succ u hu ih => exact closed_step (tr.step u) e ih

/-- A delivered item either awaits its local reaction at the offered FIFO head,
or has already been processed. Reliability does not assume that a snapshot completes. -/
def Delivered (s : State edge M D) (e : Edge edge) : ChanItem M → Prop
  | .marker => (s.chan e).closed = true
  | .app m => ∃ r ∈ (s.chan e).received, r.packet = m

def ReliableDelivery : Prop :=
  ∀ t e item, item ∈ ((tr.state t).chan e).queue →
    ∃ u, t ≤ u ∧ (Delivered (tr.state u) e item ∨
      ((tr.state u).ready e = true ∧ ∃ tail, ((tr.state u).chan e).queue = item :: tail))

/-- Weak fairness for continuously enabled local snapshot reactions. The effects
name actual false-to-true transitions, not eventual global completion. Application
and offer scheduling remain subject to ReliableDelivery. -/
structure WeakFairness : Prop where
  initiate : ∀ t, (∀ u, t ≤ u → ((tr.state u).node root).started = false) →
    ∃ u, t ≤ u ∧ ((tr.state u).node root).started = false ∧
      ((tr.state (u + 1)).node root).started = true
  marker : ∀ e t, (∀ u, t ≤ u → MarkerEnabled (tr.state u) e) →
    ∃ u, t ≤ u ∧ ((tr.state u).chan e).closed = false ∧
      ((tr.state (u + 1)).chan e).closed = true

theorem root_eventually_started (wf : tr.WeakFairness) :
    ∃ t, ((tr.state t).node root).started = true := by
  by_contra hn
  have hf : ∀ t, ((tr.state t).node root).started = false := by
    intro t; cases h : ((tr.state t).node root).started
    · rfl
    · exact False.elim (hn ⟨t, h⟩)
  obtain ⟨u, _, _, hu⟩ := wf.initiate 0 (fun u _ => hf u)
  exact hn ⟨u + 1, hu⟩

theorem enabled_eventually_closed (wf : tr.WeakFairness) (e : Edge edge) (t : ℕ)
    (ht : MarkerEnabled (tr.state t) e) :
    ∃ u, t ≤ u ∧ ((tr.state u).chan e).closed = true := by
  by_contra hn
  have noClose : ∀ u, t ≤ u → ((tr.state u).chan e).closed ≠ true := by
    intro u hu hc; exact hn ⟨u, hu, hc⟩
  have enabled : ∀ u, t ≤ u → MarkerEnabled (tr.state u) e := by
    intro u hu
    induction u, hu using Nat.le_induction with
    | base => exact ht
    | succ u hu ih =>
      exact (marker_enabled_step (tr.step u) e ih).resolve_left (noClose _ (by omega))
  obtain ⟨u, hu, _, hc⟩ := wf.marker e t enabled
  exact noClose (u + 1) (by omega) hc

theorem started_sender_eventually_closed (reliable : tr.ReliableDelivery) (wf : tr.WeakFairness)
    (t : ℕ) (e : Edge edge) (hs : ((tr.state t).node e.val.1).started = true) :
    ∃ u, t ≤ u ∧ ((tr.state u).chan e).closed = true := by
  have hi := reachable_invariant (tr.reachable t) e
  cases hc : ((tr.state t).chan e).closed
  · have hm : ChanItem.marker ∈ ((tr.state t).chan e).queue := by
      have hp := hi.phase
      rw [hs, hc] at hp
      exact phase_has_marker hp
    obtain ⟨u, htu, hu⟩ := reliable t e .marker hm
    rcases hu with hc' | hen
    · exact ⟨u, htu, hc'⟩
    · obtain ⟨v, huv, hv⟩ := tr.enabled_eventually_closed wf e u hen
      exact ⟨v, htu.trans huv, hv⟩
  · exact ⟨t, le_rfl, hc⟩

end Execution

/-- Directed reachability, including paths of length zero and directed self-loops. -/
inductive Path (edge : Fin n → Fin n → Prop) (root : Fin n) : Fin n → Prop where
  | root : Path edge root root
  | next {u v} : Path edge root u → edge u v → Path edge root v

def Complete (s : State edge M D) : Prop :=
  (∀ i, (s.node i).started = true) ∧ (∀ e, (s.chan e).closed = true)

theorem snapshot_conditional_termination {root : Fin n} {data : Fin n → D}
    (tr : Execution (M := M) (edge := edge) root data)
    (connected : ∀ i, Path edge root i) (reliable : tr.ReliableDelivery) (wf : tr.WeakFairness) :
    ∃ T, ∀ t, T ≤ t → Complete (tr.state t) := by
  classical
  have nodes : ∀ i, ∃ t, ((tr.state t).node i).started = true := by
    intro i
    induction connected i with
    | root => exact tr.root_eventually_started wf
    | @next u v path edgeUV ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨k, _, hk⟩ := tr.started_sender_eventually_closed reliable wf t ⟨(u,v), edgeUV⟩ ht
      exact ⟨k, (reachable_invariant (tr.reachable k) ⟨(u,v), edgeUV⟩).closed_receiver hk⟩
  have channels : ∀ e : Edge edge, ∃ t, ((tr.state t).chan e).closed = true := by
    intro e
    obtain ⟨t, ht⟩ := nodes e.val.1
    obtain ⟨k, _, hk⟩ := tr.started_sender_eventually_closed reliable wf t e ht
    exact ⟨k, hk⟩
  choose nt hn using nodes
  choose ct hc using channels
  let T := max (Finset.univ.sup nt) (Finset.univ.sup ct)
  refine ⟨T, fun t ht => ⟨?_, ?_⟩⟩
  · intro i
    apply tr.started_mono (i := i) _ (hn i)
    exact (Finset.le_sup (f := nt) (Finset.mem_univ i)).trans ((le_max_left _ _).trans ht)
  · intro e
    apply tr.closed_mono (e := e) _ (hc e)
    exact (Finset.le_sup (f := ct) (Finset.mem_univ e)).trans ((le_max_right _ _).trans ht)

/-- The relaxed model changes only delivery order, preserving the two items. -/
def swapHead (s : State edge M D) (e : Edge edge) (a b : ChanItem M)
    (tail : List (ChanItem M)) : State edge M D :=
  { s with chan := Function.update s.chan e { s.chan e with queue := b :: a :: tail } }

inductive NonFifoReachable (root : Fin n) (data : Fin n → D) : State edge M D → Prop where
  | init : NonFifoReachable root data (initState edge data)
  | protocol {s t} : NonFifoReachable root data s → Step root s t → NonFifoReachable root data t
  | overtake {s} (e) (a b : ChanItem M) (tail)
      (hr : NonFifoReachable root data s) (head : (s.chan e).queue = a :: b :: tail)
      (notOffered : s.ready e = false) : NonFifoReachable root data (swapHead s e a b tail)

namespace Examples

def oneEdge (u v : Fin 2) : Prop := u = 0 ∧ v = 1
instance : DecidableRel oneEdge := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
def e01 : Edge oneEdge := ⟨(0,1), by decide⟩
theorem edge_unique (e : Edge oneEdge) : e = e01 := by
  apply Subtype.ext
  exact Prod.ext e.property.1 e.property.2

def zeroData : Fin 2 → ℕ := fun _ => 0
def empty0 : State oneEdge ℕ ℕ := initState oneEdge zeroData
def empty1 := capture empty0 0
def empty2 := offer empty1 e01
def empty3 := closeMarker (capture empty2 1) e01 []

def emptyRun : ℕ → State oneEdge ℕ ℕ
  | 0 => empty0
  | 1 => empty1
  | 2 => empty2
  | _ + 3 => empty3

def emptyExecution : Execution (edge := oneEdge) (M := ℕ) 0 zeroData where
  state := emptyRun
  initial := rfl
  step t := by
    rcases t with _ | (_ | (_ | t))
    · exact Step.initiate _ rfl
    · exact Step.offer _ _ (by decide)
    · exact Step.firstMarker empty2 e01 [] (by decide) (by decide) (by decide)
    · exact Step.idle _

theorem empty_reliable : emptyExecution.ReliableDelivery := by
  intro t e item hm
  rw [edge_unique e] at *
  have hi : item = .marker := by
    rcases t with _ | (_ | (_ | t)) <;>
      simp_all [emptyExecution, emptyRun, empty0, empty1, empty2, empty3, initState,
        capture, offer, closeMarker, startChannel, receiveMarker, e01]
  subst item
  exact ⟨t + 3, by omega, Or.inl rfl⟩

theorem empty_fair : emptyExecution.WeakFairness where
  initiate t h := by
    have bad := h (t + 3) (by omega)
    change true = false at bad
    cases bad
  marker e t h := by
    rw [edge_unique e] at h
    obtain ⟨tail, bad⟩ := (h (t + 3) (by omega)).2
    change [] = ChanItem.marker :: tail at bad
    cases bad

theorem one_edge_connected : ∀ i, Path oneEdge 0 i := by
  intro i
  by_cases h : i = 0
  · subst i; exact Path.root
  · have hi : i = 1 := by
      apply Fin.ext
      have hn : i.val ≠ 0 := by intro hz; apply h; exact Fin.ext hz
      have := i.isLt
      omega
    subst i
    exact Path.next Path.root (by decide)

theorem empty_execution_completes : ∃ T, ∀ t, T ≤ t → Complete (emptyExecution.state t) :=
  snapshot_conditional_termination emptyExecution one_edge_connected empty_reliable empty_fair

/-- The marker overtakes a pre-cut application packet. The receiver closes the
channel, then receives that packet after its cut without recording it. -/
def prePacket : Packet ℕ := ⟨0, 7, false⟩
def bad1 := sendApp empty0 e01 7 0
def bad2 := capture bad1 0
def bad3 := swapHead bad2 e01 (.app prePacket) .marker []
def bad4 := offer bad3 e01
def bad5 := closeMarker (capture bad4 1) e01 [.app prePacket]
def bad6 := offer bad5 e01
def bad7 := deliverApp bad6 e01 prePacket [] 7

theorem bad_reachable : NonFifoReachable 0 zeroData bad7 := by
  have h1 : NonFifoReachable 0 zeroData bad1 :=
    .protocol .init (Step.send empty0 e01 7 0)
  have h2 : NonFifoReachable 0 zeroData bad2 := .protocol h1 (Step.initiate _ rfl)
  have h3 : NonFifoReachable 0 zeroData bad3 := .overtake _ _ _ _ h2 rfl rfl
  have h4 : NonFifoReachable 0 zeroData bad4 := .protocol h3 (Step.offer _ _ (by decide))
  have h5 : NonFifoReachable 0 zeroData bad5 :=
    .protocol h4 (Step.firstMarker bad4 e01 [.app prePacket] (by decide) (by decide) (by decide))
  have h6 : NonFifoReachable 0 zeroData bad6 := .protocol h5 (Step.offer _ _ (by decide))
  exact .protocol h6 (Step.app _ _ _ _ _ rfl rfl)

/-- This network has an unreachable second process; fairness and delivery alone
cannot initiate a snapshot at it. -/
def noEdge (_ _ : Fin 2) : Prop := False
def isolated0 : State noEdge ℕ ℕ := initState noEdge zeroData
def isolated1 := capture isolated0 0

def isolatedRun : ℕ → State noEdge ℕ ℕ
  | 0 => isolated0
  | _ + 1 => isolated1

def isolatedExecution : Execution (edge := noEdge) (M := ℕ) 0 zeroData where
  state := isolatedRun
  initial := rfl
  step t := by
    cases t with
    | zero => exact Step.initiate _ rfl
    | succ t => exact Step.idle _

theorem isolated_reliable : isolatedExecution.ReliableDelivery := by
  intro t e; exact False.elim e.property

theorem isolated_fair : isolatedExecution.WeakFairness where
  initiate t h := by
    have bad := h (t + 1) (by omega)
    change true = false at bad
    cases bad
  marker e := False.elim e.property

theorem isolated_never_complete : ∀ t, ¬ Complete (isolatedExecution.state t) := by
  intro t h
  have bad := h.1 1
  cases t <;> change false = true at bad <;> cases bad

end Examples

theorem non_fifo_anomaly_counterexample :
    ∃ s : State Examples.oneEdge ℕ ℕ,
      NonFifoReachable 0 Examples.zeroData s ∧
      (s.chan Examples.e01).closed = true ∧
      (s.chan Examples.e01).transit ≠ crossing (s.chan Examples.e01).received := by
  exact ⟨Examples.bad7, Examples.bad_reachable, by decide, by decide⟩

theorem reachability_assumption_necessary :
    Examples.isolatedExecution.ReliableDelivery ∧ Examples.isolatedExecution.WeakFairness ∧
      (∀ t, ¬ Complete (Examples.isolatedExecution.state t)) :=
  ⟨Examples.isolated_reliable, Examples.isolated_fair, Examples.isolated_never_complete⟩

/-- The phase observation is equivalent to strict event order relative to a local
capture. The application event leaves the snapshot flag unchanged, whereas capture
is the false-to-true transition at k. -/
theorem application_event_precedes_cut {root : Fin n} {data : Fin n → D}
    (tr : Execution (M := M) (edge := edge) root data) (i : Fin n) (k t : ℕ)
    (before : ((tr.state k).node i).started = false)
    (after : ((tr.state (k + 1)).node i).started = true)
    (unchanged : ((tr.state (t + 1)).node i).started = ((tr.state t).node i).started) :
    ((tr.state t).node i).started = false ↔ t < k := by
  constructor
  · intro ht
    have hle : t ≤ k := by
      by_contra hn
      have := tr.started_mono (by omega : k + 1 ≤ t) i after
      rw [ht] at this
      cases this
    have hne : t ≠ k := by
      intro he; subst t
      rw [before] at unchanged
      rw [after] at unchanged
      cases unchanged
    omega
  · intro htk
    cases ht : ((tr.state t).node i).started
    · rfl
    · have := tr.started_mono (Nat.le_of_lt htk) i ht
      rw [before] at this
      cases this

theorem send_event_precedes_cut {root : Fin n} {data : Fin n → D}
    (tr : Execution (M := M) (edge := edge) root data)
    (e : Edge edge) (k t : ℕ) (msg : M) (next : D)
    (before : ((tr.state k).node e.val.1).started = false)
    (after : ((tr.state (k + 1)).node e.val.1).started = true)
    (event : tr.state (t + 1) = sendApp (tr.state t) e msg next) :
    ((tr.state t).node e.val.1).started = false ↔ t < k :=
  application_event_precedes_cut tr _ k t before after (by rw [event, send_started])

theorem receive_event_precedes_cut {root : Fin n} {data : Fin n → D}
    (tr : Execution (M := M) (edge := edge) root data) (e : Edge edge) (k t : ℕ)
    (m : Packet M) (tail) (next : D)
    (before : ((tr.state k).node e.val.2).started = false)
    (after : ((tr.state (k + 1)).node e.val.2).started = true)
    (event : tr.state (t + 1) = deliverApp (tr.state t) e m tail next) :
    ((tr.state t).node e.val.2).started = false ↔ t < k :=
  application_event_precedes_cut tr _ k t before after (by rw [event, app_started])

@[simp] theorem capture_transit (s : State edge M D) (u e) :
    ((capture s u).chan e).transit = (s.chan e).transit := by
  simp [capture, apply_ite, startChannel]

@[simp] theorem close_transit (s : State edge M D) (a tail e) :
    ((closeMarker s a tail).chan e).transit = (s.chan e).transit := by
  by_cases h : e = a <;> simp [closeMarker, h, receiveMarker]

theorem closed_recording_preserved {root : Fin n} {s t : State edge M D}
    (hs : Step root s t) (e : Edge edge) (closed : (s.chan e).closed = true) :
    (t.chan e).transit = (s.chan e).transit := by
  cases hs with
  | idle => rfl
  | initiate => simp
  | offer => rfl
  | send a msg next =>
    by_cases h : e = a <;> simp [sendApp, h, sendChannel]
  | app a msg tail next ready head =>
    by_cases h : e = a
    · subst a; simp [deliverApp, receiveApp, closed]
    · simp [deliverApp, h]
  | firstMarker => simp
  | laterMarker => simp

theorem first_marker_empty {root : Fin n} {data : Fin n → D} {s : State edge M D}
    (h : Reachable root data s) (e : Edge edge) (tail)
    (fresh : (s.node e.val.2).started = false) :
    ((closeMarker (capture s e.val.2) e tail).chan e).transit = [] := by
  simp only [close_transit, capture_transit]
  have hi := reachable_invariant h e
  rw [hi.recorded]
  have he : (s.chan e).received.filter
      (fun r => r.afterReceive && !r.packet.afterSend) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro r hr
    simp [hi.pending fresh r hr]
  simp [crossing, he]

theorem complete_stops_recording {s : State edge M D} (h : Complete s) (e : Edge edge) :
    recording s e = false := by simp [recording, h.2 e]

structure NetworkProperties (edge : Fin n → Fin n → Prop) (M D : Type) [DecidableEq M]
    : Prop where
  invariant : ∀ (root : Fin n) (data : Fin n → D) (s : State edge M D),
    Reachable root data s → NetworkInvariant s
  consistency : ∀ (root : Fin n) (data : Fin n → D) (s : State edge M D),
    Reachable root data s → ∀ e r,
    r ∈ (s.chan e).received → r.afterReceive = false →
      r.packet.afterSend = false ∧ r.packet ∈ (s.chan e).sent
  exact_channels : ∀ (root : Fin n) (data : Fin n → D) (s : State edge M D),
    Reachable root data s → ∀ e,
    (s.chan e).closed = true →
    (s.chan e).transit = crossing (s.chan e).received ∧
    (s.chan e).transit = (sentBefore (s.chan e)).filter
      (fun m => !(receivedBefore (s.chan e)).contains m)
  snapshots_immutable : ∀ (root : Fin n) (s t : State edge M D), Step root s t → ∀ i snap,
    (s.node i).localSnap = some snap → (t.node i).localSnap = some snap
  channels_immutable : ∀ (root : Fin n) (s t : State edge M D), Step root s t → ∀ e,
    (s.chan e).closed = true →
    (t.chan e).transit = (s.chan e).transit
  termination : ∀ (root : Fin n) (data : Fin n → D)
    (tr : Execution (M := M) (edge := edge) root data),
    (∀ i, Path edge root i) → tr.ReliableDelivery → tr.WeakFairness →
      ∃ T, ∀ t, T ≤ t → Complete (tr.state t)

theorem network_properties (edge : Fin n → Fin n → Prop) (M D : Type) [DecidableEq M]
    : NetworkProperties edge M D where
  invariant := fun _ _ _ h => reachable_invariant h
  consistency := fun _ _ _ h => consistent_cut_safety h
  exact_channels := fun _ _ _ h => channel_recording_soundness h
  snapshots_immutable := fun _ _ _ h => snapshot_single_assignment h
  channels_immutable := fun _ _ _ h => closed_recording_preserved h
  termination := fun _ _ tr => snapshot_conditional_termination tr

structure DistributedChandyLamportGeneralSuite : Prop where
  all_networks : ∀ (n : ℕ) (edge : Fin n → Fin n → Prop)
    (M D : Type) [DecidableEq M], NetworkProperties edge M D
  fair_execution_exists : Examples.emptyExecution.ReliableDelivery ∧
    Examples.emptyExecution.WeakFairness
  non_fifo_boundary : ∃ s : State Examples.oneEdge ℕ ℕ,
    NonFifoReachable 0 Examples.zeroData s ∧ (s.chan Examples.e01).closed = true ∧
      (s.chan Examples.e01).transit ≠ crossing (s.chan Examples.e01).received
  reachability_boundary : Examples.isolatedExecution.ReliableDelivery ∧
    Examples.isolatedExecution.WeakFairness ∧ (∀ t, ¬ Complete (Examples.isolatedExecution.state t))

theorem distributed_chandy_lamport_general_master_suite : DistributedChandyLamportGeneralSuite where
  all_networks := fun _ edge M D _ => network_properties edge M D
  fair_execution_exists := ⟨Examples.empty_reliable, Examples.empty_fair⟩
  non_fifo_boundary := non_fifo_anomaly_counterexample
  reachability_boundary := reachability_assumption_necessary

end DistributedChandyLamportGeneral
