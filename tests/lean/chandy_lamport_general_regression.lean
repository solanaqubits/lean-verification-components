import Verification.DistributedChandyLamportGeneral

open DistributedChandyLamportGeneral

section General
variable {n : ℕ} {edge : Fin n → Fin n → Prop}
variable {M D : Type} [DecidableEq M] {root : Fin n} {data : Fin n → D}

example : NetworkProperties edge M D :=
  distributed_chandy_lamport_general_master_suite.all_networks n edge M D

example (tr : Execution (edge := edge) (M := M) root data)
    (hpath : ∀ i, Path edge root i) (hd : tr.ReliableDelivery) (hf : tr.WeakFairness) :
    ∃ T, ∀ t, T ≤ t → Complete (tr.state t) := snapshot_conditional_termination tr hpath hd hf

example (s : State edge M D) (h : Reachable root data s) (e : Edge edge)
    (r : Receipt M) (hr : r ∈ (s.chan e).received) (hb : r.afterReceive = false) :
    r.packet.afterSend = false := (consistent_cut_safety h e r hr hb).1

example (s : State edge M D) (h : Reachable root data s) (e : Edge edge)
    (hc : (s.chan e).closed = true) :
    (s.chan e).transit = (sentBefore (s.chan e)).filter
      (fun m => !(receivedBefore (s.chan e)).contains m) := (channel_recording_soundness h e hc).2

example (tr : Execution (edge := edge) (M := M) root data) (e : Edge edge) (k t : ℕ)
    (m : Packet M) (tail) (next : D) (hpre : ((tr.state k).node e.val.2).started = false)
    (hpost : ((tr.state (k+1)).node e.val.2).started = true)
    (hevent : tr.state (t+1) = deliverApp (tr.state t) e m tail next) :
    ((tr.state t).node e.val.2).started = false ↔ t < k :=
  receive_event_precedes_cut tr e k t m tail next hpre hpost hevent
end General

example : Examples.emptyExecution.ReliableDelivery ∧ Examples.emptyExecution.WeakFairness :=
  distributed_chandy_lamport_general_master_suite.fair_execution_exists
example : ∃ T, ∀ t, T ≤ t → Complete (Examples.emptyExecution.state t) :=
  Examples.empty_execution_completes
example : ∀ t, ¬ Complete (Examples.isolatedExecution.state t) :=
  reachability_assumption_necessary.2.2
example : (Examples.bad7.chan Examples.e01).transit = [] ∧
    crossing (Examples.bad7.chan Examples.e01).received = [Examples.prePacket] := by decide
example : ¬ Reachable 0 Examples.zeroData Examples.bad7 := by
  intro h
  have exactRecord := (channel_recording_soundness h Examples.e01 (by decide)).1
  have bad : (Examples.bad7.chan Examples.e01).transit ≠
      crossing (Examples.bad7.chan Examples.e01).received := by decide
  exact bad exactRecord

namespace MultipleIncoming

def edge (u v : Fin 3) : Prop := (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2)
instance : DecidableRel edge := fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))
def e01 : Edge edge := ⟨(0,1), by decide⟩
def e02 : Edge edge := ⟨(0,2), by decide⟩
def e12 : Edge edge := ⟨(1,2), by decide⟩
def d : Fin 3 → ℕ := fun _ => 0

def s0 : State edge String ℕ := initState edge d
def s1 := sendApp s0 e02 "same" 1
def s2 := sendApp s1 e02 "same" 2
def s3 := capture s2 0
def s4 := offer s3 e01
def s5 := closeMarker (capture s4 1) e01 []
def s6 := offer s5 e12
def s7 := closeMarker (capture s6 2) e12 []
def p0 : Packet String := ⟨0,"same",false⟩
def p1 : Packet String := ⟨1,"same",false⟩
def s8 := offer s7 e02
def s9 := deliverApp s8 e02 p0 [.app p1,.marker] 1
def s10 := offer s9 e02
def s11 := deliverApp s10 e02 p1 [.marker] 2
def s12 := offer s11 e02
def s13 := closeMarker s12 e02 []

theorem reach7 : Reachable 0 d s7 := by
  have h1 : Reachable 0 d s1 := .step .init (Step.send _ _ _ _)
  have h2 : Reachable 0 d s2 := .step h1 (Step.send _ _ _ _)
  have h3 : Reachable 0 d s3 := .step h2 (Step.initiate _ (by decide))
  have h4 : Reachable 0 d s4 := .step h3 (Step.offer _ _ (by decide))
  have h5 : Reachable 0 d s5 :=
    .step h4 (Step.firstMarker s4 e01 [] (by decide) (by decide) (by decide))
  have h6 : Reachable 0 d s6 := .step h5 (Step.offer _ _ (by decide))
  exact .step h6 (Step.firstMarker s6 e12 [] (by decide) (by decide) (by decide))

theorem reach13 : Reachable 0 d s13 := by
  have h8 : Reachable 0 d s8 := .step reach7 (Step.offer _ _ (by decide))
  have h9 : Reachable 0 d s9 := .step h8 (Step.app _ _ _ _ _ (by decide) (by decide))
  have h10 : Reachable 0 d s10 := .step h9 (Step.offer _ _ (by decide))
  have h11 : Reachable 0 d s11 := .step h10 (Step.app _ _ _ _ _ (by decide) (by decide))
  have h12 : Reachable 0 d s12 := .step h11 (Step.offer _ _ (by decide))
  exact .step h12 (Step.laterMarker s12 e02 [] (by decide) (by decide) (by decide))

-- First marker on one incoming edge leaves the other incoming edge recording.
example : (s7.chan e12).closed = true ∧ recording s7 e02 = true := by decide
example : (s7.chan e12).transit = [] := by decide
-- Repeated payloads retain distinct packet identities and the exact FIFO order.
example : recordedChan s13 e02 = ["same","same"] := by decide
example : ((s13.chan e02).transit.map Packet.id) = [0,1] := by decide
example : Complete s13 := by unfold Complete; decide
example : (s13.node 0).localSnap = some (2,2) ∧ (s13.node 2).localSnap = some (0,0) := by decide
example : (s13.chan e02).transit = crossing (s13.chan e02).received :=
  (channel_recording_soundness reach13 e02 (by decide)).1
end MultipleIncoming

namespace UnreachableIncoming

def edge (u v : Fin 3) : Prop := (u = 0 ∨ u = 2) ∧ v = 1
instance : DecidableRel edge := fun _ _ => inferInstanceAs (Decidable ((_ ∨ _) ∧ _))
def e01 : Edge edge := ⟨(0,1), by decide⟩
def e21 : Edge edge := ⟨(2,1), by decide⟩
def d : Fin 3 → ℕ := fun _ => 0
def s0 : State edge ℕ ℕ := initState edge d
def s1 := capture s0 0
def s2 := offer s1 e01
def s3 := closeMarker (capture s2 1) e01 []
example : Reachable 0 d s3 := by
  have h1 : Reachable 0 d s1 := .step .init (Step.initiate _ (by decide))
  have h2 : Reachable 0 d s2 := .step h1 (Step.offer _ _ (by decide))
  exact .step h2 (Step.firstMarker s2 e01 [] (by decide) (by decide) (by decide))
example : recording s3 e21 = true ∧ (s3.node 2).started = false := by decide
example : ¬ Path edge 0 2 := by
  intro h
  cases h with
  | next path he => have bad : (2 : Fin 3) = 1 := he.2; exact (show (2 : Fin 3) ≠ 1 from by decide) bad
end UnreachableIncoming
