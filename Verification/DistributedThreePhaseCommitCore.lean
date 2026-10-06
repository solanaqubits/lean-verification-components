/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedTwoPhaseCommit
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Finite-control two-participant 3PC

One transaction, individual request/response slots, irreversible crashes, and an
external accurate epoch-fencing service. Votes and report bodies are immutable
between send and consumption. The service does not inspect phases to decide.
-/
namespace DistributedThreePhaseCommit

/-- Phase codes: 0 vote, 1 reports, 2 align commit, 3 align abort,
4 final commit, 5 final abort. Participant codes: 0 init, 1 prepared,
2 precommit, 3 committed, 4 aborted. Process 0 is the original coordinator. -/
structure Core where
  left : Nat
  right : Nat
  yes : Nat
  live : Nat
  members : Nat
  owner : Nat
  epoch : Nat
  phase : Nat
  leftSlot : Nat
  rightSlot : Nat
  leftBody : Nat
  rightBody : Nat
  deriving DecidableEq, Repr

def initial : Core := ⟨0, 0, 0, 7, 3, 0, 0, 0, 0, 0, 0, 0⟩
def bit (n p : Nat) : Bool := n / 2 ^ p % 2 == 1
def localState (s : Core) (p : Bool) : Nat := if p then s.right else s.left
def slot (s : Core) (p : Bool) : Nat := if p then s.rightSlot else s.leftSlot
def body (s : Core) (p : Bool) : Nat := if p then s.rightBody else s.leftBody
def member (s : Core) (p : Bool) : Bool := bit s.members (if p then 1 else 0)
def alive (s : Core) (p : Bool) : Bool := bit s.live (if p then 2 else 1)
def running (s : Core) : Bool := bit s.live s.owner

def setLocal (s : Core) (p : Bool) (v : Nat) : Core :=
  if p then { s with right := v } else { s with left := v }
def setSlot (s : Core) (p : Bool) (v : Nat) : Core :=
  if p then { s with rightSlot := v } else { s with leftSlot := v }
def setBody (s : Core) (p : Bool) (v : Nat) : Core :=
  if p then { s with rightBody := v } else { s with leftBody := v }
def startPhase (s : Core) (v : Nat) : Core :=
  { s with phase := v, leftSlot := 0, rightSlot := 0, leftBody := 0, rightBody := 0 }

/-- An addressed request and an addressed response occupy separate directed slots.
Bodies 0..4 describe the participant state at the response send event. -/
structure Packet where
  transaction : Nat
  epoch : Nat
  sender : Nat
  recipient : Nat
  phase : Nat
  response : Bool
  payload : Nat
  deriving DecidableEq, Repr

def request (s : Core) (p : Bool) : Packet :=
  ⟨0, s.epoch, s.owner, if p then 2 else 1, s.phase, false, 0⟩
def response (s : Core) (p : Bool) : Packet :=
  ⟨0, s.epoch, if p then 2 else 1, s.owner, s.phase, true, body s p⟩
def channel (s : Core) (p : Bool) : List Packet :=
  if slot s p = 1 then [request s p]
  else if slot s p = 3 then [response s p] else []
def packets (s : Core) : List Packet := channel s false ++ channel s true

/-- Events 0,1 send requests; 2..5 receive requests (yes/no alternatives in voting);
6,7 send replies; 8,9 receive replies; 10 advances the coordinator;
11..13 crash a process; 14 installs an accurate fenced view; 15 is an idle tick. -/
def coreStep (s : Core) (e : Nat) : Option Core := Id.run do
  if e = 15 then return some s
  if 11 ≤ e ∧ e ≤ 13 then
    let mask := 2 ^ (e - 11)
    if bit s.live (e - 11) then return some { s with live := s.live - mask }
    return none
  if e = 14 then
    let survivors := s.live / 2 % 4
    if survivors = 0 ∨ (running s ∧ s.members = survivors) then return none
    let t := { s with
      members := survivors
      owner := (if bit survivors 0 then 1 else 2)
      epoch := s.epoch + 1 }
    return some (startPhase t 1)
  if e ≤ 1 then
    let p := e = 1
    if ¬running s ∨ ¬member s p ∨ slot s p ≠ 0 then return none
    if p ∧ member s false ∧ s.leftSlot = 0 then return none
    return some (setSlot s p 1)
  if 2 ≤ e ∧ e ≤ 5 then
    let p := 4 ≤ e
    let negative := e % 2 = 1
    if ¬alive s p ∨ slot s p ≠ 1 then return none
    if negative ∧ s.phase ≠ 0 then return none
    let mut t := s
    if s.phase = 0 then
      if localState s p ≠ 0 then return none
      t := setLocal s p (if negative then 4 else 1)
      if ¬negative then
        t := { t with yes := s.yes + (if bit s.yes (if p then 1 else 0)
          then 0 else if p then 2 else 1) }
    else if s.phase = 2 then
      if localState s p ≠ 1 ∧ localState s p ≠ 2 ∧ localState s p ≠ 3 then return none
      if localState s p ≠ 3 then t := setLocal s p 2
    else if s.phase = 4 then
      if localState s p ≠ 2 ∧ localState s p ≠ 3 then return none
      t := setLocal s p 3
    else if s.phase = 5 then
      if localState s p = 3 then return none
      t := setLocal s p 4
    return some (setSlot t p 2)
  if e = 6 ∨ e = 7 then
    let p := e = 7
    if ¬alive s p ∨ slot s p ≠ 2 then return none
    return some (setSlot (setBody s p (localState s p)) p 3)
  if e = 8 ∨ e = 9 then
    let p := e = 9
    if ¬running s ∨ slot s p ≠ 3 then return none
    return some (setSlot s p 4)
  if e = 10 then
    if ¬running s ∨ (member s false ∧ s.leftSlot ≠ 4) ∨
        (member s true ∧ s.rightSlot ≠ 4) then return none
    if s.phase = 0 then
      return some (startPhase s (if s.leftBody = 1 ∧ s.rightBody = 1 then 2 else 5))
    if s.phase = 1 then
      let commitReport := (member s false ∧ (s.leftBody = 2 ∨ s.leftBody = 3)) ∨
        (member s true ∧ (s.rightBody = 2 ∨ s.rightBody = 3))
      return some (startPhase s (if commitReport then 2 else 3))
    if s.phase = 2 then return some (startPhase s 4)
    if s.phase = 3 then return some (startPhase s 5)
    return none
  return none

/-- Request/response queues are bounded by the handshake discipline, not by trace length. -/
inductive Step : Core → Nat → Core → Prop where
  | execute {s t e} (bound : e < 16) (h : coreStep s e = some t) : Step s e t

inductive Execution : Core → List Nat → Core → Prop where
  | nil (s) : Execution s [] s
  | cons {s t u e es} (h : Step s e t) (tail : Execution t es u) : Execution s (e :: es) u

def Reachable (s : Core) : Prop := ∃ es, Execution initial es s

def Agreement (s : Core) : Prop :=
  ¬(s.left = 3 ∧ s.right = 4) ∧ ¬(s.left = 4 ∧ s.right = 3)
def AllTerminal (s : Core) : Prop :=
  (alive s false → s.left = 3 ∨ s.left = 4) ∧
  (alive s true → s.right = 3 ∨ s.right = 4)
def Stable (s : Core) : Prop :=
  running s ∧ s.members = s.live / 2 % 4 ∧ s.members ≠ 0

def rank (s : Core) : Nat :=
  (if s.phase ≤ 1 then 4 else if s.phase ≤ 3 then 3 else 2) * 12 +
  (if member s false then 4 - s.leftSlot else 0) +
  (if member s true then 4 - s.rightSlot else 0)

def operational (e : Nat) : Prop := e ≤ 10 ∨ e = 15
instance (s : Core) : Decidable (Agreement s) := by unfold Agreement; infer_instance
instance (s : Core) : Decidable (AllTerminal s) := by unfold AllTerminal; infer_instance
instance (s : Core) : Decidable (Stable s) := by unfold Stable; infer_instance
instance (e : Nat) : Decidable (operational e) := by unfold operational; infer_instance

/-- Mixed-radix decoding is only proof-certificate storage, not the runtime parser. -/
def decode (n : Nat) : Core :=
  ⟨n % 5, n / 5 % 5, n / 25 % 4, n / 100 % 8, n / 800 % 4,
   n / 3200 % 3, n / 9600 % 3, n / 28800 % 6,
   n / 172800 % 5, n / 864000 % 5, n / 4320000 % 5, n / 21600000 % 5⟩

def encode (s : Core) : Nat := s.left + 5 * s.right + 25 * s.yes + 100 * s.live +
  800 * s.members + 3200 * s.owner + 9600 * s.epoch + 28800 * s.phase +
  172800 * s.leftSlot + 864000 * s.rightSlot + 4320000 * s.leftBody +
  21600000 * s.rightBody
end DistributedThreePhaseCommit
