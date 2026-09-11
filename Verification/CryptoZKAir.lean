import Mathlib.Data.List.Basic

set_option linter.style.header false

namespace CryptoZKAir

/-- Adjacent states follow the supplied deterministic transition function. -/
def ValidTransitions {α : Type*} (F : α → α) : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => y = F x ∧ ValidTransitions F (y :: rest)

/-- Generate the initial state followed by n transitions. -/
def generateTrace {α : Type*} (F : α → α) (init : α) : ℕ → List α
  | 0 => [init]
  | n + 1 => init :: generateTrace F (F init) n

theorem generateTrace_length {α : Type*} (F : α → α) (init : α) (n : ℕ) :
    (generateTrace F init n).length = n + 1 := by
  induction n generalizing init with
  | zero => rfl
  | succ n ih => simp [generateTrace, ih]

theorem generateTrace_head {α : Type*} (F : α → α) (init : α) (n : ℕ) :
    (generateTrace F init n).head? = some init := by
  cases n <;> rfl

theorem generateTrace_valid {α : Type*} (F : α → α) (init : α) (n : ℕ) :
    ValidTransitions F (generateTrace F init n) := by
  induction n generalizing init with
  | zero => trivial
  | succ n ih =>
      cases n with
      | zero => exact ⟨rfl, trivial⟩
      | succ m => exact ⟨rfl, ih (F init)⟩

/-- Exact equality checking, not a cryptographic proof verifier. -/
def checkTransitions {α : Type*} [DecidableEq α] (F : α → α) : List α → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => decide (y = F x) && checkTransitions F (y :: rest)

theorem checkTransitions_iff {α : Type*} [DecidableEq α] (F : α → α) (trace : List α) :
    checkTransitions F trace = true ↔ ValidTransitions F trace := by
  induction trace with
  | nil => simp [checkTransitions, ValidTransitions]
  | cons x xs ih =>
      cases xs with
      | nil => simp [checkTransitions, ValidTransitions]
      | cons y rest => simpa [checkTransitions, ValidTransitions] using and_congr Iff.rfl ih

/-- A deterministic transition, common initial state, and common length determine the trace. -/
theorem trace_uniqueness {α : Type*} (F : α → α) (t1 t2 : List α)
    (h1 : ValidTransitions F t1) (h2 : ValidTransitions F t2)
    (hh : t1.head? = t2.head?) (hl : t1.length = t2.length) : t1 = t2 := by
  induction t1 generalizing t2 with
  | nil =>
      cases t2 <;> simp_all
  | cons x xs ih =>
      cases t2 with
      | nil => simp at hl
      | cons y ys =>
          have hxy : x = y := Option.some.inj hh
          subst y
          have hlen : xs.length = ys.length := Nat.succ.inj hl
          cases xs with
          | nil =>
              cases ys <;> simp_all
          | cons z zs =>
              cases ys with
              | nil => simp at hlen
              | cons w ws =>
                  have hz : z = F x := h1.1
                  have hw : w = F x := h2.1
                  have hhead : (z :: zs).head? = (w :: ws).head? := by simp [hz, hw]
                  exact congrArg (List.cons x) (ih _ h1.2 h2.2 hhead hlen)

/-- The Boolean checker accepts every generated trace. -/
theorem check_generated_trace {α : Type*} [DecidableEq α] (F : α → α) (init : α) (n : ℕ) :
    checkTransitions F (generateTrace F init n) = true :=
  (checkTransitions_iff F _).mpr (generateTrace_valid F init n)

/-- Guarantees for generic deterministic traces; no polynomial or protocol assumptions. -/
structure CryptoZKAirFormalSuite : Prop where
  h_completeness : ∀ {α : Type*} (F : α → α) (init : α) (n : ℕ),
    ValidTransitions F (generateTrace F init n)
  h_length : ∀ {α : Type*} (F : α → α) (init : α) (n : ℕ),
    (generateTrace F init n).length = n + 1
  h_head : ∀ {α : Type*} (F : α → α) (init : α) (n : ℕ),
    (generateTrace F init n).head? = some init
  h_uniqueness : ∀ {α : Type*} (F : α → α) (t1 t2 : List α),
    ValidTransitions F t1 → ValidTransitions F t2 →
    t1.head? = t2.head? → t1.length = t2.length → t1 = t2
  h_check_equiv : ∀ {α : Type*} [DecidableEq α] (F : α → α) (trace : List α),
    checkTransitions F trace = true ↔ ValidTransitions F trace

theorem crypto_zk_air_master_verification_suite : CryptoZKAirFormalSuite := {
  h_completeness := generateTrace_valid
  h_length := generateTrace_length
  h_head := generateTrace_head
  h_uniqueness := trace_uniqueness
  h_check_equiv := checkTransitions_iff
}

#print axioms crypto_zk_air_master_verification_suite

end CryptoZKAir
