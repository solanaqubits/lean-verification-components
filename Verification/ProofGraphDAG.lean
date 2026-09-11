import Mathlib.Data.List.Basic

set_option linter.style.header false

namespace ProofGraphDAG

/-- Propositional syntax for the certificate checker. -/
inductive Formula where
  | atom (id : ℕ)
  | conj (f1 f2 : Formula)
  | impl (f1 f2 : Formula)
  | truth
  deriving DecidableEq, Repr

/-- Interpret atoms in a supplied propositional model. -/
def evalFormula (val : ℕ → Prop) : Formula → Prop
  | .atom id => val id
  | .conj f1 f2 => evalFormula val f1 ∧ evalFormula val f2
  | .impl f1 f2 => evalFormula val f1 → evalFormula val f2
  | .truth => True

/-- Finite certificate trees. The name zkFold denotes conjunction introduction only;
no shared graph nodes, commitments, or cryptographic verification are represented. -/
inductive ProofNode where
  | baseFact (id : ℕ)
  | axiomTruth
  | modusPonens (premise implication : ProofNode)
  | zkFold (p1 p2 : ProofNode)
  deriving DecidableEq, Repr

def proofDepth : ProofNode → ℕ
  | .baseFact _ => 1
  | .axiomTruth => 1
  | .modusPonens p1 p2 => 1 + max (proofDepth p1) (proofDepth p2)
  | .zkFold p1 p2 => 1 + max (proofDepth p1) (proofDepth p2)

/-- Return the conclusion of a structurally valid certificate, or reject it. -/
def targetFormula (baseVal : ℕ → Formula) : ProofNode → Option Formula
  | .baseFact id => some (baseVal id)
  | .axiomTruth => some .truth
  | .modusPonens pPrem pImpl =>
      match targetFormula baseVal pPrem, targetFormula baseVal pImpl with
      | some fPrem, some (.impl f1 f2) =>
          if fPrem = f1 then some f2 else none
      | _, _ => none
  | .zkFold p1 p2 =>
      match targetFormula baseVal p1, targetFormula baseVal p2 with
      | some f1, some f2 => some (.conj f1 f2)
      | _, _ => none

/-- External base formulas are assumed true in the chosen model. -/
def SoundBase (val : ℕ → Prop) (baseVal : ℕ → Formula) : Prop :=
  ∀ id : ℕ, evalFormula val (baseVal id)

/-- Accepted conclusions are true whenever the supplied base is sound. -/
theorem proof_soundness
    (val : ℕ → Prop) (baseVal : ℕ → Formula)
    (h_base : SoundBase val baseVal) (p : ProofNode) (f : Formula)
    (h_target : targetFormula baseVal p = some f) :
    evalFormula val f := by
  induction p generalizing f with
  | baseFact id =>
      cases h_target
      exact h_base id
  | axiomTruth =>
      cases h_target
      trivial
  | modusPonens p q ihp ihq =>
      cases hp : targetFormula baseVal p with
      | none => simp [targetFormula, hp] at h_target
      | some a =>
          cases hq : targetFormula baseVal q with
          | none => simp [targetFormula, hp, hq] at h_target
          | some b =>
              cases b with
              | atom id => simp [targetFormula, hp, hq] at h_target
              | truth => simp [targetFormula, hp, hq] at h_target
              | conj b c => simp [targetFormula, hp, hq] at h_target
              | impl b c =>
                  by_cases hab : a = b
                  · subst b
                    have hc : c = f := by simpa [targetFormula, hp, hq] using h_target
                    subst f
                    exact ihq _ hq (ihp _ hp)
                  · simp [targetFormula, hp, hq, hab] at h_target
  | zkFold p q ihp ihq =>
      cases hp : targetFormula baseVal p with
      | none => simp [targetFormula, hp] at h_target
      | some a =>
          cases hq : targetFormula baseVal q with
          | none => simp [targetFormula, hp, hq] at h_target
          | some b =>
              have hf : Formula.conj a b = f := by
                simpa [targetFormula, hp, hq] using h_target
              subst f
              exact ⟨ihp _ hp, ihq _ hq⟩

/-- Check each certificate against its expected conclusion. -/
def verifyBatch (baseVal : ℕ → Formula) : List (ProofNode × Formula) → Bool
  | [] => true
  | (p, f) :: rest =>
      match targetFormula baseVal p with
      | some f' => decide (f' = f) && verifyBatch baseVal rest
      | none => false

/-- An accepted batch consists entirely of valid target matches. -/
theorem verifyBatch_iff (baseVal : ℕ → Formula) (batch : List (ProofNode × Formula)) :
    verifyBatch baseVal batch = true ↔
      ∀ p f, (p, f) ∈ batch → targetFormula baseVal p = some f := by
  induction batch with
  | nil => simp [verifyBatch]
  | cons head tail ih =>
      rcases head with ⟨p, f⟩
      have hcons :
          (∀ q g, (q, g) ∈ (p, f) :: tail → targetFormula baseVal q = some g) ↔
          targetFormula baseVal p = some f ∧
            ∀ q g, (q, g) ∈ tail → targetFormula baseVal q = some g := by
        constructor
        · intro h
          exact ⟨h p f (List.mem_cons_self), fun q g hm => h q g (List.mem_cons_of_mem _ hm)⟩
        · rintro ⟨hh, ht⟩ q g hm
          rcases List.mem_cons.mp hm with he | he
          · cases he
            exact hh
          · exact ht q g he
      rw [hcons]
      cases ht : targetFormula baseVal p <;> simp [verifyBatch, ht, ih]

/-- Soundness of batch checking, conditional on the soundness of the base. -/
theorem batch_verification_sound
    (val : ℕ → Prop) (baseVal : ℕ → Formula) (h_base : SoundBase val baseVal)
    (batch : List (ProofNode × Formula))
    (h_ver : verifyBatch baseVal batch = true) :
    ∀ p f, (p, f) ∈ batch → evalFormula val f := by
  intro p f hmem
  exact proof_soundness val baseVal h_base p f ((verifyBatch_iff baseVal batch).mp h_ver p f hmem)

/-- Summary of the two conditional semantic soundness guarantees. -/
structure ProofDAGFormalSuite : Prop where
  h_soundness : ∀ (val : ℕ → Prop) (baseVal : ℕ → Formula),
    SoundBase val baseVal → ∀ (p : ProofNode) (f : Formula),
    targetFormula baseVal p = some f → evalFormula val f
  h_batch_soundness : ∀ (val : ℕ → Prop) (baseVal : ℕ → Formula),
    SoundBase val baseVal → ∀ (batch : List (ProofNode × Formula)),
    verifyBatch baseVal batch = true →
    ∀ p f, (p, f) ∈ batch → evalFormula val f

theorem proof_dag_master_verification_suite : ProofDAGFormalSuite := {
  h_soundness := proof_soundness
  h_batch_soundness := batch_verification_sound
}

#print axioms proof_dag_master_verification_suite

end ProofGraphDAG
