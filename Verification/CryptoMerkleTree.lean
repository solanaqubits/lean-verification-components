import Mathlib.Data.Real.Basic

set_option linter.style.header false

namespace CryptoMerkleTree

/-- Position of the sibling relative to the current node. -/
inductive Direction where
  | left
  | right
  deriving DecidableEq, Repr

structure ProofStep where
  dir : Direction
  sibling : ℝ

structure MerkleProof2 where
  step1 : ProofStep
  step2 : ProofStep

/-- H is an arbitrary binary function, without a security assumption. -/
def applyStep (H : ℝ → ℝ → ℝ) (current : ℝ) (step : ProofStep) : ℝ :=
  match step.dir with
  | Direction.left => H step.sibling current
  | Direction.right => H current step.sibling

def computeRoot (H : ℝ → ℝ → ℝ) (leaf : ℝ) (proof : MerkleProof2) : ℝ :=
  applyStep H (applyStep H leaf proof.step1) proof.step2

def verifyProof (H : ℝ → ℝ → ℝ) (leaf : ℝ) (proof : MerkleProof2) (root : ℝ) : Prop :=
  computeRoot H leaf proof = root

/-- The verification predicate is defined by this equality. -/
theorem verify_proof_iff_compute_root (H : ℝ → ℝ → ℝ) (leaf : ℝ)
    (proof : MerkleProof2) (root : ℝ) :
    verifyProof H leaf proof root ↔ computeRoot H leaf proof = root := Iff.rfl

def canonicalRoot (H : ℝ → ℝ → ℝ) (l0 l1 l2 l3 : ℝ) : ℝ :=
  H (H l0 l1) (H l2 l3)

def proofForLeaf0 (H : ℝ → ℝ → ℝ) (l1 l2 l3 : ℝ) : MerkleProof2 :=
  ⟨⟨Direction.right, l1⟩, ⟨Direction.right, H l2 l3⟩⟩

def proofForLeaf1 (H : ℝ → ℝ → ℝ) (l0 l2 l3 : ℝ) : MerkleProof2 :=
  ⟨⟨Direction.left, l0⟩, ⟨Direction.right, H l2 l3⟩⟩

def proofForLeaf2 (H : ℝ → ℝ → ℝ) (l0 l1 l3 : ℝ) : MerkleProof2 :=
  ⟨⟨Direction.right, l3⟩, ⟨Direction.left, H l0 l1⟩⟩

def proofForLeaf3 (H : ℝ → ℝ → ℝ) (l0 l1 l2 : ℝ) : MerkleProof2 :=
  ⟨⟨Direction.left, l2⟩, ⟨Direction.left, H l0 l1⟩⟩

theorem merkle_proof_completeness_leaf0 (H : ℝ → ℝ → ℝ) (l0 l1 l2 l3 : ℝ) :
    verifyProof H l0 (proofForLeaf0 H l1 l2 l3) (canonicalRoot H l0 l1 l2 l3) := rfl

theorem merkle_proof_completeness_leaf1 (H : ℝ → ℝ → ℝ) (l0 l1 l2 l3 : ℝ) :
    verifyProof H l1 (proofForLeaf1 H l0 l2 l3) (canonicalRoot H l0 l1 l2 l3) := rfl

theorem merkle_proof_completeness_leaf2 (H : ℝ → ℝ → ℝ) (l0 l1 l2 l3 : ℝ) :
    verifyProof H l2 (proofForLeaf2 H l0 l1 l3) (canonicalRoot H l0 l1 l2 l3) := rfl

theorem merkle_proof_completeness_leaf3 (H : ℝ → ℝ → ℝ) (l0 l1 l2 l3 : ℝ) :
    verifyProof H l3 (proofForLeaf3 H l0 l1 l2) (canonicalRoot H l0 l1 l2 l3) := rfl

/-- Conjunction of the four canonical path checks. -/
theorem merkle_universal_leaf_inclusion (H : ℝ → ℝ → ℝ) (l0 l1 l2 l3 : ℝ) :
    verifyProof H l0 (proofForLeaf0 H l1 l2 l3) (canonicalRoot H l0 l1 l2 l3) ∧
    verifyProof H l1 (proofForLeaf1 H l0 l2 l3) (canonicalRoot H l0 l1 l2 l3) ∧
    verifyProof H l2 (proofForLeaf2 H l0 l1 l3) (canonicalRoot H l0 l1 l2 l3) ∧
    verifyProof H l3 (proofForLeaf3 H l0 l1 l2) (canonicalRoot H l0 l1 l2 l3) :=
  ⟨merkle_proof_completeness_leaf0 H l0 l1 l2 l3,
   merkle_proof_completeness_leaf1 H l0 l1 l2 l3,
   merkle_proof_completeness_leaf2 H l0 l1 l2 l3,
   merkle_proof_completeness_leaf3 H l0 l1 l2 l3⟩

structure CryptoMerkleTreeFormalSuite : Prop where
  h_leaf0 : ∀ (H : ℝ → ℝ → ℝ) (l0 l1 l2 l3 : ℝ),
    verifyProof H l0 (proofForLeaf0 H l1 l2 l3) (canonicalRoot H l0 l1 l2 l3)
  h_leaf1 : ∀ (H : ℝ → ℝ → ℝ) (l0 l1 l2 l3 : ℝ),
    verifyProof H l1 (proofForLeaf1 H l0 l2 l3) (canonicalRoot H l0 l1 l2 l3)
  h_leaf2 : ∀ (H : ℝ → ℝ → ℝ) (l0 l1 l2 l3 : ℝ),
    verifyProof H l2 (proofForLeaf2 H l0 l1 l3) (canonicalRoot H l0 l1 l2 l3)
  h_leaf3 : ∀ (H : ℝ → ℝ → ℝ) (l0 l1 l2 l3 : ℝ),
    verifyProof H l3 (proofForLeaf3 H l0 l1 l2) (canonicalRoot H l0 l1 l2 l3)
  h_universal : ∀ (H : ℝ → ℝ → ℝ) (l0 l1 l2 l3 : ℝ),
    verifyProof H l0 (proofForLeaf0 H l1 l2 l3) (canonicalRoot H l0 l1 l2 l3) ∧
    verifyProof H l1 (proofForLeaf1 H l0 l2 l3) (canonicalRoot H l0 l1 l2 l3) ∧
    verifyProof H l2 (proofForLeaf2 H l0 l1 l3) (canonicalRoot H l0 l1 l2 l3) ∧
    verifyProof H l3 (proofForLeaf3 H l0 l1 l2) (canonicalRoot H l0 l1 l2 l3)

/-- Registry of completeness properties, not cryptographic soundness. -/
theorem crypto_merkle_tree_master_verification_suite : CryptoMerkleTreeFormalSuite := {
  h_leaf0 := merkle_proof_completeness_leaf0
  h_leaf1 := merkle_proof_completeness_leaf1
  h_leaf2 := merkle_proof_completeness_leaf2
  h_leaf3 := merkle_proof_completeness_leaf3
  h_universal := merkle_universal_leaf_inclusion
}

end CryptoMerkleTree
