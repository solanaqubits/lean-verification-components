import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false

namespace CryptoPedersenCommitment

/-- Scalar parameters, not an implementation of cryptographic group generators. -/
structure PedersenGenerators where
  G : ℝ
  H : ℝ
  hH_ne_zero : H ≠ 0

/-- Real scalar model of the additive commitment equation. -/
def commit (gen : PedersenGenerators) (m r : ℝ) : ℝ :=
  m * gen.G + r * gen.H

theorem pedersen_homomorphic_add (gen : PedersenGenerators) (m1 r1 m2 r2 : ℝ) :
    commit gen m1 r1 + commit gen m2 r2 = commit gen (m1 + m2) (r1 + r2) := by
  dsimp [commit]
  ring

theorem pedersen_homomorphic_smul (gen : PedersenGenerators) (k m r : ℝ) :
    k * commit gen m r = commit gen (k * m) (k * r) := by
  dsimp [commit]
  ring

/-- Algebraic change of opening. No distribution of randomness is specified,
so this is not a probabilistic perfect-hiding theorem. -/
theorem pedersen_perfect_hiding_equiv (gen : PedersenGenerators) (m1 m2 r1 : ℝ) :
    let r2 := r1 + (m1 - m2) * gen.G / gen.H
    commit gen m1 r1 = commit gen m2 r2 := by
  dsimp [commit]
  field_simp [gen.hH_ne_zero]
  ring

/-- A collision implies a scalar ratio identity. In this real model G/H is
already available; no discrete-log hardness or computational binding is proved. -/
theorem pedersen_binding_discrete_log (gen : PedersenGenerators) (m1 r1 m2 r2 : ℝ)
    (h_diff_m : m1 ≠ m2)
    (h_collision : commit gen m1 r1 = commit gen m2 r2) :
    gen.G = ((r2 - r1) / (m1 - m2)) * gen.H := by
  have h_sub_m : m1 - m2 ≠ 0 := sub_ne_zero.mpr h_diff_m
  have h_alg : (m1 - m2) * gen.G = (r2 - r1) * gen.H := by
    calc (m1 - m2) * gen.G
      _ = commit gen m1 r1 - commit gen m2 r1 := by dsimp [commit]; ring
      _ = commit gen m2 r2 - commit gen m2 r1 := by rw [h_collision]
      _ = (r2 - r1) * gen.H := by dsimp [commit]; ring
  calc gen.G
    _ = ((m1 - m2) * gen.G) / (m1 - m2) := (mul_div_cancel_left₀ gen.G h_sub_m).symm
    _ = ((r2 - r1) * gen.H) / (m1 - m2) := by rw [h_alg]
    _ = ((r2 - r1) / (m1 - m2)) * gen.H := by ring

/-- Two nonzero real parameters. Nonzeroness does not assert independence. -/
structure PedersenSetup where
  g : ℝ
  h : ℝ
  hg_ne : g ≠ 0
  hh_ne : h ≠ 0

/-- Compatibility with the existing, more general scalar commitment API. -/
def PedersenSetup.toGenerators (setup : PedersenSetup) : PedersenGenerators :=
  ⟨setup.g, setup.h, setup.hh_ne⟩

instance : Coe PedersenSetup PedersenGenerators := ⟨PedersenSetup.toGenerators⟩

theorem commit_homomorphic_add (setup : PedersenSetup) (m1 r1 m2 r2 : ℝ) :
    commit setup m1 r1 + commit setup m2 r2 = commit setup (m1 + m2) (r1 + r2) :=
  pedersen_homomorphic_add setup m1 r1 m2 r2

theorem commit_homomorphic_smul (setup : PedersenSetup) (k m r : ℝ) :
    k * commit setup m r = commit setup (k * m) (k * r) :=
  pedersen_homomorphic_smul setup k m r

/-- A compatible opening, not a probabilistic perfect-hiding statement. -/
theorem commit_perfect_hiding_witness (setup : PedersenSetup) (m1 r1 m2 : ℝ) :
    let r2 := r1 + (m1 - m2) * setup.g / setup.h
    commit setup m2 r2 = commit setup m1 r1 :=
  (pedersen_perfect_hiding_equiv setup m1 m2 r1).symm

/-- Scalar collision identity; no computational hardness is asserted. -/
theorem commit_binding_dlog_reduction (setup : PedersenSetup) (m1 r1 m2 r2 : ℝ)
    (h_coll : commit setup m1 r1 = commit setup m2 r2) (h_diff_m : m1 ≠ m2) :
    setup.g = ((r2 - r1) / (m1 - m2)) * setup.h :=
  pedersen_binding_discrete_log setup m1 r1 m2 r2 h_diff_m h_coll

/-- A supplied scalar relation, with no secrecy or hardness interpretation. -/
structure DLogRelation (setup : PedersenSetup) where
  x : ℝ
  hx_ne : x ≠ 0
  h_dlog : setup.h = x * setup.g

def addCommit (c1 c2 : ℝ) : ℝ := c1 + c2

def smulCommit (k c : ℝ) : ℝ := k * c

/-- Reverse orientation of the preserved additive theorem. -/
theorem commit_add_eq_addCommit (setup : PedersenSetup) (m1 r1 m2 r2 : ℝ) :
    commit setup (m1 + m2) (r1 + r2) = addCommit (commit setup m1 r1) (commit setup m2 r2) :=
  (commit_homomorphic_add setup m1 r1 m2 r2).symm

theorem commit_smul_eq_smulCommit (setup : PedersenSetup) (k m r : ℝ) :
    commit setup (k * m) (k * r) = smulCommit k (commit setup m r) :=
  (commit_homomorphic_smul setup k m r).symm

theorem commit_zero (setup : PedersenSetup) : commit setup 0 0 = 0 := by
  simp [commit]

/-- Explicit alternative opening via a supplied ratio; no distributions are modeled. -/
theorem pedersen_perfect_hiding
    (setup : PedersenSetup) (dlog : DLogRelation setup) (m r m' : ℝ) :
    let r' := r + (m - m') / dlog.x
    commit setup m' r' = commit setup m r := by
  dsimp [commit, PedersenSetup.toGenerators]
  rw [dlog.h_dlog]
  field_simp [dlog.hx_ne]
  ring

/-- The alternative blinding scalar is unique for a fixed target message. -/
theorem pedersen_hiding_unique
    (setup : PedersenSetup) (dlog : DLogRelation setup) (m r m' : ℝ) :
    ∃! r', commit setup m' r' = commit setup m r := by
  refine ⟨r + (m - m') / dlog.x, pedersen_perfect_hiding setup dlog m r m', ?_⟩
  intro t ht
  have hw := pedersen_perfect_hiding setup dlog m r m'
  dsimp [commit, PedersenSetup.toGenerators] at ht hw
  have heq : (t - (r + (m - m') / dlog.x)) * setup.h = 0 := by linarith
  rcases mul_eq_zero.mp heq with heq | heq
  · exact sub_eq_zero.mp heq
  · exact False.elim (setup.hh_ne heq)

noncomputable def extractDLog (m1 r1 m2 r2 : ℝ) : ℝ := (m1 - m2) / (r2 - r1)

theorem pedersen_collision_implies_blinding_diff
    (setup : PedersenSetup) (m1 r1 m2 r2 : ℝ)
    (h_eq : commit setup m1 r1 = commit setup m2 r2) (h_m_diff : m1 ≠ m2) :
    r2 - r1 ≠ 0 := by
  intro hr
  have hr' : r2 = r1 := sub_eq_zero.mp hr
  dsimp [commit, PedersenSetup.toGenerators] at h_eq
  rw [hr'] at h_eq
  have hprod : (m1 - m2) * setup.g = 0 := by linarith
  rcases mul_eq_zero.mp hprod with hm | hg
  · exact h_m_diff (sub_eq_zero.mp hm)
  · exact setup.hg_ne hg

/-- Extracts the real ratio H/G; no computational binding is asserted. -/
theorem pedersen_binding_extracts_dlog
    (setup : PedersenSetup) (m1 r1 m2 r2 : ℝ)
    (h_eq : commit setup m1 r1 = commit setup m2 r2) (h_m_diff : m1 ≠ m2) :
    let x := extractDLog m1 r1 m2 r2
    setup.h = x * setup.g := by
  have hr := pedersen_collision_implies_blinding_diff setup m1 r1 m2 r2 h_eq h_m_diff
  dsimp [commit, PedersenSetup.toGenerators] at h_eq
  have hprod : (r2 - r1) * setup.h = (m1 - m2) * setup.g := by linarith
  dsimp [extractDLog]
  calc setup.h
    _ = ((r2 - r1) * setup.h) / (r2 - r1) := (mul_div_cancel_left₀ setup.h hr).symm
    _ = ((m1 - m2) * setup.g) / (r2 - r1) := by rw [hprod]
    _ = ((m1 - m2) / (r2 - r1)) * setup.g := by ring

/-- Three nonzero real parameters, without a claim of generator independence. -/
structure VectorPedersenSetup where
  g1 : ℝ
  g2 : ℝ
  h : ℝ
  hg1_ne : g1 ≠ 0
  hg2_ne : g2 ≠ 0
  hh_ne : h ≠ 0

def commitVector (setup : VectorPedersenSetup) (m1 m2 r : ℝ) : ℝ :=
  m1 * setup.g1 + m2 * setup.g2 + r * setup.h

theorem vector_pedersen_homomorphic_add
    (setup : VectorPedersenSetup) (m1 m2 r1 n1 n2 r2 : ℝ) :
    commitVector setup (m1 + n1) (m2 + n2) (r1 + r2) =
      commitVector setup m1 m2 r1 + commitVector setup n1 n2 r2 := by
  dsimp [commitVector]
  ring

structure CryptoPedersenCommitmentFormalSuite : Prop where
  h_add_homo : ∀ (setup : PedersenSetup) (m1 r1 m2 r2 : ℝ),
    commit setup (m1 + m2) (r1 + r2) = addCommit (commit setup m1 r1) (commit setup m2 r2)
  h_smul_homo : ∀ (setup : PedersenSetup) (k m r : ℝ),
    commit setup (k * m) (k * r) = smulCommit k (commit setup m r)
  h_zero : ∀ setup : PedersenSetup, commit setup 0 0 = 0
  h_hiding : ∀ (setup : PedersenSetup) (dlog : DLogRelation setup) (m r m' : ℝ),
    commit setup m' (r + (m - m') / dlog.x) = commit setup m r
  h_hiding_unique : ∀ (setup : PedersenSetup) (_dlog : DLogRelation setup) (m r m' : ℝ),
    ∃! r', commit setup m' r' = commit setup m r
  h_blind_diff : ∀ (setup : PedersenSetup) (m1 r1 m2 r2 : ℝ),
    commit setup m1 r1 = commit setup m2 r2 → m1 ≠ m2 → r2 - r1 ≠ 0
  h_binding : ∀ (setup : PedersenSetup) (m1 r1 m2 r2 : ℝ),
    commit setup m1 r1 = commit setup m2 r2 → m1 ≠ m2 →
    setup.h = extractDLog m1 r1 m2 r2 * setup.g
  h_vec_add : ∀ (setup : VectorPedersenSetup) (m1 m2 r1 n1 n2 r2 : ℝ),
    commitVector setup (m1 + n1) (m2 + n2) (r1 + r2) =
      commitVector setup m1 m2 r1 + commitVector setup n1 n2 r2

theorem crypto_pedersen_commitment_master_suite : CryptoPedersenCommitmentFormalSuite := {
  h_add_homo := commit_add_eq_addCommit
  h_smul_homo := commit_smul_eq_smulCommit
  h_zero := commit_zero
  h_hiding := pedersen_perfect_hiding
  h_hiding_unique := pedersen_hiding_unique
  h_blind_diff := pedersen_collision_implies_blinding_diff
  h_binding := pedersen_binding_extracts_dlog
  h_vec_add := vector_pedersen_homomorphic_add
}

structure CryptoPedersenFormalSuite : Prop where
  h_extended : CryptoPedersenCommitmentFormalSuite
  h_add_homo : ∀ (gen : PedersenGenerators) (m1 r1 m2 r2 : ℝ),
    commit gen m1 r1 + commit gen m2 r2 = commit gen (m1 + m2) (r1 + r2)
  h_smul_homo : ∀ (gen : PedersenGenerators) (k m r : ℝ),
    k * commit gen m r = commit gen (k * m) (k * r)
  h_hiding : ∀ (gen : PedersenGenerators) (m1 m2 r1 : ℝ),
    let r2 := r1 + (m1 - m2) * gen.G / gen.H
    commit gen m1 r1 = commit gen m2 r2
  h_binding : ∀ (gen : PedersenGenerators) (m1 r1 m2 r2 : ℝ),
    m1 ≠ m2 → commit gen m1 r1 = commit gen m2 r2 →
    gen.G = ((r2 - r1) / (m1 - m2)) * gen.H

/-- Selected algebraic guarantees of the real scalar model. -/
theorem crypto_pedersen_master_verification_suite : CryptoPedersenFormalSuite := {
  h_extended := crypto_pedersen_commitment_master_suite
  h_add_homo := pedersen_homomorphic_add
  h_smul_homo := pedersen_homomorphic_smul
  h_hiding := pedersen_perfect_hiding_equiv
  h_binding := pedersen_binding_discrete_log
}

#print axioms crypto_pedersen_master_verification_suite

end CryptoPedersenCommitment
