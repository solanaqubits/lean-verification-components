import Mathlib.Data.Real.Basic
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

structure CryptoPedersenFormalSuite : Prop where
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
  h_add_homo := pedersen_homomorphic_add
  h_smul_homo := pedersen_homomorphic_smul
  h_hiding := pedersen_perfect_hiding_equiv
  h_binding := pedersen_binding_discrete_log
}

#print axioms crypto_pedersen_master_verification_suite

end CryptoPedersenCommitment
