/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# CryptoKZGPolynomialCommitment

Algebraic and conditional invariants; see the theorem hypotheses and knowledge card for scope.
-/

noncomputable section
namespace CryptoKZGPolynomialCommitment

/-! Quadratic scalar KZG identities. The setup exposes tau; no security game or SRS ceremony. -/
structure Poly2 where
  a : ℝ
  b : ℝ
  c : ℝ

def evalPoly (p : Poly2) (x : ℝ) : ℝ := p.a * x ^ 2 + p.b * x + p.c

structure KZGSetup where
  g1 : ℝ
  g2 : ℝ
  tau : ℝ
  hg1_ne : g1 ≠ 0
  hg2_ne : g2 ≠ 0

def commit (setup : KZGSetup) (p : Poly2) : ℝ := evalPoly p setup.tau * setup.g1
/-- Scalar multiplication models only the pairing identity. -/
def pairing (P Q : ℝ) : ℝ := P * Q
/-- Polynomial quotient, defined also at X = z without division. -/
def quotientPoly (p : Poly2) (z : ℝ) : Poly2 := ⟨0, p.a, p.a * z + p.b⟩
def openProof (setup : KZGSetup) (p : Poly2) (z : ℝ) : ℝ :=
  evalPoly (quotientPoly p z) setup.tau * setup.g1

def verifyKZG (setup : KZGSetup) (C v z proof : ℝ) : Prop :=
  pairing (C - v * setup.g1) setup.g2 = pairing proof ((setup.tau - z) * setup.g2)

theorem poly_eval_sub_factor (p : Poly2) (X z : ℝ) :
    (X - z) * evalPoly (quotientPoly p z) X = evalPoly p X - evalPoly p z := by
  dsimp [evalPoly, quotientPoly]
  ring

theorem kzg_opening_completeness (setup : KZGSetup) (p : Poly2) (z : ℝ) :
    let C := commit setup p
    let v := evalPoly p z
    let π := openProof setup p z
    verifyKZG setup C v z π := by
  dsimp [verifyKZG, pairing, commit, openProof]
  rw [show evalPoly p setup.tau * setup.g1 - evalPoly p z * setup.g1 =
    (evalPoly p setup.tau - evalPoly p z) * setup.g1 by ring]
  rw [← poly_eval_sub_factor p setup.tau z]
  ring

def addPoly (p1 p2 : Poly2) : Poly2 := ⟨p1.a + p2.a, p1.b + p2.b, p1.c + p2.c⟩

theorem kzg_commit_homomorphic_add (setup : KZGSetup) (p1 p2 : Poly2) :
    commit setup (addPoly p1 p2) = commit setup p1 + commit setup p2 := by
  dsimp [commit, evalPoly, addPoly]
  ring

structure CryptoKZGFormalSuite : Prop where
  h_poly_factor : ∀ (p : Poly2) (X z : ℝ),
    (X - z) * evalPoly (quotientPoly p z) X = evalPoly p X - evalPoly p z
  h_complete : ∀ (setup : KZGSetup) (p : Poly2) (z : ℝ),
    verifyKZG setup (commit setup p) (evalPoly p z) z (openProof setup p z)
  h_commit_add : ∀ (setup : KZGSetup) (p1 p2 : Poly2),
    commit setup (addPoly p1 p2) = commit setup p1 + commit setup p2

theorem crypto_kzg_master_verification_suite : CryptoKZGFormalSuite := {
  h_poly_factor := poly_eval_sub_factor
  h_complete := kzg_opening_completeness
  h_commit_add := kzg_commit_homomorphic_add
}

end CryptoKZGPolynomialCommitment
