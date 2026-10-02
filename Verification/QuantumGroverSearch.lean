import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.style.header false
noncomputable section

namespace QuantumGroverSearch

/-- Four real amplitudes; normalization is not built into the type. -/
@[ext] structure QState4 where
  x0 : ℝ
  x1 : ℝ
  x2 : ℝ
  x3 : ℝ

def dot (u v : QState4) : ℝ :=
  u.x0 * v.x0 + u.x1 * v.x1 + u.x2 * v.x2 + u.x3 * v.x3

def vadd (u v : QState4) : QState4 :=
  ⟨u.x0 + v.x0, u.x1 + v.x1, u.x2 + v.x2, u.x3 + v.x3⟩

def vsub (u v : QState4) : QState4 :=
  ⟨u.x0 - v.x0, u.x1 - v.x1, u.x2 - v.x2, u.x3 - v.x3⟩

def smul (c : ℝ) (v : QState4) : QState4 :=
  ⟨c * v.x0, c * v.x1, c * v.x2, c * v.x3⟩

def stateS : QState4 := ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩
def basis0 : QState4 := ⟨1, 0, 0, 0⟩
def basis1 : QState4 := ⟨0, 1, 0, 0⟩
def basis2 : QState4 := ⟨0, 0, 1, 0⟩
def basis3 : QState4 := ⟨0, 0, 0, 1⟩

theorem stateS_normalized : dot stateS stateS = 1 := by
  norm_num [dot, stateS]

/-- Phase-reflection formula; reflection interpretation requires a unit target. -/
def oracle (target v : QState4) : QState4 :=
  vsub v (smul (2 * dot target v) target)

def diffusion (v : QState4) : QState4 :=
  vsub (smul (2 * dot stateS v) stateS) v

def groverStep (target v : QState4) : QState4 := diffusion (oracle target v)

theorem grover_search_basis0 : groverStep basis0 stateS = basis0 := by
  ext <;> norm_num [groverStep, diffusion, oracle, stateS, basis0, vsub, smul, dot]

theorem grover_search_basis1 : groverStep basis1 stateS = basis1 := by
  ext <;> norm_num [groverStep, diffusion, oracle, stateS, basis1, vsub, smul, dot]

theorem grover_search_basis2 : groverStep basis2 stateS = basis2 := by
  ext <;> norm_num [groverStep, diffusion, oracle, stateS, basis2, vsub, smul, dot]

theorem grover_search_basis3 : groverStep basis3 stateS = basis3 := by
  ext <;> norm_num [groverStep, diffusion, oracle, stateS, basis3, vsub, smul, dot]

theorem grover_exact_quantum_search (target : QState4)
    (h_target : target = basis0 ∨ target = basis1 ∨ target = basis2 ∨ target = basis3) :
    groverStep target stateS = target := by
  rcases h_target with rfl | rfl | rfl | rfl
  · exact grover_search_basis0
  · exact grover_search_basis1
  · exact grover_search_basis2
  · exact grover_search_basis3

/-- This retained API states unit overlap amplitude. -/
theorem grover_success_probability_one (target : QState4)
    (h_target : target = basis0 ∨ target = basis1 ∨ target = basis2 ∨ target = basis3) :
    dot (groverStep target stateS) target = 1 := by
  rw [grover_exact_quantum_search target h_target]
  rcases h_target with rfl | rfl | rfl | rfl <;>
    norm_num [dot, basis0, basis1, basis2, basis3]

/-- Squared overlap for the normalized basis target in this real-amplitude model. -/
theorem grover_success_probability_sq_one (target : QState4)
    (h_target : target = basis0 ∨ target = basis1 ∨ target = basis2 ∨ target = basis3) :
    (dot (groverStep target stateS) target) ^ 2 = 1 := by
  rw [grover_success_probability_one target h_target, one_pow]

/-- Bit-labelled coordinate accessors preserving the original record fields. -/
abbrev QState4.x00 (v : QState4) : ℝ := v.x0
abbrev QState4.x01 (v : QState4) : ℝ := v.x1
abbrev QState4.x10 (v : QState4) : ℝ := v.x2
abbrev QState4.x11 (v : QState4) : ℝ := v.x3
abbrev basis00 := basis0
abbrev basis01 := basis1
abbrev basis10 := basis2
abbrev basis11 := basis3
abbrev uniformSuperposition := stateS

inductive TargetItem where
  | t00 | t01 | t10 | t11
  deriving DecidableEq, Repr

def targetToBasis (t : TargetItem) : QState4 :=
  match t with
  | .t00 => basis00
  | .t01 => basis01
  | .t10 => basis10
  | .t11 => basis11

def phaseOracle (t : TargetItem) (v : QState4) : QState4 :=
  match t with
  | .t00 => ⟨-v.x0, v.x1, v.x2, v.x3⟩
  | .t01 => ⟨v.x0, -v.x1, v.x2, v.x3⟩
  | .t10 => ⟨v.x0, v.x1, -v.x2, v.x3⟩
  | .t11 => ⟨v.x0, v.x1, v.x2, -v.x3⟩

theorem phase_oracle_eq_reflection (t : TargetItem) (v : QState4) :
    phaseOracle t v = oracle (targetToBasis t) v := by
  cases t <;> ext <;>
    simp [phaseOracle, oracle, targetToBasis, basis00, basis01, basis10, basis11,
      basis0, basis1, basis2, basis3, dot, vsub, smul] <;> ring

/-- The existing diffusion operator is inversion about the coordinate mean. -/
theorem diffusion_eq_mean (v : QState4) :
    diffusion v =
      let avg := (v.x0 + v.x1 + v.x2 + v.x3) / 4
      ⟨2 * avg - v.x0, 2 * avg - v.x1, 2 * avg - v.x2, 2 * avg - v.x3⟩ := by
  ext <;> dsimp [diffusion, vsub, smul, dot, stateS] <;> ring

def groverIteration (t : TargetItem) : QState4 :=
  diffusion (phaseOracle t uniformSuperposition)

theorem grover_universal_exactness (t : TargetItem) :
    groverIteration t = targetToBasis t := by
  unfold groverIteration
  rw [phase_oracle_eq_reflection]
  cases t
  · exact grover_search_basis0
  · exact grover_search_basis1
  · exact grover_search_basis2
  · exact grover_search_basis3

theorem grover_search_00 : groverIteration .t00 = basis00 := grover_universal_exactness .t00
theorem grover_search_01 : groverIteration .t01 = basis01 := grover_universal_exactness .t01
theorem grover_search_10 : groverIteration .t10 = basis10 := grover_universal_exactness .t10
theorem grover_search_11 : groverIteration .t11 = basis11 := grover_universal_exactness .t11

theorem grover_success_prob_one (t : TargetItem) :
    dot (groverIteration t) (targetToBasis t) = 1 := by
  rw [grover_universal_exactness]
  cases t <;> norm_num [targetToBasis, basis00, basis01, basis10, basis11,
    basis0, basis1, basis2, basis3, dot]

theorem grover_initial_norm : dot uniformSuperposition uniformSuperposition = 1 :=
  stateS_normalized

structure QuantumGroverFormalSuite : Prop where
  h_norm_s : dot stateS stateS = 1
  h_find_b0 : groverStep basis0 stateS = basis0
  h_find_b1 : groverStep basis1 stateS = basis1
  h_find_b2 : groverStep basis2 stateS = basis2
  h_find_b3 : groverStep basis3 stateS = basis3
  h_exact_find : ∀ target,
    (target = basis0 ∨ target = basis1 ∨ target = basis2 ∨ target = basis3) →
    groverStep target stateS = target
  h_prob_one : ∀ target,
    (target = basis0 ∨ target = basis1 ∨ target = basis2 ∨ target = basis3) →
    dot (groverStep target stateS) target = 1
  h_prob_sq_one : ∀ target,
    (target = basis0 ∨ target = basis1 ∨ target = basis2 ∨ target = basis3) →
    (dot (groverStep target stateS) target) ^ 2 = 1

  h_find_00 : groverIteration .t00 = basis00
  h_find_01 : groverIteration .t01 = basis01
  h_find_10 : groverIteration .t10 = basis10
  h_find_11 : groverIteration .t11 = basis11
  h_universal : ∀ t, groverIteration t = targetToBasis t
  h_target_prob_one : ∀ t, dot (groverIteration t) (targetToBasis t) = 1
  h_init_norm : dot uniformSuperposition uniformSuperposition = 1

theorem quantum_grover_master_verification_suite : QuantumGroverFormalSuite := {
  h_find_00 := grover_search_00
  h_find_01 := grover_search_01
  h_find_10 := grover_search_10
  h_find_11 := grover_search_11
  h_universal := grover_universal_exactness
  h_target_prob_one := grover_success_prob_one
  h_init_norm := grover_initial_norm
  h_norm_s := stateS_normalized
  h_find_b0 := grover_search_basis0
  h_find_b1 := grover_search_basis1
  h_find_b2 := grover_search_basis2
  h_find_b3 := grover_search_basis3
  h_exact_find := grover_exact_quantum_search
  h_prob_one := grover_success_probability_one
  h_prob_sq_one := grover_success_probability_sq_one
}

#print axioms quantum_grover_master_verification_suite

end QuantumGroverSearch
