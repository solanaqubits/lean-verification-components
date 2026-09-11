import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

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

theorem quantum_grover_master_verification_suite : QuantumGroverFormalSuite := {
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
