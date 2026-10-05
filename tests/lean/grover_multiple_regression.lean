import Verification.QuantumGroverMultipleTargets

noncomputable section
open QuantumGroverMultipleTargets

-- Compatibility is for arbitrary inputs, not just the initial uniform state.
example (t : QuantumGroverSearch.TargetItem) (v : State) :
    toLegacy (groverStep {itemIndex t} v) =
      QuantumGroverSearch.groverStep (QuantumGroverSearch.targetToBasis t) (toLegacy v) :=
  singleton_step_legacy t v

example (k : ℕ) : successWeight {0,2} (stateAt {0,2} k) = 1/2 :=
  grover_targets_M2_stationary _ (by decide) k

example (k : ℕ) : successWeight {1,3} (stateAt {1,3} k) = 1/2 :=
  grover_targets_M2_stationary _ (by decide) k

example (T : Finset (Fin 4)) (h : T.card=2) (k : ℕ) :
    successWeight T (stateAt T k) ≠ 1 := by
  rw [grover_targets_M2_stationary T h k]; norm_num

-- A three-target oracle drives the state to minus the only unmarked basis vector.
example : groverStep {0,1,3} uniform = ![0,0,-1,0] := by
  rw [M3_output _ (by decide)]
  funext i; fin_cases i <;> norm_num [twoLevel, Fin.ext_iff, Matrix.cons_val_two]

example (k : ℕ) : successWeight {0,2,3} (stateAt {0,2,3} k) =
    if k%3=1 then 0 else 3/4 := success_M3_all _ (by decide) k

example (k : ℕ) : successWeight {2} (stateAt {2} k) =
    if k%3=1 then 1 else 1/4 := success_M1_all _ (by decide) k

example : successWeight {2} (stateAt {2} 2) = 1/4 := by
  rw [success_M1_all _ (by decide)]; norm_num

example (k : ℕ) : successWeight ∅ (stateAt ∅ k) = 0 := success_M0_all k
example (k : ℕ) : successWeight Finset.univ (stateAt Finset.univ k) = 1 := success_M4_all k
example : stateAt Finset.univ 1 = -uniform := grover_targets_M4
example : stateAt Finset.univ 2 = uniform := by
  rw [stateAt_full]; funext i; norm_num

-- Arbitrary signed amplitudes retain their norm; normalization is not built into State.
example : normSquared (groverStep {0,2} ![1,-2,3,-4]) = 30 := by
  rw [grover_step_preserves_norm]
  norm_num [normSquared, inner, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]

example : successWeight {0,1} ![1,-1,0,0] = 2 := by
  norm_num [successWeight, Fin.ext_iff]

example : multiTargetOracle {0,1} ![1,-1,0,0] ≠ rankOneOracle {0,1} ![1,-1,0,0] :=
  rankOne_not_general

example : multiTargetOracle {0} ![0,1,-1,0] = rankOneOracle {0} ![0,1,-1,0] ∧
    ¬ InPlane {0} ![0,1,-1,0] := rankOne_agrees_outside_plane

example (a b c d : ℝ) (h : planeState {0,2} a b = planeState {0,2} c d) : a=c ∧ b=d :=
  plane_coordinates_unique _ (by decide) (by decide) a b c d h

example (k : ℕ) : InPlane {0,1,3} (stateAt {0,1,3} k) :=
  stateAt_in_plane _ (by decide) (by decide) k

example (a b : ℝ) : groverStep {0,2} (planeState {0,2} a b) =
    planeState {0,2} (rotationC {0,2}*a+rotationS {0,2}*b)
      (-rotationS {0,2}*a+rotationC {0,2}*b) :=
  plane_step _ (by decide) (by decide) a b

-- Endpoint subsets do not supply a normalized pair.
example : normSquared (marked ∅) = 0 := by
  norm_num [normSquared, inner, marked, twoLevel]
example : normSquared (unmarked Finset.univ) = 0 := by
  norm_num [normSquared, inner, unmarked, twoLevel]

example : QuantumGroverMultipleTargetsSuite := quantum_grover_multiple_targets_master_suite
