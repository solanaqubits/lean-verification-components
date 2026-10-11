import Verification.QuantumE91ProtocolBellCHSH

open QuantumE91ProtocolBellCHSH
open scoped BigOperators

example : S rho_minus = -2 * Real.sqrt 2 := chsh_quantum_exact
example : |S rho_minus| = QuantumBellCHSH.tsirelsonBound := bridge_to_quantum_bell_chsh
example : ∀ i j, ∑ a, ∑ b, probability i j a b = 1 := probability_normalized
example (i j : Setting) : correlator i j = corrTable i j := correlator_table i j
example : qber 1 0 = 0 := key_qber_zero 1 0 (Or.inl ⟨rfl,rfl⟩)
example : qber 2 1 = 0 := key_qber_zero 2 1 (Or.inr ⟨rfl,rfl⟩)
example : ¬IsTest 1 0 := by norm_num [IsTest]
example (U V : Q) (hU : IsDensity U) (hV : IsDensity V) :
    (tensor U V).trace = 1 ∧ |S (tensor U V)| ≤ 2 := by
  refine ⟨?_,product_bound U V hU hV⟩
  rw [tensor_trace,hU.2,hV.2,mul_one]
example (x z : ℝ) (h : x^2+z^2=1) (tau : Outcome → Q) (ht : ∀ a, IsDensity (tau a)) :
    |S (interceptResend x z tau rho_minus)| ≤ 2 ∧
    (interceptResend x z tau rho_minus).trace = 1 :=
  ⟨(intercept_resend_forces_separable x z h tau ht).2.2,intercept_trace_one x z h tau ht⟩
example : S zAttack = -Real.sqrt 2 := z_attack_chsh
-- The raw key outcomes disagree; inversion is required.
example : probability 1 0 0 0 = 0 ∧ probability 1 0 0 1 = 1/2 := by
  norm_num [probability_exact,corrTable,sign]
-- Forgetting normalization is not a valid local hidden variable law.
example : ¬ ∃ L : QuantumBB84ProtocolQBER.FiniteLaw (Fin 1), L.weight 0 = 2 := by
  rintro ⟨L,h⟩
  have hn := L.normalized
  norm_num [Fin.sum_univ_succ,h] at hn
