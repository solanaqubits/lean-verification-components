import Verification.QuantumDepolarizingChannel

open QuantumDepolarizingChannel
open scoped ComplexOrder Kronecker

example (M : Q) : depolarizingChannel 0 M = M := identity_channel M
example (M : Q) : depolarizingChannel (3/4) M = (M.trace/2) • (1:Q) :=
  complete_depolarization M
example (M : Q) : depolarizingChannel 1 M =
    (-1/3:ℂ) • M+(2/3:ℂ) • (M.trace • (1:Q)) := maximal_error_channel M
example : Physical (composeParameter 1 1) ∧ composeParameter 1 1 = 2/3 := by
  constructor
  · exact composition_physical 1 1 (by constructor <;> norm_num) (by constructor <;> norm_num)
  · norm_num [composeParameter]
example (M : Q) : depolarizingChannel 1 (depolarizingChannel 1 M) =
    depolarizingChannel (2/3) M := by
  rw [channel_composition 1 1 (by constructor <;> norm_num) (by constructor <;> norm_num)]
  norm_num [composeParameter]
example (d : ℕ) (p : ℝ) (R : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ)
    (hR : R.PosSemidef) : (extension d p R).PosSemidef := completely_positive d p R hR
example (d : ℕ) (p : ℝ) (hp : Physical p)
    (R : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) :
    (extension d p R).trace=R.trace := extension_trace_preserving d p hp R
example (p : ℝ) (hp : Physical p) :
    (noisySinglet p).PosSemidef ∧ (noisySinglet p).trace=1 :=
  ⟨singlet_positive p,singlet_trace p hp⟩
example : keyQBER 0 1 0 = 0 ∧ keyQBER (3/4) 1 0 = 1/2 ∧ keyQBER 1 1 0 = 2/3 := by
  refine ⟨?_,?_,?_⟩ <;>
    rw [e91_key_qber _ (by constructor <;> norm_num) 1 0
      (by simp [QuantumE91ProtocolBellCHSH.IsKey])] <;> norm_num
example : QuantumE91ProtocolBellCHSH.S (noisySinglet (3/4)) = 0 := by
  rw [(chsh_damping (3/4) (by constructor <;> norm_num)).1]
  norm_num [shrink]
example : shrink 1 < 0 := by norm_num [shrink]
example : withoutTrace 1 0 ≠ 0 := (counterexample_nonlinear_without_trace 1 (by norm_num)).2
example : ¬Physical (-1/4) := by norm_num [Physical]
example (p : ℝ) (hp : Physical p) :
    (noisyOutcomeLaw p hp 1 0).probability (fun ab =>
      QuantumE91ProtocolBellCHSH.sign ab.1 ≠ -QuantumE91ProtocolBellCHSH.sign ab.2) = 2*p/3 := by
  rw [qber_is_corrected_error,e91_key_qber p hp 1 0 (by simp [QuantumE91ProtocolBellCHSH.IsKey])]
example : QuantumDepolarizingChannelSuite := quantum_depolarizing_channel_master_suite
