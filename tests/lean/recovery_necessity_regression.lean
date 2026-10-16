import Verification.QuantumKnillLaflammeRecoveryNecessity

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract QuantumHelstromStateDiscrimination
open QuantumKnillLaflammeEnvironmentCriterion QuantumKnillLaflammeGeneralRecoveryTheorem
open QuantumKnillLaflammeRecoveryNecessity
namespace RecoveryNecessityRegression
abbrev C := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.complexCode
abbrev E := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.complexChannel
abbrev J := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.logicalCode
abbrev R := generalRecovery C
abbrev Z := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.zeroCode
abbrev EZ := QuantumOrthogonalErrorRecoveryContract.Examples.sectorChannel
abbrev D := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.repeatedCode
abbrev ED := QuantumUnitaryKrausDiagonalizationRecoveryContract.Examples.repeatedChannel
abbrev T := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.rectangularCode
abbrev ET := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.rectangularChannel

example : ExactRecovery E J R := general_recovery_theorem C
example : Recoverable E J := ⟨6, R, general_recovery_theorem C⟩
example (μ : Fin 6) (a : Fin 2) :
    R.operators μ * E.operators a * J = compositeCoefficient (by decide) E J R μ a • (1 : Q 2) :=
  lemma_composite_scalar (by decide) E J R (general_recovery_theorem C) μ a
example : StandardKnillLaflamme E J (recoveredCoefficients (by decide) E J R) :=
  knill_laflamme_necessity (by decide) E J R (general_recovery_theorem C)
example : recoveredCoefficients (by decide) E J R = C.coefficients :=
  recovered_coefficients_unique (by decide) E J R (general_recovery_theorem C) _ C.knill_laflamme
example : (recoveredCoefficients (by decide) E J R 0 1).im = 84/625 := by
  rw [recovered_coefficients_unique (by decide) E J R (general_recovery_theorem C)
    _ C.knill_laflamme]
  norm_num [C, Examples.complexCode]
example : (recoveredCoefficients (by decide) E J R 1 0).im = -84/625 := by
  rw [recovered_coefficients_unique (by decide) E J R (general_recovery_theorem C)
    _ C.knill_laflamme]
  norm_num [C, Examples.complexCode]
example : recoveredCoefficients (by decide) E J R 0 1 =
    ∑ μ, star (compositeCoefficient (by decide) E J R μ 0) *
      compositeCoefficient (by decide) E J R μ 1 := rfl
example : ∃ σ : Q 2, Density σ ∧ EnvironmentConstant E J σ :=
  (recovery_environment_density_equivalence (by decide) E J C.isometry).mp
    ⟨6, R, general_recovery_theorem C⟩
example : EnvironmentConstant E J C.coefficients.transpose :=
  (knill_laflamme_equiv_environment _ _ _).mp ((standard_iff_transpose _ _ _).mp C.knill_laflamme)
example : apply_channel R (apply_channel E (encode J (Matrix.single 0 1 Complex.I))) =
    Matrix.single 0 1 Complex.I := general_recovery_theorem C _
example : apply_channel R (apply_channel E (encode J (Matrix.single 1 0 (2+Complex.I)))) =
    Matrix.single 1 0 (2+Complex.I) := general_recovery_theorem C _
example {s : ℕ} (R' : KrausChannel 4 2 s) (h : ExactRecovery E J R') :
    recoveredCoefficients (by decide) E J R' = C.coefficients :=
  recovered_coefficients_unique (by decide) E J R' h _ C.knill_laflamme
example {s : ℕ} (R' : KrausChannel 4 2 s) (h : ExactRecovery E J R') (μ : Fin s) (a : Fin 2) :
    compositeOperator E J R' μ a = compositeCoefficient (by decide) E J R' μ a • (1 : Q 2) :=
  lemma_composite_scalar (by decide) E J R' h μ a
example : Recoverable EZ J := ⟨6, generalRecovery Z, general_recovery_theorem Z⟩
example : recoveredCoefficients (by decide) EZ J (generalRecovery Z) = Matrix.diagonal ![1, 0] :=
  recovered_coefficients_unique (by decide) EZ J _ (general_recovery_theorem Z) _ Z.knill_laflamme
example : apply_channel (generalRecovery Z)
    (apply_channel EZ (encode J (Matrix.single 0 1 Complex.I))) = Matrix.single 0 1 Complex.I :=
  general_recovery_theorem Z _
example : Recoverable ED J := ⟨7, generalRecovery D, general_recovery_theorem D⟩
example : recoveredCoefficients (by decide) ED J (generalRecovery D) =
    Matrix.diagonal ![1/2, 1/2, 0] :=
  recovered_coefficients_unique (by decide) ED J _ (general_recovery_theorem D) _ D.knill_laflamme
example : apply_channel (generalRecovery D)
    (apply_channel ED (encode J (Matrix.single 1 0 Complex.I))) = Matrix.single 1 0 Complex.I :=
  general_recovery_theorem D _
example : Recoverable ET (1 : Q 2) := ⟨5, generalRecovery T, general_recovery_theorem T⟩
example : recoveredCoefficients (by decide) ET (1 : Q 2) (generalRecovery T) = 1 :=
  recovered_coefficients_unique (by decide) ET _ _ (general_recovery_theorem T) _ T.knill_laflamme
example (X : Q 2) : apply_channel (generalRecovery T) (apply_channel ET X) = X :=
  Examples.rectangular_recovery X
example : ∑ μ, ((generalRecovery T).operators μ).conjTranspose *
    (generalRecovery T).operators μ = (1 : Q 4) := (generalRecovery T).complete
example : ¬ Recoverable (dephasing_channel 2) (1 : Q 2) := dephasing_not_recoverable
example {s : ℕ} (R' : KrausChannel 2 2 s) :
    ¬ ExactRecovery (dephasing_channel 2) (1 : Q 2) R' := by
  intro h; exact dephasing_not_recoverable ⟨s, R', h⟩
example : ¬ ∃ Λ : Q 2, StandardKnillLaflamme (dephasing_channel 2) (1 : Q 2) Λ := by
  intro h
  exact dephasing_not_recoverable
    ((recovery_necessity_equivalence (by decide) _ _ (by simp)).mpr h)
example : ¬ ∃ σ : Q 2, Density σ ∧ EnvironmentConstant (dephasing_channel 2) (1 : Q 2) σ := by
  intro h
  exact dephasing_not_recoverable
    ((recovery_environment_density_equivalence (by decide) _ _ (by simp)).mpr h)
example (n : ℕ) : Recoverable (identity_channel (n+1)) (1 : Q (n+1)) := by
  refine ⟨1, identity_channel (n+1), ?_⟩
  intro X; simp [encode]
example : QuantumKnillLaflammeRecoveryNecessitySuite := verification_suite
end RecoveryNecessityRegression
