import Verification.CryptoSchnorrBatchVerification
import Mathlib.Tactic.NormNum

open CryptoSchnorrBatchVerification

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

-- Exhaustive finite computations independently check a nonzero residual hyperplane.
example : Fintype.card {z : Fin 2 → ZMod 3 // batchCheck z ![1, 1]} = 3 := by decide

example : Fintype.card {z : Fin 2 → Fin 2 → ZMod 3 // roundsCheck z ![1, 1]} = 9 := by
  decide

-- Invalid individual equations can cancel with deterministic weights.
example : batchCheck (![1, 2] : Fin 2 → ZMod 3) ![1, 1] := by decide
example : ¬ batchCheck (![1, 1] : Fin 2 → ZMod 3) ![1, 1] := by decide

-- A singleton invalid equation accepts exactly the zero coefficient.
example : Fintype.card {z : Fin 1 → ZMod 3 // batchCheck z ![2]} = 1 := by decide

-- The nonzero-residual premise is essential: the zero vector accepts every input.
example : Fintype.card {z : Fin 2 → ZMod 3 // batchCheck z ![0, 0]} = 9 := by decide

example : falsePositiveFraction (![1, 1] : Fin 2 → ZMod 3) = 1 / 3 := by
  apply batch_verification_false_positive_prob
  exact ⟨0, by decide⟩

example : roundsFalsePositiveFraction (![1, 1] : Fin 2 → ZMod 3) 2 = 1 / 9 := by
  rw [batch_verification_k_rounds_bound _ ⟨0, by decide⟩]
  norm_num

-- Zero repetitions do not reject any batch.
example : roundsFalsePositiveFraction (![1, 1] : Fin 2 → ZMod 3) 0 = 1 := by
  rw [batch_verification_k_rounds_bound _ ⟨0, by decide⟩]
  norm_num

-- All individual scalar verification equations imply any weighted batch equation.
example (G : ZMod 3) (s R c pk z : Fin 4 → ZMod 3)
    (h : ∀ i, s i * G = R i + c i * pk i) :
    (∑ i, z i * s i) * G = (∑ i, z i * R i) + ∑ i, z i * c i * pk i := by
  apply (batch_discrepancy_iff G s R c pk z).mp
  apply batch_verification_completeness
  intro i
  exact (discrepancy_zero_iff G (s i) (R i) (c i) (pk i)).mpr (h i)
