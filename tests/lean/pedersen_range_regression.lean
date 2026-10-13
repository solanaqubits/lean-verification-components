import Verification.CryptoPedersenRangeProofLinear

open CryptoPedersenRangeProofLinear

instance : Fact (Nat.Prime 17) := ⟨by decide⟩
def rangeSetup : Setup 17 (ZMod 17) := CryptoPedersenHomomorphicSum.scalarSetup 3 (by decide)
def bits3 : Fin 3 → Bool := ![false, true, false]
def blinds3 : Fin 3 → ZMod 17 := ![2, 4, 5]
def coins3 : Fin 3 → Coins 17 := fun _ => (3, 7, 11)
def transcript3 (e : ZMod 17) := rangeHonest rangeSetup bits3 blinds3 e coins3
def commitment3 := commit rangeSetup 2 (blindSum blinds3)

example : CryptoPedersenRangeProofLinearSuite := verification_suite
example : bitValue (fun i => (bits3 i).toNat) = 2 := by decide
example : verify_range_proof rangeSetup commitment3 (transcript3 5) := by decide
example : SameFirst (transcript3 5) (transcript3 9) :=
  range_first_message_independent _ _ _ _ _ _
example : (extract_range_witness (transcript3 5) (transcript3 9)).1 = 2 := by decide
example : (extract_range_witness (transcript3 5) (transcript3 9)).2 = blindSum blinds3 := by
  have h := (range_proof_extract_witness rangeSetup commitment3 (transcript3 5) (transcript3 9)
    (range_first_message_independent _ _ _ _ _ _) (by decide) (by decide) (by decide)).2
  have hv : (extract_range_witness (transcript3 5) (transcript3 9)).1 = 2 := by decide
  rw [hv] at h
  exact (CryptoPedersenHomomorphicSum.commit_bijective rangeSetup 2).1 h.symm

example : ∃ b : Fin 1 → ℕ, (∀ i, b i ≤ 1) ∧ bitValue b = 0 :=
  (nat_bit_decomp_iff 1 0).mp (by decide)
example : ∃ b : Fin 1 → ℕ, (∀ i, b i ≤ 1) ∧ bitValue b = 1 :=
  (nat_bit_decomp_iff 1 1).mp (by decide)
example : ∃ b : Fin 3 → ℕ, (∀ i, b i ≤ 1) ∧ bitValue b = 7 :=
  (nat_bit_decomp_iff 3 7).mp (by decide)
example : ¬ ∃ b : Fin 3 → ℕ, (∀ i, b i ≤ 1) ∧ bitValue b = 8 :=
  upper_endpoint_no_decomposition 3
example : ¬ verify_range_proof rangeSetup (commitment3 + 1) (transcript3 5) := by decide
example : rangeRealLaw rangeSetup bits3 4 6 =
    rangeSimLaw rangeSetup (commit rangeSetup (bitValue (fun i => (bits3 i).toNat)) 4) 6 :=
  range_proof_hvzk_sim_eq_dist _ _ _ _
example : rangePublicSimulator (n := 2) rangeSetup commitment3 8 =
    rangeSimLaw rangeSetup commitment3 8 := public_simulator_eq _ _ _
example : rangeInteractionLaw rangeSetup bits3 4 (PMF.uniformOfFintype (ZMod 17)) =
    (PMF.uniformOfFintype (ZMod 17)).bind
      (rangePublicSimulator rangeSetup (commit rangeSetup (bitValue (fun i => (bits3 i).toNat)) 4)) :=
  range_hvzk_independent_challenge _ _ _ _
example : (2 : ℕ) = 2 := range_cast_injective (q := 17) (m := 3)
  (by decide) (by decide) (by decide) rfl
example : ∃ t : RangeProofTranscript 17 1 (ZMod 17),
    t.challenge = 4 ∧ verify_range_proof rangeSetup (commit rangeSetup 1 6) t :=
  range_completeness_for_opening _ _ (by decide) _ _ (fun _ => (0, 0, 0))
example : let t := orSim rangeSetup 0 0 (0, 0, 0)
    ORVerify rangeSetup 0 0 t ∧
      (0 : ZMod 17) ≠ commit rangeSetup (extractBit t t).1.toNat (extractBit t t).2 :=
  same_challenge_extractor_failure _
example : commit rangeSetup 2 4 = commit rangeSetup 3 15 := by decide
example : rangeSetup.g = (6 : ZMod 17) • rangeSetup.h := by
  have h := pedersen_binding_violation_extracts_dlog rangeSetup 2 4 3 15 (by decide) (by decide)
  norm_num at h
  exact h
example : commit rangeSetup 2 4 = commit rangeSetup 3 (4 + (2 - 3) * 6) :=
  known_relation_alternate_opening _ 6 2 4 3 (by decide)

#eval do
  let t := transcript3 5
  unless decide (verify_range_proof rangeSetup commitment3 t) do throw (IO.userError "honest")
  unless decide (¬ verify_range_proof rangeSetup (commitment3 + 1) t) do throw (IO.userError "aggregate")
  unless decide ((extract_range_witness t (transcript3 9)).1 = 2) do throw (IO.userError "extract bits")
  unless decide ((extract_range_witness t (transcript3 9)).2 = blindSum blinds3) do throw (IO.userError "extract blind")
  let bad := orSim rangeSetup 0 0 (0, 0, 0)
  unless decide ((0 : ZMod 17) ≠ commit rangeSetup (extractBit bad bad).1.toNat (extractBit bad bad).2) do
    throw (IO.userError "same challenge")
  unless decide (commit rangeSetup 2 4 = commit rangeSetup 3 15) do throw (IO.userError "alternate opening")
  let cs := commitmentTailEquiv (q := 17) (n := 2) commitment3 ![7, 9]
  unless decide (verify_range_proof rangeSetup commitment3 (rangeSim rangeSetup cs.val 6 coins3)) do
    throw (IO.userError "public simulator")
  let rs := openingTailEquiv (n := 2) (4 : ZMod 17) ![3, 5]
  unless decide (blindSum rs.val = 4) do throw (IO.userError "constrained blinds")
  IO.println "PEDERSEN_RANGE_EXEC_OK: 8 cases"
