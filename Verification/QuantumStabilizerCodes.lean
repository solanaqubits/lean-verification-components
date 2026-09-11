import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum

set_option linter.style.header false

namespace QuantumStabilizerCodes

/-- Binary Pauli labels, with global phase omitted. -/
structure PauliOp where
  x : Bool
  z : Bool
  deriving DecidableEq, Repr

def pauliI : PauliOp := ⟨false, false⟩
def pauliX : PauliOp := ⟨true, false⟩
def pauliZ : PauliOp := ⟨false, true⟩
def pauliY : PauliOp := ⟨true, true⟩

def pauliMul (p1 p2 : PauliOp) : PauliOp :=
  ⟨p1.x != p2.x, p1.z != p2.z⟩

def symplecticProd1 (p1 p2 : PauliOp) : Bool :=
  (p1.x && p2.z) != (p1.z && p2.x)

theorem symplecticProd1_comm (p1 p2 : PauliOp) :
    symplecticProd1 p1 p2 = symplecticProd1 p2 p1 := by
  rcases p1 with ⟨x1, z1⟩
  rcases p2 with ⟨x2, z2⟩
  cases x1 <;> cases z1 <;> cases x2 <;> cases z2 <;> rfl

theorem symplecticProd1_identity (p : PauliOp) :
    symplecticProd1 pauliI p = false := by
  rcases p with ⟨x, z⟩
  cases x <;> cases z <;> rfl

theorem pauliMul_identity (p : PauliOp) : pauliMul pauliI p = p ∧ pauliMul p pauliI = p := by
  rcases p with ⟨x, z⟩
  cases x <;> cases z <;> decide

theorem x_z_anticommute : symplecticProd1 pauliX pauliZ = true := rfl

abbrev PauliString := List PauliOp

/-- List multiplication truncates to the shorter input. -/
def pauliNMul (p1 p2 : PauliString) : PauliString := List.zipWith pauliMul p1 p2

def symplecticProd (p1 p2 : PauliString) : Bool :=
  (List.zipWith symplecticProd1 p1 p2).foldl (fun acc b => acc != b) false

def pauliCommute (p1 p2 : PauliString) : Bool := !(symplecticProd p1 p2)

theorem symplecticProd_comm (p1 p2 : PauliString) :
    symplecticProd p1 p2 = symplecticProd p2 p1 := by
  dsimp [symplecticProd]
  have hz : List.zipWith symplecticProd1 p1 p2 = List.zipWith symplecticProd1 p2 p1 := by
    induction p1 generalizing p2 with
    | nil => cases p2 <;> rfl
    | cons a as ih =>
        cases p2 with
        | nil => rfl
        | cons b bs => simp only [List.zipWith_cons_cons, symplecticProd1_comm a b, ih bs]
  rw [hz]

theorem pauliCommute_comm (p1 p2 : PauliString) :
    pauliCommute p1 p2 = pauliCommute p2 p1 := by
  dsimp [pauliCommute]
  rw [symplecticProd_comm]

def syndrome (generators : List PauliString) (err : PauliString) : List Bool :=
  generators.map (fun s => symplecticProd s err)

/-- Pairwise commuting generators only; this predicate does not assert group closure. -/
def IsCommutingStabilizerGroup (generators : List PauliString) : Prop :=
  ∀ s1 s2, s1 ∈ generators → s2 ∈ generators → pauliCommute s1 s2 = true

theorem stabilizer_zero_syndrome (generators : List PauliString)
    (h_comm : IsCommutingStabilizerGroup generators) (s : PauliString) (hs : s ∈ generators) :
    ∀ check, check ∈ generators → symplecticProd check s = false := by
  intro check hc
  have hp := h_comm check s hc hs
  simpa [pauliCommute] using hp

def S1_3qubit : PauliString := [pauliZ, pauliZ, pauliI]
def S2_3qubit : PauliString := [pauliI, pauliZ, pauliZ]
def bitFlip3Generators : List PauliString := [S1_3qubit, S2_3qubit]
def errX1 : PauliString := [pauliX, pauliI, pauliI]
def errX2 : PauliString := [pauliI, pauliX, pauliI]
def errX3 : PauliString := [pauliI, pauliI, pauliX]
def errNone : PauliString := [pauliI, pauliI, pauliI]

theorem bitFlip3_generators_commute : pauliCommute S1_3qubit S2_3qubit = true := by decide

theorem bitFlip3_is_valid_stabilizer : IsCommutingStabilizerGroup bitFlip3Generators := by
  intro s1 s2 h1 h2
  simp only [bitFlip3Generators, List.mem_cons, List.not_mem_nil, or_false] at h1 h2
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> decide

theorem syndrome_errNone : syndrome bitFlip3Generators errNone = [false, false] := by decide
theorem syndrome_errX1 : syndrome bitFlip3Generators errX1 = [true, false] := by decide
theorem syndrome_errX2 : syndrome bitFlip3Generators errX2 = [true, true] := by decide
theorem syndrome_errX3 : syndrome bitFlip3Generators errX3 = [false, true] := by decide

/-- Distinct classical syndrome labels for the four specified error patterns. -/
theorem bitFlip3_syndromes_all_distinct :
    syndrome bitFlip3Generators errNone ≠ syndrome bitFlip3Generators errX1 ∧
    syndrome bitFlip3Generators errNone ≠ syndrome bitFlip3Generators errX2 ∧
    syndrome bitFlip3Generators errNone ≠ syndrome bitFlip3Generators errX3 ∧
    syndrome bitFlip3Generators errX1 ≠ syndrome bitFlip3Generators errX2 ∧
    syndrome bitFlip3Generators errX1 ≠ syndrome bitFlip3Generators errX3 ∧
    syndrome bitFlip3Generators errX2 ≠ syndrome bitFlip3Generators errX3 := by decide

structure QuantumStabilizerFormalSuite : Prop where
  h_symp1_comm : ∀ p1 p2, symplecticProd1 p1 p2 = symplecticProd1 p2 p1
  h_symp_comm : ∀ p1 p2, symplecticProd p1 p2 = symplecticProd p2 p1
  h_comm_comm : ∀ p1 p2, pauliCommute p1 p2 = pauliCommute p2 p1
  h_3q_commute : pauliCommute S1_3qubit S2_3qubit = true
  h_3q_group_valid : IsCommutingStabilizerGroup bitFlip3Generators
  h_3q_syn_distinct :
    syndrome bitFlip3Generators errNone ≠ syndrome bitFlip3Generators errX1 ∧
    syndrome bitFlip3Generators errNone ≠ syndrome bitFlip3Generators errX2 ∧
    syndrome bitFlip3Generators errNone ≠ syndrome bitFlip3Generators errX3 ∧
    syndrome bitFlip3Generators errX1 ≠ syndrome bitFlip3Generators errX2 ∧
    syndrome bitFlip3Generators errX1 ≠ syndrome bitFlip3Generators errX3 ∧
    syndrome bitFlip3Generators errX2 ≠ syndrome bitFlip3Generators errX3

theorem quantum_stabilizer_master_verification_suite : QuantumStabilizerFormalSuite := {
  h_symp1_comm := symplecticProd1_comm
  h_symp_comm := symplecticProd_comm
  h_comm_comm := pauliCommute_comm
  h_3q_commute := bitFlip3_generators_commute
  h_3q_group_valid := bitFlip3_is_valid_stabilizer
  h_3q_syn_distinct := bitFlip3_syndromes_all_distinct
}

#print axioms quantum_stabilizer_master_verification_suite

end QuantumStabilizerCodes
