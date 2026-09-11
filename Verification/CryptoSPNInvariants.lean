import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false

namespace CryptoSPNInvariants

/-- Four rational coordinates, not finite-field bytes. -/
@[ext] structure State4 where
  x0 : ℚ
  x1 : ℚ
  x2 : ℚ
  x3 : ℚ
  deriving DecidableEq, Repr

namespace State4

def zero : State4 := ⟨0, 0, 0, 0⟩
def add (a b : State4) : State4 :=
  ⟨a.x0 + b.x0, a.x1 + b.x1, a.x2 + b.x2, a.x3 + b.x3⟩
def smul (c : ℚ) (a : State4) : State4 :=
  ⟨c * a.x0, c * a.x1, c * a.x2, c * a.x3⟩

instance : Zero State4 := ⟨zero⟩
instance : Add State4 := ⟨add⟩
instance : SMul ℚ State4 := ⟨smul⟩

@[simp] theorem zero_x0 : (0 : State4).x0 = 0 := rfl

@[simp] theorem smul_x0 (c : ℚ) (a : State4) : (c • a).x0 = c * a.x0 := rfl

@[simp] theorem zero_x1 : (0 : State4).x1 = 0 := rfl

@[simp] theorem smul_x1 (c : ℚ) (a : State4) : (c • a).x1 = c * a.x1 := rfl

@[simp] theorem zero_x2 : (0 : State4).x2 = 0 := rfl

@[simp] theorem smul_x2 (c : ℚ) (a : State4) : (c • a).x2 = c * a.x2 := rfl

@[simp] theorem zero_x3 : (0 : State4).x3 = 0 := rfl

@[simp] theorem smul_x3 (c : ℚ) (a : State4) : (c • a).x3 = c * a.x3 := rfl

def nz (q : ℚ) : ℕ := if q = 0 then 0 else 1

/-- Count the nonzero rational coordinates. -/
def hammingWeight (s : State4) : ℕ :=
  nz s.x0 + nz s.x1 + nz s.x2 + nz s.x3

@[simp] theorem hammingWeight_zero : hammingWeight 0 = 0 := rfl

end State4

open State4

/-- The specified rational circulant diffusion, with right-shifted rows. -/
def diffLinear (s : State4) : State4 :=
  ⟨2 * s.x0 + 3 * s.x1 + s.x2 + s.x3,
   s.x0 + 2 * s.x1 + 3 * s.x2 + s.x3,
   s.x0 + s.x1 + 2 * s.x2 + 3 * s.x3,
   3 * s.x0 + s.x1 + s.x2 + 2 * s.x3⟩

/-- Inverse for this row convention: circ(-4, 3, -11, 17) / 35. -/
def diffLinearInv (s : State4) : State4 :=
  ⟨(-4 / 35) * s.x0 + (3 / 35) * s.x1 + (-11 / 35) * s.x2 + (17 / 35) * s.x3,
   (17 / 35) * s.x0 + (-4 / 35) * s.x1 + (3 / 35) * s.x2 + (-11 / 35) * s.x3,
   (-11 / 35) * s.x0 + (17 / 35) * s.x1 + (-4 / 35) * s.x2 + (3 / 35) * s.x3,
   (3 / 35) * s.x0 + (-11 / 35) * s.x1 + (17 / 35) * s.x2 + (-4 / 35) * s.x3⟩

theorem diffLinear_inv_right (s : State4) : diffLinear (diffLinearInv s) = s := by
  ext <;> dsimp [diffLinear, diffLinearInv] <;> ring

theorem diffLinear_inv_left (s : State4) : diffLinearInv (diffLinear s) = s := by
  ext <;> dsimp [diffLinear, diffLinearInv] <;> ring

theorem diffLinear_bijective : Function.Bijective diffLinear :=
  ⟨Function.LeftInverse.injective diffLinear_inv_left,
   Function.RightInverse.surjective diffLinear_inv_right⟩

/-- Only coordinate 0 is active. -/
def IsActiveByte0 (s : State4) : Prop :=
  s.x0 ≠ 0 ∧ s.x1 = 0 ∧ s.x2 = 0 ∧ s.x3 = 0

theorem active_byte0_full_diffusion (s : State4) (h : IsActiveByte0 s) :
    hammingWeight (diffLinear s) = 4 := by
  rcases h with ⟨h0, h1, h2, h3⟩
  simp [diffLinear, hammingWeight, nz, h0, h1, h2, h3]

theorem branch_number_active_byte0 (s : State4) (h : IsActiveByte0 s) :
    hammingWeight s + hammingWeight (diffLinear s) = 5 := by
  rw [active_byte0_full_diffusion s h]
  rcases h with ⟨h0, h1, h2, h3⟩
  simp [hammingWeight, nz, h0, h1, h2, h3]

/-- Only coordinate 1 is active. -/
def IsActiveByte1 (s : State4) : Prop :=
  s.x0 = 0 ∧ s.x1 ≠ 0 ∧ s.x2 = 0 ∧ s.x3 = 0

theorem active_byte1_full_diffusion (s : State4) (h : IsActiveByte1 s) :
    hammingWeight (diffLinear s) = 4 := by
  rcases h with ⟨h0, h1, h2, h3⟩
  simp [diffLinear, hammingWeight, nz, h0, h1, h2, h3]

theorem branch_number_active_byte1 (s : State4) (h : IsActiveByte1 s) :
    hammingWeight s + hammingWeight (diffLinear s) = 5 := by
  rw [active_byte1_full_diffusion s h]
  rcases h with ⟨h0, h1, h2, h3⟩
  simp [hammingWeight, nz, h0, h1, h2, h3]

/-- Only coordinate 2 is active. -/
def IsActiveByte2 (s : State4) : Prop :=
  s.x0 = 0 ∧ s.x1 = 0 ∧ s.x2 ≠ 0 ∧ s.x3 = 0

theorem active_byte2_full_diffusion (s : State4) (h : IsActiveByte2 s) :
    hammingWeight (diffLinear s) = 4 := by
  rcases h with ⟨h0, h1, h2, h3⟩
  simp [diffLinear, hammingWeight, nz, h0, h1, h2, h3]

theorem branch_number_active_byte2 (s : State4) (h : IsActiveByte2 s) :
    hammingWeight s + hammingWeight (diffLinear s) = 5 := by
  rw [active_byte2_full_diffusion s h]
  rcases h with ⟨h0, h1, h2, h3⟩
  simp [hammingWeight, nz, h0, h1, h2, h3]

/-- Only coordinate 3 is active. -/
def IsActiveByte3 (s : State4) : Prop :=
  s.x0 = 0 ∧ s.x1 = 0 ∧ s.x2 = 0 ∧ s.x3 ≠ 0

theorem active_byte3_full_diffusion (s : State4) (h : IsActiveByte3 s) :
    hammingWeight (diffLinear s) = 4 := by
  rcases h with ⟨h0, h1, h2, h3⟩
  simp [diffLinear, hammingWeight, nz, h0, h1, h2, h3]

theorem branch_number_active_byte3 (s : State4) (h : IsActiveByte3 s) :
    hammingWeight s + hammingWeight (diffLinear s) = 5 := by
  rw [active_byte3_full_diffusion s h]
  rcases h with ⟨h0, h1, h2, h3⟩
  simp [hammingWeight, nz, h0, h1, h2, h3]

/-- Classification of states with exactly one nonzero coordinate. -/
theorem weight_one_cases (s : State4) (h : hammingWeight s = 1) :
    IsActiveByte0 s ∨ IsActiveByte1 s ∨ IsActiveByte2 s ∨ IsActiveByte3 s := by
  unfold hammingWeight nz at h
  by_cases h0 : s.x0 = 0 <;> by_cases h1 : s.x1 = 0 <;>
    by_cases h2 : s.x2 = 0 <;> by_cases h3 : s.x3 = 0 <;>
    simp_all [IsActiveByte0, IsActiveByte1, IsActiveByte2, IsActiveByte3]

theorem weight_one_full_diffusion (s : State4) (h : hammingWeight s = 1) :
    hammingWeight (diffLinear s) = 4 := by
  rcases weight_one_cases s h with h0 | h1 | h2 | h3
  · exact active_byte0_full_diffusion s h0
  · exact active_byte1_full_diffusion s h1
  · exact active_byte2_full_diffusion s h2
  · exact active_byte3_full_diffusion s h3

/-- The input/output weight sum for weight-one inputs, not a global branch-number theorem. -/
theorem branch_number_weight_one (s : State4) (h : hammingWeight s = 1) :
    hammingWeight s + hammingWeight (diffLinear s) = 5 := by
  rw [h, weight_one_full_diffusion s h]

/-- A nonzero vector on any coordinate axis is sent outside that axis. -/
theorem weight_one_not_eigenvector (s : State4) (h : hammingWeight s = 1) (c : ℚ) :
    diffLinear s ≠ c • s := by
  have hd := weight_one_full_diffusion s h
  have hs : hammingWeight (c • s) ≤ 1 := by
    rcases weight_one_cases s h with hs | hs | hs | hs <;>
      rcases hs with ⟨h0, h1, h2, h3⟩ <;>
      simp [hammingWeight, nz, h0, h1, h2, h3] <;> split <;> omega
  intro he
  rw [he] at hd
  omega

set_option maxHeartbeats 2000000 in
-- The eight zero/nonzero tests generate up to 256 support cases for linear arithmetic.
/-- Global input/output weight bound for every nonzero rational state. -/
theorem branch_number_ge_five (s : State4) (hs : s ≠ 0) :
    5 ≤ hammingWeight s + hammingWeight (diffLinear s) := by
  by_contra hw
  unfold hammingWeight nz at hw
  split_ifs at hw <;> norm_num at hw
  all_goals
    apply hs
    ext <;> dsimp [diffLinear] at * <;> linarith

/-- Coordinatewise application of an arbitrary rational function. -/
def applySubBytes (S : ℚ → ℚ) (s : State4) : State4 :=
  ⟨S s.x0, S s.x1, S s.x2, S s.x3⟩

def spnRound (S : ℚ → ℚ) (s : State4) : State4 :=
  diffLinear (applySubBytes S s)

theorem spn_round_bijective (S S_inv : ℚ → ℚ)
    (h_left : Function.LeftInverse S_inv S)
    (h_right : Function.RightInverse S_inv S) :
    Function.Bijective (spnRound S) := by
  have hl : Function.LeftInverse (applySubBytes S_inv) (applySubBytes S) := by
    intro s
    ext <;> exact h_left _
  have hr : Function.RightInverse (applySubBytes S_inv) (applySubBytes S) := by
    intro s
    ext <;> exact h_right _
  exact diffLinear_bijective.comp ⟨hl.injective, hr.surjective⟩

/-- Injectivity and preservation of zero ensure preservation of coordinate activity. -/
theorem subBytes_weight (S : ℚ → ℚ) (hS : Function.Injective S) (h0 : S 0 = 0)
    (s : State4) : hammingWeight (applySubBytes S s) = hammingWeight s := by
  have hz (q : ℚ) : S q = 0 ↔ q = 0 := by
    simpa only [h0] using (hS.eq_iff : S q = S 0 ↔ q = 0)
  simp [hammingWeight, nz, applySubBytes, hz]

theorem spn_weight_one_full_diffusion (S : ℚ → ℚ)
    (hS : Function.Injective S) (h0 : S 0 = 0) (s : State4)
    (hs : hammingWeight s = 1) : hammingWeight (spnRound S s) = 4 := by
  apply weight_one_full_diffusion
  rw [subBytes_weight S hS h0, hs]

/-- Algebraic guarantees over rationals; no finite-field cipher security claim. -/
structure CryptoSPNFormalSuite : Prop where
  h_invertible : ∀ s : State4, diffLinear (diffLinearInv s) = s ∧ diffLinearInv (diffLinear s) = s
  h_global_branch : ∀ s : State4, s ≠ 0 → 5 ≤ hammingWeight s + hammingWeight (diffLinear s)
  h_bijective : Function.Bijective diffLinear
  h_diffusion : ∀ s : State4, IsActiveByte0 s → hammingWeight (diffLinear s) = 4
  h_branch5 : ∀ s : State4, IsActiveByte0 s → hammingWeight s + hammingWeight (diffLinear s) = 5
  h_all_single : ∀ s : State4, hammingWeight s = 1 → hammingWeight (diffLinear s) = 4
  h_spn_bij : ∀ (S S_inv : ℚ → ℚ),
    Function.LeftInverse S_inv S → Function.RightInverse S_inv S →
    Function.Bijective (spnRound S)

theorem crypto_spn_master_verification_suite : CryptoSPNFormalSuite := {
  h_invertible := fun s => ⟨diffLinear_inv_right s, diffLinear_inv_left s⟩
  h_global_branch := branch_number_ge_five
  h_bijective := diffLinear_bijective
  h_diffusion := active_byte0_full_diffusion
  h_branch5 := branch_number_active_byte0
  h_all_single := weight_one_full_diffusion
  h_spn_bij := spn_round_bijective
}

#print axioms crypto_spn_master_verification_suite
#print axioms weight_one_not_eigenvector
#print axioms spn_weight_one_full_diffusion

end CryptoSPNInvariants
