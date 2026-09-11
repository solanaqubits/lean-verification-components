import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.style.header false
noncomputable section

namespace NonAbelianHolonomy

/-- A real matrix in explicit coordinates. -/
@[ext] structure Mat3 where
  a11 : ℝ
  a12 : ℝ
  a13 : ℝ
  a21 : ℝ
  a22 : ℝ
  a23 : ℝ
  a31 : ℝ
  a32 : ℝ
  a33 : ℝ

def zeroMat : Mat3 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def add (M N : Mat3) : Mat3 :=
  ⟨M.a11 + N.a11,
   M.a12 + N.a12,
   M.a13 + N.a13,
   M.a21 + N.a21,
   M.a22 + N.a22,
   M.a23 + N.a23,
   M.a31 + N.a31,
   M.a32 + N.a32,
   M.a33 + N.a33⟩

def sub (M N : Mat3) : Mat3 :=
  ⟨M.a11 - N.a11,
   M.a12 - N.a12,
   M.a13 - N.a13,
   M.a21 - N.a21,
   M.a22 - N.a22,
   M.a23 - N.a23,
   M.a31 - N.a31,
   M.a32 - N.a32,
   M.a33 - N.a33⟩

def smul (c : ℝ) (M : Mat3) : Mat3 :=
  ⟨c * M.a11, c * M.a12, c * M.a13,
   c * M.a21, c * M.a22, c * M.a23,
   c * M.a31, c * M.a32, c * M.a33⟩

def transpose (M : Mat3) : Mat3 :=
  ⟨M.a11, M.a21, M.a31, M.a12, M.a22, M.a32, M.a13, M.a23, M.a33⟩

def mul (M N : Mat3) : Mat3 :=
  ⟨M.a11 * N.a11 + M.a12 * N.a21 + M.a13 * N.a31,
   M.a11 * N.a12 + M.a12 * N.a22 + M.a13 * N.a32,
   M.a11 * N.a13 + M.a12 * N.a23 + M.a13 * N.a33,
   M.a21 * N.a11 + M.a22 * N.a21 + M.a23 * N.a31,
   M.a21 * N.a12 + M.a22 * N.a22 + M.a23 * N.a32,
   M.a21 * N.a13 + M.a22 * N.a23 + M.a23 * N.a33,
   M.a31 * N.a11 + M.a32 * N.a21 + M.a33 * N.a31,
   M.a31 * N.a12 + M.a32 * N.a22 + M.a33 * N.a32,
   M.a31 * N.a13 + M.a32 * N.a23 + M.a33 * N.a33⟩

def comm (M N : Mat3) : Mat3 := sub (mul M N) (mul N M)
def IsSkewSymmetric (M : Mat3) : Prop := transpose M = smul (-1) M

def Lx : Mat3 := ⟨0, 0, 0, 0, 0, -1, 0, 1, 0⟩
def Ly : Mat3 := ⟨0, 0, 1, 0, 0, 0, -1, 0, 0⟩
def Lz : Mat3 := ⟨0, -1, 0, 1, 0, 0, 0, 0, 0⟩

theorem Lx_skew : IsSkewSymmetric Lx := by
  unfold IsSkewSymmetric
  ext <;> dsimp [IsSkewSymmetric, transpose, smul, Lx] <;> ring

theorem Ly_skew : IsSkewSymmetric Ly := by
  unfold IsSkewSymmetric
  ext <;> dsimp [IsSkewSymmetric, transpose, smul, Ly] <;> ring

theorem Lz_skew : IsSkewSymmetric Lz := by
  unfold IsSkewSymmetric
  ext <;> dsimp [IsSkewSymmetric, transpose, smul, Lz] <;> ring

theorem transpose_comm (A B : Mat3) :
    transpose (comm A B) = comm (transpose B) (transpose A) := by
  ext <;> dsimp [transpose, comm, sub, mul] <;> ring

theorem comm_preserves_skew (A B : Mat3) (hA : IsSkewSymmetric A)
    (hB : IsSkewSymmetric B) : IsSkewSymmetric (comm A B) := by
  change transpose A = smul (-1) A at hA
  change transpose B = smul (-1) B at hB
  unfold IsSkewSymmetric
  rw [transpose_comm, hA, hB]
  ext <;> dsimp [comm, sub, mul, smul] <;> ring

/-- The commutator term only, without derivatives of a connection field. -/
def wilczekZeeCurvature (A1 A2 : Mat3) : Mat3 := comm A1 A2

theorem wilczek_zee_comm_xy : comm Lx Ly = Lz := by
  ext <;> dsimp [comm, sub, mul, Lx, Ly, Lz] <;> ring

theorem wilczek_zee_comm_yz : comm Ly Lz = Lx := by
  ext <;> dsimp [comm, sub, mul, Lx, Ly, Lz] <;> ring

theorem wilczek_zee_comm_zx : comm Lz Lx = Ly := by
  ext <;> dsimp [comm, sub, mul, Lx, Ly, Lz] <;> ring

/-- Explicit matrix noncommutativity; no parallel transport is constructed. -/
theorem wilczek_zee_non_abelian : comm Lx Ly ≠ zeroMat := by
  rw [wilczek_zee_comm_xy]
  intro h
  have he := congrArg Mat3.a21 h
  norm_num [Lz, zeroMat] at he

theorem jacobi_identity (A B C : Mat3) :
    add (add (comm (comm A B) C) (comm (comm B C) A)) (comm (comm C A) B) = zeroMat := by
  ext <;> dsimp [add, comm, sub, mul, zeroMat] <;> ring

structure NonAbelianHolonomyFormalSuite : Prop where
  h_Lx_skew : IsSkewSymmetric Lx
  h_Ly_skew : IsSkewSymmetric Ly
  h_Lz_skew : IsSkewSymmetric Lz
  h_comm_skew : ∀ A B, IsSkewSymmetric A → IsSkewSymmetric B → IsSkewSymmetric (comm A B)
  h_comm_xy : comm Lx Ly = Lz
  h_comm_yz : comm Ly Lz = Lx
  h_comm_zx : comm Lz Lx = Ly
  h_non_abelian : comm Lx Ly ≠ zeroMat
  h_jacobi : ∀ A B C,
    add (add (comm (comm A B) C) (comm (comm B C) A)) (comm (comm C A) B) = zeroMat

theorem non_abelian_holonomy_master_verification_suite : NonAbelianHolonomyFormalSuite := {
  h_Lx_skew := Lx_skew
  h_Ly_skew := Ly_skew
  h_Lz_skew := Lz_skew
  h_comm_skew := comm_preserves_skew
  h_comm_xy := wilczek_zee_comm_xy
  h_comm_yz := wilczek_zee_comm_yz
  h_comm_zx := wilczek_zee_comm_zx
  h_non_abelian := wilczek_zee_non_abelian
  h_jacobi := jacobi_identity
}

#print axioms non_abelian_holonomy_master_verification_suite

end NonAbelianHolonomy
