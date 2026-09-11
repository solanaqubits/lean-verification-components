import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.style.header false
noncomputable section

namespace QuantumMajoranaChain

open Complex

@[ext] structure CMat2 where
  a11 : ℂ
  a12 : ℂ
  a21 : ℂ
  a22 : ℂ

def matZero : CMat2 := ⟨0, 0, 0, 0⟩
def matI : CMat2 := ⟨1, 0, 0, 1⟩
def cadd (A B : CMat2) : CMat2 :=
  ⟨A.a11 + B.a11, A.a12 + B.a12, A.a21 + B.a21, A.a22 + B.a22⟩
def csub (A B : CMat2) : CMat2 :=
  ⟨A.a11 - B.a11, A.a12 - B.a12, A.a21 - B.a21, A.a22 - B.a22⟩
def csmul (z : ℂ) (A : CMat2) : CMat2 :=
  ⟨z * A.a11, z * A.a12, z * A.a21, z * A.a22⟩
def cmul (A B : CMat2) : CMat2 :=
  ⟨A.a11 * B.a11 + A.a12 * B.a21, A.a11 * B.a12 + A.a12 * B.a22,
   A.a21 * B.a11 + A.a22 * B.a21, A.a21 * B.a12 + A.a22 * B.a22⟩
def anticomm (A B : CMat2) : CMat2 := cadd (cmul A B) (cmul B A)
def comm (A B : CMat2) : CMat2 := csub (cmul A B) (cmul B A)
def cadjoint (A : CMat2) : CMat2 := ⟨star A.a11, star A.a21, star A.a12, star A.a22⟩
def sigmaX : CMat2 := ⟨0, 1, 1, 0⟩
def sigmaY : CMat2 := ⟨0, -I, I, 0⟩
def sigmaZ : CMat2 := ⟨1, 0, 0, -1⟩
def gamma1 : CMat2 := sigmaX
def gamma2 : CMat2 := sigmaY

def diracC : CMat2 := csmul (1 / 2 : ℂ) (cadd gamma1 (csmul I gamma2))
def diracCDag : CMat2 := csmul (1 / 2 : ℂ) (csub gamma1 (csmul I gamma2))
def numberOp : CMat2 := cmul diracCDag diracC
def parityOp : CMat2 := csub matI (csmul 2 numberOp)

theorem gamma1_self_adjoint : cadjoint gamma1 = gamma1 := by
  ext <;> norm_num [cadjoint, gamma1, gamma2, sigmaX, sigmaY, sigmaZ, cmul,
    cadd, csub, csmul, anticomm, comm, matI, matZero, diracC, diracCDag, numberOp, parityOp]

theorem gamma2_self_adjoint : cadjoint gamma2 = gamma2 := by
  ext <;> norm_num [cadjoint, gamma1, gamma2, sigmaX, sigmaY, sigmaZ, cmul,
    cadd, csub, csmul, anticomm, comm, matI, matZero, diracC, diracCDag, numberOp, parityOp]

theorem gamma1_sq_identity : cmul gamma1 gamma1 = matI := by
  ext <;> norm_num [cadjoint, gamma1, gamma2, sigmaX, sigmaY, sigmaZ, cmul,
    cadd, csub, csmul, anticomm, comm, matI, matZero, diracC, diracCDag, numberOp, parityOp]

theorem gamma2_sq_identity : cmul gamma2 gamma2 = matI := by
  ext <;> norm_num [cadjoint, gamma1, gamma2, sigmaX, sigmaY, sigmaZ, cmul,
    cadd, csub, csmul, anticomm, comm, matI, matZero, diracC, diracCDag, numberOp, parityOp]

theorem majorana_anticommute : anticomm gamma1 gamma2 = matZero := by
  ext <;> norm_num [cadjoint, gamma1, gamma2, sigmaX, sigmaY, sigmaZ, cmul,
    cadd, csub, csmul, anticomm, comm, matI, matZero, diracC, diracCDag, numberOp, parityOp]

theorem diracC_matrix_form : diracC = ⟨0, 1, 0, 0⟩ := by
  ext <;> norm_num [cadjoint, gamma1, gamma2, sigmaX, sigmaY, sigmaZ, cmul,
    cadd, csub, csmul, anticomm, comm, matI, matZero, diracC, diracCDag, numberOp, parityOp]

theorem diracCDag_matrix_form : diracCDag = ⟨0, 0, 1, 0⟩ := by
  ext <;> norm_num [cadjoint, gamma1, gamma2, sigmaX, sigmaY, sigmaZ, cmul,
    cadd, csub, csmul, anticomm, comm, matI, matZero, diracC, diracCDag, numberOp, parityOp]

theorem dirac_nilpotent : cmul diracC diracC = matZero := by
  ext <;> norm_num [cadjoint, gamma1, gamma2, sigmaX, sigmaY, sigmaZ, cmul,
    cadd, csub, csmul, anticomm, comm, matI, matZero, diracC, diracCDag, numberOp, parityOp]

theorem dirac_dag_nilpotent : cmul diracCDag diracCDag = matZero := by
  ext <;> norm_num [cadjoint, gamma1, gamma2, sigmaX, sigmaY, sigmaZ, cmul,
    cadd, csub, csmul, anticomm, comm, matI, matZero, diracC, diracCDag, numberOp, parityOp]

theorem dirac_anticommutation_relation : anticomm diracC diracCDag = matI := by
  ext <;> norm_num [cadjoint, gamma1, gamma2, sigmaX, sigmaY, sigmaZ, cmul,
    cadd, csub, csmul, anticomm, comm, matI, matZero, diracC, diracCDag, numberOp, parityOp]

theorem numberOp_matrix_form : numberOp = ⟨0, 0, 0, 1⟩ := by
  ext <;> norm_num [cadjoint, gamma1, gamma2, sigmaX, sigmaY, sigmaZ, cmul,
    cadd, csub, csmul, anticomm, comm, matI, matZero, diracC, diracCDag, numberOp, parityOp]

theorem numberOp_idempotent : cmul numberOp numberOp = numberOp := by
  ext <;> norm_num [cadjoint, gamma1, gamma2, sigmaX, sigmaY, sigmaZ, cmul,
    cadd, csub, csmul, anticomm, comm, matI, matZero, diracC, diracCDag, numberOp, parityOp]

theorem parityOp_eq_sigmaZ : parityOp = sigmaZ := by
  ext <;> norm_num [cadjoint, gamma1, gamma2, sigmaX, sigmaY, sigmaZ, cmul,
    cadd, csub, csmul, anticomm, comm, matI, matZero, diracC, diracCDag, numberOp, parityOp]

theorem parityOp_majorana_representation : parityOp = csmul (-I) (cmul gamma1 gamma2) := by
  ext <;> norm_num [cadjoint, gamma1, gamma2, sigmaX, sigmaY, sigmaZ, cmul,
    cadd, csub, csmul, anticomm, comm, matI, matZero, diracC, diracCDag, numberOp, parityOp]

theorem parityOp_involutive : cmul parityOp parityOp = matI := by
  ext <;> norm_num [cadjoint, gamma1, gamma2, sigmaX, sigmaY, sigmaZ, cmul,
    cadd, csub, csmul, anticomm, comm, matI, matZero, diracC, diracCDag, numberOp, parityOp]

theorem parity_commutes_with_number : comm parityOp numberOp = matZero := by
  ext <;> norm_num [cadjoint, gamma1, gamma2, sigmaX, sigmaY, sigmaZ, cmul,
    cadd, csub, csmul, anticomm, comm, matI, matZero, diracC, diracCDag, numberOp, parityOp]

theorem parity_anticomm_gamma1 : anticomm parityOp gamma1 = matZero := by
  ext <;> norm_num [cadjoint, gamma1, gamma2, sigmaX, sigmaY, sigmaZ, cmul,
    cadd, csub, csmul, anticomm, comm, matI, matZero, diracC, diracCDag, numberOp, parityOp]

theorem parity_anticomm_gamma2 : anticomm parityOp gamma2 = matZero := by
  ext <;> norm_num [cadjoint, gamma1, gamma2, sigmaX, sigmaY, sigmaZ, cmul,
    cadd, csub, csmul, anticomm, comm, matI, matZero, diracC, diracCDag, numberOp, parityOp]

structure QuantumMajoranaFormalSuite : Prop where
  h_g1_adj : cadjoint gamma1 = gamma1
  h_g2_adj : cadjoint gamma2 = gamma2
  h_g1_sq : cmul gamma1 gamma1 = matI
  h_g2_sq : cmul gamma2 gamma2 = matI
  h_g_anticomm : anticomm gamma1 gamma2 = matZero
  h_car_c_sq : cmul diracC diracC = matZero
  h_car_cdag_sq : cmul diracCDag diracCDag = matZero
  h_car_anticom : anticomm diracC diracCDag = matI
  h_n_proj : cmul numberOp numberOp = numberOp
  h_p_maj_repr : parityOp = csmul (-I) (cmul gamma1 gamma2)
  h_p_invol : cmul parityOp parityOp = matI
  h_p_comm_n : comm parityOp numberOp = matZero
  h_p_anti_g1 : anticomm parityOp gamma1 = matZero
  h_p_anti_g2 : anticomm parityOp gamma2 = matZero

theorem quantum_majorana_master_verification_suite : QuantumMajoranaFormalSuite := {
  h_g1_adj := gamma1_self_adjoint
  h_g2_adj := gamma2_self_adjoint
  h_g1_sq := gamma1_sq_identity
  h_g2_sq := gamma2_sq_identity
  h_g_anticomm := majorana_anticommute
  h_car_c_sq := dirac_nilpotent
  h_car_cdag_sq := dirac_dag_nilpotent
  h_car_anticom := dirac_anticommutation_relation
  h_n_proj := numberOp_idempotent
  h_p_maj_repr := parityOp_majorana_representation
  h_p_invol := parityOp_involutive
  h_p_comm_n := parity_commutes_with_number
  h_p_anti_g1 := parity_anticomm_gamma1
  h_p_anti_g2 := parity_anticomm_gamma2
}

#print axioms quantum_majorana_master_verification_suite

end QuantumMajoranaChain
