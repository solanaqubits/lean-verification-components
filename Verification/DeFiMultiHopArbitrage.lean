import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.style.header false
noncomputable section

namespace DeFiMultiHopArbitrage

/-- Fixed positive rates and fee multipliers; no reserve updates are modeled. -/
structure Cycle3Params where
  p12 : ℝ
  p23 : ℝ
  p31 : ℝ
  gamma1 : ℝ
  gamma2 : ℝ
  gamma3 : ℝ
  hp12_pos : 0 < p12
  hp23_pos : 0 < p23
  hp31_pos : 0 < p31
  hgamma1_pos : 0 < gamma1
  hgamma1_le : gamma1 ≤ 1
  hgamma2_pos : 0 < gamma2
  hgamma2_le : gamma2 ≤ 1
  hgamma3_pos : 0 < gamma3
  hgamma3_le : gamma3 ≤ 1

def totalFeeFactor3 (c : Cycle3Params) : ℝ := c.gamma1 * c.gamma2 * c.gamma3
def spotCycleProduct3 (c : Cycle3Params) : ℝ := c.p12 * c.p23 * c.p31
def effectiveReturn3 (c : Cycle3Params) : ℝ :=
  (c.gamma1 * c.p12) * (c.gamma2 * c.p23) * (c.gamma3 * c.p31)
def cycleOutput (x0 : ℝ) (c : Cycle3Params) : ℝ := x0 * effectiveReturn3 c

theorem effective_return_factoring (c : Cycle3Params) :
    effectiveReturn3 c = totalFeeFactor3 c * spotCycleProduct3 c := by
  dsimp [effectiveReturn3, totalFeeFactor3, spotCycleProduct3]
  ring

theorem totalFeeFactor3_le_one (c : Cycle3Params) : totalFeeFactor3 c ≤ 1 := by
  have h12 : c.gamma1 * c.gamma2 ≤ 1 := by
    calc
      c.gamma1 * c.gamma2 ≤ 1 * c.gamma2 :=
        mul_le_mul_of_nonneg_right c.hgamma1_le c.hgamma2_pos.le
      _ = c.gamma2 := one_mul _
      _ ≤ 1 := c.hgamma2_le
  calc
    totalFeeFactor3 c ≤ 1 * c.gamma3 :=
      mul_le_mul_of_nonneg_right h12 c.hgamma3_pos.le
    _ = c.gamma3 := one_mul _
    _ ≤ 1 := c.hgamma3_le

theorem totalFeeFactor3_strict_lt_one (c : Cycle3Params) (h_fee : c.gamma1 < 1) :
    totalFeeFactor3 c < 1 := by
  have h12 : c.gamma1 * c.gamma2 < 1 := by
    calc
      c.gamma1 * c.gamma2 < 1 * c.gamma2 := mul_lt_mul_of_pos_right h_fee c.hgamma2_pos
      _ = c.gamma2 := one_mul _
      _ ≤ 1 := c.hgamma2_le
  calc
    totalFeeFactor3 c < 1 * c.gamma3 := mul_lt_mul_of_pos_right h12 c.hgamma3_pos
    _ = c.gamma3 := one_mul _
    _ ≤ 1 := c.hgamma3_le

/-- Conditional decay for a single fixed-rate cycle. -/
theorem no_arbitrage_cyclic_decay (c : Cycle3Params)
    (h_spot_equil : spotCycleProduct3 c ≤ 1) (h_fee : c.gamma1 < 1) :
    effectiveReturn3 c < 1 := by
  rw [effective_return_factoring]
  have hp : 0 < totalFeeFactor3 c :=
    mul_pos (mul_pos c.hgamma1_pos c.hgamma2_pos) c.hgamma3_pos
  calc
    totalFeeFactor3 c * spotCycleProduct3 c ≤ totalFeeFactor3 c * 1 :=
      mul_le_mul_of_nonneg_left h_spot_equil hp.le
    _ = totalFeeFactor3 c := mul_one _
    _ < 1 := totalFeeFactor3_strict_lt_one c h_fee

theorem cyclic_swap_net_loss (x0 : ℝ) (c : Cycle3Params) (hx0 : 0 < x0)
    (h_spot_equil : spotCycleProduct3 c ≤ 1) (h_fee : c.gamma1 < 1) :
    cycleOutput x0 c < x0 := by
  calc
    cycleOutput x0 c < x0 * 1 :=
      mul_lt_mul_of_pos_left (no_arbitrage_cyclic_decay c h_spot_equil h_fee) hx0
    _ = x0 := mul_one _

def listFeeProduct : List ℝ → ℝ
  | [] => 1
  | g :: gs => g * listFeeProduct gs

def ValidFeeList : List ℝ → Prop
  | [] => True
  | g :: gs => 0 < g ∧ g ≤ 1 ∧ ValidFeeList gs

theorem listFeeProduct_nonneg (l : List ℝ) (h : ValidFeeList l) :
    0 ≤ listFeeProduct l := by
  induction l with
  | nil => norm_num [listFeeProduct]
  | cons g gs ih =>
      exact mul_nonneg h.1.le (ih h.2.2)

theorem listFeeProduct_le_one (l : List ℝ) (h : ValidFeeList l) :
    listFeeProduct l ≤ 1 := by
  induction l with
  | nil => exact le_refl 1
  | cons g gs ih =>
      calc
        listFeeProduct (g :: gs) ≤ 1 * listFeeProduct gs :=
          mul_le_mul_of_nonneg_right h.2.1 (listFeeProduct_nonneg gs h.2.2)
        _ = listFeeProduct gs := one_mul _
        _ ≤ 1 := ih h.2.2

structure DeFiMultiHopFormalSuite : Prop where
  h_factoring : ∀ c, effectiveReturn3 c = totalFeeFactor3 c * spotCycleProduct3 c
  h_fee_le_one : ∀ c, totalFeeFactor3 c ≤ 1
  h_fee_strict_lt : ∀ c, c.gamma1 < 1 → totalFeeFactor3 c < 1
  h_no_arbitrage : ∀ c, spotCycleProduct3 c ≤ 1 → c.gamma1 < 1 → effectiveReturn3 c < 1
  h_net_capital_loss : ∀ x0 c,
    0 < x0 → spotCycleProduct3 c ≤ 1 → c.gamma1 < 1 → cycleOutput x0 c < x0
  h_list_fee_le_one : ∀ l, ValidFeeList l → listFeeProduct l ≤ 1

theorem defi_multihop_arbitrage_master_verification_suite : DeFiMultiHopFormalSuite := {
  h_factoring := effective_return_factoring
  h_fee_le_one := totalFeeFactor3_le_one
  h_fee_strict_lt := totalFeeFactor3_strict_lt_one
  h_no_arbitrage := no_arbitrage_cyclic_decay
  h_net_capital_loss := cyclic_swap_net_loss
  h_list_fee_le_one := listFeeProduct_le_one
}

#print axioms defi_multihop_arbitrage_master_verification_suite

end DeFiMultiHopArbitrage
