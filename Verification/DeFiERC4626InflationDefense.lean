import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option linter.style.header false

namespace DeFiERC4626InflationDefense

/-! Integer conversion identities for a supplied virtual-offset formula.
These static calculations do not prove general inflation-attack resistance. -/

def naiveConvertToShares (depositAssets totalAssets totalSupply : ℕ) : ℕ :=
  if totalAssets = 0 then depositAssets else depositAssets * totalSupply / totalAssets

theorem naive_vault_zero_shares_exploit : naiveConvertToShares 999 1000 1 = 0 := by
  decide

/-- Static redemption arithmetic, assuming the attacker owns the entire supply. -/
theorem naive_vault_loss_of_capital :
    let attackerShares := 1
    let victimShares := naiveConvertToShares 999 1000 attackerShares
    let newTotalSupply := attackerShares + victimShares
    let newTotalAssets := 1000 + 999
    victimShares = 0 ∧ attackerShares * newTotalAssets / newTotalSupply = 1999 := by
  decide

def protectedConvertToShares (depositAssets totalAssets totalSupply offsetDecimals : ℕ) : ℕ :=
  depositAssets * (totalSupply + 10 ^ offsetDecimals) / (totalAssets + 1)

def protectedConvertToAssets (shares totalAssets totalSupply offsetDecimals : ℕ) : ℕ :=
  shares * (totalAssets + 1) / (totalSupply + 10 ^ offsetDecimals)

theorem protected_vault_mitigates_zero_shares :
    protectedConvertToShares 999 1000 1 3 = 999 := by
  decide

/-- Positivity under an explicit sufficient lower bound on the deposit. -/
theorem protected_shares_strictly_positive
    (depositAssets totalAssets totalSupply offsetDecimals : ℕ)
    (h_dep : totalAssets + 1 ≤ depositAssets) :
    0 < protectedConvertToShares depositAssets totalAssets totalSupply offsetDecimals := by
  dsimp [protectedConvertToShares]
  have h_pow_pos : 0 < 10 ^ offsetDecimals := by positivity
  apply Nat.div_pos
  · nlinarith
  · omega

theorem protected_shares_monotone
    (d1 d2 totalAssets totalSupply offsetDecimals : ℕ) (h_le : d1 ≤ d2) :
    protectedConvertToShares d1 totalAssets totalSupply offsetDecimals ≤
      protectedConvertToShares d2 totalAssets totalSupply offsetDecimals := by
  exact Nat.div_le_div_right
    (Nat.mul_le_mul_right (totalSupply + 10 ^ offsetDecimals) h_le)

/-- Virtual offsets alone do not rule out zero minting for every deposit. -/
theorem protected_zero_shares_still_possible :
    protectedConvertToShares 1 1000000 1 3 = 0 := by
  decide

structure DeFiERC4626InflationDefenseFormalSuite : Prop where
  h_naive_exploit : naiveConvertToShares 999 1000 1 = 0
  h_naive_capital_loss : naiveConvertToShares 999 1000 1 = 0 ∧
    (1 * (1000 + 999) : ℕ) / (1 + 0) = 1999
  h_protected_mitigate : protectedConvertToShares 999 1000 1 3 = 999
  h_protected_pos : ∀ (dep assets supply off : ℕ), assets + 1 ≤ dep →
    0 < protectedConvertToShares dep assets supply off
  h_protected_mono : ∀ (d1 d2 assets supply off : ℕ), d1 ≤ d2 →
    protectedConvertToShares d1 assets supply off ≤ protectedConvertToShares d2 assets supply off
  h_zero_possible : protectedConvertToShares 1 1000000 1 3 = 0

theorem defi_erc4626_inflation_defense_master_suite : DeFiERC4626InflationDefenseFormalSuite := {
  h_naive_exploit := naive_vault_zero_shares_exploit
  h_naive_capital_loss := naive_vault_loss_of_capital
  h_protected_mitigate := protected_vault_mitigates_zero_shares
  h_protected_pos := protected_shares_strictly_positive
  h_protected_mono := protected_shares_monotone
  h_zero_possible := protected_zero_shares_still_possible
}

end DeFiERC4626InflationDefense
