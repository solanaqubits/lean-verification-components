import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false
noncomputable section

namespace DeFiERC4626Vault

/-- Positive balances in an ideal real-valued proportional vault. -/
structure VaultState where
  totalAssets : ℝ
  totalSupply : ℝ
  hAssets_pos : 0 < totalAssets
  hSupply_pos : 0 < totalSupply

def convertToShares (assets totalAssets totalSupply : ℝ) : ℝ :=
  (assets * totalSupply) / totalAssets

def convertToAssets (shares totalAssets totalSupply : ℝ) : ℝ :=
  (shares * totalAssets) / totalSupply

def sharePrice (v : VaultState) : ℝ := v.totalAssets / v.totalSupply

theorem convert_assets_roundtrip (assets : ℝ) (v : VaultState) :
    convertToAssets (convertToShares assets v.totalAssets v.totalSupply)
      v.totalAssets v.totalSupply = assets := by
  dsimp [convertToAssets, convertToShares]
  field_simp [ne_of_gt v.hAssets_pos, ne_of_gt v.hSupply_pos]

theorem convert_shares_roundtrip (shares : ℝ) (v : VaultState) :
    convertToShares (convertToAssets shares v.totalAssets v.totalSupply)
      v.totalAssets v.totalSupply = shares := by
  dsimp [convertToAssets, convertToShares]
  field_simp [ne_of_gt v.hAssets_pos, ne_of_gt v.hSupply_pos]

/-- Exact proportional minting preserves the ratio; no rounding or fees are modeled. -/
theorem share_price_invariant_on_deposit (v : VaultState) (assets : ℝ)
    (hAssets : 0 < assets) :
    let mintedShares := convertToShares assets v.totalAssets v.totalSupply
    let newTotalAssets := v.totalAssets + assets
    let newTotalSupply := v.totalSupply + mintedShares
    newTotalAssets / newTotalSupply = sharePrice v := by
  dsimp [sharePrice, convertToShares]
  have hA : v.totalAssets ≠ 0 := ne_of_gt v.hAssets_pos
  have hS : v.totalSupply ≠ 0 := ne_of_gt v.hSupply_pos
  have h_sum_ne : v.totalAssets + assets ≠ 0 := ne_of_gt (add_pos v.hAssets_pos hAssets)
  have h_denom : v.totalSupply + (assets * v.totalSupply) / v.totalAssets =
      (v.totalSupply * (v.totalAssets + assets)) / v.totalAssets := by
    field_simp [hA]
  rw [h_denom]
  field_simp [hA, hS, h_sum_ne]

theorem convert_to_shares_linear (assets : ℝ) (v : VaultState) (c : ℝ) :
    convertToShares (c * assets) v.totalAssets v.totalSupply =
      c * convertToShares assets v.totalAssets v.totalSupply := by
  dsimp [convertToShares]
  ring

theorem convert_to_shares_strict_mono (a1 a2 : ℝ) (v : VaultState) (h_lt : a1 < a2) :
    convertToShares a1 v.totalAssets v.totalSupply <
      convertToShares a2 v.totalAssets v.totalSupply := by
  dsimp [convertToShares]
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right h_lt v.hSupply_pos) v.hAssets_pos

structure DeFiERC4626FormalSuite : Prop where
  h_assets_roundtrip : ∀ (assets : ℝ) (v : VaultState),
    convertToAssets (convertToShares assets v.totalAssets v.totalSupply)
      v.totalAssets v.totalSupply = assets
  h_shares_roundtrip : ∀ (shares : ℝ) (v : VaultState),
    convertToShares (convertToAssets shares v.totalAssets v.totalSupply)
      v.totalAssets v.totalSupply = shares
  h_price_invariant : ∀ (v : VaultState) (assets : ℝ), 0 < assets →
    let mintedShares := convertToShares assets v.totalAssets v.totalSupply
    let newTotalAssets := v.totalAssets + assets
    let newTotalSupply := v.totalSupply + mintedShares
    newTotalAssets / newTotalSupply = sharePrice v
  h_linear_scale : ∀ (assets : ℝ) (v : VaultState) (c : ℝ),
    convertToShares (c * assets) v.totalAssets v.totalSupply =
      c * convertToShares assets v.totalAssets v.totalSupply
  h_strict_mono : ∀ (a1 a2 : ℝ) (v : VaultState), a1 < a2 →
    convertToShares a1 v.totalAssets v.totalSupply <
      convertToShares a2 v.totalAssets v.totalSupply

/-- Registry of exact proportional conversion identities. -/
theorem defi_erc4626_master_verification_suite : DeFiERC4626FormalSuite := {
  h_assets_roundtrip := convert_assets_roundtrip
  h_shares_roundtrip := convert_shares_roundtrip
  h_price_invariant := share_price_invariant_on_deposit
  h_linear_scale := convert_to_shares_linear
  h_strict_mono := convert_to_shares_strict_mono
}

end DeFiERC4626Vault
