import Verification.DeFiConstantProductVirtualReserves

open DeFiConstantProductVirtualReserves

def bounded : DiscreteState := ⟨10, 5, 0, 5⟩
def ordinary : DiscreteState := ⟨100, 100, 0, 0⟩
def rational : VirtualReservesState := bounded.lift (by decide +kernel)
def reserves (s : VirtualReservesState) : ℚ × ℚ := (s.x, s.y)

example : quote rational 0 0 = 0 := by decide +kernel
example : quote rational 10 0 = 5 := by decide +kernel
example : quote rational 20 0 > rational.y := by decide +kernel
example : execute_swap_x_to_y rational 20 0 = none := by decide +kernel
example : (execute_swap_x_to_y rational 10 0).map reserves = some (20, 0) := by decide +kernel
example : execute_swap_x_to_y rational (-1) 0 = none := by decide +kernel
example : execute_swap_x_to_y rational 1 1 = none := by decide +kernel
example : execute_swap_x_to_y rational 1 (-1) = none := by decide +kernel
example : discrete_swap_floor ordinary 1 0 = some ⟨101, 100, 0, 0⟩ := by decide +kernel
example : discrete_swap_floor ordinary 100 0 = some ⟨200, 50, 0, 0⟩ := by decide +kernel
example : discrete_swap_floor bounded 10 0 = some ⟨20, 0, 0, 5⟩ := by decide +kernel
example : discrete_swap_floor bounded 20 0 = none := by decide +kernel
example : discrete_swap_floor bounded 10 (1/10) = some ⟨20, 1, 0, 5⟩ := by decide +kernel
example : discrete_swap_ceil bounded 5 (1/10) = some ⟨22, 0, 0, 5⟩ := by decide +kernel
example : discrete_swap_ceil ordinary 100 0 = none := by decide +kernel
example : discrete_swap_ceil ordinary 1 0 = some ⟨102, 99, 0, 0⟩ := by decide +kernel
example : discrete_step ordinary ⟨true, false, 100, 0⟩ = some ⟨50, 200, 0, 0⟩ := by decide +kernel
example : discrete_chain ordinary [⟨false, false, 100, 0⟩, ⟨true, false, 50, 0⟩] =
    some ordinary := by decide +kernel
example (s : VirtualReservesState) (d : ℕ) (γ : ℚ) (hg : valid_fee γ) :
    0 ≤ quote s d γ - (floor_div_output s d γ : ℚ) ∧
      quote s d γ - (floor_div_output s d γ : ℚ) < 1 := floor_output_error s d hg
example (s : VirtualReservesState) (o d : ℕ) (γ : ℚ) (hg : valid_fee γ)
    (hY : (o : ℚ) < Y s) :
    ceil_div_input s o γ ≤ d ↔ (o : ℚ) ≤ quote s d γ := ceil_input_minimal s o d hg hY
example (as : List DiscreteStep) (s t : DiscreteState) (hs : s.Valid)
    (h : discrete_chain s as = some t) : t.Valid ∧ s.K ≤ t.K := discrete_chain_monotone as s t hs h
example : DeFiConstantProductVirtualReservesSuite := verification_suite

/-- Monotone average price requires a fixed fee: a lower second fee can reverse it. -/
example : quote rational 2 0 / 2 > quote rational 1 (9/10) / 1 := by decide +kernel
/-- A rounded zero payout is solvent, but the conservative exact-input guard rejects. -/
example : discrete_swap_floor ⟨1, 0, 0, 1⟩ 1 0 = none := by decide +kernel

def main : IO Unit := do
  let cases : List Bool := [
    decide (quote rational 0 0 = 0),
    decide (quote rational 10 0 = 5),
    decide (quote rational 20 0 > rational.y),
    decide (execute_swap_x_to_y rational 20 0 = none),
    decide ((execute_swap_x_to_y rational 10 0).map reserves = some (20, 0)),
    decide ((execute_swap_x_to_y rational 0 0).map reserves = some (10, 5)),
    decide (execute_swap_x_to_y rational (-1) 0 = none),
    decide (execute_swap_x_to_y rational 1 1 = none),
    decide (execute_swap_x_to_y rational 1 (-1) = none),
    decide (discrete_swap_floor ordinary 1 0 = some ⟨101, 100, 0, 0⟩),
    decide (discrete_swap_floor ordinary 100 0 = some ⟨200, 50, 0, 0⟩),
    decide (discrete_swap_floor bounded 10 0 = some ⟨20, 0, 0, 5⟩),
    decide (discrete_swap_floor bounded 20 0 = none),
    decide (discrete_swap_floor bounded 10 (1/10) = some ⟨20, 1, 0, 5⟩),
    decide (discrete_swap_ceil bounded 5 (1/10) = some ⟨22, 0, 0, 5⟩),
    decide (discrete_swap_ceil ordinary 100 0 = none),
    decide (discrete_swap_ceil ordinary 1 0 = some ⟨102, 99, 0, 0⟩),
    decide (discrete_step ordinary ⟨true, false, 100, 0⟩ = some ⟨50, 200, 0, 0⟩),
    decide (discrete_step ordinary ⟨true, true, 1, 0⟩ = some ⟨99, 102, 0, 0⟩),
    decide (discrete_chain ordinary [] = some ordinary),
    decide (discrete_chain ordinary [⟨false, false, 100, 0⟩, ⟨true, false, 50, 0⟩] = some ordinary),
    decide (discrete_chain bounded [⟨false, false, 10, 1/10⟩, ⟨true, true, 1, 1/5⟩] =
      some ⟨19, 2, 0, 5⟩),
    decide (discrete_swap_floor ⟨0, 1, 0, 0⟩ 1 0 = none),
    decide (discrete_swap_floor ⟨1, 0, 0, 1⟩ 1 0 = none),
    decide (quote rational 2 0 / 2 > quote rational 1 (9/10) / 1)]
  if cases.all id then IO.println s!"VIRTUAL_RESERVES_EXEC_OK: {cases.length} cases"
  else throw (IO.userError s!"Virtual reserve regression failed: {cases}")

#eval main
