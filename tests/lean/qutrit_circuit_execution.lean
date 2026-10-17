import Verification.QuantumQutritDecoderCircuitRefinement

open QuantumQutritDecoderCircuitRefinement

def main : IO Unit := do
  let outputs := (List.finRange 9).map fun i => (runIndex decoderCircuit i).val
  IO.println (String.intercalate "," (outputs.map toString))
