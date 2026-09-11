import Lean
-- IMPORTS

open Lean in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  let mut found : Array String := #[]
  let mut violations : Array Json := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[idx.toNat]!
    if !(`Verification).isPrefixOf moduleName then continue
    count := count + 1
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      if !found.contains ax.toString then found := found.push ax.toString
      if !allowed.contains ax then
        violations := violations.push (Json.mkObj [
          ("declaration", toJson name.toString), ("axiom", toJson ax.toString)])
  if count == 0 then throwError "Audit found no project declarations"
  let report := Json.mkObj [("declarations", toJson count),
    ("axioms", toJson found), ("violations", toJson violations)]
  logInfo m!"VERIFIER_AUDIT_JSON={report.compress}"
  if !violations.isEmpty then throwError "Unauthorized axiom dependencies"
