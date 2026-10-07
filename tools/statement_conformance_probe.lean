import Lean
import Verification.Specs.QuantumSimonsConformance
-- CANDIDATE_IMPORT

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let actual := "__CANDIDATE__".toName
  let gold := `QuantumSimonsSpec
  let definitions : Array (String × String) := #[
    ("Register", "Register"), ("JointState", "JointState"),
    ("xorVec", "xorVec"), ("SimonPromise", "GoldSimonPromise"),
    ("hermitian", "hermitian"), ("xorOracle", "xorOracle"),
    ("inputHadamard", "inputHadamard"), ("initial", "initial"),
    ("runSimon", "runSimon"), ("fiberSum", "fiberSum"),
    ("probability", "probability"), ("bit", "bit"),
    ("encode", "encode"), ("dot", "dot"), ("BinarySpace", "BinarySpace"),
    ("rowSpan", "rowSpan")]
  for (a, g) in definitions do
    let ac ← mkConstWithFreshMVarLevels (actual ++ a.toName)
    let gc ← mkConstWithFreshMVarLevels (gold ++ g.toName)
    unless ← withTransparency .all (isDefEq (← inferType ac) (← inferType gc)) do
      throwError "CONFORMANCE_MISMATCH definition type: {a}"
    unless ← withTransparency .all (isDefEq ac gc) do
      throwError "CONFORMANCE_MISMATCH definition body: {a}"
  let env ← getEnv
  let suite := actual ++ `QuantumSimonsSuite
  let some ai := getStructureInfo? env suite
    | throwError "CONFORMANCE_MISMATCH candidate suite must be a structure"
  let some gi := getStructureInfo? env ``QuantumSimonsSpec.GoldSimonSuite
    | throwError "Missing trusted gold structure"
  unless ai.fieldNames == gi.fieldNames do
    throwError "CONFORMANCE_MISMATCH suite field names"
  let ac ← getConstInfo (suite ++ `mk)
  let gc ← getConstInfo ``QuantumSimonsSpec.GoldSimonSuite.mk
  forallTelescope ac.type fun av _ => forallTelescope gc.type fun gv _ => do
    unless av.size == gv.size && av.size == 7 do
      throwError "CONFORMANCE_MISMATCH suite field count"
    for i in [:av.size] do
      let actualType ← inferType av[i]!
      let goldType ← inferType gv[i]!
      -- This is a narrow syntactic diagnostic, not a general consistency decision.
      let falseAntecedent := actualType.find? fun e => match e with
        | .forallE _ d _ _ => d.isConstOf ``False
        | _ => false
      if falseAntecedent.isSome then
        throwError "CONFORMANCE_MISMATCH explicit False antecedent: {ai.fieldNames[i]!}"
      unless ← withTransparency .all (isDefEq actualType goldType) do
        throwError "CONFORMANCE_MISMATCH suite field type: {ai.fieldNames[i]!}"
  let master ← getConstInfo (actual ++ `quantum_simons_master_suite)
  unless master matches .thmInfo _ do
    throwError "CONFORMANCE_MISMATCH master must be a theorem"
  unless ← withTransparency .all (isDefEq master.type (mkConst suite)) do
    throwError "CONFORMANCE_MISMATCH master theorem type"

namespace StatementConformanceProbe

theorem candidate_to_gold (h : __CANDIDATE__.QuantumSimonsSuite) :
    QuantumSimonsSpec.GoldSimonSuite := by
  exact ⟨h.oracle_unitary, h.hadamard_unitary, h.circuit_amplitude, h.odd_amplitude,
    h.exact_distribution, h.normalized, h.recovery⟩

theorem candidate_gold_verified : QuantumSimonsSpec.GoldSimonSuite :=
  candidate_to_gold __CANDIDATE__.quantum_simons_master_suite

end StatementConformanceProbe

open Lean in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  let mut axioms : Array String := #[]
  let mut violations : Array Json := #[]
  for (name, _) in env.constants.toList do
    let selected := if let some idx := env.getModuleIdxFor? name then
      (`Verification).isPrefixOf env.header.moduleNames[idx.toNat]!
    else (`StatementConformanceProbe).isPrefixOf name
    if !selected then continue
    count := count + 1
    for ax in ← Lean.collectAxioms name do
      if !axioms.contains ax.toString then axioms := axioms.push ax.toString
      if !allowed.contains ax then
        violations := violations.push (Json.mkObj [
          ("declaration", toJson name.toString), ("axiom", toJson ax.toString)])
  if count == 0 || !violations.isEmpty then
    throwError "CONFORMANCE_AXIOM_FAILURE {violations}"
  logInfo m!"STATEMENT_CONFORMANCE_JSON={(Json.mkObj [
    ("ok", toJson true), ("checked_definitions", toJson (16 : Nat)),
    ("checked_suite_fields", toJson (7 : Nat)), ("audited_declarations", toJson count),
    ("axioms", toJson axioms), ("violations", toJson violations)]).compress}"
