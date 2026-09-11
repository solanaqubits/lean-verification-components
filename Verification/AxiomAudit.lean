import Lean
import Verification.MasterSuite

set_option linter.style.header false

open Lean

namespace AxiomAudit

/-- The standard axioms permitted by this project's dependency policy. -/
def allowedAxioms : List Name :=
  [`propext, `Classical.choice, `Quot.sound]

/-- Check all transitive axiom dependencies of the named declaration.
This checks the selected declaration, not every declaration in its imported modules. -/
elab "#audit_axioms " id:ident : command => do
  let constName ← Lean.resolveGlobalConstNoOverload id
  let axioms ← Lean.collectAxioms constName
  let unauthorized := axioms.filter fun ax => !allowedAxioms.contains ax
  if unauthorized.isEmpty then
    logInfo m!"[AXIOM AUDIT PASSED] '{constName}': all dependencies are allowed: {axioms.toList}"
  else
    throwError m!"[AXIOM AUDIT FAILED] Unauthorized axioms in '{constName}': {unauthorized.toList}"

#audit_axioms MasterSuite.verification_master_registry

end AxiomAudit
