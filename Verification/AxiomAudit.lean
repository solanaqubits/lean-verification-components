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
#audit_axioms MasterHundredRegistry.master_hundred_registry_verified

#audit_axioms NumericRoundingCertificates.numeric_rounding_certificates_master_suite

end AxiomAudit

#audit_axioms NumericSQLIntervalBounds.numeric_sql_interval_master_suite

#audit_axioms NumericCertificateDigestBridge.numeric_digest_bridge_master_suite

#audit_axioms NumericSQLGapBounds.numeric_sql_gap_master_suite

#audit_axioms DistributedChandyLamportSnapshot.chandy_lamport_master_suite
