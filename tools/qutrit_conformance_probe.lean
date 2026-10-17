import Lean
import Verification.Specs.QuantumQutritDecoderSpec
-- CANDIDATE_IMPORT

open scoped BigOperators
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract
open QuantumKnillLaflammeEnvironmentCriterion QuantumReferencePreservingRecoveryContract
open QuantumErasureCorrectabilityContract QuantumQutritTwoOfThreeSecretSharingContract

namespace QutritExpected
-- These signatures are pinned independently of the candidate proof bodies.
def left : Prop := Function.LeftInverse QuantumQutritDecoderSpec.backward
  QuantumQutritDecoderSpec.forward
def right : Prop := Function.RightInverse QuantumQutritDecoderSpec.backward
  QuantumQutritDecoderSpec.forward
def unitaryLeft : Prop := QuantumQutritDecoderSpec.decoder.conjTranspose *
  QuantumQutritDecoderSpec.decoder = 1
def unitaryRight : Prop := QuantumQutritDecoderSpec.decoder *
  QuantumQutritDecoderSpec.decoder.conjTranspose = 1
def complete : Prop := ∑ t, (QuantumQutritDecoderSpec.kraus t).conjTranspose *
  QuantumQutritDecoderSpec.kraus t = 1
def recovery : Prop := ∀ (q : Fin 3) (X : Q 3),
  apply_channel __CANDIDATE__.explicitRecovery
    (QuantumQutritDecoderSpec.retainedPair q (encode QuantumQutritDecoderSpec.code X)) = X
def reference : Prop := ∀ (q : Fin 3) (m : ℕ) (X : Joint m 3),
  liftedRecovery (erasureChannel 9 3) (groupedCode q) __CANDIDATE__.explicitRecovery m X = X
end QutritExpected

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let actual := "__CANDIDATE__".toName
  let gold := `QuantumQutritDecoderSpec
  let definitions : Array (Name × Name) := #[
    (actual ++ `decodeCoordinates, gold ++ `forward),
    (actual ++ `encodeCoordinates, gold ++ `backward),
    (actual ++ `decoder, gold ++ `decoder),
    (actual ++ `recoveryOperator, gold ++ `kraus),
    (`QuantumQutritTwoOfThreeSecretSharingContract.code, gold ++ `code),
    (`QuantumQutritTwoOfThreeSecretSharingContract.physicalIndex, gold ++ `regroupIndex),
    (`QuantumQutritTwoOfThreeSecretSharingContract.retainedPair, gold ++ `retainedPair)]
  for (a,g) in definitions do
    let ac ← mkConstWithFreshMVarLevels a
    let gc ← mkConstWithFreshMVarLevels g
    unless ← withTransparency .all (isDefEq ac gc) do
      throwError "QUTRIT_CONFORMANCE definition mismatch: {a}"
  let ops ← Lean.Elab.Term.elabTerm (← `( __CANDIDATE__.explicitRecovery.operators )) none
  unless ← withTransparency .all (isDefEq ops (mkConst (gold ++ `kraus))) do
    throwError "QUTRIT_CONFORMANCE channel operators mismatch"
  let claims : Array (Name × Name) := #[
    (`coordinates_left_inverse, `QutritExpected.left),
    (`coordinates_right_inverse, `QutritExpected.right),
    (`decoder_unitary_left, `QutritExpected.unitaryLeft),
    (`decoder_unitary_right, `QutritExpected.unitaryRight),
    (`recovery_complete, `QutritExpected.complete),
    (`explicit_recovery, `QutritExpected.recovery),
    (`explicit_reference_recovery, `QutritExpected.reference)]
  for (a,g) in claims do
    let info ← getConstInfo (actual ++ a)
    unless info matches .thmInfo _ do
      throwError "QUTRIT_CONFORMANCE expected theorem: {a}"
    for ax in ← Lean.collectAxioms (actual ++ a) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "QUTRIT_CONFORMANCE forbidden axiom: {ax}"
    unless ← withTransparency .all (isDefEq info.type (mkConst g)) do
      throwError "QUTRIT_CONFORMANCE statement mismatch: {a}"
  logInfo "QUTRIT_CONFORMANCE_OK definitions=8 statements=7"

-- A kernel-checked proof of the pinned all-matrix claim, not just a success log.
theorem qutrit_candidate_recovery : QutritExpected.recovery :=
  __CANDIDATE__.explicit_recovery
