/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumSimonsAlgorithm
import Verification.Specs.QuantumSimonsSpec

/-! A fieldwise bridge, not a universal non-vacuity detector. The executable
checker additionally checks types and definitions against the independent gold. -/
namespace QuantumSimonsConformance

theorem simon_conformance_verified :
    QuantumSimonsAlgorithm.QuantumSimonsSuite ↔ QuantumSimonsSpec.GoldSimonSuite := by
  constructor
  · intro h
    exact ⟨h.oracle_unitary, h.hadamard_unitary, h.circuit_amplitude, h.odd_amplitude,
      h.exact_distribution, h.normalized, h.recovery⟩
  · intro h
    exact ⟨h.oracle_unitary, h.hadamard_unitary, h.circuit_amplitude, h.odd_amplitude,
      h.exact_distribution, h.normalized, h.recovery⟩

theorem gold_simon_verified : QuantumSimonsSpec.GoldSimonSuite :=
  simon_conformance_verified.mp QuantumSimonsAlgorithm.quantum_simons_master_suite

end QuantumSimonsConformance
