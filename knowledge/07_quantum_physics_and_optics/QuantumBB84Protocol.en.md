---
id: QuantumBB84Protocol
language: en
section: quantum-physics
source: Verification/QuantumBB84Protocol.lean
source_sha256: d35acd467d3ade0b693b9efb22ed93bb4ad874fbe09b24e6fdc07cd0508fa6ca
novelty: not-assessed
status: reviewed
---

# QuantumBB84Protocol

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumBB84Protocol.lean)

## Verified result

siftMatch returns true exactly for equal basis labels. measuredBitOnMatch is the identity function, so its output equals its input; the basis-equality hypothesis is retained but unused. The scalar parameter eveErrorProbabilityPerBit is defined as 1/4, and the arithmetic equalities 1-1/4 = 3/4 and 1-(3/4)^2 = 7/16 are proved.

## Assumptions and limitations

Basis contains labels only. There are no quantum states, preparation or measurement operators, Born-rule probabilities, basis sampling, Eve operations, or list-level key sifting. The bit agreement theorem is definitional, not a derivation of matched-basis measurement behavior.

The error rate 1/4 is supplied rather than derived. The model does not specify conditioning on sifted bits, an Eve basis mismatch, or a probability space; it therefore does not establish a conditional mismatch error rate. The two-bit expression is an arithmetic identity without an independence assumption or a theorem connecting it to detection events. The claimed general probability 1-(3/4)^k is not formalized for arbitrary k.

Information reconciliation, privacy amplification, key secrecy, authentication, optical-fiber noise and full BB84 security are not formalized.

## Value and novelty

Small basis-label and arithmetic checks usable as ingredients in a later explicit probabilistic protocol model. Scientific priority and first formalization have not been assessed.

## Verification

[Validation record](../VERIFICATION.en.md). Entry point: `QuantumBB84Protocol.quantum_bb84_master_verification_suite`.
