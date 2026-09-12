---
id: QuantumSuperdenseCoding
language: en
section: quantum-physics
source: Verification/QuantumSuperdenseCoding.lean
source_sha256: 546494ec9f2b9b70e8cba7284dafe66e47981955487016098f62a426997cab64
novelty: not-assessed
status: reviewed
---

# QuantumSuperdenseCoding

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumSuperdenseCoding.lean)

## Verified result

The four explicitly supplied Bell-vector representatives are normalized when s*s = 1/2 and pairwise orthogonal for different bit pairs. For every positive s, the coordinate/sign classifier returns the bit pair used to construct the vector. The four cases and the universal decoding theorem are included in the registry.

## Assumptions and limitations

QState4 is an arbitrary real four-vector. Decoding requires s > 0 but not normalization. Normalization requires s*s = 1/2 but not positivity. Orthogonality holds for every real s, even zero; normalization excludes that degenerate case.

The encoder is a table of vectors, not an implementation of local Pauli gates or U tensor I. The decoder reads exact amplitudes and their signs; it is not a projective Bell measurement, a Born-rule model, or an executable physical procedure. It does not respect global-phase equivalence: encode s false false and encode (-s) false false represent opposite vectors, yet the classifier returns different first bits for s > 0. Correctness is restricted to the stated positive-scale representatives.

No transmission process or communication-resource count is defined, so sending two classical bits by transmitting one qubit is not proved here. Complex phases, channel noise, dephasing, gate unitarity, physical preparation and generalized qudit superdense coding are outside the model.

## Value and novelty

Exact checks of Bell-vector conventions, normalization, orthogonality and a coordinate decoder on its specified inputs. These can support later circuit and measurement formalizations. Scientific priority and first formalization have not been assessed.

## Verification

[Validation record](../VERIFICATION.en.md). Entry point: `QuantumSuperdenseCoding.quantum_superdense_master_verification_suite`.
