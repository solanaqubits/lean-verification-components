# Explicit qutrit decoder statement conformance

[Hierarchy](verification-hierarchy.en.md) · [Module](../Verification/QuantumQutritSecretSharingExplicitDecoder.lean)

The Mathlib-only normative file Verification/Specs/QuantumQutritDecoderSpec.lean
fixes forward/inverse coordinates, normalization, encoding, cyclic regrouping,
partial trace and recovery Kraus matrices independently of candidate imports.
An explicit nine-entry permutation table is checked by Lean's kernel.

The pinned probe compares eight definitions/operator families and seven theorem
signatures: both inverse laws, both unitary identities, Kraus completeness,
recovery for every erased position and every complex matrix, and recovery with
an arbitrary finite reference. It also kernel-checks a bridge to the expected
all-matrix recovery statement and inspects axioms of the selected theorems.
The reference signature uses the established amplification API; this is not a
new independent semantics for every supporting module or for physical systems.

```bash
python3 tools/qutrit_conformance_checker.py
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p test_qutrit_conformance.py -v
```

Five unittest methods cover the original, an alternative proof, six mutations,
invalid identifiers and a tampered normative specification. Mutation subcases
weaken recovery to False antecedents, True conclusions, one erased position,
diagonal-only matrices or one reference dimension, or change the coordinates.
These are distinct counters, not eleven independently named unittest methods.

The trusted contract manifest pins the specification, probe and Lean toolchain.
Do not regenerate these pins from a failed candidate. The initial normative
contract implements the approved module-190 requirement; future changes need
separate specification review. The manifest/checker remain part of the trusted
process. An actor who can replace both them and their acceptance policy is not
constrained by hashes alone. This is not a hostile-code sandbox or a universal
semantic-equivalence/non-vacuity decision procedure.
