---
id: NumericBinaryGrid
language: en
section: numeric-certificates
source: Verification/NumericBinaryGrid.lean
source_sha256: e99fc432306360240ae307e2d8a3828ccacc400daad458fbd3181966e54ed5b4
novelty: not-assessed
status: reviewed
---

# NumericBinaryGrid

[Lean](../../Verification/NumericBinaryGrid.lean)[Rounding certificates](NumericRoundingCertificates.md)

## Exact magnitude decoder

This supporting module constructs the rational grid used by the rounding specification. For a natural base `B > 1` and positive rational quantum `q`, the magnitude of code `k` is

```text
q * (if k < B then k else (B + k % B) * 2^(k / B − 1)).
```

The exponent uses natural subtraction; the normal branch has `k / B ≥ 1`. For a binary format, `B = 2^fractionBits`. Below `B`, the grid advances in units of the subnormal quantum. Above it, the quantum doubles at successive binades.

`magnitudeUnits_lt_succ` proves strict increase by distinguishing a within-binade increment from the quotient/remainder carry. `magnitudeUnits_strictMono` and `magnitude_strictMono` extend this to arbitrary ordered indices; they do not enumerate the finite format. `magnitude_zero` establishes zero and `magnitude_subnormal` provides the exact subnormal formula.

`magnitudeUnits_virtual` gives the next-binade value at code `(E+1)*B`. The decoder is defined on all natural codes; consumers restrict admissible representations to their chosen last code. The helper itself neither rounds nor interprets an arbitrary large code as a valid floating-point value.

## Binary64 instance and parity

`binary64Base = 2^52`, `binary64Quantum = 1/2^1074`, and `binary64Last = 2047*2^52`. `binary64Value` is the exact rational decoder. Its theorems prove zero, strict monotonicity, the least positive subnormal, the general subnormal formula, and terminal virtual value `2^1024`.

`significand B k` is `k` in the subnormal range and `B + k % B` otherwise. `significand_parity` proves that its parity equals code parity when `2 ∣ B`. The binary64 specialization and even terminal code justify the ties-to-even rule used by the main module, including the virtual overflow neighbor.

The terminal rational is a virtual neighbor used to locate the overflow midpoint. It is not infinity. Signed zeros, signed results, tagged infinity, interval checks, exact midpoint decisions and their soundness are defined in `NumericRoundingCertificates`.

## Scope

These theorems establish exact rational grid arithmetic. They do not establish equivalence to a Python decoder, machine instructions, JSON parsing, SHA-256, or SQL enclosure construction. Static examples and their external provenance are recorded in the [curated fixture file](../../data/numeric_rounding/regression_provenance.json); this metadata is not consumed by a verified Lean parser. No hardware or detector property follows.

The helper is an implementation dependency, not an extra subject-suite import. It introduces no user axioms. Mathematical novelty is not assessed. Repository build and audit results are recorded in the [validation record](../VERIFICATION.en.md).
