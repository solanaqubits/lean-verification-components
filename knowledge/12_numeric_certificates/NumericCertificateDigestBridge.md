---
id: NumericCertificateDigestBridge
language: en
section: numeric-certificates
source: Verification/NumericCertificateDigestBridge.lean
source_sha256: 7370e1299360e9217c95ef1a0e05020c76347c5bbeb8d705760db3dbdfb6cf3f
novelty: not-assessed
status: reviewed
---

# NumericCertificateDigestBridge

[Section](README.md) · [Lean](../../Verification/NumericCertificateDigestBridge.lean)

## Conditional composition from bytes

This module composes a caller-supplied digest function, a caller-supplied decoder and the previously verified mathematical interval checker. `Digest32` is a 32-byte function type; `DigestFunction` maps a list of bytes to that type. The output width alone does not make a function SHA-256. No digest algorithm or JSON grammar is implemented here.

`ParsedCertificate g` contains rational `lo` and `hi` plus a claimed floating representation for a fixed `MagnitudeGrid g`. `PayloadParser g` is an explicit pure function from bytes to an optional record. `parsePayload` is only an adapter to that function. Neither a parser correctness theorem nor a standard serialization format is assumed or proved.

`validatePayload` checks three concrete conditions in order:

1. The digest of the supplied bytes equals the supplied expected digest.
2. Decoding those same bytes succeeds and yields a record `p`.
3. `checkIntervalCertificate` accepts `p.lo`, `p.hi` and `p.claimedFloat`.

`validate_payload_eq_some_iff` characterizes acceptance by exactly these three conditions for the same record. It does not substitute an unrelated parsed object. `accepted_bounds_ordered` derives endpoint order from mathematical acceptance. `reject_wrong_digest` and `reject_failed_parse` prove rejection of their respective failed gates. `checkedPayloadOfAccepted` packages the checked digest equation in `RawCertificatePayload`; this wrapper is not an authenticated message type.

## Numerical and SQL conclusions

`end_to_end_certificate_validation` proves that an accepted payload's claimed encoding equals `realRound g x` **provided** the real value `x` lies between the parsed endpoints. A digest match cannot supply that enclosure premise. `rational_certificate_validation` gives the corresponding result for rational arguments and the earlier rational rounding specification.

`sql_e2e_verified_pipeline` supplies a particular enclosure through [NumericSQLIntervalBounds](NumericSQLIntervalBounds.md). Its target is `sqrt(hbar/(mass*frequency))`, not the SimLab optimization gap. Positive input intervals `H`, `M`, `W`, their containment of the actual real parameters, and an accepted rational root witness `R` are additional hypotheses. Explicit equalities `R.lo = p.lo` and `R.hi = p.hi` link that root interval to the parsed certificate. The input intervals and root witness themselves are external parameters: this theorem does not claim that they were decoded from the same bytes.

`numeric_digest_bridge_master_suite : NumericCertificateDigestBridgeSuite` collects digest congruence/separation, exact acceptance conditions and the conditional real/SQL conclusions.

## Integrity and context boundaries

`digest_preserved_of_bytes_eq` is ordinary function congruence. `digest_integrity_soundness` is its contrapositive: different digest outputs imply different inputs. Neither proves collision resistance or the converse. `digest_equality_does_not_imply_bytes_equality` constructs a constant digest for which `[]` and `[0]` have equal outputs while their bytes differ.

The expected digest's source is not authenticated. Digest function, parser and grid are fixed external context; they are not authenticated by a match. Equal bytes or digests need not have the same interpretation under different parsers or grids. The model does not check a format/version identifier, domain separation, a digital signature, or a commitment to decoder configuration. An attacker able to replace both bytes and the expected digest is not excluded by these theorems.

The result is a parameterized composition theorem. It does **not** discharge the full JSON/SHA-256/byte-correspondence obligation, verify Python, identify an executable decoder with this abstraction, authenticate authorship, or establish physical detector behavior. Mathematical novelty is not assessed. Final build and audit outcomes are recorded separately in the [validation record](../VERIFICATION.en.md).
