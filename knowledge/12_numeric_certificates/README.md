# Exact numeric certificates

[All sections](../README.md)

| Module | Scope |
|---|---|
| [NumericBinaryGrid](NumericBinaryGrid.md) | Exact increasing binary magnitude decoder and significand parity. |
| [NumericRoundingCertificates](NumericRoundingCertificates.md) | Signed nearest-even rounding, local interval and midpoint certificates, static SimLab regressions. |
| [NumericRealRounding](NumericRealRounding.md) | Real semantic extension and soundness of rational rounding certificates for real enclosed values. |
| [NumericSQLIntervalBounds](NumericSQLIntervalBounds.md) | Conditional rational enclosures of sqrt(hbar/(mass*frequency)) and the rounding bridge. |
| [NumericCertificateDigestBridge](NumericCertificateDigestBridge.md) | Conditional composition of a supplied byte digest, parser and numerical certificate checker. |
| [NumericSQLGapBounds](NumericSQLGapBounds.md) | Affine gap enclosure, exact zero and real rounding composition. |

Input localization is an explicit hypothesis. The square-root target enclosure is separate from the SimLab gap A/I + B*I − 2*sqrt(A*B), whose affine mathematical enclosure and rounding composition are now covered separately; the external certificate pipeline is not verified here. Python equivalence, JSON parsing, hashing and correspondence with external bytes remain separate obligations.

The digest bridge assumes a fixed external digest function, parser, grid and expected digest. It checks that those functions accept the actual bytes; it does not implement SHA-256/JSON, authenticate context, or complete the external byte-correspondence obligation.
