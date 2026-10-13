---
id: CryptoThresholdSchnorrFrostGroup
language: en
section: cryptography
source: Verification/CryptoThresholdSchnorrFrostGroup.lean
source_sha256: ca2c95c4613c847e3a3fd4b5b6a6c106f89f677108bf112786d4987a05dfa25b
novelty: not-assessed
status: reviewed
---

# Algebraic threshold Schnorr signatures with FROST contexts

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoThresholdSchnorrFrostGroup.lean)

## Model and assumptions

The setup reuses Shamir's `Setup q t n B`: q is prime, 1 ≤ t ≤ n < q,
participant coordinates are distinct nonzero elements of ZMod q, and the additive
commutative group B is a ZMod q module. Scalar multiplication of the generator is
bijective. `ConsistencyModel` supplies coordinates 1,...,n and B = ZMod q with
generator 1. This witnesses consistency, not discrete-logarithm hardness.

Shares are evaluations of one polynomial f with f.natDegree < t; the common
public key is f(0) • G. Any selected finite set I with |I| ≥ t is supported.
No assumption that exactly t participants sign is imposed. The algebraic core
is proved over arbitrary fields and modules, then specialized by the session suite.

Each participant has two scalar nonces d_i, e_i and public commitments
D_i = d_i • G and E_i = e_i • G. `canonicalOrder` sorts by the natural-number
representatives of the actual scalar identifiers, which need not match node indices.
`commitmentList` contains these identifiers and both commitments. A valid input
list is duplicate-free; `sessionFromList` requires that validation before using its set.

`HashContext.binding` takes the common key, message, canonical commitment list
and participant identifier. Its output is rho_i. The aggregate commitment is
R = sum (D_i + rho_i • E_i). `HashContext.challenge` takes R, the common key and
message. These are arbitrary deterministic functions with distinct typed interfaces;
no hash-to-scalar implementation, byte encoding or random-oracle property is assumed.
Nonces are inputs, not sampled values or a stateful nonce store.

## Proven statements

For lambda_i equal to the Shamir coefficient for the selected I, the response is
z_i = d_i + rho_i e_i + c lambda_i f(xi_i). The partial equation is
z_i • G = R_i + (c lambda_i) • Y_i. The proof reuses MuSig's module identity.
`frost_group_interpolation` directly applies Shamir's group reconstruction at
threshold |I|, using deg f < t ≤ |I|. Summing partial equations gives
(sum z_i) • G = R + c • (f(0) • G). Composition also holds for arbitrary partial
responses that satisfy the individual equations under the same public context.

`canonical_session_invariance` proves equality of binding factors, challenge,
aggregate commitment and response when duplicate-free enumerations are permuted.
`frost_alternate_coalition_correctness` accepts two arbitrary valid sessions,
recomputing nonces, coefficients and challenges for each. Both verify under the
same key; their signatures need not be equal.

With the transcript fixed, shifting a valid scalar response by nonzero delta
breaks its equation by generator injectivity. This applies to a partial response
and the aggregate. `sum_shiftAt` relates an actual single-component replacement
to that aggregate shift. `session_error_cancellation` constructs two distinct
selected participants' opposite errors: both partial equations fail but their
aggregate still verifies. Aggregate validity does not certify every partial response.

## Regressions and interfaces

- `frost_reduction_to_schnorr_t1`: a constant polynomial and singleton signer set
  yield the Schnorr response with combined nonce d + rho e.
- `frost_threshold_two` and `frost_threshold_all`: threshold pair and full participation.
- The live Lean regression uses f = 3 + X over ZMod 7 with two-of-three and
  three-of-three signing at threshold two, deterministic context-dependent functions,
  alternative coalitions, permutation, duplicate rejection and opposite-error cancellation.
- `CryptoThresholdSchnorrFrostGroupSuite` and
  `crypto_threshold_schnorr_frost_group_master_suite` integrate the session properties,
  parameter model and singleton reduction into the cryptography suite.

## Verification and Clean Water

The release workflow uses strict module verify/audit, `lake build --wfail`, full
`verify-all`, live unittest, the registry axiom audit, an independent pinned full
axiom auditor and the knowledge validator. Measured results are recorded separately.
Only propext, Classical.choice and Quot.sound are permitted.

The result is algebraic completeness and fixed-transcript tamper sensitivity.
Unforgeability, ROM reductions, resistance to concurrent-session attacks, nonce
sampling and enforced one-time nonce use, DKG/Feldman VSS, concrete curves and byte
serialization are not modeled. No claim of safety under nonce reuse is made.
Python, JSON/SHA-256 and SimLab obligations remain open.

Reference: [RFC 9591, sections 4–5](https://www.rfc-editor.org/rfc/rfc9591.html#section-4).
The RFC requires nonce deletion and prohibits reuse; this module does not prove
that an implementation enforces those requirements.

## Public release validation

The [v0.5.49 report](../../docs/release-v0.5.49.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 151 |
| Lean files under Verification/ | 191 top-level + 2 auxiliary = 193 |
| Root-inclusive sources identical to the private snapshot | 194 |
| Clean strict build | 3742 jobs; no warnings |
| Complete verifier audit | 20451 declarations; no violations |
| Pinned independent full audit | 20451 declarations; no violations |
| Public live tests | 96; no failures or skips; 302.683s |
