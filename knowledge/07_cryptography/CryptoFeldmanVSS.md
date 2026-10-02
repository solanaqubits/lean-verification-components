---
id: CryptoFeldmanVSS
language: en
section: cryptography
source: Verification/CryptoFeldmanVSS.lean
source_sha256: c093b765d886c521e4c47426cc588051f368073fb43ed62fb924c80073cb9af4
novelty: not-assessed
status: reviewed
---

# CryptoFeldmanVSS

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoFeldmanVSS.lean)

## Model and results

`FeldmanSetup` contains a real scalar `g ≠ 0`. The existing Shamir polynomial is
reused: `P(x) = secret + slope * x`, of degree at most one. Commitments are
`a0 = secret * g` and `a1 = slope * g`. `verifyShare` is the equation
`value * g = a0 + x * a1`. These are additive scalar identities, not real
exponentials or an implementation of a finite-group commitment.

- `feldman_vss_honest_completeness`: every honest evaluation satisfies the equation.
- `feldman_vss_cheating_detection`: verification against these fixed commitments
  holds if and only if the supplied value equals `P(x)`; cancellation uses `g ≠ 0`.
- `feldman_vss_rejects_inconsistent_share`: an altered value is rejected.
- `commitment_lagrange_linear`: scalar commitment commutes with the two-node
  Lagrange combination, even for arbitrary supplied values.
- `feldman_vss_reconstruction_homomorphism`: for `x1 ≠ x2`, the Lagrange combination
  of honest share commitments equals `a0`. The proof reuses Shamir reconstruction.
- `feldman_vss_verified_reconstruction`: any two accepted shares at distinct
  coordinates reconstruct the committed polynomial's secret.
- `scalar_commitment_reveals_secret`: `a0 / g = secret`, explicitly documenting
  the absence of secrecy in this scalar model.

`FeldmanVSSFormalSuite` collects completeness, the verification equivalence,
commitment reconstruction, and reconstruction from accepted shares. Its instance
is `crypto_feldman_vss_master_suite`; the registry field is `CryptoFullSuite.feldman_vss`.

## Assumptions and limits

The commitments must be the same fixed pair for all participants. The theorems
cannot detect a dealer consistently publishing another polynomial, nor a dealer
sending different commitments to different participants. There is no reliable
broadcast or complaint/disqualification protocol here. No protocol termination,
robust reconstruction, or Byzantine agreement is proved.

Reconstruction needs distinct coordinates; it does not need nonzero coordinates.
A share at zero equals the secret. Cryptographic Shamir deployments use nonzero
participant coordinates, but this module proves algebraic consistency only.
No randomized sampling, hiding, finite cyclic group, discrete-logarithm hardness,
computational binding, or implementation security is modeled. Arbitrary thresholds
above two and distributed key generation are outside the scope. The scalar
reconstruction result is not proof of full Feldman VSS security. Novelty is not assessed.

## Verification

The module passed `verifier_skill.py verify` and `audit`, with source hashes
unchanged and only `propext`, `Classical.choice`, and `Quot.sound` dependencies.
See the [project validation record](../VERIFICATION.en.md) for complete-project checks.
