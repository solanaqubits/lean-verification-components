---
id: CryptoSchnorrIdentification
language: en
section: cryptography
source: Verification/CryptoSchnorrIdentification.lean
source_sha256: ad11b94e5b5399adc1f7f24fbacef433d096ea72689e43b474f4a82ef2eb424b
novelty: not-assessed
status: reviewed
---

# Schnorr identification: finite groups and exact transcript laws

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoSchnorrIdentification.lean)

## Model and reuse

The module imports CryptoPedersenHomomorphicSum and reuses its Setup: prime q,
F = ZMod q, an abstract finite AddCommGroup G with Module F G, card G = q, and
nonzero generators. Only g is used; h plays no role. oneGeneratorSetup embeds
any valid one-generator group by setting h=g, so no second independent generator
or unknown generator relation is required. The prior real-scalar Schnorr and
Fiat-Shamir modules retain their APIs and source bytes.

Statement contains only the public X. Holds S P x states X = x • g.
Transcript contains (R,c,s), and Verify is s • g = R + c • X.
The honest prover computes R=r • g and s=r+c*x. The simulator takes only X,c,s
and computes R=s • g−c • X; it has no secret witness argument or witness lookup.
The extractor takes only two challenges and two responses.

## Checked contract

| Declaration | Result |
|---|---|
| schnorr_perfect_completeness | Every honest transcript is accepted for all x,r,c. |
| schnorr_special_soundness | Two accepting transcripts with the same R and distinct challenges yield c₁−c₂ ≠ 0 and X = ((s₁−s₂)/(c₁−c₂)) • g. |
| challenge_difference_inverse | (c₁−c₂)*(c₁−c₂)⁻¹ = 1 under distinct challenges. |
| extracted_witness_eq_secret | If X=x • g, the extracted scalar equals x, using the nonzero generator. |
| schnorr_hvzk_simulator_valid | Every simulated transcript is accepted for any public X. |
| schnorr_hvzk_distribution | For each fixed c and valid statement X=x • g, the full real and simulated transcript PMFs are identical. |
| schnorr_hvzk_pairs | The joint laws of (R,s) are identical as a corollary. |
| schnorr_hvzk_independent_challenge | Equality extends to any fixed challenge PMF independent of the nonce, including uniform challenges. |
| real_support_iff / simulated_support_iff | Support is exactly the accepting transcripts with challenge c. |
| statement_has_unique_witness | Every public group element has a unique witness, derived from prime-order setup, not assumed by a statement field. |

realLaw samples r uniformly over all F. simulatedLaw samples s uniformly over
all F. The response map r ↦ r+c*x is an explicit equivalence with inverse
s ↦ s−c*x. Reusing the uniform-pushforward theorem proves equality of the
entire correlated transcript, not merely acceptance or equal marginals.
honestInteractionLaw samples r first, then the independent verifier challenge;
simulatedInteractionLaw samples the challenge first and then runs the simulator.
The equality is proved by commuting independent PMF draws and using the
fixed-challenge theorem. No assumption of that equality is stored in Setup.

The master suite quantifies all valid group setups, packages the results and
includes the existing constructive setup witness over ZMod q. Zero secrets,
zero challenges, zero nonces and q=2 are admitted. Uniform sampling includes zero.
This is the stated full-field additive convention, not a mechanical verification
of every parameter convention or preprocessing procedure in the original paper.

## Regression boundaries and Clean Water

Tests retain arbitrary prime q and abstract group G and check the full joint law,
independent random challenges, exact support and unique witnesses. Concrete tests
exercise q=5 extraction, q=2, invalid responses and zero inputs. Equal-challenge
accepting transcripts can give an incorrect extractor; different commitments
also invalidate extraction despite distinct challenges. The tests make both
soundness hypotheses necessary rather than hiding them in prose.

Special soundness here is algebraic extraction from two supplied transcripts.
It does not provide an adversarial rewinding algorithm, an impersonation bound,
a PPT model, a security parameter, polynomial runtime, or DLOG hardness.
Perfect special HVZK covers fixed challenges and independent honest-verifier
challenge distributions; challenge selection depending on R is not covered.
General malicious-verifier zero knowledge, random oracles, Fiat-Shamir signatures,
concurrent composition, side channels and concrete curve/RNG implementations are
not modeled. PMFs are mathematical distribution semantics, not a verified random
sampler implementation. Python, JSON/SHA-256 and SimLab linkage remain open.
Scientific novelty is not assessed.

Reference: C. P. Schnorr, *Efficient Signature Generation by Smart Cards*, 1991,
[paper](https://mit6875.github.io/PAPERS/Schnorr-POK-DLOG.pdf),
[DOI](https://doi.org/10.1007/BF00196725).
[Commands and source hashes](../../tools/validation_snapshot.json).

## Historical source-side validation

Base snapshot: `2c01798362d54124a711be83a0855e40dbf0efdc`.

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 123 |
| Lean files under Verification/ | 163 top-level + 2 support = 165 |
| Root-inclusive byte-identical export | 166 sources |
| Clean strict private build | 3614 jobs; no warnings |
| Both full axiom audits | 13805 declarations; no violations |
| Private live tests | 71; no failures or skips; 255.206s |
| Export live tests | 68; no failures or skips; 269.391s |
| Export clean strict build | 3614 jobs; no warnings |

Module verify and audit each covered 193 declarations in the imported project closure,
including the reused Pedersen module. Both full audits permit only propext,
Classical.choice and Quot.sound. Independent auditor source is pinned to
46024e005996495c65ef609368e11ab39c4222e3; executable SHA-256:
8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: v4.33.1. Auditor source toolchain file: v4.32.0-rc1;
the executable is pinned separately. The registry hook passed as an additional
check; no second independent proof kernel is asserted. Counts include generated
declarations. Both project build directories started empty, with isolated caches
of pinned dependencies. Integration is idempotent. Earlier subject proof files
are unchanged. Original workspace HEAD and 406 tracked files outside simulations/
are preserved. This task makes no writes to simulations/ and no public release.

## Public release validation

The separate [v0.5.21 report](../../docs/release-v0.5.21.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 123 |
| Lean files under Verification/ | 163 top-level + 2 auxiliary = 165 |
| Root-inclusive sources identical to the private snapshot | 166 |
| Clean strict build | 3614 jobs; no warnings |
| Complete verifier audit | 13805 declarations; no violations |
| Pinned independent full audit | 13805 declarations; no violations |
| Public live tests | 68; no failures or skips; 257.020s |
