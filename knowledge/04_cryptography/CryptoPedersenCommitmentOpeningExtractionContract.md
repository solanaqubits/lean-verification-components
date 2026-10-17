---
id: CryptoPedersenCommitmentOpeningExtractionContract
language: en
section: cryptography
source: Verification/CryptoPedersenCommitmentOpeningExtractionContract.lean
source_sha256: ec5ea7f608ec280fa36d846065f9c32c08ff7cb251f3b46b02f35a5b6f6888be
novelty: not-assessed
status: reviewed
---

# Two-branch extraction of Pedersen openings

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoPedersenCommitmentOpeningExtractionContract.lean)

## Proven interface

Module 193 proves deterministic special soundness of a linear representation
protocol. A transcript stores the public statement, announcement, challenge and
response, not the original secret. For a linear map L : W -> A, two accepted
transcripts for the same C and announcement, with distinct field challenges,
give w = (x1-x2)^(-1) * (z1-z2) and L(w)=C. Neither randomness, nonzero individual
challenges, generator independence nor an unknown discrete logarithm is assumed.
The formula itself is total; correctness requires a nonzero challenge difference.

scalarMap and vectorMap specialize this theorem to scalar and vector Pedersen
commitments over ZMod q, q prime. Coordinate lemmas identify the displayed division
formulas. vector_soundness uses the existing commit_vec; scalar_existing_commit
identifies the existing scalar commitment. No real-number surrogate is used.

checked_extract rejects statement mismatch, announcement mismatch, equal
challenges and invalid responses in that order. checked_extract_success_iff
states its exact acceptance conditions; checked_extract_sound proves its output
opens C. No equality decision on the witness type is required by the checker.

honest_extracts returns the original witness only for honestly constructed
responses with a common mask. honest_mask_independent quantifies over arbitrary
common masks. Arbitrary accepted forks guarantee a valid opening, not a unique
or historically original opening. collision_extracts_dlog reuses the existing
prime-order Setup and dlog_extraction_from_collision: distinct colliding pairs
imply distinct blindings and H=((v1-v2)/(gamma2-gamma1))*G. This is an algebraic
identity, not a computational binding-security theorem. The general extraction
core does not require the stronger nonzero-generator assumptions of this lemma.

## Conditional bridge to module 178

OpeningForks supplies three separate two-branch representation proofs: two for
vector commitments Ac and Sc, one for the scalar V. Each pair shares its own
announcement; the pairs need not share a mask or challenge. extractCertificate
computes all a,b,s,t,alpha,rho,v,gamma fields with explicit formulas.
extracted_certificate_valid proves ValidOpenings for the actual Ac,Sc,V.
range_extraction_from_opening_forks then invokes module 178's extraction_soundness,
retaining ValidFamily, 2^(2^k)<q, and the RangeWitness OR nontrivial-generator-relation
result. No bit/range property of the extracted openings is assumed.

These extra representation-protocol transcripts are explicit inputs. They are
NOT fields extracted from the original Bulletproofs TranscriptFamily. This closes
a conditional algebraic construction of the certificate, not the complete
protocol-level obligation to obtain openings from the original prover.

## Regressions

Independent numeric scalar and vector transcripts over ZMod 7 exercise exact
expected values, reversed branch order, a zero challenge, nonzero masks and
empty vectors. Negative cases cover repeated challenges, substituted statements
and announcements, damaged responses and an incorrect denominator sign.
Dependent generators demonstrate nonunique openings; zero generators are allowed
only in the general algebraic core. Concrete extraction over ZMod 101 constructs
all three openings and composes with a genuine accepting range family for value 3.
Kernel proofs and executable scenarios are counted separately from unittest.
No native_decide shortcut is used.

## Clean Water and validation

Permitted axioms: propext, Classical.choice, Quot.sound. Explicit extraction does
not use Classical.choose; this does not claim all imported proofs are constructive.
No rewinding algorithm, General Forking Lemma, expected/PPT runtime bound, random
oracle or Fiat-Shamir security, HVZK, byte parser or deployed Bulletproofs
implementation equivalence is proved. Existing elementary finite-matrix forking
results are not a substitute for that missing protocol connection. Perfect hiding
and computational binding are separate properties, not consequences claimed here.
Python equivalence, JSON/SHA-256 and SimLab obligations remain open. Novelty is not
assessed.

Hierarchy: epsilon 193, cryptography/pedersen-opening-extraction, direction
cryptography. Parent private snapshot: 92193b9a12359197dd9f0ac5c5d573f90bbc11a5.
Historical beta 7 remains unchanged. Public scoped checks and measured counts
are recorded separately in the final-tree evidence and annotated release tag.
The preceding full public basis remains v0.7.1; private evidence is separate.
