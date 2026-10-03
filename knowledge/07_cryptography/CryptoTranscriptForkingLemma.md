---
id: CryptoTranscriptForkingLemma
language: en
section: cryptography
source: Verification/CryptoTranscriptForkingLemma.lean
source_sha256: 8732acdc0702e7e6f5edff6e1942848307d0a21f727ea03cf2d72d0f7ce39792
novelty: not-assessed
status: reviewed
---

# CryptoTranscriptForkingLemma

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoTranscriptForkingLemma.lean)

## Finite experiment and exact counts

The counting model fixes a Boolean matrix `M : Ω → C → Bool`, with finite nonempty row type `Ω` and finite challenge-label type `C` of cardinality `q > 1`. A row represents fixed state before the challenge. Let `n = |Ω|` and let `aω = rowCount M ω` be the number of accepting labels in row `ω`.

`successCount` is `∑ ω, aω`. `forkCount` counts ordered accepting pairs with distinct labels in the same row, using `(accepted M ω).offDiag`. `row_fork_cast` and `fork_cast` express the exact real-valued count as `∑ ω, (aω² - aω)`. The fractions are

```text
ε     = successFraction M = (∑ ω, aω) / (n * q)
pFork = forkFraction M    = (∑ ω, (aω² - aω)) / (n * q²).
```

These are exact real ratios of finite counts. Their probability interpretation chooses a uniform row and then two independent uniform challenge labels with replacement, keeping the row fixed. Equal draws count as fork failure. The denominator is `n * q²`; this is neither sampling without replacement nor conditioning on a first acceptance. `successOutcomes`, `forkOutcomes`, their cardinality theorems, and `experiment_space_card` make the underlying finite spaces explicit. The module does not define a probability measure or randomized sampler.

## Lower bound and existence

`count_bound` applies the finite Cauchy–Schwarz inequality to row counts. `forking_elementary_bound` gives

```text
ε * (ε - 1 / q) ≤ pFork.
```

Nonnegativity and upper-bound lemmas place both fractions in `[0,1]` under the stated nonempty-space conditions. `fork_exists_of_positive` turns positive fork fraction into two distinct accepting labels in one row. `fork_exists_above_threshold` obtains such a fork when `ε > 1/q`. The threshold is strict: at or below it, the displayed lower bound need not be positive. These are existence and counting results, with no search procedure or runtime guarantee.

## Scalar extraction and matrix bridge

Over any `Field K`, `accepts G PK R c s` means `s * G = R + c * PK`. For two accepted equations sharing `R` and satisfying `c1 ≠ c2`, `forking_witness_extractable` proves

```text
extractWitness s1 s2 c1 c2 = (s1 - s2) / (c1 - c2)
extractWitness s1 s2 c1 c2 * G = PK.
```

This compatibility statement needs no assumption `G ≠ 0`. If additionally `PK = x * G` and `G ≠ 0`, `extracted_witness_eq` identifies the result with `x`. `extraction_matches_schnorr` connects the same expression to the existing real-valued verifier and `publicKey` in `CryptoSchnorrSignature`.

`transcriptMatrix` fixes a commitment `commitment ω` for each row and allows responses to depend on row and label. `transcript_fork_extracts` requires an injective encoding `challenge : C → K`, so distinct labels become distinct field challenges. `forking_matrix_extracts` combines this bridge with `ε > 1/q` to obtain an accepting pair and a compatible scalar witness. Arbitrary changing commitments or noninjective label encodings are not covered.

## Scope, sources, and dependencies

The definitions form a noncomputable finite specification and scalar algebra. No adaptive oracle-query execution, rewinding algorithm, runtime bound, ROM reduction, EUF-CMA theorem, distributional HVZK theorem, CSPRNG, or group discrete-logarithm hardness is formalized. Scalars do not hide a discrete logarithm: when `G ≠ 0`, the equation `PK = x * G` already determines `x = PK / G`.

[Bellare–Neven, §3, Lemma 1](https://cseweb.ucsd.edu/~mihir/papers/multisignatures.pdf) gives the general bound `acc * (acc / Qquery - 1 / |H|)`. Here `q` counts challenge labels, not oracle queries. This finite one-challenge matrix theorem is not that general theorem; no reduction or equivalence to it is formalized.

The direct project dependency is [`CryptoSchnorrSignature`](../../Verification/CryptoSchnorrSignature.lean); finite-set counting, Cauchy–Schwarz, and field arithmetic come from Mathlib. Mathematical novelty and priority of formalization are not assessed.

## Verification

The module passed `verify`, `audit`, and integration as `CryptoFullSuite.forking_lemma`. Strict build, `verify-all`, independent axiom audit, all 35 public tests without skips, and catalog checks passed. Compiler regressions cover exact counts, equality and strictness of the bound, the threshold boundary, extraction over ZMod 5, noninjective challenge encoding, and the combined matrix bridge. `ForkingLemmaFormalSuite` collects the bound, fork existence, extraction, and matrix bridge; its entry point is `transcript_forking_master_suite`. See the [validation record](../VERIFICATION.en.md).
