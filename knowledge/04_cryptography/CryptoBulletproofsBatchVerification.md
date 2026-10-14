---
id: CryptoBulletproofsBatchVerification
language: en
section: cryptography
source: Verification/CryptoBulletproofsBatchVerification.lean
source_sha256: 15067d3969cbe769b9949b313c6c4ba672f5750ac1b35ba2ac4eb2989aa18c0e
novelty: not-assessed
status: reviewed
---

# Bulletproofs batch verification with uniform field weights

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoBulletproofsBatchVerification.lean)

## Model and public verifier

The batch has m proofs with common dimension n=2^k and common public generators
B,Hblind,U,G,H over a prime field ZMod q. All theorems hold for any additive
commutative group with a ZMod q module structure, and hence for cyclic prime-order
groups. No independence of generators, injectivity of commitments, or discrete
logarithm hardness is assumed. The suite includes a satisfiable cyclic model.

`ProofInstance` stores public V, external y,z,x and unit IPA challenges, and the
unchanged `RangeReductionTranscript` from module 159. Residuals are calculated
from these public data, not supplied as trusted certificates.
`polynomial_residual` is
 tx*B+taux*Hblind-(z^2*V+delta(y,z)*B+x*T1+x^2*T2).
`inner_product_residual` subtracts the expanded final IPA expression from the
corrected range target plus all round corrections of module 158.

`individual_verify` adds an explicit x != 0 guard to the existing range verifier.
Module 159 itself permits x=0; this wrapper does not change its API or silently
claim equivalence to that less restrictive verifier. It requires y != 0 and x != 0;
IPA challenges are already nonzero by their unit type. `individual_iff_residuals_zero`
proves exact equivalence of this wrapper to those guards and both zero residuals,
for every transcript, including maliciously constructed ones. Guards are checked
deterministically even when all random weights happen to be zero.

## Finite probability theorem

`residual_vector` places the m polynomial residuals first and the m IPA residuals
second, preserving all occurrences. `batch_residual_sum` computes their weighted
sum. `verify_batch` checks all guards and equality of that sum to zero.
`batch_protocol_completeness` proves acceptance for every weight vector if all
individual verifications accept. Honest completeness is connected directly to
module 159 by `honest_individual_completeness`.

`acceptance_probability` uses the actual PMF.uniformOfFintype on the full function
space Fin N -> ZMod q, including zero coefficients. Its event probability is
expressed by the PMF's outer measure, avoiding irrelevant measurable-space
choices on this finite domain. This is the uniform product distribution: all
q^N vectors are equiprobable. The batch, statements and all existing protocol
challenges are fixed before this fresh vector is sampled. The result does not
cover adversaries selecting a batch after observing its weights.

`accepting_pivot_unique` fixes a nonzero residual D_j. Equal weights away from j
and two accepting sums force the remaining weights to be equal, because scalar
multiplication into a nonzero vector is injective over a field. Restriction away
from j therefore injects accepting vectors into q^(N-1) assignments.
`accepting_card_bound` proves the count, and `batch_soundness_error_bound` converts
it to probability <= 1/q. `batch_protocol_soundness` includes guard failures:
any fixed batch with an individually rejected proof has acceptance probability
at most 1/q. This is a comparison to individual verification, not range-proof
knowledge soundness. No claim is made that every false range statement necessarily
produces nonzero residuals.

## One explicit MSM

`SharedIndex` enumerates B,Hblind,U and each original G_i,H_i. `LocalIndex` enumerates
V,A,S,T1,T2 and all L,R points for each proof. `msm_coefficients` sums coefficients
on shared bases across proofs. For polynomial weight u and IPA weight w, those
coefficients include u*(tx-delta) on B, u*taux-w*mu on Hblind,
w*(tx-a_final*b_final) on U, w*(-z-a_final*weights_G_i) on G_i, and
w*(z*y^i+z^2*2^i-b_final*weights_H_i)*(y^-1)^i on the original H_i.
All coefficients on proof-specific points are also explicit.
`weighted_residual_expansion` and `msm_rearrangement_equiv` prove exact equality
with the sum of weighted residuals, without honesty hypotheses.
`verify_batch_msm_equiv` connects the executable single-MSM checker to the
residual checker. Common bases occur once in its index; no optimized curve backend
or complexity model is asserted. Original IPA transcripts are preserved; this
operation creates neither a new IPA nor a shorter transmitted proof.

`batch_joint_permutation_invariance` permutes proof data together with both of
its coefficient coordinates. An arbitrary proof permutation with fixed weight
positions is not claimed to preserve the result.

## Regressions and counterexamples

Kernel regressions and compiled runs cover empty and singleton batches, n=1,2,4,
honest multi-proof batches, nontrivial y scaling, zero-y and zero-x rejection,
zero weights on a bad proof, damaged T1 and tx, and equivalence of the two checkers.
For two concrete corrupted single proofs over ZMod 17, full enumeration of 289
weight vectors gives exactly 17 acceptances each. Those examples witness the
sharpness of 1/q; they do not replace the general PMF theorem.
Equal fixed weights cancel residuals D,-D. Independence from the batch alone is
insufficient if weights are mutually dependent. Independent uniform sampling
across all coordinates is the distribution covered by the theorem.
`altered_T1_batch_error_bound` proves the general bound for replacing one honest
polynomial commitment T1 by T1+D when D != 0 and x != 0. Arbitrary syntactic changes
need not alter verification equations in groups with dependent generators.

## Validation and Clean Water

Source reference snapshot: 3ae1fc1bffa43c957cdabaf661e375f4f99580b4.
Actual verification results and source digests are recorded in
[the validation record](../VERIFICATION.en.md) and tools/validation_snapshot.json.
Allowed axioms are propext, Classical.choice, Quot.sound. No native-decide proof
shortcut, custom axiom or assumed zero-residual certificate is used.

Proved: exact individual residual characterization, deterministic guards,
perfect batching completeness, finite-uniform error bound, public MSM expansion,
paired permutation invariance and explicit cancellation/corruption cases.
Excluded: witness extraction, special soundness of Bulletproofs, computational
binding/DLOG security, HVZK, Fiat-Shamir/ROM, implementation of a CSPRNG, concrete
curves, serialization, and MSM speed or side-channel guarantees.
Python, JSON/SHA-256 and SimLab correspondence obligations remain open.
Scientific novelty is not assessed.

Sources: [Bünz et al., Bulletproofs](https://eprint.iacr.org/2017/1066) and
[Dalek verification equations and MSM combination](https://github.com/dalek-cryptography/bulletproofs/blob/main/docs/range-proof-protocol.md).

[`individual_iff_residuals_zero`](../../Verification/CryptoBulletproofsBatchVerification.lean#L131) · [`accepting_card_bound`](../../Verification/CryptoBulletproofsBatchVerification.lean#L53) · [`batch_soundness_error_bound`](../../Verification/CryptoBulletproofsBatchVerification.lean#L74) · [`batch_protocol_soundness`](../../Verification/CryptoBulletproofsBatchVerification.lean#L188) · [`msm_rearrangement_equiv`](../../Verification/CryptoBulletproofsBatchVerification.lean#L272) · [`honest_individual_completeness`](../../Verification/CryptoBulletproofsBatchVerification.lean#L293) · [`batch_joint_permutation_invariance`](../../Verification/CryptoBulletproofsBatchVerification.lean#L307) · [`altered_T1_batch_error_bound`](../../Verification/CryptoBulletproofsBatchVerification.lean#L344) · [`verification_suite`](../../Verification/CryptoBulletproofsBatchVerification.lean#L399)
