---
id: CryptoBulletproofsInnerProduct
language: en
section: cryptography
source: Verification/CryptoBulletproofsInnerProduct.lean
source_sha256: 43e397f8f36785b6f6941239963e9bc9919d65dff535fb334aab6f7df35f4207
novelty: not-assessed
status: reviewed
---

# Bulletproofs inner product algebra

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoBulletproofsInnerProduct.lean)

## Model and relation

For prime q, the scalar field is ZMod q. The theorems hold in any additive
commutative group A with a ZMod q module structure, hence in cyclic prime-order
group instances. No independence, nonzero or unknown-discrete-log assumption is
imposed on the indexed generators. `verification_suite.cyclic_model` reuses the
existing satisfiable Pedersen setup over ZMod q; this scalar instance is not a
cryptographically hard group.

`Vec k B` is exactly `Fin (2^k) → B`. The public relation is
P = sum a_i*G_i + sum b_i*H_i + (sum a_i*b_i)*U. `vector_commitment_bridge`
identifies each vector term with the existing vector Pedersen commitment API.
The actual dependency is named CryptoCommitmentVectorPedersenGroup.

## Executable protocol and proofs

`round_messages` constructs L from (a_lo,G_hi), (b_hi,H_lo), (a_lo,b_hi), and R
from the opposite cross terms. Contiguous halves preserve the original order.
Challenges have type `(ZMod q)ˣ`, excluding zero without a division-by-zero branch.
The fold uses a'=x*a_lo+x^-1*a_hi, b'=x^-1*b_lo+x*b_hi, with inverse weights on
G and H. `ipa_round_invariant` proves that the new relation equals
x²*L + P + x^-2*R. No claimed relation is embedded as a transcript hypothesis.

`prover` and `verifier` recurse on k, ending at one coordinate. The verifier
receives only U, G, H, P, verifier challenges and the proof, never the witnesses.
`ipa_completeness` proves acceptance for every honest input and every sequence of
unit challenges. `prover_first_message` proves independence of each round's first
message from that round's subsequent challenge. Challenge generation and network
interaction are external; no randomness or unpredictability theorem is asserted.

`weights_G` and `weights_H` expand products of challenge powers onto the original
2^k coordinates. `final_G_expansion` and `final_H_expansion` prove these expansions.
`batch_verifier` evaluates a multiscalar equation over those original generators
and the sum of round corrections. `ipa_batch_verification_equivalence` applies
to every transcript, including corrupt ones, not just outputs of the prover.

`ipa_proof_elements_count` counts the flattened payload: k rounds, 2k group
elements and two final scalars. Public parameters and verifier challenges are
excluded from this prover-message count. It is not a byte-size or running-time
bound; logarithmic communication does not imply logarithmic verifier work.

## Regressions and validation

Kernel examples and compiled execution cover k=0,1,2, nontrivial unit challenges,
zero vectors, explicit expanded weights, both verifier forms, first-message
independence, exact payload lengths, and selected corruptions of L, R and each
final scalar. Rejection examples use explicit parameters over ZMod 17; no general
claim that every alteration is rejected is made for dependent generators.

Module verify/audit and complete project validation are recorded in
`tools/validation_snapshot.json` and the validation record. Only propext,
Classical.choice and Quot.sound are allowed. No native-decide proof shortcut is used.

## Clean Water

Proved: algebraic folding, recursive perfect completeness, expanded verification
equivalence and exact element counts. These results are not a proof of knowledge.
Knowledge extraction via transcript trees, reduction of range constraints to IPA,
blinding/HVZK, Fiat-Shamir/ROM, adversarial security, concrete curves, serialization
and verified runtime bounds are outside scope. The basic IPA reveals final scalars;
zero knowledge is not inherited from the separate CDS range-proof module.
Python, JSON/SHA-256 and SimLab correspondence obligations remain open.
Scientific novelty is not assessed.

Reference: [Bünz et al., Bulletproofs, Section 3](https://eprint.iacr.org/2017/1066).

[`ipa_round_invariant`](../../Verification/CryptoBulletproofsInnerProduct.lean#L101) · [`ipa_completeness`](../../Verification/CryptoBulletproofsInnerProduct.lean#L143) · [`ipa_proof_elements_count`](../../Verification/CryptoBulletproofsInnerProduct.lean#L168) · [`ipa_batch_verification_equivalence`](../../Verification/CryptoBulletproofsInnerProduct.lean#L262) · [`verification_suite`](../../Verification/CryptoBulletproofsInnerProduct.lean#L316)
