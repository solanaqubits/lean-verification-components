---
id: QuantumQutritSecretSharingExplicitDecoder
language: en
section: quantum-physics
source: Verification/QuantumQutritSecretSharingExplicitDecoder.lean
source_sha256: fa7f46e47baea5f6c7c1f02f8bdce1bfbd517a7767826350c99939b267fa0447
novelty: not-assessed
status: reviewed
---

# Explicit unitary decoder for qutrit two-of-three secret sharing

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumQutritSecretSharingExplicitDecoder.lean)

## Explicit permutation and tensor convention

This module uses the fixed 27-by-3 code and cyclic regroupings of module 189.
q=0 retains BC and loses A; q=1 retains CA and loses B; q=2 retains AB and
loses C. Each pair has dimension 9, with finProdFinEquiv ordering.

    D|u,v> = |v-u,2v-u>,    (s,t) -> (t-2s,t-s)

All arithmetic is in Fin 3. decodeCoordinates and encodeCoordinates are
proved mutual inverses. decoderEquiv packages the explicit finite bijection.
decoder is its permutation matrix: entry (y,x) is 1 iff y=decoderEquiv x.
decoder_basis fixes the column-action convention. Both D†D=I_9 and DD†=I_9
are proved directly. No spectral certificate or chosen recovery defines D.

## Full-state factorization

liftedDecoder is D tensor I_3 in the flat ((logical,auxiliary),lost) order.
separatedCode has entries amplitude when logical output equals logical input
and the auxiliary and lost labels agree, and zero otherwise. Thus its columns
are |s> tensor |Omega_3>, with the normalized maximally entangled state from
module 187. decoder_code proves liftedDecoder * groupedCode q=separatedCode
for all three erased positions.

factorized X represents X tensor |Omega_3><Omega_3| with explicit associative
indexing. separated_factorization and decoding_factorization prove the full
matrix identity for every complex logical X, including off-diagonal matrices.
The result preserves coherence and separates the secret from a fixed auxiliary
pair; it does not measure individual shares.

## Three Kraus operators and exact recovery

recoveryOperator t = erasureOperator 3 3 t * decoder = (I_3 tensor <t|)D.
recovery_complete proves sum_t R_t†R_t=I_9 from the partial-trace completeness
and D†D=I. explicitRecovery is KrausChannel 9 3 3 with exactly three specified
operators. The existing module 175 supplies complete positivity, trace
preservation and preservation of density matrices on the entire input space.

recovery_branch establishes R_t E_w J_q = delta_tw amplitude I_3 for each
syndrome and erased-basis index. Summing these branches yields explicit_recovery
for all complex X and all q. The new construction does not call Classical.choose
to select recovery operators. Classical.choice can still occur among dependencies
of proofs; no reduction of the project's permitted axiom set is claimed.

explicit_reference_recovery lifts the same explicit decoder to every finite
reference dimension through modules 188 and 187. agrees_with_pairRecovery
compares actions on the encoded pair inputs with the previously chosen recovery
of module 189. Equality of the two channels on arbitrary pair inputs is not
asserted. Tests include complex coherences, every erased position, CPTP,
syndrome branches and maximally entangled qutrit/reference inputs.

## Clean Water and validation

This is a finite algebraic decoder for the specific exact (2,3) qutrit scheme.
Executable numerical simulators, hardware realizations, robustness to noise,
active share substitution and general threshold families are outside scope.
Python, JSON/SHA-256 and SimLab obligations remain open. Novelty is not assessed.

Public gamma release v0.5.88 exports private snapshot
98c20f1755dc36138a2e7394e4473864328c5059. The previous public scoped release is
066c91704b4bad5e6b0bf440a6d204d930197b27 (v0.5.87). The last fully validated PUBLIC
baseline remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
Public-tree checks are recorded in [the release report](../../docs/release-v0.5.88.en.md).
Private evidence is not substituted for public validation; no new full-project
verify-all or full unittest result is claimed. The permitted axioms remain
propext, Classical.choice and Quot.sound.

Background: [Cleve, Gottesman and Lo, How to share a quantum secret](https://arxiv.org/abs/quant-ph/9901025).
