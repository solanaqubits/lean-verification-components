---
id: QuantumKnillLaflammeRecoveryNecessity
language: en
section: quantum-physics
source: Verification/QuantumKnillLaflammeRecoveryNecessity.lean
source_sha256: 6f78cb1e118d4eae0e87a2586ae811a835c60f8c99dbc58181561f7df7720042
novelty: not-assessed
status: reviewed
---

# Necessity of Knill-Laflamme conditions and exact recovery criterion

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumKnillLaflammeRecoveryNecessity.lean)

## Exact scope and inputs

For E : KrausChannel d e r, encoding J : Matrix (Fin d) (Fin k) C, k>0 and
J†J=I_k, recovery is an arbitrary R : KrausChannel e k s. The size s is independent
of r and is existentially quantified by `Recoverable E J`.
`ExactRecovery E J R` means R(Phi_E(J X J†))=X for EVERY complex logical matrix X.
No scalar composite, coefficient matrix, spectral data, environment independence
or particular construction of R is assumed.

`recovery_necessity_equivalence` proves

    Recoverable E J <-> exists Lambda, StandardKnillLaflamme E J Lambda.

`recovery_environment_equivalence` and its density variant prove equivalence
with existence of sigma such that Phi^c(J X J†)=trace(X) sigma for every X.
The density variant additionally states sigma is positive semidefinite and has
unit trace. For density inputs the environment is consequently the same sigma.
This is a finite-dimensional exact criterion for the stated Kraus-channel model.

## Scalar Kraus lemma, proved from matrix units

`identity_entry` applies an identity Kraus sum to matrix units E_pq and extracts
entries. For each fixed operator, `identity_offdiagonal` uses nonnegativity of
squared complex norms to derive all off-diagonal entries are zero.
`identity_diagonal` uses pairings from E_aa, E_bb and E_ab: the sum of
normSq(F_t(a,a)-F_t(b,b)) is zero, hence each difference is zero.
`identity_kraus_scalar` concludes F_t=c_t I_k with c_t=F_t(0,0).
The index 0 exists because k>0. The lemma works for any finite indexed family
and needs only its identity-channel action, not an assumed scalar decomposition.

`composite_action` expands the two channels and encoding into the Kraus family
F_(mu,a)=R_mu E_a J. `lemma_composite_scalar` applies the identity lemma and
sets c_(mu,a) to the logical (0,0) entry. `knill_laflamme_necessity` uses the
FULL recovery completeness sum_mu R_mu†R_mu=I_e, yielding

    J† E_a† E_b J = (sum_mu conj(c_(mu,a)) c_(mu,b)) I_k.

`recoveredCoefficients` uses this exact conjugation order. Necessity itself
needs k>0 and exact recovery; J's isometry is only required in the stated
bidirectional criterion. `recovered_coefficients_unique` proves the Gram
coefficients equal any supplied coefficient matrix satisfying the same equations.

## Composition and counterexample

The reverse direction constructs GeneralCode and invokes module 185's spectral
recovery, with one possible family size r+e. This does NOT restrict the arbitrary
recovery in the necessity direction. Module 182 provides the environment bridge
with sigma=Lambda^T. `dephasing_not_recoverable` uses its proved distinction of
basis-state environments to rule out recovery of the FULL qubit after complete
dephasing, for every possible finite recovery Kraus count. No claim is made that
every subcode of a dephasing channel is uncorrectable.

## Regressions

The complex non-diagonal example from module 185 is recovered; necessity then
reconstructs the original coefficient matrix, including imaginary entries
+84i/625 and -84i/625. Tests quantify arbitrary alternative recovery counts and
operators as well as the concrete constructed recovery. Complex off-diagonal
logical matrices, zero and repeated weights, rectangular C^2 -> C^4 channels,
full completeness I_4, fixed density environments and identity channels are covered.
Dephasing regressions reject recovery, Knill-Laflamme coefficients and a fixed
density environment. Lean examples are compiled inside targeted Python unittest
wrappers; their counts are not additional independent runs.

## Clean Water and validation

Both necessity and sufficiency are proved for finite-dimensional exact recovery
in the specified Kraus-channel and isometric-code model. The environment identity
and recovery hypothesis are quantified over all complex matrices. No executable
numerical decoder, approximate/asymptotic correction, fault-tolerance threshold,
physical noise correspondence or physical implementation is certified.
Classical spectral construction is inherited from module 185. General dilation
minimality/uniqueness, quantum capacity, remaining Bulletproofs protocol
extraction/security, Tendermint reference acquisition/slashing, Python,
JSON/SHA-256 and SimLab remain separate obligations. Novelty is not assessed.

Public gamma release v0.5.84 exports private snapshot
23becc8e3952239aa0142d72c97c530d3442c4b2. The previous public scoped release is
0b41b074d540b0d23a18823235e713d00bac7b04 (v0.5.83). The last fully validated PUBLIC
baseline remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
Public-tree checks are recorded in [the release report](../../docs/release-v0.5.84.en.md).
Private evidence is not substituted for public validation; no new full-project
verify-all or full unittest result is claimed. The permitted axioms remain
propext, Classical.choice and Quot.sound.

Background: [Knill and Laflamme, A Theory of Quantum Error-Correcting Codes](https://arxiv.org/abs/quant-ph/9604034).
