---
id: QuantumErasureCorrectabilityContract
language: en
section: quantum-physics
source: Verification/QuantumErasureCorrectabilityContract.lean
source_sha256: cc9de3d7ee7e983943d83d32415c90bd75f05d9729e3ff5e1e2546217cae4023
novelty: not-assessed
status: reviewed
---

# Exact subsystem erasure correction and independence of the lost part

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumErasureCorrectabilityContract.lean)

## Fixed tensor split and input contract

The physical space is A tensor B with dimensions a,b. The flat Fin (a*b) index
is identified with Fin a × Fin b by finProdFinEquiv, A first, B second.
The code is J : Matrix (Fin (a*b)) (Fin k) C, with k>0 and J†J=I_k.
Erasing the specified B means tracing out B and retaining A. Tr_A instead
retains the lost subsystem B. Neither output is a conjugate-space surrogate.

The model fixes the erased factor in advance. It has no probabilistic erasure
flag and does not infer an unknown error location. Recoveries are arbitrary
KrausChannel a k s, with their finite Kraus count s independently quantified.

## Channel construction and exact complement

pair uses finProdFinEquiv. erasureOperator a b j has entries

    K_j(i,x) = if pair(i,j)=x then 1 else 0.

These are precisely I_A tensor <j|_B. erasure_complete proves sum_j K_j†K_j=I
by resolving both physical indices into their tensor factors. erasureChannel
packages the proved completeness. Its CPTP and density-preservation properties
reuse module 175. traceB is existing partialTrace after toProduct; traceA is
existing partialTrace_system after the same reindexing.

erasure_apply proves Phi_E(Y)=traceB(Y) for every complex physical matrix Y.
erasure_complement proves Phi_E^c(Y)=traceA(Y) for the declared Kraus ordering,
with no transpose or conjugation of the B output. Complex off-diagonal regression
entries distinguish this statement from an incorrectly transposed complement.

## Correctability and external references

ErasureRecoverable J means exists s,R, forall complex logical X,
R(traceB(J X J†))=X. erasure_correctability_equivalence proves, for k>0 and
isometric J, equivalence with

    exists sigma : Q b, Density sigma and
    forall X : Q k, traceA(J X J†)=trace(X) sigma.

Both implications reuse module 186 with the explicitly constructed erasure
channel and the two trace bridges. Existence of R, independence of B and the
coefficient matrix are not simultaneous input assumptions.

erasure_reference_recovery invokes module 187: the SAME R recovers every joint
complex matrix for every finite reference dimension m. erased_reference_independence
derives a density sigma with amplify(Phi_E^c composed with encoding J)(X)
=Tr_logical(X) tensor sigma. The complementary map includes encoding. For joint
density inputs this states that the reference and erased B have a product state.

## Explicit examples and counterexample

fixedCode k v=K_v† encodes |psi> as |psi> tensor |v>. Its isometry and
traceB(J X J†)=X are proved for every X; recovery is the identity channel.
Tests include k=2,b=3 and complex logical coherences.

entangledCode encodes a logical qubit together with the fixed auxiliary pair
(3/5)|00>+(4/5)|11>. A consists of the logical qubit and the retained auxiliary
qubit (dimension 4); B is the other auxiliary qubit (dimension 2). The flat
rows are 000,...,111: code column 0 has entries 3/5 at 000 and 4/5 at 011;
column 1 has entries 3/5 at 100 and 4/5 at 111. Isometry is proved.
Recovery is explicitly erasureChannel 2 2 on A, tracing its auxiliary factor.
entangledCode_recovery holds for every complex logical X. The lost state is
mixedLost=diag(9/25,16/25); its density property and failure of idempotence
are proved. Thus the example does not reduce to an unused pure B factor.

repetitionCode maps |0> to |00>, |1> to |11>. It is isometric, but
repetition_survivor equals full logical dephasing. In particular E_01 is sent
to zero. Module 186 excludes exact recovery for EVERY finite recovery Kraus
count. Tests also reject fixed density environments and Knill-Laflamme
coefficients. No impossibility for all smaller subcodes is asserted.

Regressions exercise CPTP properties, trace preservation, complex complementary
entries, the three codes, Bell/reference recovery, and reference/B factorization.
Lean assertions run inside the selected Python unittest wrappers; their counts
are separate from the number of unittest methods.

## Clean Water and validation

This proves exact finite-dimensional correctability for a specified tensor split
and known erased subsystem. Unknown error locations, stochastic erasure with
flags, approximate correction, general threshold quantum secret sharing,
numerical decoders and physical implementation remain outside scope.
The relation to secret sharing is motivation, not a threshold-scheme theorem.
General dilation minimality/uniqueness, quantum capacity, remaining Bulletproofs
protocol extraction/security, Tendermint reference acquisition/slashing, Python,
JSON/SHA-256 and SimLab remain separate obligations. Novelty is not assessed.

Public gamma release v0.5.86 exports private snapshot
edc9fadd245c6da61c333448cb5211daac76a9ae. The previous public scoped release is
6a73333e0d1a4af1a14f02461e9370808fd13043 (v0.5.85). The last fully validated PUBLIC
baseline remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
Public-tree checks are recorded in [the release report](../../docs/release-v0.5.86.en.md).
Private evidence is not substituted for public validation; no new full-project
verify-all or full unittest result is claimed. The permitted axioms remain
propext, Classical.choice and Quot.sound.

Background: [Cleve, Gottesman and Lo, How to share a quantum secret](https://arxiv.org/abs/quant-ph/9901025).
