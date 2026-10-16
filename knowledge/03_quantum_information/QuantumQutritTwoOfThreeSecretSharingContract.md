---
id: QuantumQutritTwoOfThreeSecretSharingContract
language: en
section: quantum-physics
source: Verification/QuantumQutritTwoOfThreeSecretSharingContract.lean
source_sha256: ecc47f4d1ab9732b87db5f36168421bdeb6fdbea49044747f30fd1dfe1d2b23a
novelty: not-assessed
status: reviewed
---

# Qutrit quantum secret sharing: two of three shares

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumQutritTwoOfThreeSecretSharingContract.lean)

## Encoding and tensor ordering

The logical space is C^3; the physical space is A tensor B tensor C, with
three qutrit shares. Flat indices use finProdFinEquiv twice, in ((A,B),C)
order. code is an explicit 27-by-3 matrix. Its columns satisfy code_column:

    J|s> = (1/sqrt(3)) sum_{r in Fin 3} |r, r+s, r+2*s>.

All label arithmetic is modulo 3. amplitude_star, amplitude_conj and
amplitude_sq establish conjugation and normalization; code_isometry proves
J†J=I_3. The sum specification is proved from the matrix definition.
This formalizes the existing Cleve–Gottesman–Lo construction; mathematical
or formalization priority is not assessed.

physicalIndex q maps the grouped (retained pair, lost share) basis to ABC:
q=0 loses A and retains BC; q=1 loses B and retains CA; q=2 loses C and
retains AB. physicalIndex_bijective verifies genuine permutations. regroup
acts on both matrix indices. regroup_encode connects physical encoded
matrices with groupedCode q. cyclic_code proves the code's cyclic symmetry.

## Single-share privacy and pair recovery

share q traces out the retained pair, leaving q. retainedPair q traces out
q. single_share and share_privacy prove for EVERY complex logical matrix X:

    share q (J X J†) = trace(X) mixedShare,    mixedShare = I_3/3.

mixedShare_density proves positivity and unit trace using module 182.
share_coherence kills every off-diagonal matrix unit with arbitrary complex
coefficient, so privacy is not limited to computational-basis inputs.

pair_recoverable applies erasure_correctability_equivalence from module 188.
Recovery is derived from the proved isometry and privacy, not assumed.
recoverySize q and pairRecovery q select a finite Kraus family from this
existence proof using Classical.choice. The type KrausChannel 9 3
(recoverySize q) includes completeness on the whole nine-dimensional input.
Module 175 supplies complete positivity, trace and density preservation.
pair_recovery proves R_q(retainedPair q (J X J†))=X for every complex X.
No executable gate decomposition or numerical decoder is produced.

single_share_not_recoverable excludes recovery from any single share for
EVERY finite number of recovery Kraus operators. It uses E_01: the singleton
channel sends it to zero whereas recovery would have to return E_01.
Together these results establish the two-of-three threshold. All three
shares suffice by discarding one before pair recovery; the formal core
statements quantify over singletons and their complementary pairs.

## External references and tests

reference_recovery applies module 187 through module 188: one selected R_q
works for all finite reference dimensions m and every joint complex matrix.
reference_share_independence identifies the complementary channel INCLUDING
encoding with Tr_logical(X) tensor I_3/3 after amplification. For joint
states this is the absence of correlations with an individual share.
maximally_entangled_recovery specializes to the normalized maximally
entangled logical qutrit and a three-dimensional reference.

Live regressions cover all three permutations and erasures, the explicit
modulo-3 code entries, complex coherences, Kraus completeness/CPTP, reference
dimensions, maximal entanglement, and all three singleton impossibilities.
Lean examples compile inside the selected Python unittest methods; the two
counts are reported separately.

## Clean Water and validation

This is one exact finite-dimensional (2,3) qutrit scheme with known erasure
location. General threshold families, active share substitution, approximate
correction, distribution protocols, executable decoders and physical
implementation are outside scope. Python, JSON/SHA-256 and SimLab obligations
remain open. No general threshold result follows solely from this example.

Public gamma release v0.5.87 exports private snapshot
330ea2350bae059cac7b546fb9d8748ccf4ae0ef. The previous public scoped release is
e24f559654d9edf3ded8949637cce8475512eb2c (v0.5.86). The last fully validated PUBLIC
baseline remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
Public-tree checks are recorded in [the release report](../../docs/release-v0.5.87.en.md).
Private evidence is not substituted for public validation; no new full-project
verify-all or full unittest result is claimed. The permitted axioms remain
propext, Classical.choice and Quot.sound.

Source: [Cleve, Gottesman and Lo, How to share a quantum secret](https://arxiv.org/abs/quant-ph/9901025), equation (1).
