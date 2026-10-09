---
id: PhotonicsHongOuMandelInterference
language: en
section: quantum-physics
source: Verification/PhotonicsHongOuMandelInterference.lean
source_sha256: 1501e6f001508e641eb0c91a07e34183cb739d58112d20f06838dfb64d6ce3bf
novelty: not-assessed
status: reviewed
---

# Hong–Ou–Mandel interference in the normalized two-photon sector

[Section](../quantum-physics/README.md) · [Lean](../../Verification/PhotonicsHongOuMandelInterference.lean)

## Model and construction

For 0≤T≤1, R=1−T, the imported complex splitter is B=[[√T,i√R],[i√R,√T]].
The occupation basis is ordered |2,0⟩, |1,1⟩, |0,2⟩. A state is a vector Fin 3 → ℂ;
Fin 3 itself indexes the basis. The normalized polynomial representation is
v20 x²/√2 + v11 xy + v02 y²/√2. The theorem symmetric_square_substitution proves
that symmetricSquare A acts by substitution of the two linear mode expressions
for every complex 2×2 matrix A. Thus the two-photon lift is derived from the
single-mode matrix with the factorial normalization; its probabilities are not
postulated scalar formulas. This finite homogeneous-polynomial model represents
creation monomials on the vacuum, without constructing an infinite Fock space
or proving canonical commutation relations.

Writing k=i√(2TR), the derived matrix is
U_two_photon=[[T,k,−R],[k,T−R,k],[−R,k,T]]. Both U†U=I and UU†=I are proved,
as is preservation of the sum of squared complex moduli for arbitrary input vectors.

## HOM output and probabilities

The actual matrix output on |1,1⟩ is (i√(2TR), T−R, i√(2TR)).
Outcome probabilities are defined by Complex.normSq of these components:
P20=2TR, P11=(2T−1)², P02=2TR. Each is in [0,1] and their sum is one.
At T=1/2 the exact state is (i/√2)(|2,0⟩+|0,2⟩) and P11=0.
This assumes indistinguishable modes and the stated preparation and lossless optics.
The Born-rule interpretation is the modeling link to measurement.

## Phase convention bridge

The imported real transformation uses A_real=[[t,−r],[r,t]]. With D=diag(1,i),
B=D A_real D†. The induced occupation gauge Q=diag(1,i,−1) is unitary and
U_two_photon=Q symmetricSquare(A_real) Q†. The real lift equals the existing
QuantumBeamSplitterTransform.twoPhotonTransform after embedding coordinates into ℂ.
For arbitrary inputs, comparison rephases the input as well as the output:
|U(Qv)_j|²=|symmetricSquare(A_real)v_j|². For |1,1⟩ the input rephasing is only
a global factor i, so all three outcome probabilities coincide directly.

## Distinguishable reference and HOM visibility

The reference model retains two particle labels. Its four ordered output weights
are w(j,k)=|B(j,0)|² |B(k,1)|². They are nonnegative, sum to one and factor as the
product of their actual marginal distributions. Coincidence is the disjoint event
j≠k, giving P_dist=T²+R²≥1/2>0. Independent alternatives are added as probabilities.

HOM visibility is defined with this reference denominator:
V_HOM=(P_dist−P11)/P_dist=2TR/(T²+R²). It lies in [0,1] and equals one exactly
when T=1/2. This is not a definition using an intensity maximum-plus-minimum
denominator. No time-delay scan is constructed by this theorem.

## Theorems and regressions

Main results: symmetric_square_substitution, two_photon_unitary,
two_photon_norm_preserved, hom_output_state_exact, hom_probabilities_exact,
hom_prob_normalization, hom_balanced_bunching, phase_convention_bridge,
hom_real_convention_probabilities, labeled_weight_independence,
hom_distinguishable_baseline and hom_visibility_exact.
Master theorem: photonics_hong_ou_mandel_master_suite.

Kernel regressions cover arbitrary input vectors and normalized substitution,
the exact balanced state, all three real-convention probabilities, the rephased
generic input bridge, normalized independent reference weights, T=0 and T=1,
and T=1/4: (P20,P11,P02)=(3/8,1/4,3/8), P_dist=5/8, V_HOM=3/5.
At T=1/2 the distinguishable reference is 1/2, while the indistinguishable coincidence is zero.

## Clean Water

These are ideal finite-mode algebraic results. Temporal wave packets, delay τ,
spectral overlap, the shape and width of a time-dependent HOM dip, partial
distinguishability, detector jitter, photon losses and hardware implementation
are not modeled. The reference independence assumption is explicit; it is not
a statement about all experimental sources. Python, JSON/SHA-256 and SimLab → Lean
correspondence remain open obligations. Scientific priority is not assessed.

Physical reference: [Hong, Ou and Mandel, Physical Review Letters 59, 2044 (1987)](https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.59.2044).
[Validation commands and source hashes](../../tools/validation_snapshot.json).

## Historical source-side validation

Base snapshot: `0556810415b74197251b6a7e8c2e712f5375b97f`.

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 127 |
| Lean files under Verification/ | 167 top-level + 2 support = 169 |
| Root-inclusive byte-identical export | 170 sources |
| Clean strict private build | 3618 jobs; no warnings |
| Both full axiom audits | 14510 declarations; no violations |
| Private live tests | 75; no failures or skips; 260.682s |
| Export live tests | 72; no failures or skips; 274.457s |
| Export clean strict build | 3618 jobs; no warnings |

Module verify and audit each covered 349 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
The independent auditor source is pinned to 46024e005996495c65ef609368e11ab39c4222e3;
binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; a second independent proof kernel is not asserted.
Counts include generated declarations. Both project build directories started empty,
with isolated copies of pinned dependency caches. Integration is idempotent.
Prior subject proof sources, original HEAD and 406 tracked files outside simulations/
are preserved. This task makes no writes to simulations/ and no public release.

## Public release validation

The separate [v0.5.25 report](../../docs/release-v0.5.25.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 127 |
| Lean files under Verification/ | 167 top-level + 2 auxiliary = 169 |
| Root-inclusive sources identical to the private snapshot | 170 |
| Clean strict build | 3618 jobs; no warnings |
| Complete verifier audit | 14510 declarations; no violations |
| Pinned independent full audit | 14510 declarations; no violations |
| Public live tests | 72; no failures or skips; 260.670s |
