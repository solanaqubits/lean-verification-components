---
id: QuantumBeamSplitterTransform
language: en
section: quantum-physics
source: Verification/QuantumBeamSplitterTransform.lean
source_sha256: e1c41a70782fb73dca7f68df696594da522cdaf2a006887cba188879b2747895
novelty: not-assessed
status: reviewed
---

# QuantumBeamSplitterTransform

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumBeamSplitterTransform.lean)

## Real two-mode transformation

`BeamSplitter` supplies real amplitudes `r` and `t` with `r² + t² = 1`. They may be signed. `bs_transform` uses the fixed real phase convention

```text
U = [[t, -r], [r, t]]
(a, b) ↦ (t*a - r*b, r*a + t*b).
```

`transform_add` and `transform_smul` establish real linearity. `channels_orthogonal` proves that the two transformed input basis modes have zero real inner product; `energy_conservation` preserves `a² + b²`. Together these describe a real orthogonal map. The field name `h_unitary` is the scalar losslessness constraint, not a definition of a general complex unitary matrix.

`interference_terms` expands both output squares: their mixed terms have opposite signs and cancel in the sum. `symmetricBS` fixes `r = t = 1 / sqrt(2)`; `symmetric_bs_properties` gives equal power splitting and the transform `((a-b)/sqrt(2), (a+b)/sqrt(2))`. For the input `(1,0)`, `single_photon_partition` identifies the squared output amplitudes as `(t²,r²)`, proves their nonnegativity, and proves that they sum to one.

## Normalized basis and finite two-boson lift

`TwoPhotonState` contains three real coordinates in the stipulated orthonormal occupation basis `|2,0⟩, |1,1⟩, |0,2⟩`. The basis is normalized; the structure permits arbitrary coordinate triples and does not require unit norm. `twoPhotonNormSq` is the sum of their squares.

`statePolynomial` encodes these coordinates as

```text
P_v(x,y) = a20*x²/sqrt(2) + a11*x*y + a02*y²/sqrt(2).
```

The factors `sqrt(2)` supply the factorial normalization for two photons in one mode. `twoPhotonTransform` is the finite symmetric-square lift. Its connection to the one-mode images is proved by `two_photon_polynomial_substitution`:

```text
P_(twoPhotonTransform bs v)(x,y)
  = P_v(t*x + r*y, -r*x + t*y).
```

These substituted expressions are the polynomial images of the two input basis modes, matching the columns of `U`. `two_photon_norm_conservation` proves preservation of the three-coordinate squared norm for every real input triple. This is an explicit finite algebraic construction, not a full Fock-space or creation-operator formalization.

## Ideal coincidence suppression

`oneEach = (0,1,0)` represents one indistinguishable photon in each input mode. `two_photon_one_each` derives the output amplitudes

```text
(-sqrt(2)*t*r, t²-r², sqrt(2)*t*r).
```

`coincidenceProbability` is defined as the square of the middle coordinate. `coincidence_formula` gives `(t²-r²)²`; `two_photon_probability_partition` proves that the three squared amplitudes for this normalized input sum to one, and `coincidence_bounds` places the coincidence value in `[0,1]`.

`hom_coincidence_suppression` proves that balanced power splitting, `t² = r² = 1/2`, makes both the coincidence amplitude and its square zero. `symmetric_hom` specializes this to `symmetricBS`. Under the losslessness condition, `hom_zero_iff_balanced` proves the converse as well: the defined coincidence value vanishes exactly at balanced power splitting.

## Physical interpretation and limits

The model has two **modes**, not two colors. No frequency or color labels occur. Indistinguishability is built into the chosen bosonic occupation model; it is not established from an experimental preparation. Interpreting squared amplitudes as measurement probabilities uses the Born rule externally. The module proves algebraic identities for the quantities so defined, not the Born rule or detector behavior.

The model uses real amplitudes. It does not prove a complex reflection phase of `π/2` or an equivalence between real and complex phase conventions. Full Fock space, distinguishable photons, partial overlap, wave packets, temporal HOM dip profiles, losses, detector efficiency, hardware behavior, and equivalence to an existing Mach–Zehnder model are outside its scope.

[Hong, Ou and Mandel (1987), Eq. (2)](https://physics.wm.edu/~inovikova/QuantOptF15/lecturenotes/PhysRevLett.59.2044.pdf) provides physical context for the balanced coincidence zero. This card does not claim formal equivalence with the paper's complex convention or wave-packet experiment.

There are no direct imports of other `Verification` modules; real square roots and algebraic tactics come from Mathlib. Mathematical novelty and priority of formalization are not assessed.

## Verification

The module passed `verify`, `audit`, and integration as `QuantumPhysicsFullSuite.beam_splitter`. Strict build, `verify-all`, independent axiom audit, all 35 public tests without skips, and catalog checks passed. Compiler regressions cover transparent, reflecting, unbalanced and balanced splitters, signed amplitude, nonunit input norm, normalized outputs of |1,1⟩, polynomial substitution, and the distinction between adding path probabilities and squaring the sum of amplitudes. The entry point `beam_splitter_master_suite` has type `BeamSplitterFormalSuite`. See the [validation record](../VERIFICATION.en.md).
