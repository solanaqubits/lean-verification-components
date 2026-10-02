---
id: MithraicPhaseCollapse
language: en
section: quantum-physics
source: Verification/MithraicPhaseCollapse.lean
source_sha256: b55654dcd4cc96fe2708bb1656a4f6a5d985d43a54d920162e506e745ede82a8
novelty: not-assessed
status: reviewed
---

# MithraicPhaseCollapse

[Section](../quantum-physics/README.md) · [Lean](../../Verification/MithraicPhaseCollapse.lean)

## Scalar model

`InterferencePattern` supplies real extrema `i_max`, `i_min` with
`0 ≤ i_min`, `i_min ≤ i_max`, and `0 < i_max + i_min`.
These assumptions exclude the all-zero pattern and imply `0 < i_max`.
Visibility is the dimensionless scalar
`visibility = (i_max - i_min) / (i_max + i_min)`.

The extrema describe one interference pattern. They are not intensities of two
simultaneously observed Mach–Zehnder output ports. The model contains no phase
parameter, phase scan, or derivation of these extrema from an optical field.

## Formal properties

- `visibility_bounds`: visibility lies in `[0, 1]`.
- `visibility_ideal_iff`: visibility equals `1` exactly when `i_min = 0`.
  `visibility_ideal` supplies the forward construction from a zero minimum.
- `visibility_collapse_iff`: visibility equals `0` exactly when `i_max = i_min`.
  `visibility_collapse` supplies the zero-contrast result from equal extrema.
- `visibility_strict_decay` and `visibility_antitone`: for two admissible
  patterns with the same `i_max`, increasing `i_min` strictly decreases
  visibility; a non-strict increase cannot increase visibility.
  Both statements require the shared maximum to remain fixed.
- `is_coherence_valid p v_crit` is the specified predicate
  `v_crit ≤ visibility p`, for any real threshold. `coherence_valid_of_lower_min`
  proves that lowering `i_min` at fixed `i_max` preserves validity.
- `below_threshold_invalid` proves rejection strictly below the threshold;
  `invalid_iff_below_threshold` proves the equivalence.
  `threshold_equality_valid` accepts equality with the threshold.
- `collapsed_invalid_if_pos`: equal extrema fail every strictly positive
  threshold. `nonpositive_threshold_valid` accepts every admissible pattern
  at a nonpositive threshold; `above_one_threshold_invalid` rejects every
  admissible pattern at a threshold strictly above `1`.

Declarations belong to namespace `MithraicPhaseCollapse`. The summary structure
is `MithraicPhaseCollapseFormalSuite`, instantiated by
`mithraic_phase_collapse_master_suite`. There are no direct `Verification`
imports; the module imports Mathlib real arithmetic and tactics.

## Interpretation and limits

Despite its name, `is_coherence_valid` is a specification for a scalar comparison. Defining and
proving properties of this predicate does not implement a dump driver, route
signals, or prove any hardware transition invariant. No controller or hardware
behavior is modeled.

Equal extrema establish zero fringe contrast; they do not establish physical
noise, decoherence, or wavefunction collapse. Unit visibility does not establish
quantum coherence. There is no claim that a phase offset alone reduces fringe
visibility, and no physical mechanism is inferred from the fixed-maximum
monotonicity result.

The module has no density-matrix dynamics, electromagnetic field or field-noise
model, non-Markovian thermal environment, or hardware control. Connecting this
scalar specification to measurements or a physical implementation requires a
separate model and validation. Mathematical and scientific priority have not
been assessed.

## Verification status

The module passed `verify`, `audit`, and integration as `PhotonicsInterposerFullSuite.mithraic_collapse`. Strict build, `verify-all`, independent axiom audit, the public regression tests without skips, and catalog checks passed. See the [validation record](../VERIFICATION.en.md).
