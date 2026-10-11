---
id: QuantumDepolarizingChannel
language: en
section: quantum-physics
source: Verification/QuantumDepolarizingChannel.lean
source_sha256: 1c8f5699c765e765ca604b13521e838f066a9519d2f8d7edd076ea42d6c5b088
novelty: not-assessed
status: reviewed
---

# Qubit depolarization and noisy E91 correlations

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumDepolarizingChannel.lean)

## Model and proved results

The parameter p in [0,1] is the total probability of a nonidentity Pauli error.
Kraus operators are sqrt(1-p) I and sqrt(p/3) times X,Y,Z. The channel is defined
as their conjugation sum; completeness and trace preservation are proved.
For every complex matrix M, including unnormalized and non-Hermitian matrices,
D_p(M)=(1-4p/3) M+(2p/3) Tr(M) I. Additivity and complex homogeneity are proved.
The trace factor is essential for linearity.

The extension is independently defined by applying D_p to each 2x2 block of a
matrix indexed by Fin d x Fin 2. Its equality to the conjugation sum with
I_d tensor K_j is proved. Thus positivity holds for every finite ancilla dimension
d and every positive input, including entangled inputs. The extension also
preserves trace for physical p. This proves finite-dimensional complete positivity,
not merely positivity on product states. Since the real square-root definition
exists outside [0,1], the Kraus sum is positive there too; trace preservation and
the stated Pauli weights are only asserted on [0,1].

With lambda=1-4p/3, the Bloch vector is mapped to lambda r. The Euclidean norm
is multiplied by |lambda|; lambda is negative precisely for p>3/4. On the physical
interval lambda lies in [-1/3,1], so the norm does not increase. At p=3/4 the
output is Tr(M) I/2, hence I/2 on density matrices. The maximally mixed state is
fixed. Composition has parameter p+q-4pq/3, proved to remain in [0,1].

## Bridge to E91

The existing singlet is reindexed into the product basis and D_p acts on Bob's
half through the block extension. The output is exactly
lambda rho_minus+(1-lambda) I_4/4 and is positive with trace one. For p>3/4
this affine expression is not a convex decomposition; positivity follows from
Kraus operators. All E91 correlators scale by lambda. Consequently
S(p)=-2 sqrt(2) lambda and |S(p)|=2 sqrt(2) |lambda|.

Noisy probabilities are computed from the existing E91 projectors and the actual
output state. They are nonnegative and normalized for every setting pair and
physical p, and define a finite probability law. The event that Alice's sign
differs from Bob's inverted sign has probability QBER=2p/3 on either key pair.
This is a conditional single-round probability, not a deterministic finite-sample
error fraction. The CHSH violation threshold is not a secret-key threshold.

Regressions cover p=0,3/4,1, the states |0>,|+>,|+i>, composition at p=q=1,
ancilla positivity and trace, noisy key errors and complete loss of CHSH at p=3/4.
The requested malformed map lambda M+(2p/3)(I/2) maps zero to (p/3)I, nonzero
for p != 0; it cannot be linear. Besides omitting the trace, that malformed map
has an extra factor 1/2 compared with the correct normalized-state expression.

## Clean Water boundaries

This is an ideal qubit Pauli-noise model with finite-dimensional ancillas.
Channel capacity, optimal codes, error-correction protocols, DI-QKD security,
final-key secrecy and finite-key statistics are not proved. E91 source, local
measurements, independent setting choices and authenticated classical channel
retain the assumptions of module 138. Python, JSON/SHA-256 and SimLab obligations
remain open. Scientific novelty is not assessed.

References: [Cirq depolarize](https://quantumai.google/reference/python/cirq/depolarize);
[Qiskit Aer](https://qiskit.github.io/qiskit-aer/stubs/qiskit_aer.noise.depolarizing_error.html).
Cirq uses p as above; Qiskit's mixing parameter is 4p/3.

## Validation

Base snapshot: 1816caf49a2eee5ccc791a388fb28b1a83bb1da2.
All project and export checks passed; measured results follow.

## Source theorem links

- [kraus_completeness](../../Verification/QuantumDepolarizingChannel.lean#L49)
- [depolarizing_exact](../../Verification/QuantumDepolarizingChannel.lean#L78)
- [trace_preserving](../../Verification/QuantumDepolarizingChannel.lean#L88)
- [extension_kraus](../../Verification/QuantumDepolarizingChannel.lean#L110)
- [completely_positive](../../Verification/QuantumDepolarizingChannel.lean#L120)
- [bloch_action_exact](../../Verification/QuantumDepolarizingChannel.lean#L144)
- [bloch_length](../../Verification/QuantumDepolarizingChannel.lean#L151)
- [complete_depolarization](../../Verification/QuantumDepolarizingChannel.lean#L154)
- [channel_composition](../../Verification/QuantumDepolarizingChannel.lean#L174)
- [singlet_depolarization_exact](../../Verification/QuantumDepolarizingChannel.lean#L192)
- [chsh_damping](../../Verification/QuantumDepolarizingChannel.lean#L221)
- [e91_key_qber](../../Verification/QuantumDepolarizingChannel.lean#L255)
- [counterexample_nonlinear_without_trace](../../Verification/QuantumDepolarizingChannel.lean#L283)
- [extension_trace_preserving](../../Verification/QuantumDepolarizingChannel.lean#L321)
- [qber_is_corrected_error](../../Verification/QuantumDepolarizingChannel.lean#L361)
- [quantum_depolarizing_channel_master_suite](../../Verification/QuantumDepolarizingChannel.lean#L408)

## Private snapshot validation: Qubit depolarization

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 139 |
| Lean sources | 181 under Verification/; 182 including root |
| Strict clean private build | 3729 jobs; no warnings |
| Both full axiom audits | 17940 declarations; no violations |
| Private live tests | 87; no failures or skips; 283.725s |
| Export live tests | 84; no failures or skips; 300.159s |
| Strict clean export build | 3729 jobs; no warnings |

Module verify and audit each covered 1311 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
Independent audit source commit: 46024e005996495c65ef609368e11ab39c4222e3.
Binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: leanprover/lean4:v4.33.1; auditor source toolchain file: leanprover/lean4:v4.32.0-rc1.
The executable is pinned separately; a second independent proof kernel is not claimed.
Counts include generated declarations. Both builds started with empty project
.lake/build directories and isolated pinned dependency caches. All 182 exported
Lean files match byte-for-byte; repeated exports agree. Integration is idempotent.
Original HEAD and 406 tracked files are preserved. No writes to simulations/.
That earlier private integration did not publish a public release.

The Kraus channel is CPTP for p in [0,1], with complete positivity proved for
arbitrary finite ancillas. Bloch scaling, composition and the actual noisy E91
singlet are derived. Key error probability is 2p/3; CHSH scales by 1-4p/3.
Channel capacity, final-key secrecy and finite-key statistics are outside scope.

## Public release validation

The [v0.5.37 report](../../docs/release-v0.5.37.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 139 |
| Lean files under Verification/ | 179 top-level + 2 auxiliary = 181 |
| Root-inclusive sources identical to the private snapshot | 182 |
| Clean strict build | 3729 jobs; no warnings |
| Complete verifier audit | 17940 declarations; no violations |
| Pinned independent full audit | 17940 declarations; no violations |
| Public live tests | 84; no failures or skips; 281.541s |
