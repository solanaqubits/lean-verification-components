---
id: QuantumE91ProtocolBellCHSH
language: en
section: quantum-physics
source: Verification/QuantumE91ProtocolBellCHSH.lean
source_sha256: e2dfee759081d3ba6264136388ccec39bacfaf7c7f561d68a4f5c62ee8b44890
novelty: not-assessed
status: reviewed
---

# E91: singlet Born probabilities and CHSH separation

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumE91ProtocolBellCHSH.lean)

## Model and proved results

The input is the normalized two-qubit singlet in Fin 4. Its density matrix is
positive semidefinite with trace one. The Pauli matrices X,Z define observables
obs(x,z)=xX+zZ for real x,z with x^2+z^2=1. Hermiticity, involution, positive
orthogonal projectors (I+aO)/2 and measurement completeness are proved.
Born's rule is a physical modeling postulate; the resulting probabilities and
correlators are calculated from matrix products and traces. The real-valued
probabilities are proved equal to the complex traces, so taking real parts hides
no imaginary component.

Alice uses Z,(Z+X)/sqrt(2),X; Bob uses (Z+X)/sqrt(2),X,(X-Z)/sqrt(2).
Lean indices are zero-based. With r=sqrt(2)/2 the complete correlation table is
[[-r,0,r],[-1,-r,0],[-r,-1,-r]]. All nine outcome distributions are nonnegative,
normalized and have uniform local marginals. The CHSH combination
E00-E02+E20+E22 equals -2*sqrt(2), with absolute value strictly greater than two.
This derives attainability and bridges the earlier scalar tsirelsonBound; it does
not prove a universal upper bound over arbitrary observables or dimensions.
The singlet vector also agrees with PhotonicsBellStateAnalyzer.bellVector.psiMinus.

Key pairs are (1,0),(2,1) in Lean: opposite signs each occur with probability one
half, and Bob's sign inversion yields agreement with probability one and QBER zero.
Independent uniform settings give key/test/discard probabilities 2/9,4/9,1/3.
Finite real probability laws have the existing BB84 bridge to Mathlib PMF.

The LHV theorem quantifies over arbitrary finite hidden-variable laws and local
binary response functions; the same law is used for every setting. The scalar
CHSH bound is also proved for local expectations in [-1,1]. For any finite convex
mixture of products of positive trace-one qubit matrices, the bound |S|<=2 follows
from positivity-derived local expectation bounds. Tensor products and mixtures
are proved positive, and normalized mixtures have trace one.

## Explicit intercept-resend instrument

Eve measures Alice's half of the ideal singlet along any real unit direction in
the XZ plane, discards that qubit, and prepares an arbitrary valid density matrix
tau(a) conditioned on her outcome. measuredBob is the partial trace of the actual
local projector sandwich. Its exact value is (1/2)*proj(obs(x,z),-sign(a)).
The reconstructed pair is therefore an explicit two-term separable mixture,
positive with trace one and |S|<=2. The concrete Z measurement/re-preparation
channel yields diag(0,1/2,1/2,0) and S=-sqrt(2).
This is a full intercept on the supplied singlet, not a theorem classifying every
quantum attack, every input state or arbitrary POVM instruments.

## Clean Water boundaries

A Bell violation excludes the specified local/separable correlation models.
It does not certify absence of all eavesdropping or secrecy of a final key.
The universal Tsirelson operator bound, DI-QKD security, finite-key statistics
(the empirical S is random), information reconciliation, privacy amplification,
source and detector imperfections, losses and detection loopholes are not modeled.
No guaranteed detection on a finite sample is asserted. Settings are independently
chosen, the source and local measurements are ideal, and the authenticated classical
channel is assumed ideal. Python, JSON/SHA-256 and SimLab obligations remain open.
Scientific novelty is not assessed.

References: [Ekert (1991)](https://cqi.inf.usi.ch/qic/91_Ekert.pdf);
[Acin et al. (2007)](https://arxiv.org/abs/quant-ph/0702152).

## Validation

Base snapshot: c3a0f1586f2d4271fd1bb0ff3d1a22261341b235.
All project and export checks passed; measured results follow.

## Source theorem links

- [singlet_density](../../Verification/QuantumE91ProtocolBellCHSH.lean#L56)
- [projector_properties](../../Verification/QuantumE91ProtocolBellCHSH.lean#L72)
- [correlator_exact](../../Verification/QuantumE91ProtocolBellCHSH.lean#L143)
- [chsh_quantum_violation](../../Verification/QuantumE91ProtocolBellCHSH.lean#L160)
- [round_routing_probabilities](../../Verification/QuantumE91ProtocolBellCHSH.lean#L191)
- [lhv_classical_bound](../../Verification/QuantumE91ProtocolBellCHSH.lean#L230)
- [separable_state_chsh_bound](../../Verification/QuantumE91ProtocolBellCHSH.lean#L314)
- [measured_singlet_exact](../../Verification/QuantumE91ProtocolBellCHSH.lean#L332)
- [intercept_resend_forces_separable](../../Verification/QuantumE91ProtocolBellCHSH.lean#L350)
- [bridge_to_quantum_bell_chsh](../../Verification/QuantumE91ProtocolBellCHSH.lean#L393)
- [intercepted_density](../../Verification/QuantumE91ProtocolBellCHSH.lean#L428)
- [born_trace_real](../../Verification/QuantumE91ProtocolBellCHSH.lean#L436)
- [key_corrected_agreement](../../Verification/QuantumE91ProtocolBellCHSH.lean#L451)
- [quantum_e91_protocol_bell_chsh_master_suite](../../Verification/QuantumE91ProtocolBellCHSH.lean#L503)

## Private snapshot validation: Born-derived E91

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 138 |
| Lean sources | 180 under Verification/; 181 including root |
| Strict clean private build | 3728 jobs; no warnings |
| Both full axiom audits | 17806 declarations; no violations |
| Private live tests | 86; no failures or skips; 283.649s |
| Export live tests | 83; no failures or skips; 292.539s |
| Strict clean export build | 3728 jobs; no warnings |

Module verify and audit each covered 1178 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
Independent audit source commit: 46024e005996495c65ef609368e11ab39c4222e3.
Binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: leanprover/lean4:v4.33.1; auditor source toolchain file: leanprover/lean4:v4.32.0-rc1.
The executable is pinned separately; a second independent proof kernel is not claimed.
Counts include generated declarations. Both builds started with empty project
.lake/build directories and isolated pinned dependency caches. All 181 exported
Lean files match byte-for-byte; repeated exports agree. Integration is idempotent.
Original HEAD and 406 tracked files are preserved. No writes to simulations/.
That earlier private integration did not publish a public release.

Born probabilities are derived from the specified singlet and local projectors.
The classical bound covers finite local laws and convex products of physical qubit
states. The explicit XZ intercept/resend instrument on the supplied singlet produces
a separable state. No universal Tsirelson bound, finite-key or secrecy theorem is claimed.

## Public release validation

The [v0.5.36 report](../../docs/release-v0.5.36.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 138 |
| Lean files under Verification/ | 178 top-level + 2 auxiliary = 180 |
| Root-inclusive sources identical to the private snapshot | 181 |
| Clean strict build | 3728 jobs; no warnings |
| Complete verifier audit | 17806 declarations; no violations |
| Pinned independent full audit | 17806 declarations; no violations |
| Public live tests | 83; no failures or skips; 279.434s |
