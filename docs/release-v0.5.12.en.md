# Release v0.5.12: Simon exact sampling and rank-conditional recovery

Private proof snapshot: `8a58301154937e277e38e417dda503cff403e1b6`.
Previous public main: `c4d6d779552d5b52b71778464f2048f0fa22c4a8`.

## Scope

The module derives the complex two-register H-input / XOR-oracle / H-input
circuit for arbitrary finite input/output registers. The XOR oracle is linear,
involutive, self-adjoint and Hermitian-product preserving. Under the nonzero
Simon promise, the marginal probability is exactly 2/(2^n) on the binary
orthogonal hyperplane s-perp and zero elsewhere. Normalization follows from
the actual circuit, even without the promise.

Period recovery requires s nonzero, every supplied row orthogonal to s, and
rank n-1 of their span over F2. Under these assumptions the solutions are
exactly {0,s}. Row count alone is insufficient. Independent repeated sampling,
sample-count bounds, Gaussian-elimination complexity, the injective s=0 branch,
gate synthesis and physical implementation are not claimed. Python, JSON/SHA-256
and external SimLab input-to-byte binding remain external obligations.

See the [English card](../knowledge/03_quantum_physics_and_optics/QuantumSimonsAlgorithm.md),
[private verification record](simon-verification.en.md) and
[Reservoir readiness](reservoir-readiness.en.md).

## Public validation

- **114 unique direct imports**, **154 Lean files** under Verification/.
- Fresh project strict build: **3537 jobs**, zero warnings. The project build directory started empty; pinned dependency caches are isolated copies, not a from-source rebuild of Mathlib.
- Full local verify-all: **154 modules**, **11588 declarations**, no violations or source changes.
- Independent pinned audit: **11588 declarations**, only propext, Classical.choice, Quot.sound. The strict AxiomAudit registry hook also passed.
- **49 public live tests** passed in **83.609 seconds**, without errors, failures or skips.
- Integration is idempotent; audited source hashes still match after tests.
- Catalog, local links and static 256-node placement provenance checks pass.
- The candidate-data reproducer matches all **7,824 certificate states**; Python correctness is not inferred.
- All **155 Lean sources**, including the root, match the private snapshot byte-for-byte.
- The complete exported file set is present, with public package metadata retained and no Russian-language cards.
- Original HEAD and all **406 tracked-file hashes** are unchanged.

## Reproduction

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
python3 scripts/check_three_phase_commit_certificate.py --check
python3 scripts/generate_chip_manifest.py --check
```

The independent project-wide audit uses leanprover-community/axiom-audit v0.1.2,
pinned at `46024e005996495c65ef609368e11ab39c4222e3`, compiled with Lean 4.33.1,
root Verification and allowlist propext, Classical.choice, Quot.sound.
The registry AxiomAudit hook is an additional check, not a second proof kernel.

Publication uses an annotated v0.5.12 tag and `git push --atomic origin main v0.5.12`.
This task writes nothing in simulations; concurrent SimLab activity is not
reverted or interpreted as immutability of that entire directory.
