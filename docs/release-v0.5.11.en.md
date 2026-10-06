# Release v0.5.11: arbitrary-phase Grover in four dimensions

Private proof snapshot: `2fbb1074ecec7634393cd3081938b2f9fb22edba`.
Previous public main: `3d2c1cddaf4583baeac6fd43cdd7779f7588c0dd`.

## Scope

One marked coordinate in Fin 4 → complex numbers. The oracle multiplies it by
exp(i*phi); diffusion adds (exp(i*psi)-1)*(sum v)/4 to each coordinate.
Complex linearity, explicit adjoints and both inverse identities establish
unitarity on arbitrary inputs. The Hermitian product and squared norm are preserved.

The complex plane spanned by the marked vector and the normalized uniform vector
on the other three coordinates is invariant for all real phi and psi. Equality
of phases is not necessary. All iterates from uniform stay normalized and in this plane.

For equal phases from uniform, the exact one-step success probability is
P(phi)=1-3*(1+cos(phi))^2/16. It equals one exactly when cos(phi)=-1; pi supplies
an exact phase. This is the already exact canonical one-target four-state case,
not a noncanonical fractional cure for overshoot. The raw diffusion at pi is the
negative of the old inversion about the mean, and the raw composite equals the
negative of the canonical Grover step. The bridges to both earlier real modules
prove agreement of measurement weights without claiming literal signed equality.

General Hoyer phase matching, Long schedules for arbitrary dimensions, multiple
targets with arbitrary phases, query complexity, gate synthesis, hardware phase
shifters and noise are not formalized here. Python, JSON/SHA-256 and external
SimLab input-to-byte binding remain separate obligations. Historical results remain.
See the [English card](../knowledge/03_quantum_physics_and_optics/QuantumGroverArbitraryPhase.md),
[design contract](grover-arbitrary-phase-design.en.md) and
[private verification record](grover-arbitrary-phase-verification.en.md).

## Public validation

- **113 unique direct imports**, **153 Lean files** under Verification/.
- Fresh project strict build: **3535 jobs**, zero warnings. The project build directory started empty; pinned dependency caches are isolated copies, not a from-source rebuild of Mathlib.
- Full local verify-all: **153 modules**, **11475 declarations**, no violations or source changes.
- Independent pinned audit: **11475 declarations**, only propext, Classical.choice, Quot.sound.
- The strict AxiomAudit.lean hook also passed.
- **48 public live tests** passed in **89.271 seconds**, without errors, failures or skips.
- Integration is idempotent; all audited source hashes still match after tests.
- Catalog, local links and static 256-node placement provenance checks pass.
- The candidate-data reproducer matches all 7,824 certificate states; Python correctness is not inferred.
- All **154 Lean sources**, including the root, match the private snapshot byte-for-byte.
- The complete exported file set is present, with public package metadata retained and English documentation only.
- Original HEAD and all **406 tracked-file hashes** are unchanged.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
python3 scripts/check_three_phase_commit_certificate.py --check
python3 scripts/generate_chip_manifest.py --check
```

The independent audit uses leanprover-community/axiom-audit v0.1.2, pinned commit
`46024e005996495c65ef609368e11ab39c4222e3`, root Verification, with allowlist
propext, Classical.choice, Quot.sound. The AxiomAudit registry hook is additional.

Publication uses an annotated v0.5.11 tag and `git push --atomic origin main v0.5.11`.
This task writes nothing in simulations; concurrent SimLab changes are not reverted
or interpreted as immutability of that entire directory.
