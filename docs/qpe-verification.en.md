# Exact two-bit QPE validation

Source baseline: private `520eef27466667237fff4d6ef7d9821e17f9fcfe`.
New module SHA-256: `73b042a0deffd448b9ef434570890c0f69d9d2072315ae8030bdb84b3a6a7690`.

## Formal result

The four-component complex control state uses basis order 00, 01, 10, 11. Its exact phase is b1/2+b2/4, with integer index 2*b1+b2. The positive-exponent Fourier matrix and conjugate-transpose inverse have proved exponential formulas, two-sided inverse identities and norm preservation. The actual exponential prestate is proved equal to the Fourier column. Applying the inverse yields exactly the correct basis vector, with amplitude 1 there and 0 elsewhere.

The model also includes a two-coordinate complex target, the paired-Hadamard kernel, and controlled complex-linear target operations. The low bit controls U and the high bit controls U composed with U. The eigenstate hypothesis derives phase kickback; the prestate is not assumed as the output of those gates. A norm-preserving target map and a normalized exact eigenstate form UnitaryEigenInput. The full joint output preserves the target, has total norm 1, and gives marginal weights 1 and 0 at the correct and incorrect control indices. Any positive-weight outcome decodes to the original bits.

The squared-modulus probability interpretation uses the usual Born rule. Eigenstate preparation, physical measurement and gate implementation are not certified. Approximate QPE, other rational or irrational phases, leakage/error bounds, arbitrary register sizes, elementary-gate synthesis of inverse QFT, noisy operations and Shor are outside scope.

## Regression evidence

The Lean regression covers every exact phase, bit significance, normalization, cancellation and a normalized target with two nonzero complex coordinates. A family of concrete norm-preserving phase operators supplies nonvacuous inputs for all four phases. Counterchecks show the wrong Fourier sign produces index 3 instead of 1 at phase 1/4, and reversing controlled powers changes the pre-Fourier amplitude. The zero target cannot satisfy normalization. The exponential form of the eigenstate promise is bridged explicitly to the operator theorem.

## Integration and prerequisite correction

QuantumPhysicsFullSuite gains phase_estimation in MasterSuiteComponents. Root and central imports, the axiom audit hook, reviewed integration recipe, English/English cards and exporter test allowlist are updated. Existing fields and universe parameters remain available. Aggregates referencing the quantum package inherit its new field; the historical hundred-import manifest remains unchanged.

The one-line removal of unused `import Mathlib.Tactic` from DistributedChandyLamportSnapshot is backported from public v0.5.3. Its public/private source hash is now `7db4e83d0a10a51665e09d8c7283d7df011a3ca0827611c2a80286a68c9449d2`. This changes no definitions or proof bodies and keeps the header linter enabled on fresh strict builds.

## Reproduction

```bash
lake build --wfail
python3 tools/verifier_skill.py verify Verification/QuantumPhaseEstimation.lean
python3 tools/verifier_skill.py audit Verification/QuantumPhaseEstimation.lean
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/check_knowledge.py
python3 tools/verifier_skill.py integrate Verification.QuantumPhaseEstimation QuantumPhaseEstimationSuite
```

Independent audit: leanprover-community/axiom-audit v0.1.2, pinned and checked at `46024e005996495c65ef609368e11ab39c4222e3`, allowing only `propext,Classical.choice,Quot.sound`. The CLI has no audit-all/test-all commands.

Module verify and audit cover **149 declarations** in its project import closure. Strict full build: **3524 jobs**, no warnings. Independent project audit: **9224 declarations**, only the three allowed standard axioms. The full local verifier independently covers **142 modules and 9224 declarations**, with no policy findings or source changes. All **44 private live tests passed**, without failures or skips. The central registry has **106 direct imports**. Integration is idempotent. The [validation snapshot](../tools/validation_snapshot.json) records current source hashes.

All implementation and validation run in an isolated clone. The original workspace and its simulations are not written by this task. No public release or new SimLab experiment is part of this change.

The public export allowlist includes the QPE compiler regression and this report. Stale overview templates were refreshed; exported proof counts are source-side evidence, and public release build/test results must be measured separately. No public test count or release is inferred from this private run.

## Isolation and final export check

The original `/home/cyberg/Lean` HEAD and all **406 tracked-file hashes** match
the pre-task snapshot. This task made no writes to its simulations. Concurrent
SimLab work added 30124 metadata entries and changed 11 existing entries during
the run (none removed), so whole-directory immutability is not claimed.

The final fresh export preserves all **143 Lean source files**, including the
root import file, byte-for-byte. Both QPE regression files are exported unchanged;
English cards and simulations are absent. The exported catalog and local links
pass validation. After refreshing overview templates, both export tests passed
again. This is an export check, not publication or validation of a new public
release. All Lean hashes still match the full verifier's checked snapshot after
the live tests.
