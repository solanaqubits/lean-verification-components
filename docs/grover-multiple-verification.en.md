# Multiple-target Grover verification record

Private source baseline: `13ee7282c5dd63c88eb4e4c2fd237e8dbd082e8d`.
The new module is Verification.QuantumGroverMultipleTargets. The existing QuantumGroverSearch source is preserved byte-for-byte.

## Formal result

Actual coordinate-wise marked sign inversion followed by mean diffusion preserves the quadratic norm on every real four-vector. Both components are involutions. From the uniform state, every natural-number iterate is normalized and has equal amplitudes within the marked and unmarked classes. This two-amplitude recurrence is derived from the four-coordinate operators and proved to agree with their iterates.

Success weights for every k are: 0 for M=0; 1 at k mod 3=1 and 1/4 otherwise for M=1; 1/2 for M=2; 0 at k mod 3=1 and 3/4 otherwise for M=3; and 1 for M=4. Empty targets fix the uniform state, while full targets alternate its global sign. At M=3 the first step gives minus the sole unmarked basis vector and unmarked weight 1.

For nonempty proper target sets, the marked and unmarked uniform vectors are orthonormal. Their coordinate representation is unique, their plane is closed under real linear combinations and invariant under the step, and it contains every iterate from uniform. Its exact matrix in that ordered basis is [[c,s],[-s,c]], with c=1-M/2 and s=√M*√(4-M)/2; c²+s²=1 is proved. This is an algebraic rotation description, not a formal trigonometric-angle theorem or topological-closedness theorem.

Exact coordinate conversions connect the old QState4 representation, inner product, diffusion and singleton oracles. The old one-target theorem is reused. The existing grover suite and accessor remain intact.

Two mistaken scope claims are explicitly refuted: the two symmetric vectors do not span all of ℝ⁴, and agreement with rank-one reflection is not equivalent to belonging to their plane. On that plane agreement holds. T={0,1}, v=(1,-1,0,0) refutes general agreement; T={0}, v=(0,1,-1,0) shows agreement outside the plane. An empty target set leaves the phase oracle equal to identity, but does not make diffusion the identity on arbitrary inputs.

## Checks

The standalone module verify and audit cover 295 declarations in the imported project closure, allowing only propext, Classical.choice and Quot.sound. Compiler regressions cover arbitrary-state legacy compatibility, nonadjacent marked pairs, symbolic k, three-target sign and overshoot, repeated single-target steps, empty/full sets, nonnormalized states, plane-coordinate uniqueness, both rank-one counterexamples and degenerate endpoints.

Full strict build: **3525 jobs**, no warnings. The central registry has **107 unique direct imports** and Verification/ contains **143 Lean files**. Full verify-all and the independent pinned audit each cover **9378 declarations**, allowing only the standard trio, with no source changes during verification. All **45 private live tests** passed in **74.792 seconds**, without errors, failures or skips. The repeated integration plan is empty. The catalog, local links and exact 256-node placement data pass their checks. All audited source hashes still match after the live tests.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify Verification/QuantumGroverMultipleTargets.lean
python3 tools/verifier_skill.py audit Verification/QuantumGroverMultipleTargets.lean
python3 tools/verifier_skill.py integrate Verification.QuantumGroverMultipleTargets QuantumGroverMultipleTargetsSuite --apply
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/check_knowledge.py
python3 scripts/generate_chip_manifest.py --check
```

Independent audit: leanprover-community/axiom-audit v0.1.2, pinned and checked at `46024e005996495c65ef609368e11ab39c4222e3`, allowing only the three standard axioms above. No audit-all or test-all CLI subcommands exist.

The integration recipe targets MasterSuiteComponents, where QuantumPhysicsFullSuite is defined. The proof constructor is wrapped across lines to satisfy the enabled style linter; no linter is disabled. Root/central imports, the audit hook, recipe, compiler tests, exporter allowlist, Russian/English source cards and catalog are updated. The historical hundred manifest is unchanged, while aggregates using the quantum package inherit its new field.

## Boundaries and isolation

This model fixes N=4 and real amplitudes. Born-rule interpretation of squared amplitudes is external. Theorems do not certify arbitrary N, oracle query complexity, oracle construction, unknown-count schedules, fractional phase rotations, complex gate circuits, physical measurement, quantum noise or hardware. The code does not claim scientific novelty.

All task writes occur in an isolated clone or external task scratch paths. No SimLab study is launched and no simulation archive is modified or copied. New proof source and data hashes are recorded in [validation_snapshot.json](../tools/validation_snapshot.json). No public release is part of this private implementation task.

The existing public exporter preserves all **144 Lean sources**, including the root, byte-for-byte and includes the new regression files. Its English catalog passes; no Russian cards or simulations are exported. This verifies export preparation, not a public release.

Control snapshots confirm the original workspace HEAD and all **406 tracked-file hashes** are unchanged. Concurrent SimLab work added 94 metadata entries and changed 10 existing entries between these snapshots (none removed). These artifacts were neither written nor reverted by this task; directory-wide immutability is not claimed.
