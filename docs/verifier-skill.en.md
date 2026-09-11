# Lean 4 formal verifier

[Home](../README.md)

`tools/verifier_skill.py` provides a standard-library Python CLI and API for this
trusted local Lean project. It is not an MCP server or a sandbox for hostile code.

```bash
python3 tools/verifier_skill.py verify Verification/CryptoPedersenCommitment.lean
python3 tools/verifier_skill.py audit Verification/CryptoPedersenCommitment.lean
python3 tools/verifier_skill.py verify-all
python3 tools/verifier_skill.py card Verification.CryptoPedersenCommitment
python3 tools/verifier_skill.py integrate Verification.CryptoPedersenCommitment CryptoPedersenFormalSuite
```

Reports use JSON. Check `ok`, errors, `audit`, and source hashes. Module verification
includes strict compilation, a fresh Lake build, and a transitive axiom audit of
project declarations in the imported environment. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. Audit also rebuilds before checking;
it does not trust an old compiled artifact after source changes.

`integrate` previews a diff using a recipe in
[integration_targets.json](../tools/integration_targets.json). Add `--apply` to
write the change, verify it, and build. Failure restores the registry and root
source files; it does not restore build caches. Existing guarantees and universes
must be preserved when adding recipes.

`card` returns a English draft without overwriting existing cards. Review the Lean
statements and add precise scope before saving a card .
`scaffold DOMAIN --spec-file FILE` attempts a small explicit Lean proposition;
it does not turn arbitrary prose into a verified specification. Run `--help` for
available commands and arguments.

Agents can follow the local
[SKILL.md](../.agents/skills/lean4-formal-verifier/SKILL.md) and invoke the CLI in
the repository root. [skill.json](../tools/skill.json) describes the local tool;
it is not a universal client installation manifest. For Python usage, import
`Verifier` from `tools.verifier_skill` and pass the project directory.

```python
from tools.verifier_skill import Verifier
report = Verifier(".").verify_module("Verification/CryptoPedersenCommitment.lean")
assert report["ok"], report
```
