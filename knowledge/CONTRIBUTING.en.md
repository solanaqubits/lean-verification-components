# Contributing

[Knowledge base](README.md)

Keep Lean sources under Verification/ and documentation in the relevant subject
section. Use English for public documentation, comments, and generated cards.

1. State the definitions, hypotheses, and conclusion explicitly.
2. Run `python3 tools/verifier_skill.py verify Verification/Module.lean`.
3. Add a reviewed integration recipe and inspect its diff before applying it.
4. Review the English draft from `card` against the actual Lean statements.
5. Save Module.en.md, update its catalog entry and section index, and run
   `python3 scripts/check_knowledge.py`.
6. Run the relevant tests and a complete verification before release.

Each catalog entry has one English `card`, a `source`, `section`, and ordered
`project_imports`. Preserve assumptions and scope when documenting a proof.
Axiom auditing does not prove fidelity to a physical or cryptographic application.
Do not assert scientific priority without a documented prior-work comparison.
