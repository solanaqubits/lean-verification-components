# Verification hierarchy and trust boundaries

[Policy](../VERSIONING.md) · [Qutrit conformance](qutrit-conformance.en.md)

The hierarchy is alpha/system, beta/full checkpoint, gamma/direction,
delta/batch, epsilon/module and zeta/module correction. Section IDs come from
the knowledge catalog. A batch may be a singleton. Stable IDs and local
revisions describe structure; sequential main commits describe integration.

The normative requirement, implementation and accepted evidence are separate
objects. Proof authors can propose updates to all three, but changing a pinned
specification or trust policy is a distinct reviewed change, never an automatic
response to a failed proof. The local tools assume trusted Lean/Lake and Python.
They are not sandboxes and do not establish cryptographic authorship of reports.

The beta runner checks every source, registry integration, all live tests,
registered conformance contracts and the separate pinned auditor. Structural
coverage is whole-project; independent semantic conformance is currently pinned
for Simon and the explicit qutrit decoder. Other modules are not advertised as
independently compared against an external normative specification.

Regression evidence distinguishes API/type applications, independent expected
values, counterexamples, mutation rejection and satisfiable concrete instances.
The qutrit pilot rejects weakened claims even if the weakened theorem compiles.
No universal test of non-vacuity, intent or arbitrary logical equivalence exists
in these tools. New contracts can be added incrementally with review.

For executable refinements, a next subject module can connect a finite sequence
of qutrit coordinate operations to the existing decoder. Such a future result
would not certify a numerical simulator, compiler or physical hardware by itself.

Use a publisher isolated from candidate execution in deployments: proof workers
need no release credentials, and the publisher accepts only reviewed evidence
for exact bytes. This is a deployment requirement; the local scripts do not
create OS sandboxes, GitHub branch protections or a distributed integration queue.

Historical snapshots remain valid for their recorded scope. The migration does
not retroactively relabel earlier gamma checks as whole-direction or beta checks.
