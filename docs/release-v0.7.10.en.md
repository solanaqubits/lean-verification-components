# Release v0.7.10 — finite IPA forks and explicit HCTK capture

This release synchronizes 247 Lean sources and 203 direct MasterSuite imports
with private source snapshot 5779d30ff6419ee91f787d04f45f3d3b5d483e55.
It adds epsilon203 and refines epsilon201 without allocating another number.
The Lake package version remains 0.7.1; the release is identified by its Git tag.

## Formal results

- IPA: finite square fibers have size at most two. Seven DISTINCT nonzero accepting
  challenges at a fixed expected statement and shared L,R message yield four
  distinct nonzero squares. Zero and rejected responses are excluded; repeated
  queries do not add cardinality. Recursive coverage must hold for the counted
  descendants at every level. The constructed tree feeds the existing extractor,
  returning a valid witness or a nonzero relation among the original generators.
- HCTK: the explicit transition (b,c,v,n)→(b−d,c+eta*d,v+(1−eta)*d,n) derives
  total conservation algebraically. Nonnegativity needs initial nonnegativity,
  0≤d≤b and 0≤eta≤1 at each intermediate state. Finite traces preserve these
  invariants and agree with the old two-store transfer after aggregating c+v.
  The integer label is copied; it is not a defined or proved Chern number.

## Verification boundary

The public planner computes the actual dependency scope. The export touches
cryptography and quantum-physics; any graph-based expansion is retained and
reported in the annotated tag and separate public-tree evidence. This is scoped
validation, not a new full beta checkpoint. The last full public beta basis
remains 2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1); private full control
remains 090aed141b831aee5182197e9ea205176f361c0f. Only propext, Classical.choice
and Quot.sound are allowed. Existing caches are retained; nested audit scopes
are combined rather than counted repeatedly.

## Open obligations and repository boundaries

IPA response availability, authentic shared-prefix rewinding, Heavy Rows/general
forking probability bounds, expected polynomial time, Fiat–Shamir/ROM security,
computational binding, blinding and an independent public dot-product value are
not established. A valid witness need not be an arbitrary prover's original secret.

The HCTK transition is a prescribed real-number model, not a proof of physical
brain-information preservation, resonator stability, phase conjugation or a
Chern invariant. It is not declared equivalent to the earlier NumPy profile
with eta squared and occasional negative residuals. No numerical result is
reclassified by this formal refinement.

SimLab experiments, digital-brain documents/graphs, raw chats, Russian cards and
private working evidence are excluded. Their histories and unresolved obligations
remain separate. No new physical experiment or epsilon reservation is started.
