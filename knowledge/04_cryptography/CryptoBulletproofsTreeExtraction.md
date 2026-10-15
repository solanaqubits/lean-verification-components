---
id: CryptoBulletproofsTreeExtraction
language: en
section: cryptography
source: Verification/CryptoBulletproofsTreeExtraction.lean
source_sha256: 7b52cbbe6a11eef25d0b10045f9d23964246d3d1fd94e0a5c90d9d51c23c1430
novelty: not-assessed
status: reviewed
---

# Recursive IPA tree extraction

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoBulletproofsTreeExtraction.lean)

## Input and exact result

Scalars are ZMod q for prime q. The group is any additive commutative module
over that field. A Statement contains U,G,H,P with vector length 2^k.
IPATranscriptTree is a complete four-branch tree indexed by depth k. Leaves
contain two scalars; internal nodes contain shared L,R messages, four raw scalar
challenges and four child trees. There are no internal witness fields.
Each node additionally carries a claimed statement, checked against the expected
statement supplied separately at the root and computed for children.

ValidAcceptingTree checks the terminal equation at leaves. At internal nodes it
requires nonzero challenges with pairwise distinct squares, then recursively
checks every child against fold_generators_G, fold_generators_H and update_target
from module 158. L,R are shared before branching; each branch may have its own
later messages. The expected U is preserved. Authentic storage of the root
context, transcript availability and serialization are external obligations.

TreeExtractionResult contains either original-length vectors a,b satisfying
P=MSM(a,G)+MSM(b,H)+dot(a,b)*U, or explicit coefficients cG,cH,cU, not all zero,
whose combination of the original G,H,U is zero. No independence of generators
is assumed. A relation result does not imply the absence of a witness.

## Recursive proof and executable interface

lift_generator_relation maps cG to join(cG/u,cG*u), cH to
join(cH*u,cH/u), and preserves cU. lift_generator_relation_eval_eq proves
that evaluation at parent generators equals evaluation at child generators.
lift_generator_relation_injective and lift_generator_relation_nontrivial prove
that a nonzero coefficient tuple stays nonzero. The scalar challenge is a unit;
the raw-tree checker supplies this evidence only after checking nonzero inputs.

combine selects the least branch index returning a relation and lifts it. When
all four children return witnesses, it invokes the actual local extract_local
from module 169. combine_correct establishes the induction step.
tree_extraction_soundness proves correctness by structural induction, starting
from the two leaf scalars. No internal witnesses or extraction conclusions occur
in the validity predicate.

extractTree is a total algebraic core, with no guarantee on invalid inputs.
checked_extract first checks ValidAcceptingTree and returns error "invalidTree"
otherwise. checked_extract_success_iff proves that success is equivalent to
validity, and checked_extract_sound proves validity of every returned result.
Full validation covers every branch, even if the algebraic core would return a
relation before using another child's witnesses. Thus a valid relation in one
branch does not excuse a corrupted leaf or context in another branch.

path_transcript projects a chosen path to the existing IPATranscript type.
accepting_path_verifier proves acceptance by module 158's actual verifier when
its unit challenges match that path. leaf_verifier_bridge gives the base case.
honestTree_valid and honestTree_exact prove validity and exact recovery for
honestly generated trees at every depth under the challenge conditions.

The implementation materializes the four child results and their coordinate vectors; materialize_eq proves that this preserves the mathematical result.

## Size and regressions

leaf_count counts the stored leaves recursively. tree_leaf_count_eq and
tree_leaf_count_square prove 4^k=(2^k)^2=n^2 leaves. This input size is distinct
from the 2k group elements of one IPA transcript. No expected running-time bound
or efficient method of obtaining such a tree is proved.

Concrete examples over ZMod 101 include honest depths 0,1,2,3 and a valid depth-two
tree whose first child returns a nontrivial relation. The example proves the
relation lifts to the root with nonzero coefficients and zero group evaluation.
Regressions check exact honest recovery, actual verifier paths, counts, zero and
symmetric/repeated challenges, altered child claims, altered messages and leaves,
and rejection of a bad later branch despite an earlier valid relation.

## Clean Water

This closes deterministic recursive algebraic IPA extraction from a supplied
valid tree. It does not establish the availability or probabilistic construction
of a tree by rewinding a prover, forking bounds, expected polynomial running
time, full range-witness extraction or bitness, computational binding or a
discrete-log reduction, HVZK, Fiat-Shamir/ROM, or extraction from independent
completed proofs. Concrete curves, randomized challenges, parsing and deployment
refinement are outside scope. Tendermint accountability still needs its
observation/justification contract. Python, JSON/SHA-256 and SimLab correspondence
obligations remain open. Only propext, Classical.choice and Quot.sound are allowed.
Novelty has not been assessed.

Baseline: c1171d85423c81d3d6dd6eaa8b040c9c817813ac.
Measured validation is recorded in tools/validation_snapshot.json.
Reference: [Bünz et al., Bulletproofs](https://eprint.iacr.org/2017/1066).
