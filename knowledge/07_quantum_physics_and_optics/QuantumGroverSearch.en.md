---
id: QuantumGroverSearch
language: en
section: quantum-physics
source: Verification/QuantumGroverSearch.lean
source_sha256: fbf4210e5c0a7e2e2d5e827b9b25d0f9be7bebd6b780e39d99004335304cd3ce
novelty: not-assessed
status: reviewed
---

# QuantumGroverSearch

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumGroverSearch.lean)

## Verified result

The uniform real state (1/2,1/2,1/2,1/2) has unit squared norm. For each of the four standard basis targets, one explicitly defined composition of oracle and diffusion maps this state exactly to that target. The target overlap equals one; an additional theorem establishes that its square also equals one.

## Assumptions and limitations

QState4 is an arbitrary real four-vector. Exact search assumes that the target is one of basis0, basis1, basis2 or basis3; it is not asserted for arbitrary vectors or multiple marked items. The oracle and diffusion are given by explicit reflection formulas. For an arbitrary target without unit norm, the oracle formula alone need not define a reflection. General norm preservation, involutivity and an operator-unitarity theorem are not proved here.

The original probability-named theorem states an overlap amplitude; the added squared-overlap theorem gives the real-amplitude probability expression for these normalized basis targets. No measurement process is defined. The proved step contains one oracle application by definition, but no separate query-cost model, gate decomposition, physical oracle implementation or general quantum speedup theorem is encoded. N > 4 search, iteration-count estimates, complex phases, continuous phase errors and noise are outside the model.

## Value and novelty

An exact small-dimensional example with explicit oracle and diffusion operations, suitable for checking conventions and future circuit-level proofs. Mathematical novelty and first-formalization claims have not been assessed.

## Verification

[Validation record](../VERIFICATION.en.md). Entry point: `QuantumGroverSearch.quantum_grover_master_verification_suite`.

- [`grover_exact_quantum_search`](../../Verification/QuantumGroverSearch.lean#L58)
- [`grover_success_probability_sq_one`](../../Verification/QuantumGroverSearch.lean#L76)
