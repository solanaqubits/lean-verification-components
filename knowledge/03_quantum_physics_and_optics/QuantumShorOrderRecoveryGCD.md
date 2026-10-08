---
id: QuantumShorOrderRecoveryGCD
language: en
section: quantum-physics
source: Verification/QuantumShorOrderRecoveryGCD.lean
source_sha256: 7b03dc9718cc36065b2f667d5799fb03d0cd007a38d185f853640f12ac6c1f8b
novelty: not-assessed
status: reviewed
---

# Conditional Shor order recovery by finite LCM and GCD

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumShorOrderRecoveryGCD.lean)

## Executable procedure and algebra

listLCM accepts only a finite list of natural-number candidates, recurses structurally,
and returns one on the empty list. Neither the unknown order r nor spectral numerators
are inputs. list_lcm_append proves incremental combination; list_lcm_membership_invariant
proves independence from ordering and duplicate occurrences. No running-time or bit
complexity bound is asserted.

For any qs with every q dividing r, list_lcm_dvd_order proves listLCM qs divides r.
When r>0, divisibility excludes zero candidates and makes the LCM positive. For a
nonempty list, order_recovery_criterion_quotients proves
listLCM qs = r iff foldr (gcd ∘ (r / ·)) 0 qs = 1. Nonemptiness matters: the empty
LCM is one but the empty unanchored GCD is zero. Empty input recovers order one only.

The proof uses the divisor-lattice complement identity from pinned Mathlib
Nat.div_lcm_eq_div_gcd, not a new number-theoretic principle. spectral_lcm_formula proves
LCM(map (r / gcd(s,r)) ss) = r / gcd(r, foldr gcd 0 ss), and
order_recovery_spectral_gcd gives equality to r exactly when the anchored GCD is one.
This holds for all finite lists including empty lists, for r>0. Numerators need not
be coprime individually: r=6 and ss=[3,2] give denominators [2,3] and LCM 6.
Zero spectral numerators give denominator one and need not reveal the order.

## Connection to measurements and the executable modular check

reduced_denominators_eq reuses module 119's canonical rational denominators.
shor_order_recovery_criterion instantiates the algebra for the existing Shor Parameters:
N≥2, coprime a,N, padded finite target register, and actual positive period
r=orderOf(a : ZMod N). It is a deterministic conditional theorem, not a distribution
of repeated quantum measurements.

measured_candidate_provenance assumes Q=2^n≥N² and the existing modular Nearest
condition for each pair of latent spectral label s<r and observed y<Q. It proves
that each correct reduced denominator occurs in the corresponding observable list
candidates(y,Q,N). It does not select that denominator or reveal the spectral label.

modular_check_soundness_exact combines L|r with a^L=1 in ZMod N to conclude L=r.
executable_check_exact proves the corresponding iff for the existing executable
passesModularCheck. The observable check alone proves r|L, not L|r or minimality.
A 'certified divisor' means separate mathematical provenance, not merely passing
this modular check. No candidate-selection algorithm is supplied.

## Counterexample and scope

all_candidates_can_pass_nonminimally is checked by the Lean kernel: for N=31,a=2,
the order is 5. At y=410,Q=1024, candidate denominators are [1,2,5]. Their LCM is
10, which passes the modular check but is not the order. Regressions also prove
31²≤1024 and |410/1024-2/5|≤1/(2*1024), so insufficient QPE resolution does not
explain this failure. Taking all candidates is unjustified even at adequate resolution.

Regressions cover empty input, order one, zero candidates excluded by provenance,
zero spectral numerators, duplicates, permutations, insufficient divisors, failure
of the modular check and the nonminimal passing counterexample. Concrete computation
uses decide and decide +kernel; no native_decide is used.

No i.i.d. sampling law, probability of a coprime sample family, number of quantum
runs, classical factorization through gcd(a^(r/2)±1,N), gate synthesis or hardware
model is proved. Python, JSON/SHA-256 and external SimLab input-to-byte binding remain
open. This module supplies conditional multi-sample algebra, not a complete Shor
implementation. Scientific priority has not been assessed.

Sources: pinned Mathlib Data/Nat/GCD/Basic.lean; existing
[continued fractions](QuantumShorContinuedFractions.md) and
[order-finding core](QuantumShorOrderFindingCore.md).
Measured commands and source hashes: [validation snapshot](../../tools/validation_snapshot.json).

## Historical private implementation and export validation

Base snapshot: `189077d10183ebf11198f486c48fa156c4cbf11d`.

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 120 |
| Lean files under Verification/ | 160 top-level + 2 support = 162 |
| Root-inclusive byte-identical export | 163 sources |
| Clean strict private build | 3547 jobs; no warnings |
| Both full axiom audits | 12922 declarations; no violations |
| Private live tests | 68; no failures or skips; 253.935s |
| Export live tests | 65; no failures or skips; 267.473s |
| Export clean strict build | 3547 jobs; no warnings |

Module verify and audit each covered 597 declarations including transitive project imports.
Both full audits permit only propext, Classical.choice and Quot.sound.
Independent auditor source: 46024e005996495c65ef609368e11ab39c4222e3; executable
SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source records v4.32.0-rc1, with the
executable pinned separately. The registry hook passed separately; no second
independent proof kernel is claimed. Counts include generated declarations.
Project build directories started empty, with isolated pinned dependency caches.
Integration is idempotent. Earlier subject proofs are unchanged. Original workspace
HEAD and 406 tracked files outside simulations/ are preserved. That implementation task made no writes to simulations/ and did not publish a public release.
Fresh public measurements appear in the [v0.5.18 report](../../docs/release-v0.5.18.en.md).
