# Release v0.5.66: Debt-index accrual and rounding reconciliation

This release adds DeFiLendingCompoundInterestIndex as the 168th direct MasterSuite
import. It connects rational interval accrual, scaled borrower shares and guarded
pool accounting to an executable natural-number rounding policy.

## Proved accounting behavior

For I>0, r>=0 and dt>=0, I'=I*(1+r*dt) is positive and nondecreasing. A sequence
is I0 times the product of its interval factors. Splitting a positive interval
at a positive fixed rate adds exactly I*r^2*dt1*dt2 relative to a single update;
this is not continuous exponential accrual or subdivision-independent accounting.

Total rational debt is derived from shares and equals their individual debt sum.
Accrual preserves cash and shares. Borrowing and repayment are separate guarded
transitions at a fixed index; their executable Option interfaces match the rules.
All three transitions preserve valid states and a pre-existing accounting balance.
With interest d=B*r*dt and reserve factor 0<=rho<=1, reserves grow by rho*d and
supplier liabilities by (1-rho)*d. Thus A'=A+(1-rho)*d for A=cash+B-R, and
cash+B=R+L is preserved. The exact reserve criterion is R'<=cash iff rho*d<=cash-R.
The counterexample cash=10,B=100,R=5,r=1/5,dt=1,rho=1/2 raises A from 105 to 115
but raises utilization from 20/21 to 24/23, above one.

## Directed rounding and two distinct discrepancies

At positive scale W, natural accrual floors interest and the index increment
separately, floors the reserve allocation and assigns all remaining interest to
suppliers. This preserves the integer balance exactly. Local error bounds are
proved for interest, the normalized index, reserves and the supplier allocation.

For a fixed integer index, the difference between floor((sum shares)*I/W) and
sum floor(share_i*I/W) lies in [0,n-1] for n>=1; the empty case has zero dust.
An independently accrued debt ledger can differ from the index-derived aggregate.
This separate signed gap is explicitly represented and related to reconciliation
dust by an exact identity. A one-borrower counterexample has zero reconciliation
dust but nonzero ledger/index gap: the n-1 bound does not apply to that gap.

[Detailed contract](../knowledge/01_defi/DeFiLendingCompoundInterestIndex.md)

## Scope and open obligations

These are bookkeeping guarantees, not debt recoverability, default freedom,
withdrawal cash availability or overall economic solvency. Local rounding bounds
do not give a uniform global error bound for arbitrary update chains or parameter
quantization. Natural arithmetic is unbounded. Deployed Compound/Aave refinement,
machine overflow, gas, writeoffs, liquidations, deposits/withdrawals, oracle truth
and governance updates are outside scope. No claim is made that Aave uses the
same interval formula.

Tendermint accountable safety still requires complete observations or justification
evidence. Bulletproofs extraction, binding, HVZK, Fiat-Shamir/ROM and external
Python, JSON/SHA-256 and SimLab correspondence remain open.

## Measured validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 168 |
| Lean files under Verification/ | 208 top-level + 2 auxiliary = 210 |
| Root-inclusive sources identical to the reference snapshot | 211 |
| Clean strict build | 3849 jobs; no warnings |
| Complete verifier audit | 23912 declarations; no violations |
| Pinned independent full audit | 23912 declarations; no violations |
| Public live tests | 113; no failures or skips; 328.465s |
| New kernel regression declarations | 48 |
| New executable scenarios | 30 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 211 proof sources match reference snapshot
530d758583c27e9ed8ef3b6bd2f5298c28ed20d0 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

