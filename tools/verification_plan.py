#!/usr/bin/env python3
"""Plan hierarchical verification for a trusted checkout; no proof execution."""
import argparse
import json
from pathlib import Path
import re
from verifier_skill import code_only

RANKS = ['alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta']
TRUST = ('tools/', '.github/', '.agents/', 'lean-toolchain', 'lakefile.toml',
         'lake-manifest.json', 'VERSIONING.md')
REGISTRIES = {'Verification.MasterSuite', 'Verification.MasterSuiteComponents',
              'Verification.MasterHundredRegistry', 'Verification.AxiomAudit'}


def graph(root):
    result = {}
    for p in sorted((root / 'Verification').rglob('*.lean')):
        name = str(p.relative_to(root).with_suffix('')).replace('/', '.')
        imports = []
        for line in code_only(p.read_text()).splitlines():
            if line.strip().startswith('import '):
                imports += [x for x in line.strip()[7:].split() if x.startswith('Verification.')]
        result[name] = set(imports)
    for name, deps in result.items():
        if deps - result.keys():
            raise ValueError(f'Unresolved local imports: {name}: {deps - result.keys()}')
    active, done = set(), set()
    def visit(n):
        if n in active:
            raise ValueError(f'Import cycle: {n}')
        if n in done:
            return
        active.add(n)
        for d in result[n]:
            visit(d)
        active.remove(n); done.add(n)
    for n in result:
        visit(n)
    return result


def plan(root, rank, modules=(), direction=None, batch=None, changed=()):
    root = Path(root).resolve()
    if rank not in RANKS:
        raise ValueError('Unknown rank')
    catalog = json.loads((root / 'knowledge/catalog.json').read_text())
    owners = {'Verification.' + m['id']: m['section'] for m in catalog['modules']}
    g = graph(root)
    selected = set(modules)
    if selected - g.keys():
        raise ValueError('Unknown module')
    reasons = []
    effective = rank
    if any(p.startswith(TRUST) or p.startswith('Verification/Specs/') for p in changed):
        effective = 'alpha' if rank == 'alpha' else 'beta'
        reasons.append('Trusted policy, tooling, specification or configuration changed')
    if rank == 'gamma':
        if direction not in {s['id'] for s in catalog['sections']}:
            raise ValueError('Gamma requires a catalog direction')
        selected |= {n for n, d in owners.items() if d == direction}
    if rank == 'delta':
        batches = json.loads((root / 'tools/verification_batches.json').read_text())['batches']
        if batch not in batches:
            raise ValueError('Delta requires a registered batch')
        selected |= set(batches[batch]['modules'])
        if selected - g.keys():
            raise ValueError('Batch contains unknown modules')
        direction = batches[batch]['direction']
        if any(owners.get(n) != direction for n in selected):
            raise ValueError('A batch must belong to one direction')
    if effective in ('alpha', 'beta'):
        selected = set(g)
    elif not selected:
        raise ValueError('Explicit module scope is required')
    affected = set(selected)
    while True:
        more = {n for n, deps in g.items() if deps & affected} - affected
        if not more:
            break
        affected |= more
    directions = {owners[n] for n in affected - REGISTRIES if n in owners}
    if effective not in ('alpha', 'beta') and len(directions) > 1:
        reasons.append('Cross-direction reverse dependencies: validate all listed directions')
        effective = 'gamma'
        while True:
            before = set(affected)
            affected |= {n for n, d in owners.items() if d in directions}
            affected |= {n for n, deps in g.items() if deps & affected}
            directions = {owners[n] for n in affected - REGISTRIES if n in owners}
            if affected == before:
                break
    closure = set(affected)
    while True:
        more = set().union(*(g[n] for n in closure)) - closure
        if not more:
            break
        closure |= more
    return dict(schema_version=1, requested_rank=rank, effective_rank=effective,
                direction=direction, batch=batch, selected=sorted(selected),
                reverse_dependents=sorted(affected - selected), build_modules=sorted(affected),
                imported_closure=sorted(closure), directions=sorted(directions), reasons=reasons,
                registry_build_required=True, test_selection='Explicit reviewed tests required for scoped runs; beta runs all',
                semantic_conformance='Registered pinned contracts only; not universal intent checking')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    p.add_argument('--rank', choices=RANKS, required=True)
    p.add_argument('--module', action='append', default=[])
    p.add_argument('--direction'); p.add_argument('--batch')
    p.add_argument('--changed', action='append', default=[])
    a = p.parse_args()
    try:
        print(json.dumps(plan(a.project, a.rank, a.module, a.direction, a.batch, a.changed), indent=2))
    except (ValueError, OSError, KeyError) as e:
        p.exit(1, str(e) + '\n')

if __name__ == '__main__':
    main()
