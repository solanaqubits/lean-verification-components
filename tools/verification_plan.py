#!/usr/bin/env python3
"""Explain verification impact; plan commands without executing proofs."""
import argparse
import json
from pathlib import Path, PurePosixPath
import subprocess
from verifier_skill import code_only
from verification_metadata import DATA_FILES, BATCHES, RECIPES, CATALOG, load_metadata

RANKS = ['alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta']
TRUST = ('tools/', 'scripts/', '.github/', '.agents/', 'lean-toolchain', 'lakefile.toml',
         'lake-manifest.json', 'VERSIONING.md', 'Verification/Specs/')
REGISTRIES = {'Verification.MasterSuite', 'Verification.MasterSuiteComponents',
              'Verification.MasterHundredRegistry', 'Verification.AxiomAudit'}
TRUST_TESTS = {'tests/test_verifier_skill.py', 'tests/test_release_evidence.py',
               'tests/test_verification_hierarchy.py', 'tests/test_verification_scope.py',
               'tests/test_hundred_registry.py', 'tests/test_public_export.py'}
POLICY_DOCS = {'docs/verification-hierarchy.en.md', 'docs/verification-hierarchy.ru.md',
               'docs/verification-scope-policy.en.md', 'docs/verification-scope-policy.ru.md'}


def git(root, *args):
    return subprocess.check_output(['git', *args], cwd=root, stderr=subprocess.PIPE).decode()


def imports(text):
    return {x for line in code_only(text).splitlines() if line.strip().startswith('import ')
            for x in line.strip()[7:].split() if x.startswith('Verification.')}


def graph(root, reader=None, names=None):
    root = Path(root)
    names = names if names is not None else [str(p.relative_to(root)) for p in (root / 'Verification').rglob('*.lean')]
    result = {n[:-5].replace('/', '.'): imports(reader(n) if reader else (root / n).read_text()) for n in sorted(names)}
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
        active.remove(n)
        done.add(n)
    for n in result:
        visit(n)
    root_text = reader('Verification.lean') if reader else ((root / 'Verification.lean').read_text() if (root / 'Verification.lean').exists() else '')
    if root_text and imports(root_text) - result.keys():
        raise ValueError('Unresolved root imports')
    return result


def closure(g, initial, reverse=False):
    result = set(initial)
    while True:
        more = ({n for n, deps in g.items() if deps & result} if reverse else
                {d for n in result for d in g.get(n, ())}) - result
        if not more:
            return result
        result |= more


def changed_paths(root, base):
    # Include staged, unstaged, deleted, renamed (both sides), and untracked files.
    return set(filter(None, (git(root, 'diff', '--name-only', '--no-renames', '-z', base, '--') +
                            git(root, 'ls-files', '--others', '--exclude-standard', '-z')).split('\0')))


def plan(root, rank, modules=(), direction=None, batch=None, changed=(), base=None, tests=()):
    root = Path(root).resolve()
    if rank not in RANKS:
        raise ValueError('Unknown rank')
    if any(not t.startswith('tests.test_') or not all(part.isidentifier() for part in t.split('.')) for t in tests):
        raise ValueError('Use explicit unittest module/class/method names')
    reviewed_test_files = {'/'.join(t.split('.')[:2]) + '.py' for t in tests}
    g = graph(root)
    current = load_metadata(root, g)
    owners = current['owners']
    old_g, previous = g, None
    base_sha = None
    if base:
        base_sha = git(root, 'rev-parse', '--verify', base + '^{commit}').strip()
        old_names = [n for n in git(root, 'ls-tree', '-r', '--name-only', base_sha).splitlines()
                     if n.startswith('Verification/') and n.endswith('.lean')]
        def reader(name):
            try:
                return git(root, 'show', base_sha + ':' + name)
            except subprocess.CalledProcessError:
                return None
        old_g = graph(root, reader, old_names)
        previous = load_metadata(root, old_g, reader)
        changed = set(changed) | changed_paths(root, base_sha)
    paths = sorted(set(changed))
    for name in paths:
        if not name or str(PurePosixPath(name)) != name or PurePosixPath(name).is_absolute() or '..' in PurePosixPath(name).parts:
            raise ValueError('Expected normalized repository-relative changed path')
    selected = set(modules)
    if selected - g.keys():
        raise ValueError('Unknown module')
    explanations, reasons = [], []
    effective = rank
    proof_work = not paths or bool(modules)
    changed_seeds = set()
    for path in paths:
        rule, seeds, level = 'unclassified-change', set(), 'beta'
        if path in DATA_FILES:
            rule, level = 'validated-declarative-data', 'metadata'
            if path == BATCHES:
                before = previous['batches'] if previous else {}
                after = current['batches']
                for key in before.keys() | after.keys():
                    a, b = before.get(key, {}), after.get(key, {})
                    if (a.get('direction'), a.get('modules')) != (b.get('direction'), b.get('modules')):
                        seeds |= set(a.get('modules', [])) | set(b.get('modules', []))
            elif path == RECIPES:
                before = previous['recipes'] if previous else {}
                after = current['recipes']
                seeds |= {n for n in before.keys() | after.keys() if before.get(n) != after.get(n)}
                if seeds:
                    seeds |= REGISTRIES & g.keys()
            else:
                before = previous['owners'] if previous else {}
                seeds |= {n for n in before.keys() | owners.keys() if before.get(n) != owners.get(n)}
                # Import/source changes in the catalog are integrity checked against real Lean imports,
                # never used to shrink the proof graph.
            if seeds:
                rule, level = 'declarative-relations-changed', 'scoped'
        elif path.startswith(TRUST) or path in POLICY_DOCS or path in TRUST_TESTS or 'conformance' in path and path.startswith(('docs/', 'tests/')):
            rule = 'trusted-mechanism-or-configuration'
        elif path.endswith('.lean') and (path.startswith('Verification/') or path == 'Verification.lean'):
            rule, level = 'proof-source-changed', 'scoped'
            seeds = {path[:-5].replace('/', '.')} if path != 'Verification.lean' else set(g) & REGISTRIES
        elif path in reviewed_test_files:
            rule, level, proof_work = 'explicitly-selected-unittest', 'scoped', True
        elif path.startswith('tests/lean/') and path.endswith('.lean') and tests:
            test_imports = imports((root / path).read_text()) if (root / path).exists() else set()
            if test_imports and test_imports <= g.keys():
                rule, level, seeds = 'lean-regression-with-reviewed-tests', 'scoped', test_imports
        elif path.startswith(('docs/', 'knowledge/')) and path.endswith(('.md', '.json')) or path in {'README.md', 'CHANGELOG.md'}:
            rule, level = 'documentation-only', 'metadata'
        if level == 'beta':
            effective = 'alpha' if rank == 'alpha' else 'beta'
            reasons.append(path + ': ' + rule)
        if seeds:
            proof_work = True
            changed_seeds |= seeds
        explanations.append(dict(path=path, rule=rule, seeds=sorted(seeds), required_control=level,
                                 prior_evidence='Compare bound inputs, closure, tools, configuration and command; never infer validity from file type'))
    # Old edges preserve effects of removed/renamed modules and removed imports.
    union = {n: g.get(n, set()) | old_g.get(n, set()) for n in g.keys() | old_g.keys()}
    selected |= changed_seeds & g.keys()
    if rank == 'gamma':
        if direction not in current['sections']:
            raise ValueError('Gamma requires a catalog direction')
        if proof_work:
            selected |= {n for n, d in owners.items() if d == direction}
    if rank == 'delta':
        if batch in current['infrastructure_batches']:
            direction = 'verification-infrastructure'
            if not paths:
                raise ValueError('Infrastructure batch requires a change set')
        elif batch in current['batches']:
            direction = current['batches'][batch]['direction']
            if proof_work:
                selected |= set(current['batches'][batch]['modules'])
        else:
            raise ValueError('Delta requires a registered batch')
    if effective in ('alpha', 'beta'):
        selected = set(g)
    elif not selected and (not paths or proof_work and not changed_seeds):
        raise ValueError('Explicit module scope is required')
    affected = (closure(union, changed_seeds, reverse=True) & g.keys()) | closure(g, selected, reverse=True)
    directions = {owners[n] for n in affected - REGISTRIES if n in owners}
    if effective not in ('alpha', 'beta') and len(directions) > 1:
        reasons.append('Cross-direction reverse dependencies: validate all listed directions')
        effective = 'gamma'
        while True:
            before = set(affected)
            affected |= {n for n, d in owners.items() if d in directions}
            affected = closure(g, affected, reverse=True)
            directions = {owners[n] for n in affected - REGISTRIES if n in owners}
            if affected == before:
                break
    imported = closure(g, affected)
    # Maximal importing roots cover the entire affected axiom closure without auditing each node again.
    audit_roots = affected - {d for n in affected for d in g[n] if d in affected}
    level = effective if effective in ('alpha', 'beta') else ('scoped' if affected else 'metadata')
    commands = [['python3', 'tools/verification_metadata.py'], ['python3', 'scripts/check_knowledge.py'], ['git', 'diff', '--check']]
    if level == 'scoped':
        commands += [['lake', 'build', '--wfail', *sorted(affected), *(['Verification'] if (root / 'Verification.lean').exists() else [])]]
        commands += [['python3', 'tools/verifier_skill.py', 'verify', n] for n in sorted(audit_roots)]
        if tests:
            commands += [['python3', '-m', 'unittest', '-v', *sorted(set(tests))]]
    if level in ('alpha', 'beta'):
        commands = []  # The authoritative runner is release_evidence.py run-beta.
    return dict(schema_version=2, requested_rank=rank, effective_rank=effective, verification_level=level,
                base_sha=base_sha, changed=paths, direction=direction, batch=batch, selected=sorted(selected),
                reverse_dependents=sorted(affected - selected), build_modules=sorted(affected),
                imported_closure=sorted(imported), audit_roots=sorted(audit_roots), directions=sorted(directions),
                reasons=reasons, explanations=explanations, registry_build_required=bool(affected & REGISTRIES),
                commands=commands, tests=sorted(set(tests)), test_selection_required=level == 'scoped' and not tests,
                test_selection='Explicit reviewed tests required for scoped runs; beta runs all',
                semantic_conformance='Registered pinned contracts only; not universal intent checking')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    p.add_argument('--rank', choices=RANKS, required=True)
    p.add_argument('--module', action='append', default=[])
    p.add_argument('--direction'); p.add_argument('--batch'); p.add_argument('--base')
    p.add_argument('--changed', action='append', default=[])
    p.add_argument('--test', action='append', default=[])
    a = p.parse_args()
    try:
        print(json.dumps(plan(a.project, a.rank, a.module, a.direction, a.batch, a.changed, a.base, a.test), indent=2))
    except (ValueError, OSError, KeyError, TypeError, subprocess.CalledProcessError) as e:
        p.exit(1, str(e) + '\n')

if __name__ == '__main__':
    main()
