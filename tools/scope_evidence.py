#!/usr/bin/env python3
"""Execute scoped plans and reuse only externally accepted, exactly bound checks.
Hashes establish identity, not authorship. Run only in a trusted checkout.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
from release_evidence import digest, runtime_fingerprint
from verification_plan import plan, graph, closure, imports
from verification_metadata import DATA_FILES


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode()


def hash_object(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def files(root, names):
    result = {}
    for name in sorted(set(names)):
        p = root / name
        if not p.is_file() or p.is_symlink():
            raise ValueError('Missing or symlinked evidence input: ' + name)
        result[name] = digest(p)
    return result


def fingerprint(root, p, command, runtime=None):
    root = Path(root)
    def under(directory):
        return [str(f.relative_to(root)) for f in (root / directory).rglob('*')
                if f.is_file() and '__pycache__' not in f.parts and f.suffix != '.pyc']
    proof = command[0] == 'lake' or 'tools/verifier_skill.py' in command
    inputs = [n.replace('.', '/') + '.lean' for n in p['build_modules']] if proof else []
    if proof and (root / 'Verification.lean').exists():
        inputs += ['Verification.lean']
    # Tests and metadata checks bind all of their data, not just modules inferred from names.
    if not proof:
        inputs += under('knowledge') + under('tests') + under('Verification')
        inputs += [n for n in DATA_FILES if (root / n).exists()]
        if (root / 'Verification.lean').exists():
            inputs += ['Verification.lean']
    required = set(p['imported_closure'])
    if command[:2] == ['lake', 'build'] and 'Verification' in command[2:]:
        # The root build can reach more sources than a standalone module's scope.
        required |= closure(graph(root), imports((root / 'Verification.lean').read_text()))
    deps = [n.replace('.', '/') + '.lean' for n in required if n not in p['build_modules']]
    tools = [n for n in under('tools') + under('scripts') + under('.agents') + under('.github') if n not in DATA_FILES]
    config = [n for n in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'VERSIONING.md'] if (root / n).exists()]
    env = {k: os.environ.get(k) for k in ('PATH', 'LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_OPTS', 'LEAN_FLAGS', 'LAKE_HOME', 'ELAN_HOME', 'PYTHONPATH')}
    env['LEAN_VERIFIER_LIVE_TESTS'] = '1'
    values = dict(inputs=files(root, inputs), dependencies=files(root, deps), tools=files(root, tools),
                  configuration=files(root, config), runtime=runtime if runtime is not None else runtime_fingerprint(root),
                  command=command, environment=env)
    if command == ['git', 'diff', '--check']:
        values['git_diff'] = subprocess.check_output(['git', 'diff', '--binary', 'HEAD', '--'], cwd=root).decode()
        values['git_index'] = subprocess.check_output(['git', 'diff', '--binary', '--cached', '--'], cwd=root).decode()
    # Tagged canonical structure, never XOR: group/order changes cannot cancel out.
    return dict(schema_version=1, groups=values, sha256=hash_object(values))


def differences(old, new):
    return [dict(component=k, reason='bound-component-changed') for k in sorted(set(old['groups']) | set(new['groups']))
            if old['groups'].get(k) != new['groups'].get(k)]


def load_accepted(directory, accepted_digest):
    directory = Path(directory).resolve()
    if not accepted_digest or digest(directory / 'evidence.json') != accepted_digest:
        raise ValueError('An externally accepted evidence digest is required and must match')
    report = json.loads((directory / 'evidence.json').read_text())
    if report.get('schema_version') != 1 or report.get('status') != 'passed' or report.get('kind') != 'scoped-checks':
        raise ValueError('Incomplete scoped evidence')
    checks = report['checks']
    if not checks or len({hash_object(c['command']) for c in checks}) != len(checks):
        raise ValueError('Missing or duplicate checks')
    for check in checks:
        log = directory / check['log']
        if log.parent != directory or log.is_symlink() or check['exit_code'] != 0 or digest(log) != check['log_sha256']:
            raise ValueError('Failed check or changed log')
        f = check['fingerprint']
        if hash_object(f['groups']) != f['sha256'] or check['command'] != f['groups']['command']:
            raise ValueError('Malformed fingerprint')
        validate_output(check['command'], log.read_text())
    return report


def reuse_decision(check, current):
    changes = differences(check['fingerprint'], current)
    return dict(reusable=not changes and check['fingerprint'] == current, invalidations=changes)


def validate_output(command, output):
    if 'tools/verifier_skill.py' in command:
        report = json.loads(output)
        if not report.get('ok') or not report.get('source_unchanged') or report.get('policy_findings') or report['audit']['violations']:
            raise ValueError('Invalid scoped verifier result')
        if not set(report['audit']['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}:
            raise ValueError('Unexpected axiom')
    if 'unittest' in command:
        if not re.search(r'Ran [1-9][0-9]* tests?', output) or not re.search(r'^OK\s*$', output, re.M) or re.search(r'\bskipped\b', output, re.I):
            raise ValueError('Missing tests, failures or skips')
    if command[:2] == ['lake', 'build'] and ('Build completed successfully' not in output or re.search(r'\bwarning:', output, re.I)):
        raise ValueError('Invalid strict build')


def run_scoped(root, output, p, reuse=None, accepted_digest=None):
    root, output = Path(root).resolve(), Path(output).resolve()
    if p['verification_level'] in ('alpha', 'beta'):
        raise ValueError('Full control required: use release_evidence.py run-beta; reasons: ' + '; '.join(p['reasons']))
    if p['test_selection_required']:
        raise ValueError('Explicit reviewed unittest selection required')
    if output.is_relative_to(root):
        raise ValueError('Evidence must be outside the checkout')
    old = load_accepted(reuse, accepted_digest) if reuse else {'checks': []}
    output.mkdir(parents=True, exist_ok=False)
    runtime = runtime_fingerprint(root)
    before = [fingerprint(root, p, cmd, runtime) for cmd in p['commands']]
    report = dict(schema_version=1, kind='scoped-checks', status='running', plan=p, checks=[],
                  reused_from=accepted_digest if reuse else None)
    for index, (command, current) in enumerate(zip(p['commands'], before)):
        cached = next((c for c in old['checks'] if c['command'] == command), None)
        decision = reuse_decision(cached, current) if cached else dict(reusable=False, invalidations=[dict(component='check', reason='no-accepted-result')])
        log = output / f'{index:02d}.log'
        start = time.monotonic()
        if decision['reusable']:
            shutil.copyfile(Path(reuse) / cached['log'], log)
            code = 0
        else:
            with log.open('w') as stream:
                completed = subprocess.run(command, cwd=root, env={**os.environ, 'LEAN_VERIFIER_LIVE_TESTS': '1'},
                                           stdout=stream, stderr=subprocess.STDOUT, timeout=7200)
            code = completed.returncode
        check = dict(command=command, fingerprint=current, exit_code=code, log=log.name, log_sha256=digest(log),
                     seconds=round(time.monotonic() - start, 3), **decision)
        report['checks'].append(check)
        (output / 'evidence.json').write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps(dict(command=command, **decision)), flush=True)
        if code:
            raise ValueError('Scoped command failed')
        validate_output(command, log.read_text())
    after_runtime = runtime_fingerprint(root)
    if before != [fingerprint(root, p, cmd, after_runtime) for cmd in p['commands']]:
        raise ValueError('Bound inputs or runtime changed during checks')
    report['status'] = 'passed'
    (output / 'evidence.json').write_text(json.dumps(report, indent=2) + '\n')
    return dict(ok=True, checks=len(report['checks']), reused=sum(c['reusable'] for c in report['checks']),
                evidence_sha256=digest(output / 'evidence.json'), authentication='Requires external acceptance; digest alone is not authentication')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--base', required=True)
    parser.add_argument('--rank', required=True, choices=['gamma', 'delta', 'epsilon', 'zeta'])
    parser.add_argument('--module', action='append', default=[])
    parser.add_argument('--direction'); parser.add_argument('--batch')
    parser.add_argument('--test', action='append', default=[])
    parser.add_argument('--output', required=True)
    parser.add_argument('--reuse'); parser.add_argument('--accepted-digest')
    a = parser.parse_args()
    try:
        p = plan(a.project, a.rank, a.module, a.direction, a.batch, base=a.base, tests=a.test)
        print(json.dumps(run_scoped(a.project, a.output, p, a.reuse, a.accepted_digest), indent=2))
    except (ValueError, OSError, KeyError, TypeError, subprocess.SubprocessError) as e:
        parser.exit(1, str(e) + '\n')

if __name__ == '__main__':
    main()
