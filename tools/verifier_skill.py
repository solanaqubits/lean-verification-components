#!/usr/bin/env python3
"""Lean verifier CLI and Python API for a trusted local Lake project.

The kernel checks submitted statements, not their natural-language meaning.
No shell interpolation, network service, LLM credentials or third-party Python
packages are required. See docs/verifier-skill.en.md for the trust boundary.
"""
from __future__ import annotations
import argparse
from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import tempfile
import time
import uuid

HERE = Path(__file__).resolve().parent
ALLOWED_AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']
IDENTIFIER = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z')
FORBIDDEN = {'sorry', 'admit', 'axiom', 'native_decide', 'unsafe', 'implemented_by',
             'extern', 'debug.skipKernelTC', 'debug.skipKernelTC.check'}


class VerificationError(Exception):
    pass


def code_only(text: str) -> str:
    """Mask nested Lean comments and strings, retaining offsets and line breaks."""
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2; continue
            if text.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2; continue
            if text[i] != '\n': out[i] = ' '
            i += 1; continue
        if string:
            if text[i] == '\\' and i + 1 < len(text):
                out[i:i+2] = ['\n' if c == '\n' else ' ' for c in text[i:i+2]]
                i += 2; continue
            if text[i] == '"': string = False
            if text[i] != '\n': out[i] = ' '
            i += 1; continue
        if text.startswith('--', i):
            end = text.find('\n', i)
            if end == -1: end = len(text)
            out[i:end] = ' ' * (end-i); i = end; continue
        if text.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2; continue
        if text[i] == '"':
            out[i] = ' '; string = True
        i += 1
    return ''.join(out)


def policy_findings(text: str) -> list[dict]:
    cleaned = code_only(text)
    return [{'token': m.group(), 'line': cleaned.count('\n', 0, m.start()) + 1}
            for m in re.finditer(r'[A-Za-z_][A-Za-z_0-9.]*', cleaned)
            if m.group() in FORBIDDEN]


class Verifier:
    def __init__(self, project: str | Path, lake: str | None = None, timeout: int = 600):
        self.project = Path(project).resolve()
        if not (self.project / 'lean-toolchain').is_file():
            raise VerificationError('Project must contain lean-toolchain')
        selected = lake or shutil.which('lake')
        if not selected and (Path.home() / '.elan/bin/lake').is_file():
            selected = str(Path.home() / '.elan/bin/lake')
        if not selected:
            raise VerificationError('lake not found; use --lake or install elan')
        self.lake = str(Path(selected).absolute()) if '/' in selected else selected
        if timeout <= 0: raise VerificationError('Timeout must be positive')
        self.timeout = timeout

    @contextmanager
    def locked(self):
        path = self.project / '.lake/verifier.lock'
        path.parent.mkdir(exist_ok=True)
        with path.open('w') as lock:
            deadline = time.monotonic() + self.timeout
            while True:
                try:
                    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB); break
                except BlockingIOError:
                    if time.monotonic() >= deadline:
                        raise VerificationError('Another verifier operation holds the project lock')
                    time.sleep(0.1)
            try: yield
            finally: fcntl.flock(lock, fcntl.LOCK_UN)

    def run(self, args: list[str]) -> dict:
        start = time.monotonic()
        with tempfile.TemporaryFile() as log:
            process = subprocess.Popen(args, cwd=self.project, stdout=log,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            timed_out = False
            try: process.wait(timeout=self.timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                try: os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError: pass
                process.wait()
            except BaseException:
                try: os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError: pass
                process.wait()
                raise
            size = log.tell()
            log.seek(max(0, size-120000))
            output = log.read().decode('utf-8', errors='replace')
        return {'command': args, 'returncode': process.returncode, 'timeout': timed_out,
                'seconds': round(time.monotonic()-start, 3), 'output': output,
                'output_truncated': size > 120000}

    def source(self, value: str) -> tuple[Path, str]:
        if value.startswith('Verification.') and not value.endswith('.lean'):
            value = value.replace('.', '/') + '.lean'
        path = Path(value)
        path = (self.project / path).resolve() if not path.is_absolute() else path.resolve()
        try: relative = path.relative_to(self.project / 'Verification')
        except ValueError: raise VerificationError('Module must be inside project/Verification')
        module = 'Verification.' + '.'.join(relative.with_suffix('').parts)
        if path.suffix != '.lean' or not path.is_file() or not IDENTIFIER.fullmatch(module):
            raise VerificationError('Expected an existing Lean module with a regular module name')
        return path, module

    def closure(self, modules: list[str]) -> dict[str, Path]:
        found = {}
        def visit(module):
            if module in found: return
            path, _ = self.source(module)
            found[module] = path
            for dependency in re.findall(r'^import\s+(Verification\.[\w.]+)\s*$',
                                          code_only(path.read_text()), re.M):
                visit(dependency)
        for module in modules: visit(module)
        return found

    def audit(self, modules: list[str]) -> tuple[dict, dict | None]:
        for module in modules:
            if not IDENTIFIER.fullmatch(module): raise VerificationError('Invalid module identifier')
        code = (HERE / 'audit_template.lean').read_text().replace(
            '-- IMPORTS', '\n'.join('import ' + module for module in modules))
        with tempfile.TemporaryDirectory(prefix='lean-verifier-audit-') as tmp:
            path = Path(tmp) / 'Audit.lean'; path.write_text(code)
            result = self.run([self.lake, 'env', 'lean', '-DwarningAsError=true', str(path)])
        matches = re.findall(r'^VERIFIER_AUDIT_JSON=(.*)$', result['output'], re.M)
        audit = json.loads(matches[-1]) if matches else None
        return result, audit

    def _verify(self, values: list[str]) -> dict:
        modules = [self.source(value)[1] for value in values]
        closure = self.closure(modules)
        contents = {module: path.read_bytes() for module, path in closure.items()}
        report = {'ok': False, 'modules': modules, 'allowed_axioms': ALLOWED_AXIOMS,
                  'source_sha256': {m: hashlib.sha256(b).hexdigest() for m,b in contents.items()},
                  'policy_findings': [], 'steps': [], 'audit': None}
        for module, content in contents.items():
            report['policy_findings'] += [dict(f, module=module)
                                         for f in policy_findings(content.decode())]
        if report['policy_findings']: return report
        build = self.run([self.lake, 'build', '--wfail', *modules])
        report['steps'].append(build)
        if build['returncode'] != 0: return report
        for module in modules:
            check = self.run([self.lake, 'env', 'lean', '-DwarningAsError=true',
                              str(closure[module].relative_to(self.project))])
            report['steps'].append(check)
            if check['returncode'] != 0: return report
        step, audit = self.audit(modules)
        report['steps'].append(step); report['audit'] = audit
        unchanged = all(path.read_bytes() == contents[m] for m,path in closure.items())
        report['source_unchanged'] = unchanged
        report['ok'] = bool(unchanged and step['returncode'] == 0 and audit
                            and audit['declarations'] > 0 and not audit['violations'])
        return report

    def verify_module(self, file_path: str) -> dict:
        with self.locked(): return self._verify([file_path])

    def audit_module(self, file_path: str) -> dict:
        """Audit only after strict compilation and rebuilding; never trust stale oleans."""
        report = self.verify_module(file_path)
        report['operation'] = 'audit'
        return report

    def verify_all(self) -> dict:
        with self.locked():
            paths = sorted(str(p.relative_to(self.project))
                           for p in (self.project / 'Verification').rglob('*.lean'))
            return self._verify(paths)

    def scaffold_invariant(self, domain: str, spec_text: str) -> dict:
        """Prove an explicit Lean proposition; natural-language translation belongs to the agent."""
        tactics = {'nat': 'omega', 'real-polynomial': 'intros; ring',
                   'real-inequality': 'intros; nlinarith'}
        if domain not in tactics:
            raise VerificationError('Supported domains: nat, real-polynomial, real-inequality')
        if not spec_text.strip(): raise VerificationError('A Lean proposition is required')
        if policy_findings(spec_text): raise VerificationError('Specification violates source policy')
        candidate = 'VerifierCandidate' + uuid.uuid4().hex
        code = ('import Mathlib.Data.Real.Basic\nimport Mathlib.Tactic.Linarith\n'
                'import Mathlib.Tactic.Ring\n\nset_option linter.style.header false\n\n'
                f'namespace {candidate}\n\n'
                f'theorem invariant : {spec_text} := by\n  {tactics[domain]}\n\n'
                f'end {candidate}\n')
        path = self.project / 'Verification' / (candidate + '.lean')
        with self.locked():
            try:
                path.write_text(code)
                report = self._verify([str(path)])
                return {'ok': report['ok'], 'lean_code': code if report['ok'] else None,
                        'verification': report, 'scope_review_required': True,
                        'note': 'Input must be a Lean proposition. No natural-language equivalence is certified.'}
            finally:
                path.unlink(missing_ok=True)
                for base in ['.lake/build/lib/lean/Verification', '.lake/build/ir/Verification']:
                    for artifact in (self.project / base).glob(candidate + '.*'):
                        if artifact.is_file(): artifact.unlink()

    def integration_plan(self, module_name: str, suite_struct: str) -> dict:
        _, module = self.source(module_name)
        targets = json.loads((HERE / 'integration_targets.json').read_text())
        target = targets.get(module)
        if not target or target['suite_struct'] != suite_struct:
            raise VerificationError('No explicit integration recipe for this module/suite; add a reviewed recipe')
        master_path = self.project / 'Verification/MasterSuite.lean'
        original = master_path.read_text(); updated = original
        field_line = f"  {target['field']} : {target['suite_type']}"
        value_line = f"  {target['field']} := {target['proof']}"
        for start, line in [(f"structure {target['parent']} : Prop", field_line),
                            (f"theorem {target['constructor']} :", value_line)]:
            pattern = re.compile(r'^' + re.escape(start) + r'[^\n]*\n(?P<body>(?:[^\n]+\n)*?)\n', re.M)
            matches = list(pattern.finditer(updated))
            if len(matches) != 1: raise VerificationError('Registry layout changed; manual integration required')
            match = matches[0]
            existing = re.search(r'^  ' + re.escape(target['field']) + r'\s*[:=]', match.group('body'), re.M)
            if existing:
                if line + '\n' not in match.group('body'):
                    raise VerificationError('Existing field conflicts with integration recipe')
            else:
                body = match.group('body')
                if start.startswith('theorem'):
                    if not body.endswith('}\n'): raise VerificationError('Unsupported constructor layout')
                    body = body[:-2] + line + '\n}\n'
                else: body += line + '\n'
                updated = updated[:match.start('body')] + body + updated[match.end('body'):]
        if 'import ' + module + '\n' not in updated: updated = 'import ' + module + '\n' + updated
        for universe in target.get('universes', []):
            if not re.search(r'^universe .*\b' + re.escape(universe) + r'\b', updated, re.M):
                updated = updated.replace('namespace MasterSuite\n', 'namespace MasterSuite\n\nuniverse ' + universe + '\n', 1)
        if target.get('registry_type'):
            before = '  distributed_suite : DistributedSystemsFullSuite'
            lines = updated.splitlines()
            matched = [i for i,line in enumerate(lines) if line.startswith(before)]
            if len(matched) != 1: raise VerificationError('Cannot identify distributed registry field')
            lines[matched[0]] = '  distributed_suite : ' + target['registry_type']
            updated = '\n'.join(lines) + '\n'
        root_path = self.project / 'Verification.lean'
        root_before = root_path.read_text()
        root_after = root_before if 'import ' + module + '\n' in root_before else 'import ' + module + '\n' + root_before
        import difflib
        changes = [('Verification/MasterSuite.lean', original, updated),
                   ('Verification.lean', root_before, root_after)]
        return {'module': module, 'changes': changes,
                'diff': ''.join(''.join(difflib.unified_diff(a.splitlines(True), b.splitlines(True),
                                         fromfile=name, tofile=name)) for name,a,b in changes)}

    def integrate_to_mastersuite(self, module_name: str, suite_struct: str) -> dict:
        with self.locked():
            plan = self.integration_plan(module_name, suite_struct)
            report = {'ok': False, 'diff': plan['diff'], 'rolled_back': False, 'steps': []}
            try:
                for name, before, after in plan['changes']:
                    (self.project / name).write_text(after)
                report['verification'] = self._verify(['Verification.MasterSuite'])
                if not report['verification']['ok']: return report
                step = self.run([self.lake, 'build', '--wfail']); report['steps'].append(step)
                if step['returncode'] != 0: return report
                report['ok'] = True
                report['knowledge_update_required'] = True
                return report
            finally:
                if not report['ok']:
                    for name, before, after in plan['changes']:
                        (self.project / name).write_text(before)
                    report['rolled_back'] = True

    def generate_knowledge_card(self, module_name: str) -> dict:
        report = self.verify_module(module_name)
        if not report['ok']: return {'ok': False, 'verification': report}
        path, module = self.source(module_name)
        name = module.split('.')[-1]
        declarations = []
        for number,line in enumerate(code_only(path.read_text()).splitlines(), 1):
            match = re.match(r'(?:@\[.*?\]\s*)?(?:theorem|lemma)\s+(\S+)', line)
            if match: declarations.append(f'- `{match[1]}` — line {number}')
        card = (f'---\nid: {name}\nlanguage: en\nsource: {path.relative_to(self.project)}\n'
                'novelty: not-assessed\nstatus: draft-needs-scope-review\n---\n\n'
                f'# {name}\n\n## Verified declarations\n\n' + '\n'.join(declarations) +
                '\n\n## Scope and unformalized aspects\n\n'
                'Automated checks established compilation and allowed axiom dependencies, '
                'not correspondence to the application specification. Review the assumptions '
                'and meaning against the Lean types. Module names do not '
                'prove protocol security or solve an open problem. '
                'Scientific priority is not established.\n\n## Verification evidence\n\n'
                f"Project declarations audited in the imported environment: {report['audit']['declarations']}.\n"
                f"Source SHA-256: `{report['source_sha256'][module]}`.\n")
        return {'ok': True, 'markdown': card, 'verification': report,
                'note': 'Draft only; existing knowledge cards are never overwritten.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', default=str(HERE.parent))
    parser.add_argument('--lake'); parser.add_argument('--timeout', type=int, default=600)
    sub = parser.add_subparsers(dest='action', required=True)
    sub.add_parser('verify-all')
    for action in ['verify', 'audit', 'card']:
        p = sub.add_parser(action); p.add_argument('module')
    p = sub.add_parser('scaffold'); p.add_argument('domain'); p.add_argument('--spec-file', required=True)
    p = sub.add_parser('integrate'); p.add_argument('module'); p.add_argument('suite'); p.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    try:
        verifier = Verifier(args.project, args.lake, args.timeout)
        if args.action == 'verify': result = verifier.verify_module(args.module)
        elif args.action == 'audit': result = verifier.audit_module(args.module)
        elif args.action == 'verify-all': result = verifier.verify_all()
        elif args.action == 'card': result = verifier.generate_knowledge_card(args.module)
        elif args.action == 'scaffold': result = verifier.scaffold_invariant(args.domain, Path(args.spec_file).read_text())
        elif args.apply: result = verifier.integrate_to_mastersuite(args.module, args.suite)
        else:
            plan = verifier.integration_plan(args.module, args.suite)
            result = {'ok': True, 'applied': False, 'diff': plan['diff']}
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0 if result['ok'] else 1
    except (VerificationError, OSError, ValueError) as error:
        print(json.dumps({'ok': False, 'error': str(error)}, ensure_ascii=False)); return 2


if __name__ == '__main__':
    raise SystemExit(main())
