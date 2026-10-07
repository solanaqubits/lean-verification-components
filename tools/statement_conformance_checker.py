#!/usr/bin/env python3
"""Pinned Simon statement-conformance pilot for a TRUSTED LOCAL Lean project.

Not a sandbox for hostile metaprograms, a general non-vacuity decision procedure,
or a formally verified Python checker. The contract manifest and this program
must be reviewed independently of candidates. No automatic rebaselining.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import tempfile

from verifier_skill import Verifier, VerificationError, IDENTIFIER, policy_findings

ROOT = Path(__file__).resolve().parents[1]
BRIDGE = 'Verification.Specs.QuantumSimonsConformance'
GOLD = 'Verification.Specs.QuantumSimonsSpec'
SCOPE = {
    'contract': 'Simon independent definitions and seven suite field types',
    'comparison': 'Lean definitional equality; kernel-checked fieldwise bridge',
    'satisfiability': 'explicit n=1, m=0 promise and n=1 recovery-hypothesis witnesses only',
    'vacuity': 'explicit False antecedents in selected field expressions plus pinned contract comparison',
    'universal_nonvacuity': False,
    'arbitrary_propositional_equivalence_decision': False,
    'hostile_metaprogram_sandbox': False,
    'python_or_hashing_formally_verified': False,
    'trust': 'reviewed gold, bridge, probe, checker, manifest, Lean/Lake and pinned dependencies',
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot(root):
    paths = list((root / 'Verification').rglob('*.lean')) + [root / 'Verification.lean']
    paths += [root / p for p in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
              'tools/statement_conformance_contract.json', 'tools/statement_conformance_probe.lean',
              'tools/statement_conformance_checker.py', 'tools/verifier_skill.py']]
    return {str(p.relative_to(root)): digest(p) for p in paths}


def check(project=ROOT, candidate_module='Verification.QuantumSimonsAlgorithm',
          candidate_namespace='QuantumSimonsAlgorithm', timeout=180):
    report = {'ok': False, 'conformance_status': 'not_checked', 'axiom_status': 'not_checked',
              'satisfiability_status': 'not_checked', 'epistemic_scope': SCOPE, 'steps': []}
    try:
        root = Path(project).resolve()
        if not IDENTIFIER.fullmatch(candidate_module) or not candidate_module.startswith('Verification.'):
            raise VerificationError('Candidate module must be a regular Verification module name')
        if not IDENTIFIER.fullmatch(candidate_namespace):
            raise VerificationError('Candidate namespace must be a regular qualified name')
        verifier = Verifier(root, timeout=timeout)
        with verifier.locked():
            manifest = json.loads((root / 'tools/statement_conformance_contract.json').read_text())
            if manifest.get('schema_version') != 1:
                raise VerificationError('Unsupported contract manifest version')
            expected_paths = {f'Verification/Specs/{name}.lean' for name in
                              ['QuantumSimonsSpec', 'QuantumSimonsConformance']}
            expected_paths |= {'tools/statement_conformance_probe.lean', 'lean-toolchain'}
            if set(manifest['trusted_sha256']) != expected_paths:
                raise VerificationError('Unexpected trusted-file set')
            for path, expected in manifest['trusted_sha256'].items():
                if digest(root / path) != expected:
                    raise VerificationError(f'Trusted contract hash mismatch: {path}')
            report['contract_version'] = manifest['contract_version']
            modules = list(dict.fromkeys([GOLD, BRIDGE, candidate_module]))
            closure = verifier.closure(modules)
            findings = [dict(f, module=m) for m, p in closure.items()
                        for f in policy_findings(p.read_text())]
            if findings:
                report['policy_findings'] = findings
                raise VerificationError('Source-policy violation')
            before = snapshot(root)
            report['source_sha256'] = before
            commands = [[verifier.lake, 'build', '--wfail', *modules]]
            commands += [[verifier.lake, 'env', 'lean', '-DwarningAsError=true',
                          str(verifier.source(m)[0].relative_to(root))] for m in modules]
            for cmd in commands:
                result = verifier.run(cmd)
                report['steps'].append(result)
                if result['returncode'] != 0 or result['timeout']:
                    report['failure_stage'] = 'strict_compilation'
                    raise VerificationError('Strict compilation failed or timed out')
            template = (root / 'tools/statement_conformance_probe.lean').read_text()
            probe = template.replace('-- CANDIDATE_IMPORT', 'import ' + candidate_module)
            probe = probe.replace('__CANDIDATE__', candidate_namespace)
            with tempfile.TemporaryDirectory(prefix='simon-conformance-') as tmp:
                path = Path(tmp) / 'Probe.lean'
                path.write_text(probe)
                result = verifier.run([verifier.lake, 'env', 'lean', '-DwarningAsError=true', str(path)])
            report['steps'].append(result)
            # A later run_cmd can print a success-shaped record despite an earlier Lean error.
            # Accept only a successful process AND exactly one well-formed record.
            matches = re.findall(r'^STATEMENT_CONFORMANCE_JSON=(.*)$', result['output'], re.M)
            if result['returncode'] != 0 or result['timeout'] or len(matches) != 1:
                report['failure_stage'] = 'contract_probe'
                raise VerificationError('Contract probe failed, timed out, or omitted its unique report')
            evidence = json.loads(matches[0])
            if (evidence.get('ok') is not True or evidence.get('violations') != []
                    or evidence.get('checked_definitions') != 16
                    or evidence.get('checked_suite_fields') != 7
                    or not set(evidence.get('axioms', [])) <= {'propext', 'Classical.choice', 'Quot.sound'}
                    or evidence.get('audited_declarations', 0) <= 0):
                raise VerificationError('Invalid kernel-audit evidence')
            if before != snapshot(root):
                report['failure_stage'] = 'source_stability'
                raise VerificationError('Sources or trusted configuration changed during checking')
            report.update(ok=True, conformance_status='pass', axiom_status='pass',
                          satisfiability_status='pass_concrete_instances', evidence=evidence,
                          source_unchanged=True)
    except (VerificationError, OSError, ValueError, KeyError, TypeError) as exc:
        report['error'] = str(exc)
        report['conformance_status'] = 'fail'
        # Failure is never silently converted to an acceptance or universal semantic claim.
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=ROOT)
    parser.add_argument('--candidate-module', default='Verification.QuantumSimonsAlgorithm')
    parser.add_argument('--candidate-namespace', default='QuantumSimonsAlgorithm')
    parser.add_argument('--timeout', type=int, default=180)
    args = parser.parse_args()
    report = check(args.project, args.candidate_module, args.candidate_namespace, args.timeout)
    print(json.dumps(report, indent=2))
    return 0 if report['ok'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
