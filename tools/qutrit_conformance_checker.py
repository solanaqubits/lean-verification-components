#!/usr/bin/env python3
"""Pinned module-190 conformance checks in a trusted local Lean project."""
import argparse
import hashlib
import json
from pathlib import Path
import tempfile
from verifier_skill import Verifier, IDENTIFIER, VerificationError
from statement_conformance_checker import snapshot

ROOT = Path(__file__).resolve().parents[1]
DEFAULT = 'Verification.QuantumQutritSecretSharingExplicitDecoder'


def check(root=ROOT, module=DEFAULT, namespace='QuantumQutritSecretSharingExplicitDecoder'):
    root = Path(root).resolve()
    r = dict(ok=False, steps=[], conformance_status='fail',
             scope='8 selected definitions/operators and 7 theorem signatures; kernel bridge; finite table',
             universal_intent_check=False, sandbox=False)
    try:
        if not IDENTIFIER.fullmatch(module) or not module.startswith('Verification.') or not IDENTIFIER.fullmatch(namespace):
            raise ValueError('Invalid candidate identifier')
        manifest_path = root / 'tools/qutrit_conformance_contract.json'
        manifest = json.loads(manifest_path.read_text())
        expected = {'Verification/Specs/QuantumQutritDecoderSpec.lean',
                    'tools/qutrit_conformance_probe.lean', 'lean-toolchain'}
        if manifest['schema_version'] != 1 or set(manifest['trusted_sha256']) != expected:
            raise ValueError('Invalid trust manifest')
        for p, h in manifest['trusted_sha256'].items():
            if hashlib.sha256((root / p).read_bytes()).hexdigest() != h:
                raise ValueError('Trusted contract hash mismatch: ' + p)
        verifier = Verifier(root)
        with verifier.locked():
            before = snapshot(root)
            extra = {p:hashlib.sha256((root / p).read_bytes()).hexdigest() for p in
                     ['tools/qutrit_conformance_checker.py', 'tools/qutrit_conformance_contract.json',
                      'tools/qutrit_conformance_probe.lean']}
            build = verifier.run([verifier.lake, 'build', '--wfail',
                                  'Verification.Specs.QuantumQutritDecoderSpec', module])
            r['steps'].append(build)
            if build['returncode'] or build['timeout']:
                raise ValueError('Candidate build failed')
            text = (root / 'tools/qutrit_conformance_probe.lean').read_text().replace(
                '-- CANDIDATE_IMPORT', 'import ' + module).replace('__CANDIDATE__', namespace)
            with tempfile.TemporaryDirectory(prefix='qutrit-conformance-') as tmp:
                p = Path(tmp) / 'Probe.lean';p.write_text(text)
                result = verifier.run([verifier.lake, 'env', 'lean', '-DwarningAsError=true', str(p)])
            r['steps'].append(result)
            marker = 'QUTRIT_CONFORMANCE_OK definitions=8 statements=7'
            if result['returncode'] or result['timeout'] or result['output'].count(marker) != 1:
                raise ValueError('Contract probe failed')
            if snapshot(root) != before or any(hashlib.sha256((root / p).read_bytes()).hexdigest() != h for p,h in extra.items()):
                raise ValueError('Inputs changed during checking')
            r.update(ok=True, conformance_status='pass', source_sha256={**before, **extra},
                     source_unchanged=True, contract_version=manifest['contract_version'])
    except (ValueError, OSError, KeyError, TypeError, VerificationError) as e:
        r['error'] = str(e)
    return r


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--project', type=Path, default=ROOT)
    a = p.parse_args();r = check(a.project);print(json.dumps(r,indent=2))
    return 0 if r['ok'] else 1
if __name__ == '__main__':
    raise SystemExit(main())
