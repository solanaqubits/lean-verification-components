"""Conditional range composition: exact kernel checks, executable branches and registry."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class RangeWitnessLiveTests(unittest.TestCase):
    def run_lean(self, file):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run([lake, 'env', 'lean', '-DwarningAsError=true', file],
                                cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def test_kernel_and_executable_contract(self):
        output = self.run_lean('tests/lean/range_witness_regression.lean')
        import json
        error = 'error:CryptoBulletproofsRangeWitnessExtraction.ExtractionError.'
        expected = ['witness:3', 'relation:[0, 0, 0, 0, 3, 98, 0]',
                    'relation:[1, 100, 0, 0, 0, 0, 0]']
        expected += [error + 'invalidOpenings'] * 3
        expected += [error + 'invalidFamily'] * 6
        expected += ['witness:3'] + [error + 'invalidFamily'] * 3
        lines = [line.strip() for line in output.splitlines() if line.strip()]
        self.assertEqual(lines, [json.dumps(x) for x in expected] + ['(true, true)'])

    def test_master_registry_projection(self):
        self.run_lean('tests/lean/range_witness_registry.lean')


if __name__ == '__main__':
    unittest.main()
