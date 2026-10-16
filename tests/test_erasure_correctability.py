"""Kernel and registry checks for Erasure correctability."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class ErasureCorrectabilityLiveTests(unittest.TestCase):
    def run_lean(self, file):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run([lake, 'env', 'lean', '-DwarningAsError=true', file],
                                cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def test_erasure_correctability_contract(self):
        self.run_lean('tests/lean/erasure_correctability_regression.lean')

    def test_master_registry_projection(self):
        self.run_lean('tests/lean/erasure_correctability_registry.lean')


if __name__ == '__main__':
    unittest.main()
