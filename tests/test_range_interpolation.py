"""Kernel, executable and registry checks for the fixed-witness interpolation contract."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class RangeInterpolationLiveTests(unittest.TestCase):
    def run_lean(self, file):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run([lake, 'env', 'lean', '-DwarningAsError=true', file],
                                cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def test_kernel_and_executable_contract(self):
        output = self.run_lean('tests/lean/range_interpolation_regression.lean')
        values = [line.strip() for line in output.splitlines() if line.strip()]
        ok = 'Except.ok ()'
        def error(name):
            return f'Except.error (CryptoBulletproofsRangeInterpolation.GridError.{name})'
        self.assertEqual(values, [ok] * 5 + [error('invalidEquality')] * 2 +
                         [error('repeatedY')] + [error('repeatedZ')] * 2 +
                         [error('emptyWitness'), ok])

    def test_master_registry_projection(self):
        self.run_lean('tests/lean/range_interpolation_registry.lean')


if __name__ == '__main__':
    unittest.main()
