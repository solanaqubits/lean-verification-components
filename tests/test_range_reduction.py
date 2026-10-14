"""Formal polynomial range reduction and executable IPA composition."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class BulletproofsRangeReductionLiveTests(unittest.TestCase):
    def test_range_reduction_composition_and_corruption(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(
            [lake, 'env', 'lean', '-DwarningAsError=true',
             'tests/lean/range_reduction_regression.lean'],
            cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('RANGE_REDUCTION_EXEC_OK: 13 cases', result.stdout)


if __name__ == '__main__':
    unittest.main()
