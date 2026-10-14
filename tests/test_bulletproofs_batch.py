"""Public residual batching, exact finite sampling, and unified MSM regressions."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class BulletproofsBatchLiveTests(unittest.TestCase):
    def test_batch_probability_and_msm(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(
            [lake, 'env', 'lean', '-DwarningAsError=true',
             'tests/lean/bulletproofs_batch_regression.lean'],
            cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('BULLETPROOFS_BATCH_EXEC_OK: 18 cases', result.stdout)
        self.assertIn('invalid accept counts 17/289, 17/289', result.stdout)


if __name__ == '__main__':
    unittest.main()
