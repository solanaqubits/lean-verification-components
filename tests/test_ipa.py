"""Recursive IPA, expanded verification and corruption regressions."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class BulletproofsInnerProductLiveTests(unittest.TestCase):
    def test_ipa_folding_completeness_and_batch_verification(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(
            [lake, 'env', 'lean', '-DwarningAsError=true',
             'tests/lean/ipa_regression.lean'],
            cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('IPA_EXEC_OK: 12 cases', result.stdout)


if __name__ == '__main__':
    unittest.main()
