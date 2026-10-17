"""Historical epoch identity: accepted certificates, reused indices and global liabilities."""
import os
from pathlib import Path
import re
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class TendermintEpochIdentityLiveTests(unittest.TestCase):
    def run_lean(self, file):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run([lake, 'env', 'lean', '-DwarningAsError=true', file],
                                cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def test_kernel_and_executable_contract(self):
        output = self.run_lean('tests/lean/tendermint_epoch_identity_regression.lean')
        results = re.findall(r'\("([^"]+)",\s*(true|false)\)', output)
        expected = ['accepted', 'reused index', 'old queue', 'deadline', 'full', 'replay', 'permutation', 'missing', 'ambiguous', 'duplicate', 'bounds', 'dimension', 'envelope', 'reference', 'future', 'expired', 'phase', 'rate', 'conservation', 'reachable']
        self.assertEqual(results, [(name, 'true') for name in expected], output)

    def test_master_registry_projection(self):
        self.run_lean('tests/lean/tendermint_epoch_identity_registry.lean')


if __name__ == '__main__':
    unittest.main()
