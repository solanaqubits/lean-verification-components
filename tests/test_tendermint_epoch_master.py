"""Composite safety, historical attribution, unbonding, replay and settlement."""
import os
from pathlib import Path
import re
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class TendermintEpochMasterLiveTests(unittest.TestCase):
    def run_lean(self, file):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run([lake, 'env', 'lean', '-DwarningAsError=true', file],
                                cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def test_kernel_and_executable_contract(self):
        output = self.run_lean('tests/lean/tendermint_epoch_master_regression.lean')
        results = re.findall(r'\("([^"]+)",\s*(true|false)\)', output)
        expected = ['nonzero weight shift', 'shifted later commit', 'historical attribution', 'global identity', 'left membership', 'queued liability', 'half debit', 'deadline payout', 'innocent balance', 'conservation', 'processed', 'full debit', 'expired no debit', 'expired payout', 'future', 'closed', 'stale', 'zero stake', 'missing history', 'ambiguous history', 'missing reference', 'wrong height', 'not liable tranche', 'honest payout', 'safe round zero', 'safe later round', 'safe withdrawal']
        self.assertEqual(results, [(name, 'true') for name in expected], output)

    def test_master_registry_projection(self):
        self.run_lean('tests/lean/tendermint_epoch_master_registry.lean')


if __name__ == '__main__':
    unittest.main()
