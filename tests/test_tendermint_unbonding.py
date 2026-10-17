"""Two-phase unbonding: exact payouts, liability cutoffs and real evidence validation."""
import os
from pathlib import Path
import re
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class TendermintUnbondingLiveTests(unittest.TestCase):
    def run_lean(self, file):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run([lake, 'env', 'lean', '-DwarningAsError=true', file],
                                cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def test_kernel_and_executable_contract(self):
        output = self.run_lean('tests/lean/tendermint_unbonding_regression.lean')
        results = re.findall(r'\("([^"]+)",\s*(true|false)\)', output)
        expected = ['request', 'no early payout', 'future', 'deadline half', 'deadline full',
                    'expired', 'replay', 'late offence', 'honest', 'priority mutation',
                    'invalid evidence', 'invalid rate', 'mixed queue', 'slot time',
                    'conservation', 'fresh positive', 'old key', 'request overdraw',
                    'new height', 'reachable']
        self.assertEqual(results, [(name, 'true') for name in expected], output)

    def test_master_registry_projection(self):
        self.run_lean('tests/lean/tendermint_unbonding_registry.lean')


if __name__ == '__main__':
    unittest.main()
