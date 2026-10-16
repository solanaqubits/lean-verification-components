"""Kernel and executable regressions for liquidation accounting."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class LiquidationAccountingLiveTests(unittest.TestCase):
    def test_liquidation_accounting_and_rounding(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run(
            [lake, 'env', 'lean', '-DwarningAsError=true', '--run',
             'tests/lean/liquidation_accounting_regression.lean'],
            cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('LIQUIDATION_ACCOUNTING_OK 31', result.stdout)


if __name__ == '__main__':
    unittest.main()
