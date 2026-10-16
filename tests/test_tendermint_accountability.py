"""Evidence-based Tendermint accountability: kernel regressions and executable scenarios."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class TendermintAccountabilityLiveTests(unittest.TestCase):
    def run_lean(self, file):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run([lake, 'env', 'lean', '-DwarningAsError=true', file],
                                cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def test_kernel_and_executable_contract(self):
        output = self.run_lean('tests/lean/tendermint_accountability_regression.lean')
        import re
        results = re.findall(r'\("([^"]+)",\s*(true|false)\)', output)
        self.assertEqual(len(results), 24, output)
        self.assertEqual(len({name for name, _ in results}), 24)
        self.assertTrue(all(value == 'true' for _, value in results), output)

    def test_master_registry_projection(self):
        self.run_lean('tests/lean/tendermint_accountability_registry.lean')


if __name__ == '__main__':
    unittest.main()
