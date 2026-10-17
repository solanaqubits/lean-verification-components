"""Opening extraction: independent fixtures, rejection cases and range composition."""
import os
from pathlib import Path
import re
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class PedersenOpeningLiveTests(unittest.TestCase):
    def run_lean(self, file):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run([lake, 'env', 'lean', '-DwarningAsError=true', file],
                                cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def test_kernel_and_executable_contract(self):
        output = self.run_lean('tests/lean/pedersen_opening_regression.lean')
        expected = ['scalar', 'reverse', 'zero challenge', 'equal challenge',
                    'different announcement', 'different statement', 'bad response',
                    'sign mutation', 'vector', 'nonunique', 'dlog', 'empty vector']
        results = re.findall(r'\("([^"]+)",\s*(true|false)\)', output)
        self.assertEqual(results, [(name, 'true') for name in expected], output)

    def test_conditional_range_bridge(self):
        output = self.run_lean('tests/lean/pedersen_opening_bridge.lean')
        self.assertEqual(output.strip(), '"witness:3"')

    def test_master_registry_projection(self):
        self.run_lean('tests/lean/pedersen_opening_registry.lean')


if __name__ == '__main__':
    unittest.main()
