"""Weighted quorum intersection: exact arithmetic and boundary counterexamples."""
import os
from pathlib import Path
import re
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class TendermintEpochQuorumLiveTests(unittest.TestCase):
    def run_lean(self, file):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run([lake, 'env', 'lean', '-DwarningAsError=true', file],
                                cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def test_kernel_and_executable_contract(self):
        output = self.run_lean('tests/lean/tendermint_epoch_quorum_regression.lean')
        results = re.findall(r'\("([^"]+)",\s*(true|false)\)', output)
        expected = ['normalized', 'common mass', 'variation', 'directed loss', 'good quorums', 'honest subject', 'static', 'legacy', 'boundary split', 'strict split', 'fault boundary', 'strict equality', 'scale', 'zero total', 'negative weight', 'epoch bridge', 'permutation', 'different size', 'not necessary', 'two faults conservative']
        self.assertEqual(results, [(name, 'true') for name in expected], output)

    def test_master_registry_projection(self):
        self.run_lean('tests/lean/tendermint_epoch_quorum_registry.lean')


if __name__ == '__main__':
    unittest.main()
