"""Adjacent header verification, binding boundaries, and authenticated settlement."""
import os
from pathlib import Path
import re
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                     'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class TendermintHeaderAuthLiveTests(unittest.TestCase):
    def run_lean(self, file):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run([lake, 'env', 'lean', '-DwarningAsError=true', file],
                                cwd=ROOT, capture_output=True, text=True, timeout=180)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def test_kernel_and_executable_contract(self):
        output = self.run_lean('tests/lean/tendermint_header_auth_regression.lean')
        results = re.findall(r'\("([^"]+)",\s*(true|false)\)', output)
        expected = [
            'three epochs', 'trusted anchor', 'strict quorum', 'bad next commitment',
            'broken parent', 'wrong chain', 'height gap', 'wrong epoch', 'empty signers',
            'exact two thirds', 'no signatures', 'foreign signer', 'forged identities',
            'forged weights', 'forged fault annotation', 'removed next binding admits replacement',
            'full check rejects replacement', 'unlinked signed entry', 'full signer fork',
            'colliding config substitution', 'actual historical evidence', 'old subject exited',
            'without checked history no debit', 'authenticated debit', 'deadline payout',
            'innocent new owner', 'value conservation', 'processed global key',
            'rejected chain no debit', 'rejected chain payout', 'expired evidence no debit',
        ]
        self.assertEqual(results, [(name, 'true') for name in expected], output)

    def test_master_registry_projection(self):
        self.run_lean('tests/lean/tendermint_header_auth_registry.lean')


if __name__ == '__main__':
    unittest.main()
