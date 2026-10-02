"""Compiler regressions for finite-field batch counting and its boundary cases."""

import os
from pathlib import Path
import shutil
import subprocess
import unittest


ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(
    os.environ.get("LEAN_VERIFIER_LIVE_TESTS") == "1",
    "Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests",
)
class SchnorrBatchLiveTests(unittest.TestCase):
    def test_exact_counts_cancellation_and_repetition(self):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake, "lake must be available for live compiler tests")
        result = subprocess.run(
            [
                lake,
                "env",
                "lean",
                "-DwarningAsError=true",
                "tests/lean/schnorr_batch_regression.lean",
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=120,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
