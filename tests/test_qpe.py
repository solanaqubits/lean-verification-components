"""Compiler regressions for exact two-bit QPE and controlled powers."""

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
class QuantumPhaseEstimationLiveTests(unittest.TestCase):
    def test_exact_phases_complex_target_and_gate_conventions(self):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake, "lake must be available for live compiler tests")
        result = subprocess.run(
            [
                lake,
                "env",
                "lean",
                "-DwarningAsError=true",
                "tests/lean/qpe_regression.lean",
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=120,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
