"""Compiler regressions for finite forking counts and scalar extraction premises."""

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
class ForkingLiveTests(unittest.TestCase):
    def test_counting_and_extraction_boundaries(self):
        lake = shutil.which("lake")
        self.assertIsNotNone(lake, "lake must be available for live compiler tests")
        result = subprocess.run(
            [
                lake,
                "env",
                "lean",
                "-DwarningAsError=true",
                "tests/lean/forking_regression.lean",
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=120,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
