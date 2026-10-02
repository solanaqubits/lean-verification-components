"""Regression checks for the external exact-data provenance chain."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("generate_chip_manifest", ROOT / "scripts/generate_chip_manifest.py")
GEN = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GEN)


class ChipManifestTests(unittest.TestCase):
    def test_exact_source_and_generated_records(self):
        model = GEN.load_inputs()
        source = GEN.TARGET.read_text()
        block = source[source.index(GEN.START):source.index(GEN.END) + len(GEN.END)]
        self.assertEqual(GEN.render(model), block)
        self.assertEqual(len(model["nodes"]), 256)

    def test_mutated_source_bytes_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)
            for name in GEN.HASHES:
                (target / name).write_bytes((GEN.DATA / name).read_bytes())
            with (target / "corrected.json").open("ab") as file:
                file.write(b" ")
            with patch.object(GEN, "DATA", target):
                with self.assertRaisesRegex(ValueError, "hash mismatch: corrected.json"):
                    GEN.load_inputs()

    def test_mismatched_generated_lean_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / "ChipPlacementCertificate.lean"
            target.write_text(GEN.TARGET.read_text().replace("\u27e80, 125, 125, 15", "\u27e80, 126, 125, 15", 1))
            with patch.object(GEN, "TARGET", target), patch("sys.argv", ["generator", "--check"]):
                with self.assertRaisesRegex(ValueError, "Lean data differ"):
                    GEN.main()

    def test_geometric_mismatch_even_with_updated_hash_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)
            for name in GEN.HASHES:
                (target / name).write_bytes((GEN.DATA / name).read_bytes())
            data = json.loads((target / "corrected.json").read_text())
            data["activation_array"][0]["pos"][0] = 126
            raw = json.dumps(data).encode()
            (target / "corrected.json").write_bytes(raw)
            hashes = dict(GEN.HASHES, **{"corrected.json": GEN.hashlib.sha256(raw).hexdigest()})
            with patch.object(GEN, "DATA", target), patch.object(GEN, "HASHES", hashes):
                with self.assertRaisesRegex(ValueError, "corrected geometric fields 0"):
                    GEN.load_inputs()

    def test_noncanonical_rationals_rejected(self):
        for denominator in ["0", "-1"]:
            with self.assertRaisesRegex(ValueError, "nonpositive"):
                GEN.rational({"numerator": "1", "denominator": denominator})
        with self.assertRaisesRegex(ValueError, "noncanonical"):
            GEN.rational({"numerator": "2", "denominator": "2"})


if __name__ == "__main__":
    unittest.main()
