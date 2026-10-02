#!/usr/bin/env python3
"""Reproduce exact Lean placement data; --check never writes files.

The parser/generator/hash binding is an external reproducibility check, not a
Lean theorem. IDs are array positions, not persistent physical identifiers.
"""
import argparse
from decimal import Decimal
from fractions import Fraction
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data/chip_manifest"
TARGET = ROOT / "Verification/ChipPlacementCertificate.lean"
HASHES = {
    "corrected.json": "139d8b6d574d18937f0e08cf8c7b1dc4e9c5d6306f5dd7e2070ab769de89975a",
    "original.json": "3d7a2561f166d8a10f641c97aefa7b4d5ce5941b8aade41ca407491693eb0491",
    "rational_data.json": "9eecd42d3f2efcb31ab1b6576c2b203833076d5ba061293098a0ea2e2651e1f5",
}
START = "-- BEGIN GENERATED MANIFEST DATA"
END = "-- END GENERATED MANIFEST DATA"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rational(value):
    n, d = int(value["numerator"]), int(value["denominator"])
    require(d > 0, "nonpositive rational denominator")
    result = Fraction(n, d)
    require(str(result.numerator) == value["numerator"] and
            str(result.denominator) == value["denominator"], "noncanonical rational")
    return result


def load_inputs():
    loaded = {}
    for name, expected in HASHES.items():
        raw = (DATA / name).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == expected, f"hash mismatch: {name}")
        loaded[name] = json.loads(raw, parse_float=Decimal)
    rationals = loaded["rational_data.json"]
    for role in ["original", "corrected"]:
        source, model = loaded[f"{role}.json"], rationals[role]
        require(source["position_convention"] == "rectangle_centres_um", "coordinate convention")
        require(source.get("coordinate_units", "um") == "um", "source units")
        require(model["units"] == "um" and model["coordinate_frame"] == "die_local", "units/frame")
        require(model["id_policy"] == "array_index", "ID policy")
        origin = [Fraction(x) for x in source.get("chip_origin_um", [0, 0])]
        require(origin == [rational(model["source_origin_um"][k]) for k in ["x", "y"]], "origin")
        require([Fraction(x) for x in source["chip_dim_um"]] ==
                [rational(model["die"][k]) for k in ["W", "H"]] == [4000, 4000], "die")
        require(len(source["activation_array"]) == len(model["nodes"]) == 256, "node count")
        for i, (raw, node) in enumerate(zip(source["activation_array"], model["nodes"])):
            expected = [Fraction(raw["pos"][j]) - origin[j] for j in [0, 1]]
            expected += [Fraction(x) for x in raw["dim_um"]]
            require(node["id"] == i, f"{role} ID/order {i}")
            require([rational(node[k]) for k in ["x", "y", "w", "h"]] == expected,
                    f"{role} geometric fields {i}")
    for old, new in zip(rationals["original"]["nodes"], rationals["corrected"]["nodes"]):
        require(all(rational(new[k]) == rational(old[k]) - 125 for k in ["x", "y"]), "shift")
        require(all(new[k] == old[k] for k in ["id", "w", "h"]), "size/ID changed")
    return rationals["corrected"]


def literal(q):
    q = rational(q)
    return str(q.numerator) if q.denominator == 1 else f"({q.numerator} / {q.denominator})"


def render(model):
    lines = [START, "/-- SHA-256 of corrected.json; external provenance, not a verified hash function. -/",
             "def correctedManifestSHA256 : String :=", f'  "{HASHES["corrected.json"]}"', "",
             "def manifest_die_256 : DieBoundsRat := \u27e84000, 4000\u27e9", "",
             "/-- Explicit imported records in array order, in micrometres. -/",
             "def manifest_nodes_256 : List ManifestNodeRat := ["]
    for i, node in enumerate(model["nodes"]):
        row = ", ".join([str(node["id"])] + [literal(node[k]) for k in ["x", "y", "w", "h"]])
        lines.append("  \u27e8" + row + "\u27e9" + ("," if i < 255 else ""))
    return "\n".join(lines + ["]", END])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    model = load_inputs()
    text = TARGET.read_text()
    require(text.count(START) == text.count(END) == 1, "generated block markers")
    start, end = text.index(START), text.index(END) + len(END)
    updated = text[:start] + render(model) + text[end:]
    if args.check:
        require(text == updated, "Lean data differ from exact regenerated records")
    else:
        TARGET.write_text(updated)
    print(json.dumps({"ok": True, "nodes": 256, "source_hashes": HASHES,
                      "lean_sha256": hashlib.sha256(updated.encode()).hexdigest(),
                      "mode": "check" if args.check else "write"}, indent=2))


if __name__ == "__main__":
    main()
