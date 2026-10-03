"""Acyclic registry layering and compatibility of integration after the split."""
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('hundred_verifier', ROOT / 'tools/verifier_skill.py')
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


class HundredRegistryTests(unittest.TestCase):
    def test_acyclic_imports_and_milestone_layering(self):
        graph = {f'Verification.{p.stem}': re.findall(r'^import (Verification\.\w+)', p.read_text(), re.M)
                 for p in (ROOT / 'Verification').glob('*.lean')}
        visited, active = set(), set()
        def visit(node):
            self.assertNotIn(node, active, f'Import cycle at {node}')
            if node in visited:
                return
            active.add(node)
            for child in graph[node]:
                visit(child)
            active.remove(node)
            visited.add(node)
        for node in graph:
            visit(node)
        master = graph['Verification.MasterSuite']
        self.assertEqual(len(master), len(set(master)))
        self.assertGreaterEqual(len(master), 100)
        self.assertIn('Verification.MasterHundredRegistry', master)
        self.assertEqual(graph['Verification.MasterHundredRegistry'], ['Verification.MasterSuiteComponents'])
        closure = mod.Verifier(ROOT).closure(['Verification.MasterHundredRegistry'])
        self.assertNotIn('Verification.MasterSuite', closure)

    def test_all_existing_integration_recipes_are_idempotent(self):
        verifier = mod.Verifier(ROOT)
        for module, recipe in json.loads((ROOT / 'tools/integration_targets.json').read_text()).items():
            with self.subTest(module=module):
                self.assertEqual(verifier.integration_plan(module, recipe['suite_struct'])['diff'], '')

    def test_parent_recipe_cannot_escape_verification_sources(self):
        module = 'Verification.MasterHundredRegistry'
        recipe = json.loads((ROOT / 'tools/integration_targets.json').read_text())[module]
        recipe['parent_module'] = '../outside.lean'
        with patch.object(mod.json, 'loads', return_value={module: recipe}):
            with self.assertRaises(mod.VerificationError):
                mod.Verifier(ROOT).integration_plan(module, recipe['suite_struct'])

    @unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1',
                         'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
    def test_universes_and_legacy_projections_compile(self):
        lake = shutil.which('lake')
        self.assertIsNotNone(lake)
        result = subprocess.run([lake, 'env', 'lean', '-DwarningAsError=true',
                                 'tests/lean/hundred_registry_regression.lean'],
                                cwd=ROOT, capture_output=True, text=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
