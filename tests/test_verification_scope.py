"""Independent small graphs and mutations exercise the verification policy."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from verification_plan import plan
from verification_metadata import BATCHES, RECIPES, load_metadata, read_json
from scope_evidence import fingerprint, hash_object, reuse_decision, load_accepted, run_scoped
from release_evidence import digest


class ScopeFixture(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'repo'
        self.root.mkdir()
        self.git('init', '-q')
        self.git('config', 'user.name', 'Test')
        self.git('config', 'user.email', 'test@example.invalid')
        self.write('Verification/A.lean', '-- foundation\n')
        self.write('Verification/B.lean', 'import Verification.A\n')
        self.write('Verification/C.lean', 'import Verification.B\n')
        self.write('Verification/MasterSuiteComponents.lean', 'import Verification.C\n')
        self.write('Verification/MasterSuite.lean', 'import Verification.MasterSuiteComponents\n')
        self.write('Verification.lean', 'import Verification.MasterSuite\n')
        self.catalog = {'sections': [{'id': 'one'}], 'modules': [{'id': n, 'section': 'one'} for n in 'ABC']}
        self.write('knowledge/catalog.json', self.catalog)
        self.batch = {'schema_version': 1, 'batches': {'one/block': {'direction': 'one', 'modules': ['Verification.B'], 'description': 'Initial'}},
                      'infrastructure_batches': {'verification-scope-policy': {'description': 'Policy'}}}
        self.write(BATCHES, self.batch)
        self.write(RECIPES, {})
        self.write('tools/verifier_skill.py', '# checker\n')
        self.write('lakefile.toml', 'version = "0.7.0"\n')
        self.write('README.md', 'Initial\n')
        self.write('tests/test_example.py', '# example\n')
        self.git('add', '.')
        self.git('commit', '-qm', 'fixture')
        self.base = self.git('rev-parse', 'HEAD').strip()

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root, stderr=subprocess.DEVNULL).decode()

    def write(self, name, text):
        p = self.root / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(text) if isinstance(text, dict) else text)

    def planned(self, **kw):
        return plan(self.root, 'delta', batch='one/block', base=self.base, **kw)


class ImpactTests(ScopeFixture):
    def test_description_only_has_no_lean_commands(self):
        self.batch['batches']['one/block']['description'] = 'Reworded'
        self.write(BATCHES, self.batch)
        p = self.planned()
        self.assertEqual(p['verification_level'], 'metadata')
        self.assertEqual(p['build_modules'], [])
        self.assertEqual(p['requested_rank'], 'delta')
        self.assertEqual(p['commands'], [['python3', 'tools/verification_metadata.py'], ['python3', 'scripts/check_knowledge.py'], ['git', 'diff', '--check']])

    def test_new_module_selects_old_new_members_and_integration(self):
        self.write('Verification/D.lean', 'import Verification.B\n')
        self.catalog['modules'].append({'id': 'D', 'section': 'one'})
        self.write('knowledge/catalog.json', self.catalog)
        self.batch['batches']['one/block']['modules'].append('Verification.D')
        self.write(BATCHES, self.batch)
        p = self.planned()
        self.assertEqual(p['verification_level'], 'scoped')
        self.assertTrue({'Verification.B', 'Verification.C', 'Verification.D', 'Verification.MasterSuiteComponents'} <= set(p['build_modules']))
        self.assertIn('Verification.A', p['imported_closure'])
        self.assertTrue(p['test_selection_required'])

    def test_shared_definition_reaches_every_consumer(self):
        self.write('Verification/A.lean', '-- changed foundation\n')
        p = self.planned()
        self.assertTrue({'Verification.A', 'Verification.B', 'Verification.C', 'Verification.MasterSuite'} <= set(p['build_modules']))
        self.assertEqual(p['audit_roots'], ['Verification.MasterSuite'])

    def test_deleted_module_uses_old_edges(self):
        (self.root / 'Verification/A.lean').unlink()
        self.write('Verification/B.lean', '-- no longer imports A\n')
        self.catalog['modules'] = [m for m in self.catalog['modules'] if m['id'] != 'A']
        self.write('knowledge/catalog.json', self.catalog)
        p = self.planned()
        self.assertIn('Verification.C', p['build_modules'])
        self.assertNotIn('Verification.A', p['imported_closure'])

    def test_removed_batch_member_still_checked(self):
        self.batch['batches']['one/block']['modules'] = ['Verification.C']
        self.write(BATCHES, self.batch)
        p = self.planned()
        self.assertTrue({'Verification.B', 'Verification.C'} <= set(p['build_modules']))

    def test_no_baseline_does_not_assume_description_only(self):
        p = plan(self.root, 'epsilon', changed=[BATCHES])
        self.assertIn('Verification.B', p['build_modules'])

    def test_trust_changes_force_beta(self):
        for path in ['tools/verifier_skill.py', 'tools/verification_plan.py', 'lakefile.toml', 'lean-toolchain',
                     'tools/statement_conformance_contract.json', 'VERSIONING.md', 'scripts/check_knowledge.py']:
            with self.subTest(path=path):
                p = self.planned(changed=[path])
                self.assertEqual(p['verification_level'], 'beta')
                self.assertTrue(any(e['path'] == path and e['required_control'] == 'beta' for e in p['explanations']))

    def test_untracked_checker_cannot_hide_from_base_diff(self):
        self.write('tools/new_checker.py', '# newly added\n')
        self.assertEqual(self.planned()['verification_level'], 'beta')

    def test_reviewed_batch_tests_and_fixtures_remain_scoped(self):
        self.write('tests/test_example.py', '# changed regression\n')
        self.write('tests/lean/example.lean', 'import Verification.B\n')
        p = self.planned(tests=['tests.test_example'])
        self.assertEqual(p['verification_level'], 'scoped')
        self.assertFalse(p['test_selection_required'])
        self.assertIn(['python3', '-m', 'unittest', '-v', 'tests.test_example'], p['commands'])

    def test_unreviewed_test_changes_and_trust_tests_require_beta(self):
        self.write('tests/test_example.py', '# changed regression\n')
        self.assertEqual(self.planned()['verification_level'], 'beta')
        self.write('tests/test_release_evidence.py', '# altered admission checks\n')
        self.assertEqual(self.planned(tests=['tests.test_example', 'tests.test_release_evidence'])['verification_level'], 'beta')

    def test_invalid_batch_cannot_disable_checks(self):
        self.batch['batches']['one/block']['skip_checks'] = True
        self.write(BATCHES, self.batch)
        with self.assertRaises(ValueError):
            self.planned()

    def test_unknown_batch_member_rejected(self):
        self.batch['batches']['one/block']['modules'] = ['Verification.Missing']
        self.write(BATCHES, self.batch)
        with self.assertRaises(ValueError):
            self.planned()

    def test_duplicate_json_keys_rejected(self):
        with self.assertRaises(ValueError):
            read_json('{"batches": {}, "batches": {}}')

    def test_recipe_tactic_injection_rejected(self):
        row = dict(suite_struct='Suite', suite_type='Suite', parent='Parent', field='field', constructor='ctor', proof='by\n  sorry')
        self.write(RECIPES, {'Verification.A': row})
        with self.assertRaises(ValueError):
            self.planned()

    def test_valid_recipe_edit_selects_registry(self):
        row = dict(suite_struct='Suite', suite_type='Suite', parent='Parent', field='field', constructor='ctor', proof='A.suite')
        self.write(RECIPES, {'Verification.A': row})
        p = self.planned()
        self.assertEqual(p['verification_level'], 'scoped')
        self.assertIn('Verification.MasterSuiteComponents', p['build_modules'])

    def test_catalog_description_does_not_recompile(self):
        self.catalog['modules'][0]['description'] = 'Reworded'
        self.write('knowledge/catalog.json', self.catalog)
        self.assertEqual(self.planned()['verification_level'], 'metadata')

    def test_invalid_changed_path_rejected(self):
        with self.assertRaises(ValueError):
            self.planned(changed=['tools/../README.md'])

    def test_infrastructure_batch_no_mathematical_module(self):
        self.write('tools/verifier_skill.py', '# updated checker\n')
        p = plan(self.root, 'delta', batch='verification-scope-policy', base=self.base)
        self.assertEqual(p['requested_rank'], 'delta')
        self.assertEqual(p['effective_rank'], 'beta')
        self.assertEqual(p['batch'], 'verification-scope-policy')


class CacheTests(ScopeFixture):
    def binding(self):
        p = plan(self.root, 'epsilon', ['Verification.B'])
        return fingerprint(self.root, p, ['lake', 'build', '--wfail', 'Verification.B'], runtime={'lean': 'fixed'})

    def test_identical_binding_reuses(self):
        old = self.binding()
        self.assertTrue(reuse_decision({'fingerprint': old}, self.binding())['reusable'])

    def test_root_build_binds_imports_outside_standalone_module(self):
        self.write('Verification/Standalone.lean', '-- standalone\n')
        p = plan(self.root, 'epsilon', ['Verification.Standalone'])
        cmd = next(c for c in p['commands'] if c[0] == 'lake')
        old = fingerprint(self.root, p, cmd, runtime={'lean': 'fixed'})
        self.write('Verification/A.lean', '-- unrelated to Standalone, reached by root\n')
        new = fingerprint(self.root, p, cmd, runtime={'lean': 'fixed'})
        self.assertFalse(reuse_decision({'fingerprint': old}, new)['reusable'])
        self.assertIn('Verification/A.lean', new['groups']['dependencies'])

    def test_changed_dependency_invalidates(self):
        old = self.binding()
        self.write('Verification/A.lean', '-- changed\n')
        d = reuse_decision({'fingerprint': old}, self.binding())
        self.assertFalse(d['reusable'])
        self.assertEqual(d['invalidations'], [{'component': 'dependencies', 'reason': 'bound-component-changed'}])

    def test_changed_input_tool_and_configuration_invalidate(self):
        for path, component in [('Verification/B.lean', 'inputs'), ('tools/verifier_skill.py', 'tools'), ('lakefile.toml', 'configuration')]:
            with self.subTest(path=path):
                old = self.binding()
                self.write(path, '-- changed ' + path)
                d = reuse_decision({'fingerprint': old}, self.binding())
                self.assertFalse(d['reusable'])
                self.assertIn({'component': component, 'reason': 'bound-component-changed'}, d['invalidations'])

    def test_command_flags_runtime_and_environment_invalidate(self):
        old = self.binding()
        for component in ['command', 'runtime', 'environment']:
            new = copy.deepcopy(old)
            new['groups'][component] = ['mutated']
            new['sha256'] = hash_object(new['groups'])
            self.assertFalse(reuse_decision({'fingerprint': old}, new)['reusable'])

    def test_symlinked_input_rejected(self):
        source = self.root / 'Verification/B.lean'
        source.unlink()
        source.symlink_to(self.root / 'Verification/A.lean')
        with self.assertRaises(ValueError):
            self.binding()

    def make_accepted(self):
        out = Path(self.temp.name) / 'accepted'
        out.mkdir()
        (out / '00.log').write_text('Build completed successfully (1 jobs).\n')
        f = self.binding()
        report = dict(schema_version=1, kind='scoped-checks', status='passed', checks=[dict(command=f['groups']['command'],
                      fingerprint=f, exit_code=0, log='00.log', log_sha256=digest(out / '00.log'))])
        (out / 'evidence.json').write_text(json.dumps(report))
        return out, digest(out / 'evidence.json')

    def test_missing_acceptance_pin_rejected(self):
        out, _ = self.make_accepted()
        with self.assertRaises(ValueError):
            load_accepted(out, None)

    def test_forged_report_even_with_consistent_hashes_rejected(self):
        out, pin = self.make_accepted()
        r = json.loads((out / 'evidence.json').read_text())
        r['checks'][0]['fingerprint'] = self.binding()
        r['forged'] = True
        (out / 'evidence.json').write_text(json.dumps(r))
        with self.assertRaises(ValueError):
            load_accepted(out, pin)

    def test_accepted_report_and_changed_log(self):
        out, pin = self.make_accepted()
        self.assertEqual(load_accepted(out, pin)['status'], 'passed')
        (out / '00.log').write_text('substituted')
        with self.assertRaises(ValueError):
            load_accepted(out, pin)

    def test_runner_skips_all_accepted_identical_commands(self):
        self.write('README.md', 'Reworded\n')
        p = self.planned()
        calls = []
        original_run = subprocess.run
        def execute(command, **kwargs):
            if not hasattr(kwargs.get('stdout'), 'write'):
                return original_run(command, **kwargs)
            calls.append(command)
            kwargs['stdout'].write('OK\n')
            return subprocess.CompletedProcess(command, 0)
        with patch('scope_evidence.runtime_fingerprint', return_value={'lean': 'fixed'}), patch('scope_evidence.subprocess.run', side_effect=execute):
            out = Path(self.temp.name) / 'run1'
            first = run_scoped(self.root, out, p)
            self.assertEqual(len(calls), 3)
            second = run_scoped(self.root, Path(self.temp.name) / 'run2', p, out, first['evidence_sha256'])
            self.assertEqual(second['reused'], 3)
            self.assertEqual(len(calls), 3)

    def test_runner_refuses_beta_or_missing_tests(self):
        for p in [plan(self.root, 'beta'), plan(self.root, 'epsilon', ['Verification.B'])]:
            with self.assertRaises(ValueError):
                run_scoped(self.root, Path(self.temp.name) / 'refused', p)

if __name__ == '__main__':
    unittest.main()
