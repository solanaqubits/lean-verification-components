import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('verifier_skill', ROOT / 'tools/verifier_skill.py')
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


class VerifierUnitTests(unittest.TestCase):
    def test_policy_ignores_nested_comments_and_strings(self):
        self.assertEqual(mod.policy_findings('/- sorry /- admit -/ axiom -/\n#check "sorry"\n-- native_decide\n'), [])
        self.assertEqual(mod.policy_findings('theorem x : True := by\n sorry')[0], {'token':'sorry','line':2})
        self.assertTrue(mod.policy_findings('by native_decide'))

    def test_outside_project_rejected(self):
        verifier = mod.Verifier(ROOT)
        with self.assertRaises(mod.VerificationError): verifier.source('/tmp/outside.lean')

    def test_plan_preserves_existing_packages(self):
        verifier = mod.Verifier(ROOT)
        plan = verifier.integration_plan('Verification.DeFiConcentratedLiquidity', 'DeFiConcentratedLiquidityFormalSuite')
        after = plan['changes'][0][2]
        self.assertIn('h_integral :', after)
        self.assertIn('extends FinanceDeFiFullSuite', after)
        self.assertIn('CryptoZKAirFormalSuite.{u₁, u₂, u₃, u₄, u₅}', after)

    def test_failed_integration_rolls_back_exact_bytes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); (root/'Verification').mkdir()
            (root/'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
            for source in ['Verification/MasterSuite.lean', 'Verification/DeFiConcentratedLiquidity.lean', 'Verification.lean']:
                (root/source).write_bytes((ROOT/source).read_bytes())
            for relative in ['Verification/MasterSuite.lean', 'Verification.lean']:
                path = root/relative
                path.write_text(''.join(line for line in path.read_text().splitlines(True)
                                        if 'DeFiConcentratedLiquidity' not in line))
            root_before = (root/'Verification.lean').read_bytes()
            verifier = mod.Verifier(root)
            before = (root/'Verification/MasterSuite.lean').read_bytes()
            def fail_after_checking_mutation(_):
                self.assertIn('  concentrated :', (root/'Verification/MasterSuite.lean').read_text())
                self.assertIn('import Verification.DeFiConcentratedLiquidity', (root/'Verification.lean').read_text())
                return {'ok':False}
            with patch.object(verifier, '_verify', side_effect=fail_after_checking_mutation):
                report = verifier.integrate_to_mastersuite('Verification.DeFiConcentratedLiquidity', 'DeFiConcentratedLiquidityFormalSuite')
            self.assertFalse(report['ok']); self.assertTrue(report['rolled_back'])
            self.assertEqual((root/'Verification/MasterSuite.lean').read_bytes(), before)
            self.assertEqual((root/'Verification.lean').read_bytes(), root_before)

    def test_plan_is_idempotent(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); (root/'Verification').mkdir()
            (root/'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
            for source in ['Verification/MasterSuite.lean', 'Verification/DeFiConcentratedLiquidity.lean', 'Verification.lean']:
                (root/source).write_bytes((ROOT/source).read_bytes())
            verifier = mod.Verifier(root)
            plan = verifier.integration_plan('Verification.DeFiConcentratedLiquidity', 'DeFiConcentratedLiquidityFormalSuite')
            for name, _, after in plan['changes']: (root/name).write_text(after)
            self.assertEqual(verifier.integration_plan('Verification.DeFiConcentratedLiquidity', 'DeFiConcentratedLiquidityFormalSuite')['diff'], '')

    def test_unknown_integration_is_not_guessed(self):
        with self.assertRaises(mod.VerificationError):
            mod.Verifier(ROOT).integration_plan('Verification.CollatzBase', 'MadeUpSuite')

    def test_timeout_stops_command(self):
        import sys
        report = mod.Verifier(ROOT, timeout=1).run([sys.executable, '-c', 'import time; time.sleep(30)'])
        self.assertTrue(report['timeout']); self.assertNotEqual(report['returncode'], 0)


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1', 'Set LEAN_VERIFIER_LIVE_TESTS=1 for compiler tests')
class VerifierLiveTests(unittest.TestCase):
    def setUp(self): self.verifier = mod.Verifier(ROOT)

    def test_positive_scaffold(self):
        result = self.verifier.scaffold_invariant('nat', '∀ n : ℕ, n ≤ n + 1')
        self.assertTrue(result['ok'], result)
        self.assertFalse(result['verification']['audit']['violations'])

    def test_real_polynomial_scaffold(self):
        result = self.verifier.scaffold_invariant('real-polynomial', '∀ x y : ℝ, (x + y)^2 = x^2 + 2*x*y + y^2')
        self.assertTrue(result['ok'], result)

    def test_real_inequality_scaffold(self):
        result = self.verifier.scaffold_invariant('real-inequality', '∀ x : ℝ, 0 ≤ x^2')
        self.assertTrue(result['ok'], result)

    def test_false_goal_not_returned_as_code(self):
        result = self.verifier.scaffold_invariant('nat', '∀ n : ℕ, n + 1 ≤ n')
        self.assertFalse(result['ok']); self.assertIsNone(result['lean_code'])

    def test_unsupported_natural_language_fails(self):
        result = self.verifier.scaffold_invariant('nat', 'Every quorum is safe')
        self.assertFalse(result['ok']); self.assertIsNone(result['lean_code'])

    def test_actual_transitive_axiom_audit(self):
        # Directly test the kernel dependency audit, independently of lexical policy.
        name = 'VerifierTestAudit'
        path = ROOT/'Verification'/f'{name}.lean'
        self.assertFalse(path.exists())
        with self.verifier.locked():
            try:
                path.write_text('namespace Foreign\naxiom bad : False\nend Foreign\n'
                                'theorem innocentLooking : True := False.elim Foreign.bad\n')
                build = self.verifier.run([self.verifier.lake, 'build', 'Verification.'+name])
                self.assertEqual(build['returncode'], 0, build)
                step, audit = self.verifier.audit(['Verification.'+name])
                self.assertNotEqual(step['returncode'], 0)
                self.assertTrue(any(v['axiom']=='Foreign.bad' for v in audit['violations']))
            finally:
                path.unlink(missing_ok=True)
                for base in ['.lake/build/lib/lean/Verification', '.lake/build/ir/Verification']:
                    for artifact in (ROOT/base).glob(name+'.*'):
                        if artifact.is_file(): artifact.unlink()

    def test_card_is_reviewable_draft_without_overwrite(self):
        existing = ROOT/'knowledge/distributed/DistributedRaftConsensus.en.md'
        before = existing.read_bytes()
        result = self.verifier.generate_knowledge_card('Verification.DistributedRaftConsensus')
        self.assertTrue(result['ok'], result)
        self.assertIn('draft-needs-scope-review', result['markdown'])
        self.assertIn('election_safety_unique_leader', result['markdown'])
        self.assertEqual(existing.read_bytes(), before)

    def test_audit_cli_on_append_module(self):
        import sys, subprocess
        command = [sys.executable, str(ROOT/'tools/verifier_skill.py'),
                   'audit', 'Verification/DistributedRaftLogAppend.lean']
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=120)
        report = json.loads(result.stdout)
        self.assertEqual(result.returncode, 0, report)
        self.assertTrue(report['ok'])
        self.assertEqual(report['operation'], 'audit')
        self.assertGreater(report['audit']['declarations'], 0)

    def test_audit_cli_rejects_source_changed_after_build(self):
        import sys, subprocess
        name = 'VerifierTestStale'
        path = ROOT/'Verification'/f'{name}.lean'
        self.assertFalse(path.exists())
        try:
            path.write_text('theorem beforeEdit : True := True.intro\n')
            step = self.verifier.run([self.verifier.lake, 'build', 'Verification.'+name])
            self.assertEqual(step['returncode'], 0, step)
            path.write_text('axiom afterEdit : False\n')
            result = subprocess.run([sys.executable, str(ROOT/'tools/verifier_skill.py'),
                                     'audit', str(path)], cwd=ROOT, capture_output=True,
                                    text=True, timeout=120)
            report = json.loads(result.stdout)
            self.assertEqual(result.returncode, 1, report)
            self.assertFalse(report['ok'])
            self.assertTrue(report['policy_findings'])
        finally:
            path.unlink(missing_ok=True)
            for base in ['.lake/build/lib/lean/Verification', '.lake/build/ir/Verification']:
                for artifact in (ROOT/base).glob(name+'.*'):
                    if artifact.is_file(): artifact.unlink()

    def test_sorry_and_native_are_rejected(self):
        for token in ['sorry', 'admit', 'native_decide']:
            with self.assertRaises(mod.VerificationError):
                self.verifier.scaffold_invariant('nat', 'True := by '+token)


if __name__ == '__main__': unittest.main()
