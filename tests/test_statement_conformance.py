"""Live, kernel-compiled mutation tests. Always run; no silent skip flag.

Candidates are temporary modules in the isolated test checkout. They do not
replace the production implementation, gold, or bridge. All are removed again.
"""
from contextlib import contextmanager
import json
from pathlib import Path
import shutil
import sys
import unittest
import uuid
import textwrap

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import statement_conformance_checker as checker


@contextmanager
def candidate(mutation=None):
    name = 'ConformanceFixture' + uuid.uuid4().hex
    module = 'Verification.Specs.' + name
    path = ROOT / 'Verification/Specs' / (name + '.lean')
    original = (ROOT / 'Verification/QuantumSimonsAlgorithm.lean').read_text()
    suite = original.split('structure QuantumSimonsSuite : Prop where', 1)[1]
    suite = 'structure QuantumSimonsSuite : Prop where' + suite.split('\ntheorem quantum_simons_master_suite', 1)[0]
    aliases = ['Register', 'JointState', 'xorVec', 'SimonPromise', 'hermitian', 'xorOracle',
               'inputHadamard', 'initial', 'runSimon', 'fiberSum', 'probability',
               'bit', 'encode', 'dot', 'BinarySpace', 'rowSpan']
    definitions = '\n'.join(f'abbrev {a} := @QuantumSimonsAlgorithm.{a}' for a in aliases)
    fields = ['oracle_unitary', 'hadamard_unitary', 'circuit_amplitude', 'odd_amplitude',
              'exact_distribution', 'normalized', 'recovery']
    values = ['h.' + f for f in fields]
    if mutation == 'false':
        suite = suite.replace('  exact_distribution : ∀', '  exact_distribution : False → ∀')
        values[4] = 'fun hf => False.elim hf'
    elif mutation == 'true':
        start, end = suite.index('  exact_distribution :'), suite.index('  normalized :')
        suite = suite[:start] + '  exact_distribution : True\n' + suite[end:]
        values[4] = 'True.intro'
    elif mutation == 'promise':
        definitions = definitions.replace('abbrev SimonPromise := @QuantumSimonsAlgorithm.SimonPromise',
            "def SimonPromise {n m : ℕ} (f : Register n → Register m) (s : Register n) : Prop :=\n"
            "  ∀ x x', f x = f x' ↔ x = x' ∨ x = xorVec x' s")
        # The public predicate must be checked even if the existing proof still
        # refers to the original predicate through its fully qualified name.
        suite = suite.replace('    SimonPromise f s', '    QuantumSimonsAlgorithm.SimonPromise f s')
    elif mutation == 'cardinality':
        suite = suite.replace('Module.finrank (ZMod 2) (rowSpan Y) = n - 1', 'Y.card = n - 1')
    elif mutation == 'zero_probability':
        definitions = definitions.replace('abbrev probability := @QuantumSimonsAlgorithm.probability',
            'def probability {n m : ℕ} (_f : Register n → Register m) (_y : Register n) : ℝ := 0')
        suite = suite.replace('probability f y', 'QuantumSimonsAlgorithm.probability f y')
    master = ('\ntheorem quantum_simons_master_suite : QuantumSimonsSuite := by\n'
              '  have h := QuantumSimonsAlgorithm.quantum_simons_master_suite\n'
              '  exact ⟨' + ', '.join(values) + '⟩\n')
    if mutation == 'cardinality':
        # This changed universal claim is false. It is a compilable contract,
        # not a purported proof; inspect its type before requesting a master.
        master = ''
    if mutation == 'missing_master':
        master = ''
    text = ('import Verification.QuantumSimonsAlgorithm\nnoncomputable section\n'
            'open scoped BigOperators\nopen QuantumDeutschJozsaGeneral (zeroBits)\n'
            f'namespace {name}\n' + definitions + '\n' + suite + master + f'\nend {name}\n')
    text = "\n".join("\n".join(textwrap.wrap(line, width=96,
        subsequent_indent=" " * (len(line) - len(line.lstrip()) + 2),
        break_long_words=False, break_on_hyphens=False)) if len(line) > 96 else line
        for line in text.splitlines()) + "\n"
    path.write_text(text)
    try:
        yield module, name
    finally:
        path.unlink(missing_ok=True)
        for base in ['.lake/build/lib/lean/Verification/Specs', '.lake/build/ir/Verification/Specs']:
            for artifact in (ROOT / base).glob(name + '.*'):
                artifact.unlink()


class StatementConformanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if shutil.which('lake') is None:
            raise RuntimeError('These live contract tests require lake; skipping is not permitted')

    def assert_mutation_rejected(self, mutation, diagnostic):
        with candidate(mutation) as (module, namespace):
            report = checker.check(ROOT, module, namespace)
        self.assertFalse(report['ok'], report)
        self.assertEqual(report.get('failure_stage'), 'contract_probe', report)
        self.assertIn(diagnostic, report['steps'][-1]['output'])
        self.assertEqual(report['conformance_status'], 'fail')

    def test_original_contract_and_witnesses(self):
        report = checker.check(ROOT)
        self.assertTrue(report['ok'], report)
        self.assertEqual(report['axiom_status'], 'pass')
        self.assertEqual(report['satisfiability_status'], 'pass_concrete_instances')
        self.assertFalse(report['epistemic_scope']['universal_nonvacuity'])

    def test_valid_fieldwise_alternative_proof(self):
        with candidate() as (module, namespace):
            report = checker.check(ROOT, module, namespace)
        self.assertTrue(report['ok'], report)

    def test_false_antecedent(self):
        self.assert_mutation_rejected('false', 'explicit False antecedent')

    def test_true_conclusion(self):
        self.assert_mutation_rejected('true', 'suite field type: exact_distribution')

    def test_weakened_public_promise(self):
        self.assert_mutation_rejected('promise', 'definition body: SimonPromise')

    def test_rank_replaced_by_sample_count(self):
        self.assert_mutation_rejected('cardinality', 'suite field type: recovery')

    def test_zero_probability_substitution(self):
        self.assert_mutation_rejected('zero_probability', 'definition body: probability')

    def test_missing_master_is_not_success(self):
        self.assert_mutation_rejected('missing_master', 'quantum_simons_master_suite')

    def test_invalid_module_name(self):
        report = checker.check(ROOT, 'Verification.X\nimport Bad')
        self.assertFalse(report['ok'])
        self.assertEqual(report['steps'], [])

    def test_trusted_contract_tampering(self):
        # Test a copied trust root; no mutation to the checked project itself.
        import tempfile
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / '.lake').mkdir()
            (root / 'tools').mkdir()
            shutil.copy2(ROOT / 'lean-toolchain', root / 'lean-toolchain')
            manifest = json.loads((ROOT / 'tools/statement_conformance_contract.json').read_text())
            for path in manifest['trusted_sha256']:
                dest = root / path
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(ROOT / path, dest)
            (root / 'tools/statement_conformance_contract.json').write_text(json.dumps(manifest))
            gold = root / 'Verification/Specs/QuantumSimonsSpec.lean'
            gold.write_text(gold.read_text() + '\n-- unauthorized change\n')
            report = checker.check(root)
        self.assertFalse(report['ok'])
        self.assertIn('Trusted contract hash mismatch', report['error'])
        self.assertEqual(report['steps'], [])


if __name__ == '__main__':
    unittest.main()
