"""Pinned specification, alternative proof and deliberate weakening regressions."""
from contextlib import contextmanager
import importlib.util
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import textwrap
import unittest
import uuid

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import qutrit_conformance_checker as checker


@contextmanager
def candidate(mutation=None):
    name = 'QutritCandidate' + uuid.uuid4().hex
    path = ROOT / 'Verification/Specs' / (name + '.lean')
    ns = 'QuantumQutritSecretSharingExplicitDecoder'
    definitions = '\n'.join('abbrev '+s+' := '+ns+'.'+s for s in
        ['decodeCoordinates','encodeCoordinates','decoder','recoveryOperator','explicitRecovery'])
    declarations = '\n'.join('theorem '+s+' : '+t+' := '+ns+'.'+s for s,t in [
        ('coordinates_left_inverse','Function.LeftInverse encodeCoordinates decodeCoordinates'),
        ('coordinates_right_inverse','Function.RightInverse encodeCoordinates decodeCoordinates'),
        ('decoder_unitary_left','decoder.conjTranspose * decoder = 1'),
        ('decoder_unitary_right','decoder * decoder.conjTranspose = 1'),
        ('recovery_complete','∑ t, (recoveryOperator t).conjTranspose * recoveryOperator t = 1')])
    recovery = ('theorem explicit_recovery (q : Fin 3) (X : Q 3) :\n'
                '  apply_channel explicitRecovery (retainedPair q (encode code X)) = X :=\n'
                f'  {ns}.explicit_recovery q X\n')
    reference = ('theorem explicit_reference_recovery (q : Fin 3) (m : ℕ) (X : Joint m 3) :\n'
                 '  liftedRecovery (erasureChannel 9 3) (groupedCode q) explicitRecovery m X = X :=\n'
                 f'  {ns}.explicit_reference_recovery q m X\n')
    if mutation == 'false':
        recovery = recovery.replace(' = X :=',' = X :=') .replace('  apply_channel','  False → apply_channel').replace(f'  {ns}.explicit_recovery q X',f'  fun _ => {ns}.explicit_recovery q X')
    elif mutation == 'true':
        recovery = 'theorem explicit_recovery : True := True.intro\n'
    elif mutation == 'one_erasure':
        recovery = recovery.replace('(q : Fin 3) ', '').replace('retainedPair q','retainedPair 0').replace('explicit_recovery q X','explicit_recovery 0 X')
    elif mutation == 'diagonal_only':
        recovery = recovery.replace('(X : Q 3)', '(v : Fin 3 → ℂ)').replace('code X','code (Matrix.diagonal v)').replace(' = X',' = Matrix.diagonal v').replace('q X','q (Matrix.diagonal v)')
    elif mutation == 'fixed_reference':
        reference = reference.replace('(m : ℕ) ', '').replace('Joint m','Joint 3').replace('Recovery m','Recovery 3').replace('q m X','q 3 X')
    elif mutation == 'wrong_coordinates':
        # Keep the remaining genuine proofs qualified; only the public definition is wrong.
        definitions = definitions.replace('abbrev decodeCoordinates := '+ns+'.decodeCoordinates',
            'def decodeCoordinates (p : Fin 3 × Fin 3) := (p.1-p.2, p.2)')
        declarations = declarations.replace(' encodeCoordinates decodeCoordinates',' '+ns+'.encodeCoordinates '+ns+'.decodeCoordinates')
    text = ('import Verification.QuantumQutritSecretSharingExplicitDecoder\n'
            'noncomputable section\nopen scoped BigOperators\n'
            'open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract\n'
            'open QuantumKnillLaflammeEnvironmentCriterion QuantumReferencePreservingRecoveryContract\n'
            'open QuantumErasureCorrectabilityContract QuantumQutritTwoOfThreeSecretSharingContract\n'
            f'namespace {name}\n'+definitions+'\n'+declarations+'\n'+recovery+reference+f'end {name}\n')
    text = "\n".join("\n".join(textwrap.wrap(line, width=96, subsequent_indent="  ",
        break_long_words=False, break_on_hyphens=False)) if len(line)>96 else line
        for line in text.splitlines()) + "\n"
    path.write_text(text)
    try:
        yield 'Verification.Specs.'+name, name
    finally:
        path.unlink(missing_ok=True)
        for base in ['.lake/build/lib/lean/Verification/Specs','.lake/build/ir/Verification/Specs']:
            for p in (ROOT/base).glob(name+'.*'):
                p.unlink()


@unittest.skipUnless(os.environ.get('LEAN_VERIFIER_LIVE_TESTS') == '1', 'Live Lean checks required')
class QutritConformanceTests(unittest.TestCase):
    def test_original(self):
        r=checker.check(ROOT);self.assertTrue(r['ok'],r)
    def test_alternative_proof(self):
        with candidate() as (m,n):r=checker.check(ROOT,m,n)
        self.assertTrue(r['ok'],r)
    def test_mutations(self):
        for mutation in ['false','true','one_erasure','diagonal_only','fixed_reference','wrong_coordinates']:
            with self.subTest(mutation=mutation), candidate(mutation) as (m,n):
                r=checker.check(ROOT,m,n)
                self.assertFalse(r['ok'],r)
                self.assertEqual(r['error'],'Contract probe failed',r)
    def test_invalid_identifier(self):
        r=checker.check(ROOT,'Verification.X\nimport Bad');self.assertFalse(r['ok']);self.assertEqual(r['steps'],[])
    def test_tampered_spec(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);manifest=json.loads((ROOT/'tools/qutrit_conformance_contract.json').read_text())
            for f in [*manifest['trusted_sha256'],'tools/qutrit_conformance_contract.json']:
                p=root/f;p.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/f,p)
            p=root/'Verification/Specs/QuantumQutritDecoderSpec.lean';p.write_text(p.read_text()+'\n-- changed\n')
            r=checker.check(root);self.assertFalse(r['ok']);self.assertIn('hash mismatch',r['error'])

if __name__ == '__main__':unittest.main()
