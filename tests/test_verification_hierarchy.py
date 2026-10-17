import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from verification_plan import plan


class HierarchyTests(unittest.TestCase):
    def test_beta_covers_all_sources(self):
        p=plan(ROOT,'beta')
        self.assertEqual(set(p['selected']),{str(x.relative_to(ROOT).with_suffix('')).replace('/','.') for x in (ROOT/'Verification').rglob('*.lean')})
    def test_direction_contains_every_member(self):
        p=plan(ROOT,'gamma',direction='quantum-physics')
        c=json.loads((ROOT/'knowledge/catalog.json').read_text())
        expected={'Verification.'+m['id'] for m in c['modules'] if m['section']=='quantum-physics'}
        self.assertTrue(expected<=set(p['selected']))
        self.assertIn('Verification.MasterSuite',p['build_modules'])
    def test_batch_and_module_dependents(self):
        p=plan(ROOT,'delta',batch='quantum-physics/qutrit-secret-sharing')
        self.assertEqual(set(p['selected']), {
            'Verification.QuantumQutritTwoOfThreeSecretSharingContract',
            'Verification.QuantumQutritSecretSharingExplicitDecoder',
            'Verification.QuantumQutritDecoderCircuitRefinement'})
        p=plan(ROOT,'epsilon',['Verification.QuantumQutritTwoOfThreeSecretSharingContract'])
        self.assertIn('Verification.QuantumQutritSecretSharingExplicitDecoder',p['reverse_dependents'])
    def test_trust_change_escalates(self):
        self.assertEqual(plan(ROOT,'zeta',['Verification.QuantumQutritSecretSharingExplicitDecoder'],changed=['tools/verifier_skill.py'])['effective_rank'],'beta')
    def test_unknown_scope_rejected(self):
        for args in [('epsilon', ['Verification.NoSuchModule']),('gamma',[])]:
            with self.assertRaises(ValueError):plan(ROOT,*args)
    def test_cross_direction_expansion_reaches_fixed_point(self):
        with tempfile.TemporaryDirectory() as t:
            r=Path(t);(r/'Verification').mkdir();(r/'knowledge').mkdir()
            owners={'A':'one','B':'two','C':'two','D':'three','E':'three'}
            (r/'knowledge/catalog.json').write_text(json.dumps({'sections':[
                {'id':d} for d in ['one','two','three']], 'modules':[
                {'id':n,'section':d} for n,d in owners.items()]}))
            for n,src in {'A':'','B':'import Verification.A','C':'',
                          'D':'import Verification.C','E':''}.items():
                (r/'Verification'/f'{n}.lean').write_text(src+'\n')
            p=plan(r,'epsilon',['Verification.A'])
            self.assertEqual(p['directions'],['one','three','two'])
            self.assertIn('Verification.E',p['build_modules'])
    def test_cycle_and_missing_import_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            r=Path(t);(r/'Verification').mkdir();(r/'knowledge').mkdir()
            (r/'knowledge/catalog.json').write_text(json.dumps({'sections':[],'modules':[]}))
            a=r/'Verification/A.lean';b=r/'Verification/B.lean'
            a.write_text('import Verification.B\n');b.write_text('import Verification.A\n')
            with self.assertRaises(ValueError):plan(r,'beta')
            b.unlink()
            with self.assertRaises(ValueError):plan(r,'beta')

if __name__=='__main__':unittest.main()
