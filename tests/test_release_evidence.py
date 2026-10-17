import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from release_evidence import digest, snapshot, validate_report, AUDITOR_SHA


class EvidenceTests(unittest.TestCase):
    def setUp(self):
        mock=patch("release_evidence.runtime_fingerprint",return_value={"test_runtime":1});mock.start();self.addCleanup(mock.stop)
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)/'repo';self.root.mkdir()
        subprocess.run(['git','init','-q'],cwd=self.root,check=True)
        (self.root/'Verification').mkdir();(self.root/'Verification/A.lean').write_text('theorem yes : True := True.intro\n')
        (self.root/'Verification.lean').write_text('import Verification.A\n')
        self.out=Path(self.tmp.name)/'evidence';self.out.mkdir()
        inputs=snapshot(self.root)
        logs={'root-build':'Build completed successfully (3 jobs).\n',
              'verify-all':json.dumps(dict(ok=True,source_unchanged=True,policy_findings=[],modules=['Verification.A'],source_sha256={'Verification.A':inputs['Verification/A.lean']},audit={'axioms':[],'declarations':1,'violations':[]})),
              'independent-audit':json.dumps(dict(ok=True,violations=[],audited=1,axiomsUsed=[])),
              'all-tests':'Ran 1 tests in 0.1s\n\nOK\n',
              'registry-audit':'passed','knowledge':'passed','scope':'{}','diff':''}
        self.report=dict(schema_version=1,rank='beta',status='passed',inputs=inputs,checks=[],auditor_sha256=AUDITOR_SHA,runtime={'test_runtime':1})
        for n,text in logs.items():
            p=self.out/(n+'.log');p.write_text(text)
            self.report['checks'].append(dict(name=n,exit_code=0,log=p.name,log_sha256=digest(p)))
        self.save()
    def save(self):
        (self.out/'evidence.json').write_text(json.dumps(self.report))
    def test_consistent_evidence(self):
        self.assertTrue(validate_report(self.root,self.out)['ok'])
    def test_runtime_change_rejected(self):
        self.report['runtime'] = {'test_runtime':2};self.save()
        with self.assertRaises(ValueError):validate_report(self.root,self.out)
    def test_failed_check_rejected(self):
        self.report['checks'][0]['exit_code']=1;self.save()
        with self.assertRaises(ValueError):validate_report(self.root,self.out)
    def test_tree_change_rejected(self):
        (self.root/'Verification/A.lean').write_text('-- changed\n')
        with self.assertRaises(ValueError):validate_report(self.root,self.out)
    def test_log_change_rejected(self):
        (self.out/'all-tests.log').write_text('OK\n')
        with self.assertRaises(ValueError):validate_report(self.root,self.out)
    def test_missing_check_rejected(self):
        self.report['checks'].pop();self.save()
        with self.assertRaises(ValueError):validate_report(self.root,self.out)
    def test_wrong_digest_rejected(self):
        with self.assertRaises(ValueError):validate_report(self.root,self.out,'0'*64)
    def test_skip_rejected_even_with_updated_hash(self):
        p=self.out/'all-tests.log';p.write_text('Ran 1 tests in 0.1s\nOK (skipped=1)\n')
        next(c for c in self.report['checks'] if c['name']=='all-tests')['log_sha256']=digest(p);self.save()
        with self.assertRaises(ValueError):validate_report(self.root,self.out)
    def test_incomplete_source_coverage_rejected(self):
        p=self.out/'verify-all.log';v=json.loads(p.read_text());v['modules']=[];p.write_text(json.dumps(v))
        next(c for c in self.report['checks'] if c['name']=='verify-all')['log_sha256']=digest(p);self.save()
        with self.assertRaises(ValueError):validate_report(self.root,self.out)

if __name__=='__main__':unittest.main()
