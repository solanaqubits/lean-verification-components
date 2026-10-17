#!/usr/bin/env python3
"""Run and bind beta checks in a trusted checkout. Reports are not attestations.
An authorized publisher must independently pin the accepted evidence digest.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from verification_plan import plan

ALLOWED = {'propext','Classical.choice','Quot.sound'}
AUDITOR_SHA = '8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254'


def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def snapshot(root):
    names = subprocess.check_output(['git','ls-files','--cached','--others','--exclude-standard','-z'],cwd=root).decode().split('\0')
    return {n:digest(root/n) for n in names if n and (root/n).is_file()}


def runtime_fingerprint(root):
    lean = Path(subprocess.check_output(['lake','env','which','lean'],cwd=root,text=True).strip()).resolve()
    dependencies = {}
    manifest = json.loads((root/'lake-manifest.json').read_text())
    for package in manifest['packages']:
        p = root/'.lake/packages'/package['name']
        def git(*args): return subprocess.check_output(['git',*args],cwd=p)
        extras = git('ls-files','--others','--exclude-standard','-z').decode().split('\0')
        dependencies[package['name']] = dict(head=git('rev-parse','HEAD').decode().strip(),
            tracked_diff_sha256=hashlib.sha256(git('diff','HEAD','--')).hexdigest(),
            untracked={n:digest(p/n) for n in extras if n and (p/n).is_file()})
    return dict(lean_binary_sha256=digest(lean),lake_binary_sha256=digest(lean.parent/'lake'),
                python_binary_sha256=digest(Path(sys.executable).resolve()),python_version=sys.version,
                lean_version=subprocess.check_output([str(lean),'--version'],text=True).strip(),
                dependencies=dependencies)


def validate_report(root, directory, expected_digest=None):
    root, directory = Path(root).resolve(), Path(directory).resolve()
    path=directory/'evidence.json'
    if expected_digest and digest(path) != expected_digest:
        raise ValueError('Evidence digest mismatch')
    r=json.loads(path.read_text())
    if r.get('schema_version') != 1 or r.get('rank') != 'beta' or r.get('status') != 'passed':
        raise ValueError('Incomplete beta evidence')
    required={'root-build','verify-all','registry-audit','independent-audit','all-tests','knowledge','scope','diff'}
    if len(r['checks']) != len(required) or {c['name'] for c in r['checks']} != required:
        raise ValueError('Missing or duplicate required check')
    if r.get('auditor_sha256') != AUDITOR_SHA or runtime_fingerprint(root) != r.get('runtime'):
        raise ValueError('Runtime or auditor identity mismatch')
    if snapshot(root) != r['inputs']:
        raise ValueError('Checked tree changed')
    for c in r['checks']:
        if c['exit_code'] != 0 or c.get('timeout'):
            raise ValueError('Failed check')
        p=directory/c['log']
        if p.parent != directory or digest(p) != c['log_sha256']:
            raise ValueError('Log mismatch')
    by={c['name']:c for c in r['checks']}
    v=json.loads((directory/by['verify-all']['log']).read_text())
    if not v['ok'] or not v['source_unchanged'] or v['policy_findings'] or v['audit']['violations']:
        raise ValueError('Invalid verifier result')
    expected={n[:-5].replace('/','.') for n in r['inputs'] if n.startswith('Verification/') and n.endswith('.lean')}
    if set(v['modules']) != expected or set(v['source_sha256']) != expected:
        raise ValueError('Incomplete verify-all coverage')
    if not set(v['audit']['axioms']) <= ALLOWED or v['audit']['declarations'] <= 0:
        raise ValueError('Invalid axiom closure')
    for n,h in v['source_sha256'].items():
        if h != r['inputs'][n.replace('.','/')+'.lean']:
            raise ValueError('Verifier source binding mismatch')
    independent=json.loads((directory/by['independent-audit']['log']).read_text())
    if not independent['ok'] or independent['violations'] or independent['audited'] <= 0 or not set(independent['axiomsUsed']) <= ALLOWED:
        raise ValueError('Independent audit failed')
    test=(directory/by['all-tests']['log']).read_text()
    match=re.search(r'Ran (\d+) tests',test)
    if not match or int(match[1]) <= 0 or not re.search(r'^OK\s*$',test,re.M) or re.search(r'\bskipped\b',test,re.I):
        raise ValueError('Missing tests or unexpected skips')
    build=(directory/by['root-build']['log']).read_text()
    jobs=re.search(r'Build completed successfully \((\d+) jobs\)',build)
    if not jobs or re.search(r'\bwarning:',build,re.I):
        raise ValueError('Invalid strict build')
    return dict(ok=True,checked_files=len(r['inputs']),lean_sources=len(expected)+1,
                declarations=v['audit']['declarations'],independent_declarations=independent['audited'],
                unittest_count=int(match[1]),build_jobs=int(jobs[1]),
                fresh_modules=re.findall(r'Built (Verification(?:\.[A-Za-z0-9_]+)?) \(',build),
                evidence_sha256=digest(path),authentication='Not established by hashes alone')


def run_beta(root, directory, auditor):
    root,directory,auditor=Path(root).resolve(),Path(directory).resolve(),Path(auditor).resolve()
    if directory.is_relative_to(root):
        raise ValueError('Evidence directory must be outside checked tree')
    directory.mkdir(parents=True,exist_ok=False)
    if digest(auditor) != AUDITOR_SHA:
        raise ValueError('Independent auditor binary pin mismatch')
    inputs=snapshot(root)
    r=dict(schema_version=1,rank='beta',status='running',inputs=inputs,checks=[],
           base_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
           auditor_sha256=digest(auditor),runtime=runtime_fingerprint(root),test_environment={'LEAN_VERIFIER_LIVE_TESTS':'1'},
           conformance_scope=['Simon pinned pilot','Qutrit decoder pinned contract'],
           universal_semantic_conformance=False)
    commands=[('root-build',['lake','build','--wfail']),
      ('verify-all',['python3','tools/verifier_skill.py','--timeout','3600','verify-all']),
      ('registry-audit',['lake','env','lean','-DwarningAsError=true','Verification/AxiomAudit.lean']),
      ('independent-audit',['lake','env',str(auditor),'--root','Verification','--modules-from','Verification','--allow',','.join(sorted(ALLOWED)),'--json']),
      ('all-tests',['python3','-m','unittest','discover','-s','tests','-v']),
      ('knowledge',['python3','scripts/check_knowledge.py']),
      ('scope',['python3','tools/verification_plan.py','--rank','beta']),
      ('diff',['git','diff','--check'])]
    for name,cmd in commands:
        print('RUN '+name,flush=True);start=time.monotonic();log=directory/(name+'.log')
        with log.open('w') as f:
            p=subprocess.run(cmd,cwd=root,env={**os.environ,'LEAN_VERIFIER_LIVE_TESTS':'1'},stdout=f,stderr=subprocess.STDOUT)
        c=dict(name=name,command=cmd,exit_code=p.returncode,seconds=round(time.monotonic()-start,3),log=log.name,log_sha256=digest(log))
        r['checks'].append(c)
        if p.returncode: r['status']='failed'
        (directory/'evidence.json').write_text(json.dumps(r,indent=2)+'\n')
        print(json.dumps(c),flush=True)
        if p.returncode: raise ValueError('Check failed: '+name)
    if snapshot(root) != inputs:raise ValueError('Inputs changed during beta verification')
    r['status']='passed';(directory/'evidence.json').write_text(json.dumps(r,indent=2)+'\n')
    result=validate_report(root,directory)
    (directory/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--project',type=Path,default=Path(__file__).resolve().parents[1])
    sub=p.add_subparsers(dest='op',required=True)
    run=sub.add_parser('run-beta');run.add_argument('--output',required=True);run.add_argument('--auditor',required=True)
    check=sub.add_parser('check');check.add_argument('--evidence',required=True);check.add_argument('--expected-digest')
    a=p.parse_args()
    try:
        if a.op=='run-beta':run_beta(a.project,a.output,a.auditor)
        else:print(json.dumps(validate_report(a.project,a.evidence,a.expected_digest),indent=2))
    except (ValueError,OSError,KeyError,TypeError) as e:p.exit(1,str(e)+'\n')
if __name__=='__main__':main()
