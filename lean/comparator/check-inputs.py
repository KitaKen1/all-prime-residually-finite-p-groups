#!/usr/bin/env python3
"""Check the independent three-theorem challenge and all pinned verification inputs."""
import argparse,hashlib,json,os,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'scripts'))
from fc_proposal import check_proposal,REFERENCE_NAMES
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def require(ok,message):
    if not ok:raise SystemExit(message)
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--receipt-dir',type=Path);a=ap.parse_args()
    pins=json.loads((ROOT/'lean/comparator/pins.json').read_text());cfg=json.loads((ROOT/'lean/comparator.json').read_text())
    names=list(check_proposal(ROOT));wanted=['AllPrimeGroupsFC.'+n for n in names]
    require(cfg=={'challenge_module':'ComparatorChallenge','solution_module':'FCSolution','theorem_names':wanted,'permitted_axioms':['propext','Quot.sound','Classical.choice']},'Comparator config differs')
    require(pins['targets']==wanted and len(wanted)==3,'Expected main and two variants')
    require((ROOT/'lean/lean-toolchain').read_text().strip()==pins['lean_toolchain']=='leanprover/lean4:v4.34.1','Wrong toolchain')
    deps=json.loads((ROOT/'lean/lake-manifest.json').read_text())['packages']
    require(next(x['rev'] for x in deps if x['name']=='mathlib')==pins['mathlib_commit'],'Mathlib differs')
    for name,expected in pins['files_sha256'].items():require(sha(ROOT/name)==expected,'Pinned input changed: '+name)
    challenge=(ROOT/'lean/ComparatorChallenge.lean').read_text()
    require(re.findall(r'^import (\S+)',challenge,re.M)==['Challenge'],'Comparator challenge must import only independent proposition definitions')
    definitions=(ROOT/'lean/Challenge.lean').read_text()
    require(re.findall(r'^import (\S+)',definitions,re.M)==['Mathlib.GroupTheory.FinitelyPresentedGroup','Mathlib.GroupTheory.ResiduallyFinite','Mathlib.GroupTheory.PGroup'],'Reference definitions must import only standard Mathlib predicates')
    require(not re.search(r'\b(?:sorry|admit|axiom)\b',definitions),'Independent definitions contain proof holes')
    require(challenge.count('\n  sorry\n')==3,'Unexpected challenge placeholders')
    for name in names:
        short=name.rsplit('.',1)[-1]
        body=re.search(r'theorem '+short+r'\s*:\s*(.*?)\s*:= by\n  sorry',challenge,re.S)
        require(body and body[1].strip()=='AllPrimeGroupsChallenge.'+REFERENCE_NAMES[name],'Comparator challenge differs from independent FC reference: '+name)
    for name in pins['proof_sources']:
        text=(ROOT/name).read_text()
        require(not re.search(r'^\s*(?:public )?import\s+ComparatorChallenge\b',text,re.M),'Proof imports sorried Comparator challenge')
    solution=(ROOT/'lean/FCSolution.lean').read_text()
    require(not re.search(r'\b(sorry|admit)\b',solution),'Solution bridge has placeholders')
    for name in ['comparator','lean4export']:
        require(pins['toolchain_patches'][name]=={'upstream':'leanprover/lean4:v4.34.0','build':pins['lean_toolchain'],'changed_files':['lean-toolchain']},'Wrong tool patch')
    run=subprocess.run(['git','-C',str(ROOT),'rev-parse','HEAD'],capture_output=True,text=True)
    commit=run.stdout.strip() if run.returncode==0 else None
    if os.environ.get('GITHUB_SHA'):require(commit==os.environ['GITHUB_SHA'],'Checkout differs from workflow commit')
    result={'input_check':'passed','tested_commit':commit,'pins':pins,'config':cfg,'targets':wanted,'proof_sources':len(pins['proof_sources'])}
    if a.receipt_dir:
        a.receipt_dir.mkdir(parents=True,exist_ok=True)
        (a.receipt_dir/'input-check.json').write_text(json.dumps(result,indent=2)+'\n')
        for name in ['ComparatorChallenge.lean','Challenge.lean','FCSolution.lean','FCAudit.lean']:(a.receipt_dir/name).write_bytes((ROOT/'lean'/name).read_bytes())
    print('PASS: three FC/Comparator statements, pinned Lean 4.34.1 sources and independent Mathlib-only challenge.')
if __name__=='__main__':main()
