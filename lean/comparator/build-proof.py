#!/usr/bin/env python3
"""Build all 204 project modules sequentially with Lake and retain resumable traces."""
import hashlib,json,os,re,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];LEAN=ROOT/'lean';OUT=LEAN/'.lake/build/lib/lean'
receipt=ROOT/'build-receipt';receipt.mkdir(exist_ok=True)
pins=json.loads((LEAN/'comparator/pins.json').read_text());paths=[*pins['proof_sources'],'lean/ComparatorChallenge.lean']
sources={p.removeprefix('lean/').removesuffix('.lean').replace('/','.'):ROOT/p for p in paths}
order=[];seen=set();visiting=set()
def visit(name):
    if name in seen:return
    if name in visiting:raise SystemExit('Cyclic local imports')
    visiting.add(name)
    for line in re.findall(r'^\s*(?:public )?import\s+([^\n]+)',sources[name].read_text(),re.M):
        for dep in line.split():
            if dep in sources:visit(dep)
    visiting.remove(name);seen.add(name);order.append(name)
for name in sorted(sources):visit(name)
assert len(order)==204
state={'status':'building','total':len(order),'modules':{},'tested_commit':os.environ.get('GITHUB_SHA')}
start=time.monotonic()
for i,name in enumerate(order,1):
    print(f'[{i}/{len(order)}] {name}',flush=True);t=time.monotonic()
    result=subprocess.run(['lake','build','+'+name+':olean'],cwd=LEAN)
    source=sources[name];artifact=OUT/(name.replace('.','/')+'.olean')
    state['modules'][name]={'exit_code':result.returncode,'seconds':round(time.monotonic()-t,2),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest()}
    if result.returncode==0:state['modules'][name]['olean_sha256']=hashlib.sha256(artifact.read_bytes()).hexdigest()
    (receipt/'modules.json').write_text(json.dumps(state,indent=2)+'\n')
    if result.returncode:raise SystemExit(result.returncode)
state.update(status='passed',complete=True,seconds=round(time.monotonic()-start,2));(receipt/'modules.json').write_text(json.dumps(state,indent=2)+'\n')
print('PASS: all 204 project sources built, including all three target proofs.',flush=True)
