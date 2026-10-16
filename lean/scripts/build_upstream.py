#!/usr/bin/env python3
"""Compile the exact vendored dependency closure sequentially, with resumable logs."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

from build_env import ROOT, LEAN, OUT, ENV, TOOLCHAIN
from axiom_audit import audit_axioms

REPORT = ROOT / 'reports/upstream-build.json'
LOGS = ROOT / 'reports/upstream'
LOGS.mkdir(parents=True, exist_ok=True)
OUT.mkdir(parents=True, exist_ok=True)
env = ENV
provenance = json.loads((ROOT / 'upstream/provenance.json').read_text())
for item in provenance['files']:
    digest = hashlib.sha256((ROOT / item['path']).read_bytes()).hexdigest()
    if digest != item['sha256']:
        raise SystemExit(f"Upstream source changed: {item['path']}")

order = []
seen = set()
def visit(module):
    if module in seen:
        return
    seen.add(module)
    source = ROOT / (module.replace('.', '/') + '.lean')
    for dependency in re.findall(r'^import (OAI\.\S+)', source.read_text(), re.M):
        visit(dependency)
    order.append((module, source))
visit('OAI.GroupTheory.PeriodicGroups.Main')

state = json.loads(REPORT.read_text()) if REPORT.exists() else {'modules': {}}
state.update({'lean': str(LEAN), 'toolchain': TOOLCHAIN, 'autoImplicit': False, 'total': len(order), 'complete': False})
for i, (module, source) in enumerate(order, 1):
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    olean = OUT / (module.replace('.', '/') + '.olean')
    previous = state['modules'].get(module, {})
    if (previous.get('sha256') == digest and previous.get('exit_code') == 0
            and olean.exists() and previous.get('olean_sha256') ==
            hashlib.sha256(olean.read_bytes()).hexdigest()):
        print(f'[{i}/{len(order)}] cached {module}', flush=True)
        continue
    olean.parent.mkdir(parents=True, exist_ok=True)
    log = LOGS / (module + '.log')
    command = [str(LEAN), '-j1', '-DautoImplicit=false', '-o', str(olean), str(source)]
    start = time.monotonic()
    print(f'[{i}/{len(order)}] checking {module}', flush=True)
    with log.open('w') as stream:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
    state['modules'][module] = {'sha256': digest, 'exit_code': result.returncode,
        'seconds': round(time.monotonic() - start, 2), 'log': str(log.relative_to(ROOT))}
    state['modules'][module]['log_sha256'] = hashlib.sha256(log.read_bytes()).hexdigest()
    if result.returncode == 0:
        state['modules'][module]['olean_sha256'] = hashlib.sha256(olean.read_bytes()).hexdigest()
    REPORT.write_text(json.dumps(state, indent=2) + '\n')
    if result.returncode:
        print(log.read_text()[-12000:], flush=True)
        raise SystemExit(result.returncode)
    print(f'[{i}/{len(order)}] passed ({state["modules"][module]["seconds"]}s)', flush=True)

log = ROOT / 'reports/upstream-axioms.log'
with log.open('w') as stream:
    result = subprocess.run([str(LEAN), '-j1', '-DautoImplicit=false', 'UpstreamAudit.lean'],
        cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
state['audit_exit_code'] = result.returncode
audit_text = log.read_text()
try:
    audit_axioms((ROOT / 'UpstreamAudit.lean').read_text(), audit_text,
                 ['OAI.SourceBurnside.thm_main'])
    axioms_ok = True
except ValueError:
    axioms_ok = False
state['audit_log_sha256'] = hashlib.sha256(log.read_bytes()).hexdigest()
state['axioms_ok'] = axioms_ok
state['complete'] = result.returncode == 0 and axioms_ok
REPORT.write_text(json.dumps(state, indent=2) + '\n')
print(log.read_text(), flush=True)
raise SystemExit(0 if state['complete'] else 1)
