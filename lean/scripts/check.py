#!/usr/bin/env python3
"""Check local Lean files with pinned dependencies; reject warnings, including proof holes."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
from datetime import datetime, timezone
from build_env import ROOT, LEAN, OUT, ENV, TOOLCHAIN

report = ROOT / 'reports/local-checks.json'
report.parent.mkdir(parents=True, exist_ok=True)
state = json.loads(report.read_text()) if report.exists() else {'files': {}}
state['toolchain'] = TOOLCHAIN
state['autoImplicit'] = False
state['warningsAsErrors'] = True
for filename in sys.argv[1:]:
    src = ROOT / filename
    out = OUT / Path(filename).with_suffix('.olean')
    out.parent.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    run = subprocess.run([str(LEAN), '-j1', '-DautoImplicit=false', '-DwarningAsError=true',
        '-o', str(out), str(src)], cwd=ROOT, env=ENV, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    seconds = round(time.monotonic() - start, 2)
    print(run.stdout, end='', flush=True)
    print(f'{filename}: exit={run.returncode}, {seconds}s', flush=True)
    log = ROOT / 'reports' / (Path(filename).stem + '.log')
    log.write_text(run.stdout)
    state['files'][filename] = {'source_sha256': hashlib.sha256(src.read_bytes()).hexdigest(),
        'exit_code': run.returncode, 'seconds': seconds,
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest(),
        'log': str(log.relative_to(ROOT))}
    if run.returncode == 0:
        state['files'][filename]['olean_sha256'] = hashlib.sha256(out.read_bytes()).hexdigest()
    report.write_text(json.dumps(state, indent=2) + '\n')
    if run.returncode:
        raise SystemExit(run.returncode)
