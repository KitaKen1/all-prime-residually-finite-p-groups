#!/usr/bin/env python3
"""Compile files in drafts/ in the given order, without moving or registering them.

usage: python3 scripts/compile_drafts.py PrimeMatrixNil PrimeAlgebra PrimeReduction

Each draft is compiled with warnings treated as errors. Its .olean is written to the build
directory as AllPrimeGroups/<name>.olean, so that a later draft can import it, and its output
to .lake/draft-logs/<name>.log. The Prime* drafts import upstream modules up to
Steinberg.CoefficientQuotients, so those must be built first (python3 scripts/build_upstream.py).
Stops at the first failure. A passing draft is still not part of the library: move it into
AllPrimeGroups/, add it to AllPrimeGroups.lean, Audit.lean and scripts/verify.py, then run
scripts/check.py and scripts/verify.py --audit-only."""
import json, subprocess, sys, time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from build_env import ROOT, LEAN, OUT, ENV

NEED = 'OAI.GroupTheory.PeriodicGroups.Steinberg.CoefficientQuotients'
names = sys.argv[1:]
if not names:
    raise SystemExit(__doc__)
mods = json.loads((ROOT / 'reports/upstream-build.json').read_text()).get('modules', {})
if any(n.startswith('Prime') for n in names) and mods.get(NEED, {}).get('exit_code') != 0:
    raise SystemExit(f'{NEED} is not built yet; run python3 scripts/build_upstream.py first')
logs = ROOT / '.lake/draft-logs'
logs.mkdir(parents=True, exist_ok=True)
for name in names:
    out = OUT / 'AllPrimeGroups' / f'{name}.olean'
    start = time.monotonic()
    run = subprocess.run([str(LEAN), '-j1', '-DautoImplicit=false', '-DwarningAsError=true',
        '-o', str(out), f'drafts/{name}.lean'], cwd=ROOT, env=ENV, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (logs / f'{name}.log').write_text(run.stdout)
    print(f'{name}: exit={run.returncode}, {round(time.monotonic() - start)}s', flush=True)
    if run.returncode:
        print(run.stdout[:6000], flush=True)
        raise SystemExit(1)
print('ALL DRAFTS COMPILED', flush=True)
