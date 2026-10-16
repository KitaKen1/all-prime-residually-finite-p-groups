#!/usr/bin/env python3
"""Compile the independent references and proof connections, then audit all five.

Use --reproduction NAME after reproduce.py for fresh-output verification.
The default uses an existing, hash-checked development build and says so.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from axiom_audit import audit_axioms
from build_env import ROOT, LEAN, ENV, OUT
from reproduce import inventory, resolved_dependencies, sha256

SOURCES = ('Challenge', 'FCSolution', 'FCAudit')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reproduction', help='completed full-project reproduction run name')
    args = parser.parse_args()
    env = ENV.copy()
    out = OUT
    if args.reproduction:
        if Path(args.reproduction).name != args.reproduction:
            parser.error('The reproduction name must be a single path component.')
        state = json.loads((ROOT / 'reports/reproduce' / args.reproduction / 'state.json').read_text())
        if not (state.get('status') == 'passed' and state.get('complete')
                and state.get('closure_complete') and state.get('main_checked')):
            raise SystemExit('The required full-project reproduction has not passed.')
        current = {module: sha256(path) for module, path in inventory().items()}
        if current != state['context']['sources']:
            raise SystemExit('The reproduction sources differ from the publication sources.')
        out = Path(state['output'])
        env['LEAN_PATH'] = state['lean_path']
        scope = 'Fresh project outputs from a completed full reproduction; pinned package caches reused.'
    else:
        subprocess.run([sys.executable, str(ROOT / 'scripts/verify.py'), '--audit-only'],
                       cwd=ROOT, check=True)
        scope = 'Incremental connection check using hash-checked existing project artifacts.'

    paths = [Path(p).resolve() for p in env['LEAN_PATH'].split(__import__('os').pathsep)]
    builtin = Path(subprocess.check_output([str(LEAN), '--print-libdir'], env=env,
                                          text=True).strip()).resolve()
    allowed = [*paths, builtin]
    before = {name: sha256(ROOT / (name + '.lean')) for name in SOURCES}
    modules = set(inventory()) | set(SOURCES)
    from reproduce import imports
    logs, checks = {}, {}
    for name in SOURCES:
        source = ROOT / (name + '.lean')
        dependencies = resolved_dependencies(source, env, ROOT, allowed, out.resolve(),
            [m for m in imports(source) if m in modules])
        artifact = out / (name + '.olean')
        artifact.parent.mkdir(parents=True, exist_ok=True)
        run = subprocess.run([str(LEAN), '-j1', '-DautoImplicit=false', '-DwarningAsError=true',
                              '-o', str(artifact), str(source)], cwd=ROOT, env=env,
                             text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        logs[name] = run.stdout
        print(f'{name}.lean: exit={run.returncode}', flush=True)
        if run.returncode:
            raise SystemExit(run.stdout)
        checks[name] = {'source_sha256': before[name], 'olean_sha256': sha256(artifact),
                        'log_sha256': hashlib.sha256(run.stdout.encode()).hexdigest(),
                        'resolved_dependency_count': len(dependencies), 'exit_code': 0}
    if any(before[name] != sha256(ROOT / (name + '.lean')) for name in SOURCES):
        raise SystemExit('A reference or connection source changed during verification.')
    audited = audit_axioms((ROOT / 'FCAudit.lean').read_text(), logs['FCAudit'], [
        'AllPrimeGroupsFC.finitely_presented_burnside_problem',
        'AllPrimeGroupsFC.variants.finitely_presented_burnside_problem_residually_finite',
        'AllPrimeGroupsFC.variants.finitely_presented_burnside_problem_all_primes',
        'AllPrimeGroupsFC.all_prime_groups', 'AllPrimeGroupsFC.concrete_groups'])
    verification = ROOT.parent / 'verification'
    verification.mkdir(exist_ok=True)
    (verification / 'fc-connection.log').write_text(logs['FCAudit'])
    result = {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
              'verification_scope': scope, 'fresh_full_reproduction': bool(args.reproduction),
              'modules': checks, 'axioms': audited, 'comparator_run': False,
              'independent_kernel_replay_run': False}
    (verification / 'fc-connection.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'PASS: {len(checks)} connection modules and {len(audited)} axiom audits. {scope}')


if __name__ == '__main__':
    main()
