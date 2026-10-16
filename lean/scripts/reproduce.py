#!/usr/bin/env python3
"""Rebuild frozen project sources without reading existing project oleans.

The pinned toolchain and cached Lake packages are reused. This is a separate
output build on the current machine, not an independent-machine reproduction.
"""
import argparse
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

from axiom_audit import MAIN_THEOREM, audit_axioms
from build_env import ROOT, LEAN, TOOLCHAIN


def sha256(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def fingerprint(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def save(path, value):
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def inventory():
    paths = [*sorted((ROOT / 'AllPrimeGroups').glob('*.lean')),
             *sorted((ROOT / 'OAI').rglob('*.lean')),
             ROOT / 'AllPrimeGroups.lean', ROOT / 'Audit.lean', ROOT / 'UpstreamAudit.lean']
    return {str(p.relative_to(ROOT).with_suffix('')).replace('/', '.'): p for p in paths}


def imports(source):
    # Plan the checked sources' simple headers, handling nested comments. Actual
    # compiler-resolved dependency paths are checked again before every build.
    result = []
    depth = 0
    for line in source.read_text().splitlines():
        clean = []
        i = 0
        while i < len(line):
            if line[i:i + 2] == '/-':
                depth += 1
                i += 2
            elif depth and line[i:i + 2] == '-/':
                depth -= 1
                i += 2
            elif not depth and line[i:i + 2] == '--':
                break
            else:
                if not depth:
                    clean.append(line[i])
                i += 1
        text = ''.join(clean).strip()
        match = re.fullmatch(r'(?:(?:public|private)\s+)?import\s+(.+)', text)
        if match:
            result.extend(match.group(1).split())
        elif text and not re.fullmatch(r'(?:module|prelude)', text):
            break
    return result


def build_order(sources, targets):
    order, active, visited = [], set(), set()

    def visit(module):
        if module in active:
            raise ValueError(f'Cyclic project imports at {module}')
        if module in visited:
            return
        if module not in sources:
            raise ValueError(f'Unknown project module: {module}')
        active.add(module)
        for dependency in imports(sources[module]):
            if dependency in sources:
                visit(dependency)
            elif dependency == 'AllPrimeGroups' or dependency.startswith(('AllPrimeGroups.', 'OAI.')):
                raise ValueError(f'Missing project source: {dependency}')
        active.remove(module)
        visited.add(module)
        order.append(module)

    for target in targets:
        visit(target)
    return order


def context(sources):
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    dependencies = []
    for package in manifest['packages']:
        folder = ROOT / manifest['packagesDir'] / package['name']
        head = subprocess.check_output(['git', '-C', str(folder), 'rev-parse', 'HEAD'], text=True).strip()
        dirty = subprocess.check_output(['git', '-C', str(folder), 'status', '--porcelain',
                                         '--untracked-files=no'], text=True).strip()
        if head != package['rev'] or dirty:
            raise ValueError(f'Package differs from the lock file: {package["name"]}')
        artifacts = (folder / '.lake/build/lib/lean').resolve()
        for prefix in ['AllPrimeGroups', 'OAI']:
            if (artifacts / prefix).exists() or (artifacts / f'{prefix}.olean').exists():
                raise ValueError(f'Project artifacts found inside a package cache: {artifacts}')
        dependencies.append({'name': package['name'], 'rev': head,
                             'artifacts': str(artifacts) if artifacts.is_dir() else None})
    upstream = json.loads((ROOT / 'upstream/provenance.json').read_text())
    for item in upstream['files']:
        if sha256(ROOT / item['path']) != item['sha256']:
            raise ValueError(f'Vendored source changed: {item["path"]}')
    vendored = {str(p.relative_to(ROOT)) for p in sources.values() if p.is_relative_to(ROOT / 'OAI')}
    if vendored != {item['path'] for item in upstream['files']}:
        raise ValueError('The vendored source inventory differs from its provenance manifest.')
    clean_env = os.environ.copy()
    clean_env.pop('LEAN_SYSROOT', None)
    version = subprocess.check_output([str(LEAN), '--version'], env=clean_env, text=True).strip()
    return {'toolchain': TOOLCHAIN, 'lean_version': version, 'lean_sha256': sha256(LEAN),
            'sources': {m: sha256(p) for m, p in sources.items()}, 'packages': dependencies,
            'inputs': {name: sha256(ROOT / name) for name in [
                'lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'upstream/provenance.json',
                'scripts/reproduce.py', 'scripts/axiom_audit.py', 'scripts/build_env.py']}}


def within(path, roots):
    return any(path.is_relative_to(root) for root in roots)


def resolved_dependencies(source, env, cwd, allowed_roots, project_out, project_dependencies):
    run = subprocess.run([str(LEAN), '--deps', str(source)], cwd=cwd, env=env,
                         text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
    paths = sorted({Path(line).resolve() for line in run.stdout.splitlines() if line.strip()})
    for path in paths:
        if not path.is_file() or not within(path, allowed_roots):
            raise ValueError(f'Dependency outside the isolated build or pinned caches: {path}')
    expected = {(project_out / (module.replace('.', '/') + '.olean')).resolve()
                for module in project_dependencies}
    actual = {path for path in paths if path.is_relative_to(project_out)}
    if actual != expected:
        raise ValueError(f'Lean project dependencies differ from the build plan: '
                         f'missing={expected - actual}, extra={actual - expected}')
    return {str(path): sha256(path) for path in paths}


def cache_matches(record, source, artifact, log, dependencies):
    return (record.get('exit_code') == 0 and artifact.is_file() and log.is_file()
            and record.get('source_sha256') == sha256(source)
            and record.get('olean_sha256') == sha256(artifact)
            and record.get('log_sha256') == sha256(log)
            and record.get('dependencies') == dependencies)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--name', default='full-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ'))
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--plan', action='store_true', help='print the build plan without creating a run')
    parser.add_argument('--target', action='append', help='partial closure to check (repeatable)')
    args = parser.parse_args()
    if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_-]*', args.name):
        parser.error('--name must contain only letters, digits, hyphens and underscores')
    sources = inventory()
    targets = args.target or ['Audit', 'UpstreamAudit']
    order = build_order(sources, targets)
    full = args.target is None
    if full and set(order) != set(sources):
        raise ValueError(f'Project modules omitted from the root imports: {set(sources) - set(order)}')
    inputs = context(sources)
    identity = fingerprint({'context': inputs, 'targets': targets})
    if args.plan:
        print(json.dumps({'modules': len(order), 'local_modules': sum(
            m.startswith('AllPrimeGroups.') for m in order), 'full_project': full,
            'targets': targets, 'context_sha256': identity, 'order': order}, indent=2))
        return
    build = ROOT / '.lake/reproduce' / args.name
    report_dir = ROOT / 'reports/reproduce' / args.name
    report = report_dir / 'state.json'
    report_dir.mkdir(parents=True, exist_ok=True)
    with (report_dir / 'run.lock').open('a') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise ValueError('This reproduction is already running.') from error
        if args.resume:
            state = json.loads(report.read_text())
            if state['context_sha256'] != identity:
                raise ValueError('Inputs or targets changed; use a new run name.')
        else:
            if report.exists() or build.exists():
                raise ValueError('Run already exists; choose --resume or a new name.')
            state = {'started_at_utc': now(), 'context_sha256': identity, 'context': inputs,
                     'targets': targets, 'full_project': full, 'total': len(order), 'modules': {},
                     'scope': 'Fresh project outputs; pinned toolchain and package caches reused.'}
            for module, source in sources.items():
                destination = build / 'sources' / source.relative_to(ROOT)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(source.read_bytes())
        snapshot = build / 'sources'
        out = (build / 'lib').resolve()
        existing = (ROOT / '.lake/build/lib/lean').resolve()
        if out.is_relative_to(existing) or existing.is_relative_to(out):
            raise ValueError('The reproduction output overlaps the existing project output.')
        out.mkdir(parents=True, exist_ok=True)
        logs = report_dir / 'logs'
        logs.mkdir(exist_ok=True)
        for module, digest in inputs['sources'].items():
            if sha256(snapshot / (module.replace('.', '/') + '.lean')) != digest:
                raise ValueError(f'Frozen source changed: {module}')
        env = os.environ.copy()
        env.pop('LEAN_SYSROOT', None)
        package_roots = [p['artifacts'] for p in inputs['packages'] if p['artifacts']]
        env['LEAN_PATH'] = os.pathsep.join([str(out), *package_roots])
        env['LEAN_NUM_THREADS'] = '1'
        builtin = Path(subprocess.check_output([str(LEAN), '--print-libdir'], env=env, text=True).strip()).resolve()
        allowed = [out, builtin, *[Path(p) for p in package_roots]]
        state.update({'complete': False, 'closure_complete': False, 'status': 'running',
                      'lean_path': env['LEAN_PATH'], 'output': str(out)})
        for key in ['error', 'stopped_at_utc', 'finished_at_utc', 'audits', 'main_checked']:
            state.pop(key, None)
        save(report, state)
        try:
            audits = {}
            for i, module in enumerate(order, 1):
                source = snapshot / (module.replace('.', '/') + '.lean')
                artifact = out / (module.replace('.', '/') + '.olean')
                log = logs / (module + '.log')
                dependencies = resolved_dependencies(source, env, snapshot, allowed, out,
                    [m for m in imports(source) if m in sources])
                record = state['modules'].get(module, {})
                if cache_matches(record, source, artifact, log, dependencies):
                    print(f'[{i}/{len(order)}] verified cache {module}', flush=True)
                else:
                    artifact.parent.mkdir(parents=True, exist_ok=True)
                    command = [str(LEAN), '-j1', '-DautoImplicit=false']
                    if not module.startswith('OAI.'):
                        command.append('-DwarningAsError=true')
                    command += ['-o', str(artifact), str(source)]
                    state['current_module'] = module
                    save(report, state)
                    print(f'[{i}/{len(order)}] checking {module}', flush=True)
                    started = time.monotonic()
                    with log.open('w') as stream:
                        run = subprocess.run(command, cwd=snapshot, env=env,
                                             stdout=stream, stderr=subprocess.STDOUT)
                    record = {'exit_code': run.returncode, 'source_sha256': sha256(source),
                              'seconds': round(time.monotonic() - started, 2),
                              'checked_at_utc': now(), 'log_sha256': sha256(log),
                              'dependencies': dependencies}
                    if run.returncode == 0:
                        record['olean_sha256'] = sha256(artifact)
                    state['modules'][module] = record
                    save(report, state)
                    if run.returncode:
                        print(log.read_text()[-12000:], flush=True)
                        raise ValueError(f'Lean failed: {module} (exit {run.returncode})')
                    print(f'[{i}/{len(order)}] passed {module} ({record["seconds"]}s)', flush=True)
                if module in ['Audit', 'UpstreamAudit']:
                    required = [MAIN_THEOREM] if module == 'Audit' else ['OAI.SourceBurnside.thm_main']
                    audits[module] = audit_axioms(source.read_text(), log.read_text(), required)
            if fingerprint({'context': context(inventory()), 'targets': targets}) != identity:
                raise ValueError('Original inputs changed during the build; start a new run.')
            # A final pass detects artifacts, logs or frozen sources changed after their check.
            for module in order:
                source = snapshot / (module.replace('.', '/') + '.lean')
                artifact = out / (module.replace('.', '/') + '.olean')
                deps = resolved_dependencies(source, env, snapshot, allowed, out,
                    [m for m in imports(source) if m in sources])
                if not cache_matches(state['modules'][module], source, artifact,
                                     logs / (module + '.log'), deps):
                    raise ValueError(f'Checked inputs or artifacts changed: {module}')
            state.update({'closure_complete': True, 'complete': full,
                          'status': 'passed', 'finished_at_utc': now(), 'audits': audits,
                          'main_checked': MAIN_THEOREM in audits.get('Audit', {})})
            state.pop('current_module', None)
            save(report, state)
            print(f'PASS: {len(order)} modules; full project: {full}; '
                  f'main audited: {state["main_checked"]}. Report: {report}', flush=True)
        except (Exception, KeyboardInterrupt) as error:
            state.update({'complete': False, 'closure_complete': False,
                          'status': 'interrupted' if isinstance(error, KeyboardInterrupt) else 'failed',
                          'error': str(error), 'stopped_at_utc': now()})
            save(report, state)
            raise


if __name__ == '__main__':
    main()
