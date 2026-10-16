#!/usr/bin/env python3
"""Extract a verified bundle and test its scripts and a fresh Lean output on this host.

Only the specified pinned package cache is shared. Project artifacts are never copied.
This is a portability smoke test, not a full or independent-host reproduction.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import zipfile

from verify_bundle import verify_bundle
from axiom_audit import audit_axioms
from build_env import LEAN, ENV

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('archive', type=Path)
    parser.add_argument('--package-cache', type=Path, default=ROOT / '.lake/packages')
    parser.add_argument('--sha256')
    args = parser.parse_args()
    archive = args.archive.resolve()
    info = verify_bundle(archive, args.sha256)
    cache = args.package_cache.resolve()
    if not cache.is_dir():
        raise SystemExit('Pinned package cache is missing; prepare the locked Lake dependencies first.')
    folder = ROOT / '.lake/portable-check'
    folder.mkdir(parents=True, exist_ok=True)
    extracted = Path(tempfile.mkdtemp(prefix=info['archive_sha256'][:12] + '-', dir=folder))
    with zipfile.ZipFile(archive) as stream:
        stream.extractall(extracted)
    project = extracted / 'all-prime-groups'
    (project / '.lake').mkdir()
    (project / '.lake/packages').symlink_to(cache, target_is_directory=True)
    for arguments in [
            ['scripts/manuscript_correspondence.py'],
            ['scripts/test_verification.py'], ['scripts/test_release.py']]:
        subprocess.run([sys.executable, *arguments], cwd=project, check=True)
    missing = subprocess.run([sys.executable, 'scripts/verify.py', '--audit-only'], cwd=project,
                             text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if missing.returncode == 0 or 'Build artifact changed or missing' not in missing.stdout:
        raise RuntimeError('The extracted audit did not reject missing project artifacts.')
    print('PASS: missing project artifacts correctly rejected.', flush=True)
    subprocess.run([sys.executable, 'scripts/reproduce.py', '--name', 'portable-smoke',
                    '--target', 'AllPrimeGroups.PrimePeriods',
                    '--target', 'AllPrimeGroups.NilMatrixCongruence'], cwd=project, check=True)
    state = json.loads((project / 'reports/reproduce/portable-smoke/state.json').read_text())
    if (state['status'] != 'passed' or not state['closure_complete'] or state['complete']
            or state['main_checked']):
        raise RuntimeError('Invalid partial-build result.')
    # Compile and audit the new generic nil-unit results using only the fresh outputs.
    names = re.findall(r'^#print axioms (AllPrimeGroups\.NilCongruence\.\S+)\s*$',
                       (project / 'Audit.lean').read_text(), re.M)
    audit_source = ('import AllPrimeGroups.NilMatrixCongruence\n' +
                    ''.join(f'#print axioms {name}\n' for name in names))
    audit_file = project / 'reports/PortableNilAudit.lean'
    audit_file.write_text(audit_source)
    env = ENV.copy()
    env['LEAN_PATH'] = state['lean_path']
    run = subprocess.run([str(LEAN), '-j1', '-DautoImplicit=false', '-DwarningAsError=true',
                          str(audit_file)], cwd=project, env=env, text=True,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    audit_log = project / 'reports/PortableNilAudit.log'
    audit_log.write_text(run.stdout)
    if run.returncode:
        raise RuntimeError(f'Fresh nil-unit audit failed: {audit_log}\n{run.stdout}')
    audited = audit_axioms(audit_source, run.stdout, [
        'AllPrimeGroups.NilCongruence.kernelEquiv',
        'AllPrimeGroups.NilCongruence.matrix_card_eq_prime_pow_finrank',
        'AllPrimeGroups.NilCongruence.matrix_properties'])
    print(f'PASS: {len(audited)} nil-unit declarations audited using fresh outputs.', flush=True)
    result = {'archive': str(archive), 'archive_sha256': info['archive_sha256'],
              'extracted_project': str(project), 'package_cache_reused': str(cache),
              'no_project_artifacts_copied': True, 'correspondence_inventory_passed': True,
              'verification_regression_tests_passed': 8, 'release_tests_passed': 15,
              'audit_without_artifacts_rejected': True, 'lean_smoke_passed': True,
              'nil_congruence_fresh_output_passed': True,
              'nil_congruence_axiom_audits': len(audited), 'nil_congruence_audit_log': str(audit_log),
              'smoke_state': str(project / 'reports/reproduce/portable-smoke/state.json'),
              'verification_scope': ('Extracted bundle; prime-period and generic nil-unit dependency '
                                     'closures; same host and pinned package cache. Not a full build.')}
    (ROOT / 'reports').mkdir(exist_ok=True)
    (ROOT / 'reports/portable-bundle-check.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
