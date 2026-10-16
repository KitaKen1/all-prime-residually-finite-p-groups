"""Validate archived GitHub CI receipts against the current proof and checker inputs."""
import hashlib
import json
from pathlib import Path


def check_private_ci(root):
    return check_ci(root, public=False)


def check_public_ci(root):
    return check_ci(root, public=True)


def check_ci(root, *, public):
    kind = 'public' if public else 'private'
    repository = ('KitaKen1/all-prime-residually-finite-p-groups' if public
                  else 'KitaKen1/ci-test-sandbox')
    record_path = root / f'verification/{kind}-ci-verification.json'
    if not record_path.exists():
        return None
    record = json.loads(record_path.read_text())
    archive = root / record['archive']
    if not archive.resolve().is_relative_to(root.resolve()):
        raise ValueError('CI archive must be inside this publication.')
    def load(name):
        return json.loads((archive / name).read_text())
    def require(ok, message):
        if not ok:
            raise ValueError(message)
    def sha(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()
    provenance = load('provenance.json')
    run = load('github/attempt.json')
    require(sha(archive / 'provenance.json') == record['archive_provenance_sha256'],
            'CI archive provenance digest differs.')
    require(record['status'] == provenance['conclusion'] == run['conclusion'] == 'success',
            'CI is not a successful run.')
    require(run['status'] == 'completed' and run['head_sha'] == record['tested_commit'] == provenance['tested_commit'],
            'CI tested commit differs.')
    require(run['id'] == record['run_id'] == provenance['run_id'] and
            run['run_attempt'] == record['run_attempt'] == provenance['run_attempt'],
            'CI run or attempt differs.')
    require(provenance['repository'] == record['repository'] == repository,
            f'Unexpected {kind} CI repository.')
    require(run['head_branch'] == record['branch'] and
            run['html_url'] == record['run_url'] == provenance['run_url'],
            'CI branch or run URL differs.')
    if public:
        metadata = load('github/repository.json')
        require(metadata['full_name'] == repository and metadata['private'] is False
                and metadata['visibility'] == 'public' and run['head_branch'] == 'main',
                'Public CI must run on public main.')
    expected = {'compiled_project_modules': 204, 'comparator_targets': 3,
                'core_axiom_audits': 494, 'connection_axiom_audits': 5,
                'comparator_builtin_kernel_replay': True,
                'separate_fresh_lean_kernel_replay': True,
                'external_kernel_run': False, 'public_ci_run': public}
    require(all(record.get(key) == value for key, value in expected.items()),
            'CI record verification scope differs.')
    jobs = load('github/jobs.json')['jobs']
    for name in ['build', 'comparator', 'replay', 'verification_status']:
        matches = [job for job in jobs if job['name'] == name]
        require(len(matches) == 1 and matches[0]['conclusion'] == 'success',
                'Missing successful CI job: ' + name)
    for artifact in provenance['artifacts']:
        require('sha256:' + sha(archive / artifact['file']) == artifact['github_digest'],
                'Original CI artifact ZIP differs from its GitHub API digest.')
    for line in (archive / 'SHA256SUMS').read_text().splitlines():
        expected, name = line.split('  ', 1)
        require(sha(archive / name) == expected, 'Archived receipt changed: ' + name)
    suffix = f"{record['run_id']}-{record['run_attempt']}"
    comparator = archive / 'receipt' / ('comparator-' + suffix)
    build = archive / 'receipt' / ('build-' + suffix)
    replay = archive / 'receipt' / ('replay-' + suffix)
    for folder in [build, comparator, replay]:
        require((folder / 'status.txt').read_text() == 'PASS\n', 'CI receipt is not PASS.')
    inputs = json.loads((comparator / 'input-check.json').read_text())
    require(inputs['tested_commit'] == record['tested_commit'] and inputs['input_check'] == 'passed',
            'Comparator receipt commit differs.')
    pins = inputs['pins']
    require(record['toolchain'] == pins['lean_toolchain'], 'CI record toolchain differs.')
    current = json.loads((root / 'lean/comparator/pins.json').read_text())
    require(pins == current, 'Current Comparator pins differ from the tested inputs.')
    for name, expected in pins['files_sha256'].items():
        require(sha(root / name) == expected, 'Current verified source changed: ' + name)
    require(len(inputs['targets']) == 3 and inputs['targets'] == current['targets'],
            'Missing one of the three Comparator targets.')
    environment = json.loads((comparator / 'checker-environment.json').read_text())
    require(environment['status'] == 'PASS' and environment['required_version'] == '4.34.1',
            'Checker version differs.')
    log = (comparator / 'comparator.log').read_text()
    require('Lean default kernel accepts the solution' in log and 'Your solution is okay!' in log,
            'Comparator success output missing.')
    modules = json.loads((build / 'modules.json').read_text())
    require(modules['status'] == 'passed' and modules['complete'] and modules['total'] == 204,
            'Full 204-source CI build is incomplete.')
    wanted = [*pins['proof_sources'], 'lean/ComparatorChallenge.lean']
    expected_modules = {name.removeprefix('lean/').removesuffix('.lean').replace('/', '.'): name
                        for name in wanted}
    require(set(modules['modules']) == set(expected_modules), 'CI build module inventory differs.')
    for module, path in expected_modules.items():
        entry = modules['modules'][module]
        require(entry['exit_code'] == 0 and entry['source_sha256'] == sha(root / path),
                'Incomplete or different CI module: ' + module)
    for name, count in [('axioms.json', 5), ('axioms-full.json', 494)]:
        audit = json.loads((comparator / name).read_text())
        require(audit['status'] == 'PASS' and audit['audited_targets'] == count
                and not audit['sorryAx'] and not audit['new_axioms'], 'CI axiom audit differs.')
    require('Exit status: 0' in (replay / 'time.log').read_text(), 'Fresh kernel replay failed.')
    return {'status': 'success', 'repository': record['repository'],
            'run_id': record['run_id'], 'run_attempt': record['run_attempt'],
            'tested_commit': record['tested_commit'], 'run_url': record['run_url'],
            'compiled_project_modules': 204, 'comparator_targets': 3,
            'core_axiom_audits': 494, 'connection_axiom_audits': 5,
            'separate_fresh_lean_kernel_replay': True,
            'external_kernel_run': False, 'public_ci_run': public}
