#!/usr/bin/env python3
"""Verify this publication's files, producer evidence and local links without Lean."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit
from fc_proposal import check_proposal
from ci_receipt import check_private_ci

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = 'PUBLICATION-MANIFEST.json'
sys.path.insert(0, str(ROOT / 'lean/scripts'))
from axiom_audit import audit_axioms, MAIN_THEOREM


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory(root):
    result = {}
    for path in sorted(root.rglob('*')):
        relative = path.relative_to(root)
        if any(p in {'.git', '.lake', '__pycache__'} for p in relative.parts):
            continue
        if path.is_symlink():
            raise ValueError(f'Symlink in publication: {relative}')
        if not path.is_file() or relative.as_posix() == MANIFEST:
            continue
        if path.suffix in {'.olean', '.ilean', '.pyc'} or path.name == '.DS_Store':
            raise ValueError(f'Unexpected generated artifact: {relative}')
        result[relative.as_posix()] = {'bytes': path.stat().st_size, 'sha256': digest(path)}
    return result


def check_links(root, *, allow_missing_manifest=False):
    count = 0
    for path in root.rglob('*.md'):
        if any(p in {'.git', '.lake', '__pycache__'} for p in path.relative_to(root).parts):
            continue
        for target in re.findall(r'(?<!!)\[[^\]\n]*\]\(([^\s)]+)\)', path.read_text()):
            target = target.strip('<>')
            if urlsplit(target).scheme or target.startswith('#'):
                continue
            relative = unquote(urlsplit(target).path)
            linked = (path.parent / relative).resolve()
            if allow_missing_manifest and linked == (root / MANIFEST).resolve():
                continue
            if not linked.is_relative_to(root.resolve()) or not linked.exists():
                raise ValueError(f'Broken local link: {path.relative_to(root)}: {target}')
            count += 1
    return count


def check_evidence(root):
    lean = root / 'lean'
    local = sorted((lean / 'AllPrimeGroups').glob('*.lean'))
    upstream = sorted((lean / 'OAI').rglob('*.lean'))
    core = [*local, *upstream, *[lean / n for n in
                              ['AllPrimeGroups.lean', 'Audit.lean', 'UpstreamAudit.lean']]]
    if (len(local), len(upstream), len(core)) != (134, 63, 200):
        raise ValueError('The documented core source inventory differs.')
    provenance = json.loads((lean / 'upstream/provenance.json').read_text())
    if {p.relative_to(lean).as_posix() for p in upstream} != {
            item['path'] for item in provenance['files']}:
        raise ValueError('Vendored source inventory differs from provenance.')
    for item in provenance['files']:
        if digest(lean / item['path']) != item['sha256']:
            raise ValueError(f'Vendored source changed: {item["path"]}')
    checks = json.loads((lean / 'reports/local-checks.json').read_text())['files']
    for path in [*local, lean / 'AllPrimeGroups.lean', lean / 'Audit.lean']:
        relative = path.relative_to(lean).as_posix()
        record = checks.get(relative, {})
        if record.get('exit_code') != 0 or record.get('source_sha256') != digest(path):
            raise ValueError(f'Producer compilation record differs: {relative}')
    log = lean / 'reports/Audit.log'
    if checks['Audit.lean'].get('log_sha256') != digest(log):
        raise ValueError('The core audit log differs from the compilation record.')
    audited = audit_axioms((lean / 'Audit.lean').read_text(), log.read_text(), [MAIN_THEOREM])
    if len(audited) != 494 or audited != json.loads((lean / 'reports/local-axioms.json').read_text()):
        raise ValueError('The core axiom audit differs from its exact declaration list.')
    check_proposal(root)
    fc = json.loads((root / 'verification/fc-connection.json').read_text())
    if fc.get('status') != 'passed':
        raise ValueError('The reference connection has not been checked.')
    for module in ['Challenge', 'FCSolution', 'FCAudit']:
        record = fc['modules'].get(module, {})
        if record.get('exit_code') != 0 or record.get('source_sha256') != digest(lean / (module + '.lean')):
            raise ValueError(f'Unchecked reference connection source: {module}')
    fc_log = root / 'verification/fc-connection.log'
    if fc['modules']['FCAudit']['log_sha256'] != digest(fc_log):
        raise ValueError('The reference connection audit log differs.')
    fc_axioms = audit_axioms((lean / 'FCAudit.lean').read_text(), fc_log.read_text(), [
        'AllPrimeGroupsFC.finitely_presented_burnside_problem',
        'AllPrimeGroupsFC.variants.finitely_presented_burnside_problem_residually_finite',
        'AllPrimeGroupsFC.variants.finitely_presented_burnside_problem_all_primes',
        'AllPrimeGroupsFC.all_prime_groups', 'AllPrimeGroupsFC.concrete_groups'])
    if fc_axioms != fc['axioms']:
        raise ValueError('The reference connection audit map differs.')
    proposal = json.loads((root / 'verification/fc-proposal.json').read_text())
    if proposal.get('status') != 'statement_checked':
        raise ValueError('The FC proposal statement has not been checked.')
    if proposal.get('checked_theorems') != ['finitely_presented_burnside_problem',
                                             'variants.finitely_presented_burnside_problem_residually_finite',
                                             'variants.finitely_presented_burnside_problem_all_primes']:
        raise ValueError('The FC proposal must have checked the main and both variant theorems.')
    for key, path in [('proposal_sha256', root / 'FClikelean/AllPrimeGroups.lean'),
                      ('challenge_sha256', lean / 'Challenge.lean'),
                      ('solution_sha256', lean / 'FCSolution.lean')]:
        if proposal.get(key) != digest(path):
            raise ValueError('The FC proposal source has no matching statement check.')
    proposal_log = root / 'verification/fc-proposal.log'
    check_source = proposal['generated_check_source']
    if (proposal.get('log_sha256') != digest(proposal_log)
            or proposal.get('generated_check_sha256') !=
            hashlib.sha256(check_source.encode()).hexdigest()):
        raise ValueError('The FC proposal statement-check evidence differs.')
    proposal_axioms = audit_axioms(check_source, proposal_log.read_text(), [
        'AllPrimeGroupsFCProposalCheck.finitely_presented_burnside_problem',
        'AllPrimeGroupsFCProposalCheck.variants.finitely_presented_burnside_problem_residually_finite',
        'AllPrimeGroupsFCProposalCheck.variants.finitely_presented_burnside_problem_all_primes'])
    if proposal_axioms != proposal['axioms']:
        raise ValueError('The FC proposal statement-check axiom map differs.')
    baseline = json.loads((root / 'verification/baseline-full-build.json').read_text())
    if not (baseline.get('status') == 'passed' and baseline.get('complete')
            and baseline.get('closure_complete') and baseline.get('main_checked')
            and baseline.get('total') == len(baseline['modules']) == 195
            and all(v['exit_code'] == 0 for v in baseline['modules'].values())):
        raise ValueError('The baseline full-build result is incomplete.')
    for module, record in baseline['modules'].items():
        if record['source_sha256'] != baseline['context']['sources'][module]:
            raise ValueError('Inconsistent baseline source hashes.')
    return {'local_modules': len(local), 'upstream_modules': len(upstream),
            'core_lean_sources': len(core), 'core_axiom_audits': len(audited),
            'reference_connection_modules': 3, 'reference_axiom_audits': len(fc_axioms),
            'fc_proposal_status': proposal['status']}


def verify(root=ROOT):
    manifest = json.loads((root / MANIFEST).read_text())
    if manifest.get('schema_version') != 1:
        raise ValueError('Unknown publication manifest schema.')
    actual = inventory(root)
    if set(actual) != set(manifest['files']):
        raise ValueError('Publication file inventory differs from the manifest.')
    for name, record in actual.items():
        if record != manifest['files'][name]:
            raise ValueError(f'Publication content changed: {name}')
    result = check_evidence(root)
    private_ci = check_private_ci(root)
    if private_ci is not None:
        result["private_ci"] = private_ci
    result.update(files=len(actual), local_links=check_links(root),
                  verification_scope='Source integrity and producer evidence only; no new Lean build.')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    args = parser.parse_args()
    try:
        result = verify(args.root.resolve())
    except (ValueError, OSError, KeyError) as error:
        raise SystemExit(str(error)) from error
    print('PASS: ' + json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
