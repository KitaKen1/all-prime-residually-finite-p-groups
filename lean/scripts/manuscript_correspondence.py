#!/usr/bin/env python3
"""Check the manuscript claim inventory and render the manually assessed proof scopes.

This checks references and evidence, not mathematical equivalence of statements.
"""
import argparse
import ast
from collections import Counter
import hashlib
import html
import json
import os
from pathlib import Path
import re

from axiom_audit import MAIN_THEOREM, audit_axioms

ROOT = Path(__file__).resolve().parents[1]
MANUSCRIPTS = ('build_proof_manuscript.py', 'proof_extensions.py',
               'algebra_construction.py', 'stable_detection.py')
STATUSES = {'proved': 'Proved as stated',
            'specialized': 'Needed specialization proved',
            'replaced': 'Replaced by another argument',
            'partial': 'Partial correspondence',
            'unformalized': 'Independent claim not registered'}
ASSESSMENT = ('Scope classifications are manual mathematical assessments. The checker verifies '
              'the claim inventory, source hashes and audit references, not statement equivalence.')


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def manuscript_directory(root=ROOT):
    if all((root / 'manuscript' / name).is_file() for name in MANUSCRIPTS):
        return root / 'manuscript'
    return root.parent


def extract_claims(directory):
    claims = {}
    pattern = r'<b>(Theorem|Lemma|Proposition|Corollary) (\d+\.\d+)(?: \((.*?)\))?\.</b>'
    for filename in MANUSCRIPTS:
        tree = ast.parse((directory / filename).read_text())
        for node in ast.walk(tree):
            if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                    and node.func.id == 'p' and node.args and isinstance(node.args[0], ast.Constant)
                    and isinstance(node.args[0].value, str)):
                continue
            for match in re.finditer(pattern, node.args[0].value):
                claim_id = match[2]
                if claim_id in claims:
                    raise ValueError(f'Duplicate manuscript claim: {claim_id}')
                claims[claim_id] = {'kind': match[1], 'title': match[3] or '',
                                    'file': filename, 'line': node.lineno,
                                    'heading_sha256': hashlib.sha256(
                                        node.args[0].value.encode()).hexdigest()}
    return claims


def validate(root=ROOT, directory=None, check_artifacts=False):
    directory = directory or manuscript_directory(root)
    manifest = json.loads((root / 'manuscript-claims.json').read_text())
    if manifest.get('schema_version') != 1:
        raise ValueError('Unknown correspondence manifest schema.')
    if manifest.get('assessment') != ASSESSMENT:
        raise ValueError('The manual scope-assessment qualification is missing.')
    hashes = {name: sha256(directory / name) for name in MANUSCRIPTS}
    if manifest['manuscript_sources'] != hashes:
        raise ValueError('Manuscript sources changed; review and update the claim assessments.')
    claims = extract_claims(directory)
    entries = manifest['claims']
    ids = [entry['id'] for entry in entries]
    if len(ids) != len(set(ids)) or set(ids) != set(claims):
        raise ValueError('The correspondence table must contain every manuscript claim exactly once.')
    audit_source = (root / 'Audit.lean').read_text()
    requested = set(re.findall(r'^#print axioms (\S+)\s*$', audit_source, re.M))
    audit_result = None
    checks = None
    if check_artifacts:
        checks = json.loads((root / 'reports/local-checks.json').read_text())
        record = checks['files'].get('Audit.lean', {})
        log = root / 'reports/Audit.log'
        artifact = root / '.lake/build/lib/lean/Audit.olean'
        if (record.get('exit_code') != 0 or record.get('source_sha256') != sha256(root / 'Audit.lean')
                or record.get('log_sha256') != sha256(log) or not artifact.is_file()
                or record.get('olean_sha256') != sha256(artifact)):
            raise ValueError('The current audit evidence has not been checked.')
        audit_result = audit_axioms(audit_source, log.read_text(), [MAIN_THEOREM])
    references = set()
    for entry in entries:
        if entry['manuscript'] != claims[entry['id']]:
            raise ValueError(f'Manuscript heading or location changed: {entry["id"]}')
        if entry['status'] not in STATUSES or not entry.get('scope', '').strip():
            raise ValueError(f'Missing scope assessment: {entry["id"]}')
        if entry['status'] != 'unformalized' and not entry.get('lean'):
            raise ValueError(f'Missing Lean evidence: {entry["id"]}')
        for reference in entry.get('lean', []):
            name, filename = reference['name'], reference['file']
            path = Path(filename)
            if path.is_absolute() or '..' in path.parts or not filename.startswith('AllPrimeGroups/'):
                raise ValueError(f'Invalid Lean source reference: {filename}')
            if name not in requested or not (root / path).is_file():
                raise ValueError(f'Unaudited or missing Lean reference: {name}')
            declaration = (r'^\s*(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+' +
                           re.escape(name.rsplit('.', 1)[-1]) + r'(?=[\s{(:])')
            if not re.search(declaration, (root / path).read_text(), re.M):
                raise ValueError(f'Declaration is not in the referenced source: {name}: {filename}')
            if check_artifacts:
                record = checks['files'].get(filename, {})
                artifact = root / '.lake/build/lib/lean' / path.with_suffix('.olean')
                if (name not in audit_result or record.get('exit_code') != 0
                        or record.get('source_sha256') != sha256(root / path)
                        or not artifact.is_file() or record.get('olean_sha256') != sha256(artifact)):
                    raise ValueError(f'Unchecked Lean evidence: {name}')
            references.add(name)
    report = {'claims': len(entries), 'status_counts': dict(Counter(e['status'] for e in entries)),
              'referenced_audit_declarations': len(references),
              'current_build_evidence_checked': check_artifacts, 'assessment': ASSESSMENT,
              'manifest_sha256': sha256(root / 'manuscript-claims.json')}
    return manifest, report


def render(manifest, report, root=ROOT, directory=None):
    directory = directory or manuscript_directory(root)
    rows = []
    for entry in sorted(manifest['claims'], key=lambda e: tuple(map(int, e['id'].split('.')))):
        source = entry['manuscript']
        link = Path(os.path.relpath(directory / source['file'], root)).as_posix()
        lean = '<br>'.join(f'<a href="{html.escape(r["file"], quote=True)}">'
                          f'<code>{html.escape(r["name"])}</code></a>' for r in entry.get('lean', []))
        rows.append('<tr><td><a href="' + html.escape(link, quote=True) + '">' +
                    html.escape(source['kind'] + ' ' + entry['id']) + '</a><br>' +
                    html.escape(source['file']) + ':' + str(source['line']) + '</td><td>' +
                    html.escape(STATUSES[entry['status']]) + '</td><td>' +
                    html.escape(entry['scope']) + '</td><td>' + lean + '</td></tr>')
    counts = ' / '.join(f'{STATUSES[s]}: {report["status_counts"].get(s, 0)}' for s in STATUSES)
    return ('<!doctype html><html lang="en"><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1">'
            '<title>Manuscript and Lean proof correspondence</title><style>'
            'body{font-family:system-ui,sans-serif;line-height:1.7;margin:24px;color:#1f2937}'
            'table{border-collapse:collapse;width:100%;font-size:14px}td,th{border-bottom:1px solid #ddd;'
            'padding:12px;text-align:left;vertical-align:top}code{overflow-wrap:anywhere}'
            '.note{padding:16px;background:#eef5ff}.table{overflow:auto}td:first-child{min-width:190px}'
            'td:nth-child(2){min-width:150px}td:nth-child(3){min-width:300px}</style>'
            '<h1>Manuscript and Lean proof correspondence</h1><p class="note">'
            'The scope classifications are manual mathematical assessments. '
            'The checker verifies the complete claim inventory, source hashes and references '
            'to audited declarations; it does not prove equivalence between paper and Lean statements. '
            'The main existence theorem and the four properties of the specified concrete groups '
            'have been proved and audited.</p><p>' +
            html.escape(f'{report["claims"]} claims. ' + counts) + '</p><div class="table"><table>'
            '<thead><tr><th>Manuscript claim</th><th>Status</th><th>Verified scope and remaining gaps</th>'
            '<th>Audited Lean declarations</th></tr></thead><tbody>' + ''.join(rows) +
            '</tbody></table></div></html>')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-build', action='store_true', help='also verify current local build evidence')
    parser.add_argument('--render', action='store_true', help='write the HTML table and validation report')
    args = parser.parse_args()
    manifest, report = validate(check_artifacts=args.check_build)
    if args.render:
        (ROOT / 'manuscript-correspondence.html').write_text(render(manifest, report), encoding='utf-8')
        (ROOT / 'reports/manuscript-correspondence.json').write_text(
            json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
