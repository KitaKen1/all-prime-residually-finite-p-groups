#!/usr/bin/env python3
"""Create a reproducible, portable Lean source archive after checking producer evidence."""
import json
from pathlib import Path
import subprocess
import sys
import zipfile

from manuscript_correspondence import ROOT, MANUSCRIPTS, manuscript_directory, render, validate
from verify_bundle import PREFIX, MANIFEST, digest, verify_bundle


def bundle_payload(root=ROOT):
    selected = [*sorted((root / 'AllPrimeGroups').glob('*.lean')),
                *sorted((root / 'OAI').rglob('*.lean')),
                *sorted((root / 'scripts').glob('*.py')),
                *sorted(p for p in (root / 'upstream').iterdir() if p.is_file())]
    selected += [root / name for name in [
        '.gitignore', 'AllPrimeGroups.lean', 'Audit.lean', 'UpstreamAudit.lean',
        'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'README.md',
        'manuscript-correspondence.html', 'manuscript-claims.json',
        'reports/local-checks.json', 'reports/local-axioms.json', 'reports/Audit.log',
        'reports/upstream-axioms.log', 'reports/source-integrity.json']]
    payload = {}
    for path in selected:
        if path.is_symlink() or not path.is_file():
            raise ValueError(f'Expected a regular source or evidence file: {path}')
        payload[path.relative_to(root).as_posix()] = path.read_bytes()
    directory = manuscript_directory(root)
    for name in MANUSCRIPTS:
        payload['manuscript/' + name] = (directory / name).read_bytes()
    return payload


def write_archive(payload, destination):
    lean = [name for name in payload if name.endswith('.lean')]
    locked = json.loads(payload['lake-manifest.json'])
    manifest = {'schema_version': 1, 'toolchain': payload['lean-toolchain'].decode().strip(),
                'package_revisions': {p['name']: p['rev'] for p in locked['packages']},
                'source_counts': {'local_modules': sum(n.startswith('AllPrimeGroups/') for n in lean),
                                  'upstream_modules': sum(n.startswith('OAI/') for n in lean),
                                  'lean_sources': len(lean)},
                'verification_scope': ('Producer compilation records and axiom audit are included. '
                    'This source archive contains no oleans or package caches. '
                    'Archive verification is not a new Lean build or independent-host reproduction.'),
                'files': {name: {'bytes': len(data), 'sha256': digest(data)}
                          for name, data in sorted(payload.items())}}
    contents = {PREFIX + name: data for name, data in payload.items()}
    contents[MANIFEST] = (json.dumps(manifest, ensure_ascii=False, indent=2) + '\n').encode()
    temporary = destination.with_suffix('.tmp')
    with zipfile.ZipFile(temporary, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name, data in sorted(contents.items()):
            info = zipfile.ZipInfo(name, (1980, 1, 1, 0, 0, 0))
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            archive.writestr(info, data, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    result = verify_bundle(temporary)
    temporary.replace(destination)
    return result


def main():
    subprocess.run([sys.executable, str(ROOT / 'scripts/verify.py'), '--audit-only'],
                   cwd=ROOT, check=True)
    claims, correspondence = validate(check_artifacts=True)
    payload = bundle_payload()
    payload['manuscript-correspondence.html'] = render(
        claims, correspondence, directory=ROOT / 'manuscript').encode()
    payload['reports/manuscript-correspondence.json'] = (
        json.dumps(correspondence, indent=2) + '\n').encode()
    identity = digest(json.dumps({name: digest(data) for name, data in sorted(payload.items())},
                                 sort_keys=True).encode())[:16]
    folder = ROOT / 'dist'
    folder.mkdir(exist_ok=True)
    destination = folder / f'all-prime-groups-lean-{identity}.zip'
    result = write_archive(payload, destination)
    destination.with_suffix('.zip.sha256').write_text(
        result['archive_sha256'] + '  ' + destination.name + '\n')
    summary = {'archive': destination.relative_to(ROOT).as_posix(), **result}
    (ROOT / 'reports/source-bundle.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
