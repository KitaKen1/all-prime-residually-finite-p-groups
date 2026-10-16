#!/usr/bin/env python3
"""Verify a source bundle's inventory and SHA-256 hashes without Lean or extraction.

This is source-integrity verification, not a new compilation or proof check.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import stat
import zipfile

PREFIX = 'all-prime-groups/'
MANIFEST = PREFIX + 'bundle-manifest.json'
REQUIRED = {'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
            'AllPrimeGroups.lean', 'Audit.lean', 'UpstreamAudit.lean',
            'AllPrimeGroups/PrimeCharacterExtensions.lean', 'AllPrimeGroups/PrimeGroups.lean',
            'scripts/reproduce.py', 'scripts/verify.py', 'scripts/axiom_audit.py',
            'scripts/verify_bundle.py', 'scripts/manuscript_correspondence.py',
            'manuscript-claims.json', 'upstream/provenance.json',
            'upstream/OpenAI-LICENSE', 'upstream/TauCeti-LICENSE', 'upstream/LeanPool-LICENSE'}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def safe_name(name):
    path = PurePosixPath(name)
    return (bool(name) and not path.is_absolute() and '..' not in path.parts
            and path.as_posix() == name and '\\' not in name)


def verify_bundle(path, expected_sha256=None):
    archive_hash = digest(path.read_bytes())
    if expected_sha256 is not None and archive_hash != expected_sha256:
        raise ValueError('The archive SHA-256 differs from the expected value.')
    with zipfile.ZipFile(path) as archive:
        entries = archive.infolist()
        names = [entry.filename for entry in entries]
        if len(names) != len(set(names)):
            raise ValueError('Duplicate archive entries.')
        if len(entries) > 2000 or sum(e.file_size for e in entries) > 128 * 1024 * 1024:
            raise ValueError('Archive exceeds the source-bundle size limit.')
        for entry in entries:
            if (not safe_name(entry.filename) or not entry.filename.startswith(PREFIX)
                    or entry.is_dir() or stat.S_ISLNK(entry.external_attr >> 16)):
                raise ValueError(f'Invalid archive entry: {entry.filename}')
        manifest = json.loads(archive.read(MANIFEST))
        if manifest.get('schema_version') != 1:
            raise ValueError('Unknown bundle manifest schema.')
        records = manifest['files']
        if not all(safe_name(name) for name in records):
            raise ValueError('Invalid manifest path.')
        if set(names) != {MANIFEST, *(PREFIX + name for name in records)}:
            raise ValueError('Archive inventory differs from its manifest.')
        if not REQUIRED <= set(records):
            raise ValueError('Required proof sources, configuration or licenses are missing.')
        for name, record in records.items():
            data = archive.read(PREFIX + name)
            if len(data) != record['bytes'] or digest(data) != record['sha256']:
                raise ValueError(f'Content differs from its manifest: {name}')
            if '.lake' in PurePosixPath(name).parts or name.endswith(('.olean', '.ilean', '.pyc')):
                raise ValueError(f'Build artifact found in source bundle: {name}')
        lean = {name for name in records if name.endswith('.lean')}
        local = {name for name in lean if name.startswith('AllPrimeGroups/')}
        upstream = {name for name in lean if name.startswith('OAI/')}
        if set(lean) != local | upstream | {'AllPrimeGroups.lean', 'Audit.lean', 'UpstreamAudit.lean'}:
            raise ValueError('Unexpected Lean source inventory.')
        counts = {'local_modules': len(local), 'upstream_modules': len(upstream), 'lean_sources': len(lean)}
        if manifest['source_counts'] != counts:
            raise ValueError('Source counts differ from the manifest.')
        provenance = json.loads(archive.read(PREFIX + 'upstream/provenance.json'))
        if {item['path'] for item in provenance['files']} != upstream:
            raise ValueError('Upstream inventory differs from its provenance manifest.')
        for item in provenance['files']:
            if records[item['path']]['sha256'] != item['sha256']:
                raise ValueError(f'Upstream source differs from its pin: {item["path"]}')
        toolchain = archive.read(PREFIX + 'lean-toolchain').decode().strip()
        locked = json.loads(archive.read(PREFIX + 'lake-manifest.json'))
        revisions = {item['name']: item['rev'] for item in locked['packages']}
        if manifest['toolchain'] != toolchain or manifest['package_revisions'] != revisions:
            raise ValueError('Dependency pins differ from the manifest.')
    return {'archive_sha256': archive_hash, 'files': len(records), **counts,
            'verification_scope': 'Archive inventory and source hashes; no new Lean proof check.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('archive', type=Path)
    parser.add_argument('--sha256', help='expected archive SHA-256 from the producer')
    args = parser.parse_args()
    print(json.dumps(verify_bundle(args.archive, args.sha256), indent=2))


if __name__ == '__main__':
    main()
