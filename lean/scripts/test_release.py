"""Regression checks for misleading correspondence evidence and corrupted source bundles."""
from copy import deepcopy
import json
from pathlib import Path
import shutil
import stat
import tempfile
import unittest
import warnings
import zipfile

from make_bundle import bundle_payload, write_archive
from manuscript_correspondence import ROOT, MANUSCRIPTS, manuscript_directory, validate
from verify_bundle import MANIFEST, PREFIX, digest, verify_bundle


class BundleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.folder = tempfile.TemporaryDirectory()
        cls.root = Path(cls.folder.name)
        cls.payload = bundle_payload()
        cls.good = cls.root / 'good.zip'
        write_archive(cls.payload, cls.good)
        with zipfile.ZipFile(cls.good) as archive:
            cls.contents = {name: archive.read(name) for name in archive.namelist()}

    @classmethod
    def tearDownClass(cls):
        cls.folder.cleanup()

    def mutated(self, mutate, symlink=None, duplicate=None):
        contents = deepcopy(self.contents)
        mutate(contents)
        path = self.root / 'mutated.zip'
        with zipfile.ZipFile(path, 'w') as archive:
            for name, data in contents.items():
                info = zipfile.ZipInfo(name)
                if name == symlink:
                    info.create_system = 3
                    info.external_attr = (stat.S_IFLNK | 0o777) << 16
                archive.writestr(info, data)
            if duplicate:
                with warnings.catch_warnings():
                    warnings.simplefilter('ignore', UserWarning)
                    archive.writestr(duplicate, contents[duplicate])
        return path

    def test_valid_and_deterministic(self):
        result = verify_bundle(self.good)
        self.assertEqual(result['local_modules'], 134)
        self.assertEqual(result['upstream_modules'], 63)
        other = self.root / 'again.zip'
        write_archive(self.payload, other)
        self.assertEqual(self.good.read_bytes(), other.read_bytes())

    def test_changed_lean_source(self):
        path = self.mutated(lambda c: c.update({PREFIX + 'AllPrimeGroups/PrimeGroups.lean': b'changed'}))
        with self.assertRaisesRegex(ValueError, 'Content differs'):
            verify_bundle(path)

    def test_extra_file(self):
        path = self.mutated(lambda c: c.update({PREFIX + 'unlisted.txt': b'extra'}))
        with self.assertRaisesRegex(ValueError, 'inventory'):
            verify_bundle(path)

    def test_duplicate_entry(self):
        path = self.mutated(lambda c: None, duplicate=PREFIX + 'Audit.lean')
        with self.assertRaisesRegex(ValueError, 'Duplicate'):
            verify_bundle(path)

    def test_path_escape(self):
        path = self.mutated(lambda c: c.update({PREFIX + '../escape.txt': b'escape'}))
        with self.assertRaisesRegex(ValueError, 'Invalid archive entry'):
            verify_bundle(path)

    def test_symlink_entry(self):
        path = self.mutated(lambda c: None, symlink=PREFIX + 'Audit.lean')
        with self.assertRaisesRegex(ValueError, 'Invalid archive entry'):
            verify_bundle(path)

    def test_upstream_pin_even_if_file_hash_is_updated(self):
        def mutate(contents):
            manifest = json.loads(contents[MANIFEST])
            filename = next(name for name in manifest['files'] if name.startswith('OAI/'))
            data = contents[PREFIX + filename] + b'\n-- changed upstream\n'
            contents[PREFIX + filename] = data
            manifest['files'][filename] = {'bytes': len(data), 'sha256': digest(data)}
            contents[MANIFEST] = json.dumps(manifest).encode()
        path = self.mutated(mutate)
        with self.assertRaisesRegex(ValueError, 'differs from its pin'):
            verify_bundle(path)

    def test_missing_license_even_if_inventory_is_updated(self):
        def mutate(contents):
            name = 'upstream/OpenAI-LICENSE'
            contents.pop(PREFIX + name)
            manifest = json.loads(contents[MANIFEST])
            manifest['files'].pop(name)
            contents[MANIFEST] = json.dumps(manifest).encode()
        path = self.mutated(mutate)
        with self.assertRaisesRegex(ValueError, 'licenses are missing'):
            verify_bundle(path)

    def test_wrong_archive_hash(self):
        with self.assertRaisesRegex(ValueError, 'expected value'):
            verify_bundle(self.good, '0' * 64)


class CorrespondenceTests(unittest.TestCase):
    def setUp(self):
        self.folder = tempfile.TemporaryDirectory()
        self.root = Path(self.folder.name)
        (self.root / 'manuscript').mkdir()
        for name in MANUSCRIPTS:
            shutil.copyfile(manuscript_directory(ROOT) / name, self.root / 'manuscript' / name)
        (self.root / 'AllPrimeGroups').symlink_to(ROOT / 'AllPrimeGroups', target_is_directory=True)
        (self.root / 'Audit.lean').symlink_to(ROOT / 'Audit.lean')
        self.path = self.root / 'manuscript-claims.json'
        self.manifest = json.loads((ROOT / self.path.name).read_text())

    def tearDown(self):
        self.folder.cleanup()

    def write(self):
        self.path.write_text(json.dumps(self.manifest))

    def test_valid_inventory_does_not_claim_a_new_build(self):
        self.write()
        _, report = validate(self.root)
        self.assertEqual(report['claims'], 41)
        self.assertFalse(report['current_build_evidence_checked'])

    def test_omitted_claim(self):
        self.manifest['claims'].pop()
        self.write()
        with self.assertRaisesRegex(ValueError, 'every manuscript claim'):
            validate(self.root)

    def test_duplicate_claim(self):
        self.manifest['claims'].append(deepcopy(self.manifest['claims'][0]))
        self.write()
        with self.assertRaisesRegex(ValueError, 'every manuscript claim'):
            validate(self.root)

    def test_unaudited_reference(self):
        self.manifest['claims'][0]['lean'][0]['name'] = 'AllPrimeGroups.missing_theorem'
        self.write()
        with self.assertRaisesRegex(ValueError, 'Unaudited'):
            validate(self.root)

    def test_wrong_reference_source(self):
        self.manifest['claims'][0]['lean'][0]['file'] = 'AllPrimeGroups/Target.lean'
        self.write()
        with self.assertRaisesRegex(ValueError, 'not in the referenced source'):
            validate(self.root)

    def test_changed_manuscript(self):
        self.write()
        path = self.root / 'manuscript' / MANUSCRIPTS[0]
        path.write_text(path.read_text() + '\n# changed\n')
        with self.assertRaisesRegex(ValueError, 'Manuscript sources changed'):
            validate(self.root)


if __name__ == '__main__':
    unittest.main()
