"""Reject modified or incomplete publication packages without requiring Lean."""
import json
from pathlib import Path
import shutil
import tempfile
import unittest

from check_publication import ROOT, MANIFEST, verify


class PublicationTests(unittest.TestCase):
    def setUp(self):
        self.folder = tempfile.TemporaryDirectory()
        self.root = Path(self.folder.name) / 'publication'
        shutil.copytree(ROOT, self.root, ignore=shutil.ignore_patterns(
            '.git', '.lake', '__pycache__', '*.pyc'))

    def tearDown(self):
        self.folder.cleanup()

    def resign(self, name):
        from check_publication import digest
        path = self.root / name
        manifest = json.loads((self.root / MANIFEST).read_text())
        manifest['files'][name] = {'bytes': path.stat().st_size, 'sha256': digest(path)}
        (self.root / MANIFEST).write_text(json.dumps(manifest))

    def test_complete_package(self):
        self.assertEqual(verify(self.root)['core_axiom_audits'], 494)

    def test_changed_lean_source(self):
        path = self.root / 'lean/AllPrimeGroups/PrimeGroups.lean'
        path.write_text(path.read_text() + '\n-- changed\n')
        with self.assertRaisesRegex(ValueError, 'content changed'):
            verify(self.root)

    def test_missing_timestamp(self):
        (self.root / 'PDF/all-prime-residually-finite-p-groups.pdf.ots').unlink()
        with self.assertRaisesRegex(ValueError, 'inventory'):
            verify(self.root)

    def test_extra_file(self):
        (self.root / 'unexpected.txt').write_text('extra')
        with self.assertRaisesRegex(ValueError, 'inventory'):
            verify(self.root)

    def test_manifest_update_does_not_hide_changed_source(self):
        name = 'lean/AllPrimeGroups/PrimeGroups.lean'
        path = self.root / name
        path.write_text(path.read_text() + '\n-- changed\n')
        self.resign(name)
        with self.assertRaisesRegex(ValueError, 'compilation record'):
            verify(self.root)

    def test_changed_proposal_statement(self):
        name = 'FClikelean/AllPrimeGroups.lean'
        path = self.root / name
        original = path.read_text()
        for theorem in ['finitely_presented_burnside_problem',
                        'finitely_presented_burnside_problem_residually_finite',
                        'finitely_presented_burnside_problem_all_primes']:
            with self.subTest(theorem=theorem):
                before, marker, after = original.partition(f'theorem {theorem} :')
                path.write_text(before + marker + after.replace('Infinite G', 'Finite G', 1))
                self.resign(name)
                with self.assertRaisesRegex(ValueError, 'proposal statement differs.*' + theorem):
                    verify(self.root)

    def test_variant_requires_its_own_metadata(self):
        name = 'FClikelean/AllPrimeGroups.lean'
        path = self.root / name
        source = path.read_text()
        for theorem in ['finitely_presented_burnside_problem_residually_finite',
                        'finitely_presented_burnside_problem_all_primes']:
            with self.subTest(theorem=theorem):
                end = source.index('theorem ' + theorem)
                position = source.rindex('@[category research solved', 0, end)
                path.write_text(source[:position] + source[end:])
                self.resign(name)
                with self.assertRaisesRegex(ValueError, 'proposal metadata'):
                    verify(self.root)

    def test_broken_link_even_if_manifest_updated(self):
        name = 'README.md'
        path = self.root / name
        path.write_text(path.read_text() + '\n[bad](missing-file.md)\n')
        self.resign(name)
        with self.assertRaisesRegex(ValueError, 'Broken local link'):
            verify(self.root)

    def test_incomplete_baseline_even_if_manifest_updated(self):
        name = 'verification/baseline-full-build.json'
        path = self.root / name
        state = json.loads(path.read_text())
        state['main_checked'] = False
        path.write_text(json.dumps(state))
        self.resign(name)
        with self.assertRaisesRegex(ValueError, 'baseline full-build result'):
            verify(self.root)

    @unittest.skipUnless((ROOT / 'verification/private-ci-verification.json').exists(),
                         'No private CI archive in this package')
    def test_wrong_ci_commit_even_if_manifest_updated(self):
        name = 'verification/private-ci-verification.json'
        path = self.root / name
        record = json.loads(path.read_text())
        record['tested_commit'] = '0' * 40
        path.write_text(json.dumps(record))
        self.resign(name)
        with self.assertRaisesRegex(ValueError, 'CI tested commit differs'):
            verify(self.root)

    @unittest.skipUnless((ROOT / 'verification/private-ci-verification.json').exists(),
                         'No private CI archive in this package')
    def test_changed_ci_zip_even_if_manifest_updated(self):
        record = json.loads((self.root / 'verification/private-ci-verification.json').read_text())
        provenance = json.loads((self.root / record['archive'] / 'provenance.json').read_text())
        name = record['archive'] + '/' + provenance['artifacts'][0]['file']
        path = self.root / name
        path.write_bytes(path.read_bytes() + b'changed')
        self.resign(name)
        with self.assertRaisesRegex(ValueError, 'Original CI artifact ZIP differs'):
            verify(self.root)


if __name__ == '__main__':
    unittest.main()
