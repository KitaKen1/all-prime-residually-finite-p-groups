"""Regression checks for false-positive audit and reproduction cache results."""
from pathlib import Path
import tempfile
import unittest

from axiom_audit import MAIN_THEOREM, audit_axioms
from reproduce import build_order, cache_matches, imports, sha256, within


class AxiomAuditTests(unittest.TestCase):
    source = f'#print axioms A\n#print axioms {MAIN_THEOREM}\n'
    output = ("'A' does not depend on any axioms\n"
              f"'{MAIN_THEOREM}' depends on axioms: [propext, Classical.choice, Quot.sound]\n")

    def test_complete_audit(self):
        self.assertEqual(len(audit_axioms(self.source, self.output, [MAIN_THEOREM])), 2)

    def test_same_count_wrong_declaration(self):
        with self.assertRaises(ValueError):
            audit_axioms(self.source, self.output.replace("'A'", "'B'"))

    def test_duplicate_result(self):
        with self.assertRaises(ValueError):
            audit_axioms(self.source, self.output + "'A' does not depend on any axioms\n")

    def test_proof_hole(self):
        with self.assertRaises(ValueError):
            audit_axioms(self.source, self.output.replace('propext', 'sorryAx'))

    def test_missing_main(self):
        with self.assertRaises(ValueError):
            audit_axioms('#print axioms A\n', "'A' does not depend on any axioms", [MAIN_THEOREM])


class ReproductionTests(unittest.TestCase):
    def test_cache_rejects_changed_artifact_log_source_or_dependency(self):
        with tempfile.TemporaryDirectory() as folder:
            paths = [Path(folder) / name for name in ['A.lean', 'A.olean', 'A.log']]
            for path in paths:
                path.write_text(path.name)
            source, artifact, log = paths
            dependencies = {'/isolated/B.olean': 'original-hash'}
            record = {'exit_code': 0, 'source_sha256': sha256(source),
                      'olean_sha256': sha256(artifact), 'log_sha256': sha256(log),
                      'dependencies': dependencies}
            self.assertTrue(cache_matches(record, *paths, dependencies))
            for path in paths:
                old = path.read_bytes()
                path.write_text('changed')
                self.assertFalse(cache_matches(record, *paths, dependencies))
                path.write_bytes(old)
            self.assertFalse(cache_matches(record, *paths, {'/isolated/B.olean': 'changed-hash'}))
            artifact.unlink()
            self.assertFalse(cache_matches(record, *paths, dependencies))

    def test_isolation_rejects_old_project_and_symlink_escape(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            out, old = base / 'isolated', base / 'old'
            out.mkdir()
            old.mkdir()
            (old / 'A.olean').touch()
            (out / 'A.olean').symlink_to(old / 'A.olean')
            self.assertFalse(within((out / 'A.olean').resolve(), [out.resolve()]))

    def test_import_graph_and_cycle(self):
        with tempfile.TemporaryDirectory() as folder:
            sources = {name: Path(folder) / (name + '.lean')
                       for name in ['AllPrimeGroups.A', 'AllPrimeGroups.B']}
            sources['AllPrimeGroups.A'].write_text(
                '/- import Ignored /- nested -/ -/\nimport AllPrimeGroups.B Mathlib.Data.Nat.Basic -- hi\n')
            sources['AllPrimeGroups.B'].write_text('theorem b : True := .intro\n')
            self.assertEqual(imports(sources['AllPrimeGroups.A']),
                             ['AllPrimeGroups.B', 'Mathlib.Data.Nat.Basic'])
            self.assertEqual(build_order(sources, ['AllPrimeGroups.A']),
                             ['AllPrimeGroups.B', 'AllPrimeGroups.A'])
            sources['AllPrimeGroups.B'].write_text('import AllPrimeGroups.A\n')
            with self.assertRaises(ValueError):
                build_order(sources, ['AllPrimeGroups.A'])
            sources['AllPrimeGroups.B'].write_text('import AllPrimeGroups.Missing\n')
            with self.assertRaises(ValueError):
                build_order(sources, ['AllPrimeGroups.A'])


if __name__ == '__main__':
    unittest.main()
