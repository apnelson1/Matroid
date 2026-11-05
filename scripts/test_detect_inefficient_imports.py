"""Run with: uv run python -m unittest discover -s scripts -p 'test_detect_inefficient_imports.py' -v"""
import contextlib
import io
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import detect_inefficient_imports as detector


REPO = Path(__file__).resolve().parents[1]
LEAN_SOURCES = {
    'DetectorLeaf': '''module

namespace ImportDetector

public def PublicType := Nat
public def runtimeValue : Nat := 7
def hiddenValue : Nat := 11
''',
    'DetectorHidden': '''module

namespace ImportDetector

public def secretValue : Nat := 13
''',
    'DetectorWrapper': 'module\n\npublic import DetectorLeaf\nimport DetectorHidden\n',
    'DetectorAllWrapper': 'module\n\nimport all DetectorLeaf\n',
    'DetectorMetaWrapper': 'module\n\npublic meta import DetectorLeaf\n',
}


def source_import(command, module=True):
    return next(detector.header_imports(["module\n", command] if module else [command]))[1]


class LeanFixtureTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='import-detector-', dir=REPO / 'scripts')
        self.addCleanup(temporary.cleanup)
        self.fixtures = Path(temporary.name)
        for name, source in LEAN_SOURCES.items():
            (self.fixtures / f'{name}.lean').write_text(source, encoding='utf-8')


class DetectorTests(LeanFixtureTests):
    def test_header_scanning(self):
        lines = (
            "/- license\n/- nested -/\n-/\nmodule -- header\nprelude\n"
            "public /- inline -/ meta import Mathlib.A\n"
            "import all Mathlib.B /- trailing\nimport Fake.Comment\n-/\n"
            "def x := 0\nimport Fake.Body\n"
        ).splitlines(keepends=True)
        imports = list(detector.header_imports(lines))
        self.assertEqual([(i, m['name'], depth, module) for i, m, depth, module in imports],
                         [(5, 'Mathlib.A', 0, True), (6, 'Mathlib.B', 1, True)])
        for unsupported in ('import Mathlib.Bad!', 'public meta\n', 'import Mathlib.A extra'):
            self.assertEqual(list(detector.header_imports([unsupported, 'import Mathlib.B'])), [])

    def test_actual_project_headers(self):
        self.assertEqual(len(detector.get_imports(REPO / 'Matroid/Graph/Basic.lean')), 6)
        self.assertEqual(len(detector.get_imports(REPO / 'Matroid/ForMathlib/Tactic/ENatToNat.lean')), 3)

    def test_modifier_composition(self):
        for public in ('', 'public '):
            for meta in ('', 'meta '):
                for all_ in ('', 'all '):
                    if public and all_:
                        continue  # Lean requires separate public and all import commands.
                    with self.subTest(public=public, meta=meta, all=all_):
                        match = source_import(f'{public}{meta}import {all_}Mathlib.Wrapper')
                        replacements = detector.get_transitive_imports(
                            self.fixtures / 'DetectorWrapper.lean', match, True)
                        expected = [f'{public}{meta}import DetectorLeaf']
                        if all_:
                            expected.append(f'{meta}import DetectorHidden')
                        self.assertEqual(replacements, expected)
                        self.assertEqual(detector.get_transitive_imports(
                            self.fixtures / 'DetectorAllWrapper.lean', match, True),
                            [f'{meta}import all DetectorLeaf'] if all_ else [])
        legacy = source_import('import Mathlib.Wrapper', module=False)
        self.assertEqual(detector.get_transitive_imports(
            self.fixtures / 'DetectorWrapper.lean', legacy, False),
            ['import DetectorLeaf', 'import DetectorHidden'])

    def test_dependency_meta_and_legacy_visibility(self):
        with tempfile.TemporaryDirectory(dir=self.fixtures) as directory:
            dependency = Path(directory) / 'Dependency.lean'
            match = source_import('public import Mathlib.Wrapper')
            dependency.write_text('module\npublic meta import Mathlib.Child\n')
            self.assertEqual(detector.get_transitive_imports(dependency, match, True),
                             ['public meta import Mathlib.Child'])
            dependency.write_text('import Mathlib.Child\n')
            self.assertEqual(detector.get_transitive_imports(dependency, match, True),
                             ['public import Mathlib.Child'])

    def test_rewrite_and_restoration(self):
        with tempfile.TemporaryDirectory(dir=self.fixtures) as directory:
            target = Path(directory) / 'Target.lean'
            original = b'module\r\n  public meta import Mathlib.Wrapper -- keep  \r\n'
            candidate = original.replace(b'public meta import Mathlib.Wrapper',
                                         b'public meta import DetectorLeaf')
            for outcome in (False, True, KeyboardInterrupt()):
                target.write_bytes(original)

                def compile_check(path):
                    self.assertEqual(path.read_bytes(), candidate)
                    if isinstance(outcome, BaseException):
                        raise outcome
                    return outcome

                with patch.object(detector, 'resolve_mathlib_import',
                                  return_value=self.fixtures / 'DetectorWrapper.lean'), \
                        patch.object(detector, 'check_compilation', side_effect=compile_check), \
                        contextlib.redirect_stdout(io.StringIO()):
                    if isinstance(outcome, BaseException):
                        with self.assertRaises(KeyboardInterrupt):
                            detector.process_file(target)
                    else:
                        detector.process_file(target)
                        if outcome:
                            detector.process_file(target)  # Already marked: no second compilation.
                expected = original[:-2] + b' -- inefficient import\r\n' if outcome is True else original
                self.assertEqual(target.read_bytes(), expected)

    def test_open_comment_is_not_rewritten(self):
        with tempfile.TemporaryDirectory(dir=self.fixtures) as directory:
            target = Path(directory) / 'Target.lean'
            original = b'module\nimport Mathlib.Wrapper /- note\n-/\n'
            target.write_bytes(original)
            with patch.object(detector, 'check_compilation') as compiler, \
                    contextlib.redirect_stdout(io.StringIO()):
                detector.process_file(target)
            compiler.assert_not_called()
            self.assertEqual(target.read_bytes(), original)


class LeanImportTests(LeanFixtureTests):
    def test_original_and_replacement_have_same_access(self):
        # Keep generated Lean inputs in the workspace; put compiled artifacts outside it.
        with tempfile.TemporaryDirectory() as cache:
            environment = dict(os.environ)
            environment['LEAN_PATH'] = cache + os.pathsep + environment.get('LEAN_PATH', '')

            def lean(path, output=None):
                args = ['lake', 'env', 'lean', '-R', str(self.fixtures)]
                if output:
                    args += ['-o', str(output)]
                return subprocess.run(args + [str(path)], cwd=REPO, env=environment,
                                      capture_output=True, text=True)

            for name in LEAN_SOURCES:
                result = lean(self.fixtures / f'{name}.lean', Path(cache) / f'{name}.olean')
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

            cases = [
                ('import', 'DetectorWrapper', '#check ImportDetector.PublicType', True),
                ('import', 'DetectorWrapper', '#check ImportDetector.secretValue', False),
                ('import', 'DetectorWrapper', 'public def exposed (x : ImportDetector.PublicType) := x', False),
                ('public import', 'DetectorWrapper', 'public def exposed (x : ImportDetector.PublicType) := x', True),
                ('meta import', 'DetectorWrapper', '#eval ImportDetector.runtimeValue', True),
                ('import', 'DetectorWrapper', '#eval ImportDetector.runtimeValue', False),
                ('import', 'DetectorMetaWrapper', '#eval ImportDetector.runtimeValue', True),
                ('import all', 'DetectorWrapper', '#check ImportDetector.secretValue', True),
                ('import', 'DetectorAllWrapper', '#check ImportDetector.hiddenValue', False),
                ('import all', 'DetectorAllWrapper', '#check ImportDetector.hiddenValue', True),
            ]
            target = self.fixtures / 'Check.lean'
            for command, dependency, body, success in cases:
                with self.subTest(command=command, dependency=dependency, body=body):
                    original = f'{command} {dependency}'
                    replacements = detector.get_transitive_imports(
                        self.fixtures / f'{dependency}.lean', source_import(original), True)
                    for imports in (original, '\n'.join(replacements)):
                        target.write_text(f'module\n{imports}\n{body}\n')
                        result = lean(target)
                        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
