"""Run with python3 -m unittest discover -s scripts -p 'test_register_lake_cache.py' -v."""
import os
from pathlib import Path
import stat
import shlex
import subprocess
import sys
import tempfile
import tomllib
import unittest

import tomlkit

SCRIPT = Path(__file__).with_name("register_lake_cache.sh").resolve()
NAME = "matroid-r2-public"
ENDPOINT = "https://pub-8410780127634ed2b09f7b7f09c7f4e5.r2.dev"
SERVICE = {
    "name": NAME,
    "kind": "s3",
    "artifactEndpoint": ENDPOINT + "/artifacts",
    "revisionEndpoint": ENDPOINT + "/revisions",
}
DEFAULTS = (
    'cache.defaultService = "other-service"\n',
    '[cache]\ndefaultService = "other-service"\n',
    '"cache" . "defaultService" = \'other-service\' # keep this comment\n',
    "['cache']\n'defaultService' = '''other-service''' # keep this comment\n",
)
OTHER_SERVICES = '''
[[cache.service]]
name = "other-service"
kind = "s3"
artifactEndpoint = "https://example.org/artifacts"
revisionEndpoint = "https://example.org/revisions"
[[cache.service]]
name = "second-service"
kind = "s3"
artifactEndpoint = "https://example.net/artifacts"
revisionEndpoint = "https://example.net/revisions"
[unrelated]
name = "matroid-r2-public"
message = """[cache]
defaultService = "inside a string"
"""
'''


class RegistrationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.config = self.root / "lake" / "config.toml"
        self.env = dict(os.environ, HOME=str(self.root))
        # Ensure the shell uses the interpreter running this test suite.
        bindir = self.root / "bin"
        bindir.mkdir()
        (bindir / "python3").write_text("#!/bin/sh\nexec " + shlex.quote(sys.executable) + ' "$@"\n')
        (bindir / "python3").chmod(0o755)
        # Keep user-installed dependencies visible with the isolated HOME.
        self.env["PYTHONPATH"] = str(Path(tomlkit.__file__).parent.parent)
        self.env["PATH"] = str(bindir) + os.pathsep + os.environ["PATH"]

    def write(self, text):
        self.config.parent.mkdir(parents=True, exist_ok=True)
        self.config.write_bytes(text.encode())

    def run_script(self, *args, path=None):
        return subprocess.run(
            ["bash", str(SCRIPT), *args, str(path or self.config)],
            env=self.env, capture_output=True, text=True, timeout=15,
        )

    def register(self, *args, path=None):
        result = self.run_script(*args, path=path)
        self.assertEqual(result.returncode, 0, result.stderr)
        return tomllib.loads(self.config.read_text())

    def assert_registered(self, doc):
        services = [s for s in doc["cache"]["service"] if s["name"] == NAME]
        self.assertEqual(services, [SERVICE])

    def test_missing_empty_and_comment_only(self):
        for text in (None, "", "# keep this comment\n"):
            with self.subTest(text=text):
                if text is None:
                    self.config.unlink(missing_ok=True)
                else:
                    self.write(text)
                doc = self.register()
                self.assertEqual(doc["cache"]["defaultService"], NAME)
                self.assert_registered(doc)
                if text:
                    self.assertIn(text, self.config.read_text())

    def test_defaults_multiple_services_and_set_default(self):
        for prefix in DEFAULTS:
            for override in (False, True):
                with self.subTest(prefix=prefix, override=override):
                    source = prefix + OTHER_SERVICES
                    self.write(source)
                    expected = tomllib.loads(source)
                    expected["cache"]["service"].append(SERVICE)
                    if override:
                        expected["cache"]["defaultService"] = NAME
                    actual = self.register(*(["--set-default"] if override else []))
                    self.assertEqual(actual, expected)
                    if "# keep this comment" in source:
                        self.assertIn("# keep this comment", self.config.read_text())
                    before = self.config.read_bytes()
                    inode = self.config.stat().st_ino
                    self.register(*(["--set-default"] if override else []))
                    self.assertEqual(self.config.read_bytes(), before)
                    self.assertEqual(self.config.stat().st_ino, inode)

    def test_no_default_with_existing_cache_table(self):
        for source in ('[cache]\n', OTHER_SERVICES, 'cache.service = []\n'):
            with self.subTest(source=source):
                self.write(source)
                doc = self.register()
                self.assertEqual(doc["cache"]["defaultService"], NAME)
                self.assert_registered(doc)

    def test_existing_service_is_preserved(self):
        source = """[cache]
defaultService = 'other-service'
[[cache.service]]
name='matroid-r2-public' # existing customized service
kind='s3'
artifactEndpoint='https://custom.example/artifacts'
revisionEndpoint='https://custom.example/revisions'
"""
        self.write(source)
        self.assertEqual(self.register(), tomllib.loads(source))
        self.assertEqual(self.config.read_text(), source)
        expected = tomllib.loads(source)
        expected["cache"]["defaultService"] = NAME
        self.assertEqual(self.register("--set-default"), expected)

    def test_inline_tables(self):
        for source in (
            'cache = { defaultService = "other", service = [] }\n',
            'cache.service = [{name="other", kind="s3"}]\n',
        ):
            with self.subTest(source=source):
                self.write(source)
                expected = tomllib.loads(source)
                expected["cache"].setdefault("defaultService", NAME)
                expected["cache"]["service"].append(SERVICE)
                self.assertEqual(self.register(), expected)

    def test_comment_or_unrelated_name_does_not_count_as_service(self):
        self.write('# name = "matroid-r2-public"\n[other]\nname = "matroid-r2-public"\n')
        self.assert_registered(self.register())

    def test_malformed_and_invalid_shapes_leave_original_untouched(self):
        for source in (
            '[cache\n',
            'cache.defaultService="other"\n[cache]\n',
            'cache = 1\n',
            '[cache]\ndefaultService=12\n',
            '[cache]\nservice={}\n',
            '[cache]\nservice=[1]\n',
            '[cache]\nservice=[{kind="s3"}]\n',
            '[cache]\nservice=[{name="same"},{name="same"}]\n',
        ):
            with self.subTest(source=source):
                self.write(source)
                before = self.config.read_bytes()
                inode = self.config.stat().st_ino
                self.assertNotEqual(self.run_script("--set-default").returncode, 0)
                self.assertEqual(self.config.read_bytes(), before)
                self.assertEqual(self.config.stat().st_ino, inode)
                self.assertEqual(list(self.config.parent.glob(".config.toml.*")), [])

    def test_mode_symlink_and_new_file_permissions(self):
        self.register()
        self.assertEqual(stat.S_IMODE(self.config.stat().st_mode), 0o600)
        self.write(DEFAULTS[1])
        self.config.chmod(0o640)
        link = self.root / "linked.toml"
        link.symlink_to(self.config)
        self.assert_registered(self.register(path=link))
        self.assertTrue(link.is_symlink())
        self.assertEqual(stat.S_IMODE(self.config.stat().st_mode), 0o640)

    def test_write_failures_leave_original_and_clean_up(self):
        injection = self.root / "injection"
        injection.mkdir()
        self.env["PYTHONPATH"] = str(injection) + os.pathsep + self.env["PYTHONPATH"]
        for operation in ("fsync", "replace"):
            for existing in (True, False):
                with self.subTest(operation=operation, existing=existing):
                    if existing:
                        self.write(DEFAULTS[1])
                    else:
                        self.config.unlink(missing_ok=True)
                    (injection / "sitecustomize.py").write_text(
                        "import os\n"
                        "def fail(*args, **kwargs):\n"
                        "    raise OSError('injected failure')\n"
                        f"os.{operation} = fail\n"
                    )
                    result = self.run_script()
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("injected failure", result.stderr)
                    self.assertNotIn("Updated", result.stdout)
                    if existing:
                        self.assertEqual(self.config.read_text(), DEFAULTS[1])
                    else:
                        self.assertFalse(self.config.exists())
                    self.assertEqual(list(self.config.parent.glob(".config.toml.*")), [])

    def test_concurrent_registration(self):
        self.write(DEFAULTS[1] + OTHER_SERVICES)
        processes = [subprocess.Popen(
            ["bash", str(SCRIPT), *args, str(self.config)], env=self.env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        ) for args in ([], ["--set-default"], [], [])]
        results = [process.communicate(timeout=15) for process in processes]
        for process, (out, err) in zip(processes, results):
            self.assertEqual(process.returncode, 0, out + err)
        actual = tomllib.loads(self.config.read_text())
        expected = tomllib.loads(DEFAULTS[1] + OTHER_SERVICES)
        expected["cache"]["defaultService"] = NAME
        expected["cache"]["service"].append(SERVICE)
        self.assertEqual(actual, expected)

    def test_invalid_generated_toml_is_not_installed(self):
        self.write(DEFAULTS[1])
        injection = self.root / "injection"
        injection.mkdir()
        (injection / "sitecustomize.py").write_text(
            "import tomlkit\n"
            "tomlkit.dumps = lambda doc: '[cache'\n"
        )
        self.env["PYTHONPATH"] = str(injection) + os.pathsep + self.env["PYTHONPATH"]
        result = self.run_script()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Could not register", result.stderr)
        self.assertEqual(self.config.read_text(), DEFAULTS[1])
        self.assertEqual(list(self.config.parent.glob(".config.toml.*")), [])


if __name__ == "__main__":
    unittest.main()
