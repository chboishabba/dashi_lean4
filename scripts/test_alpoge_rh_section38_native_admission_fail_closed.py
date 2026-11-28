#!/usr/bin/env python3
"""Section38 RH original-admission FAIL-CLOSED regression.

This tests only the pinned-source checker behavior, NOT RH itself.
No external network or Lean compiler is needed; a real original
proof still requires exact pinned source and native elaboration.
"""
import contextlib
import importlib.util
import io
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

CHECKER = Path(__file__).with_name("check_alpoge_rh_original_native_admission.py")

def load():
    spec = importlib.util.spec_from_file_location("rh_source_admission", CHECKER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

class ExactOriginalSourceAdmissionFailClosed(unittest.TestCase):
    def run_checker(self, root, sha="0"*64, commit="0"*40):
        checker=load()
        args=["rh-admission", "--external-root", str(root),
              "--main-sha256", sha, "--expected-git-head",commit,
              "--tree-manifest",str(Path(root)/"sha256.json")]
        with mock.patch.object(sys,"argv",args):
            with contextlib.redirect_stdout(io.StringIO()):
                return checker.main()

    def test_missing_external_directory(self):
        with tempfile.TemporaryDirectory() as t:
            self.assertEqual(self.run_checker(Path(t)/"nonexistent"),2)

    def test_malformed_original_commit_pin(self):
        with tempfile.TemporaryDirectory() as t:
            self.assertEqual(self.run_checker(t,commit="not-a-sha"),2)

    def test_unpinned_or_unborn_git_head(self):
        with tempfile.TemporaryDirectory() as t:
            self.assertEqual(self.run_checker(t),2)

    def test_only_explicit_original_witness_is_required(self):
        source=CHECKER.read_text(encoding="utf8")
        self.assertIn("example : _root_.RiemannHypothesis := _root_.riemannHypothesis",source)
        self.assertIn("#print axioms _root_.riemannHypothesis",source)
        self.assertIn("exactly one original-witness axiom report required",source)

    def test_cannot_override_compiler_version(self):
        module=load()
        self.assertEqual(module.REQUIRED_VERSION,"v4.33.1")
        source=CHECKER.read_text(encoding="utf8")
        self.assertNotIn('add_argument("--lean-version"',source)

if __name__=="__main__":
    unittest.main(verbosity=2)
