"""Offline regressions for kernel-environment Lean declaration extractor."""
import importlib.util
import pathlib
import tempfile
import unittest
from unittest.mock import patch

FILE = pathlib.Path(__file__).with_name("extract_jmd_lean_declarations.py")
spec = importlib.util.spec_from_file_location("jmd_lean_extract", FILE)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

SHA = "a"*40


class _Run:
    def __init__(self, output, code=0):
        self.stdout=output
        self.stderr=""
        self.returncode=code


class LeanExtractTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root=pathlib.Path(self.tmp.name)
        (self.root/".git").mkdir()
        self.row={"repository_id":7,"repository":"owner/repo","commit":SHA,
                  "module":"Test.Basic","declaration":"Test.Basic.foo"}

    def test_checked_type_and_axiom_diagnostics(self):
        with patch.object(m,"git",side_effect=[SHA,"git@github.com:owner/repo.git"]), \
             patch.object(m.shutil,"which",return_value="/usr/bin/lake"), \
             patch.object(m.subprocess,"run",side_effect=[
                 _Run("Test.Basic.foo : Nat → Nat\n"),
                 _Run("'Test.Basic.foo' does not depend on any axioms\n")]):
            result=m.extract(self.root,[self.row])
        self.assertEqual(len(result),1)
        self.assertEqual(result[0]["type"],"Nat → Nat")
        self.assertTrue(result[0]["source_revision_verified"])
        self.assertFalse(result[0]["kernel_proof_transport"])

    def test_revision_mismatch_rejected(self):
        row={**self.row,"commit":"b"*40}
        with patch.object(m,"git",side_effect=[SHA,"git@github.com:owner/repo.git"]), \
             patch.object(m.shutil,"which",return_value="/usr/bin/lake"):
            with self.assertRaisesRegex(ValueError,"disagrees"):
                m.extract(self.root,[row])

    def test_failed_lean_check_rejected(self):
        with patch.object(m,"git",side_effect=[SHA,"git@github.com:owner/repo.git"]), \
             patch.object(m.shutil,"which",return_value="/usr/bin/lake"), \
             patch.object(m.subprocess,"run",return_value=_Run("unknown constant",1)):
            with self.assertRaisesRegex(ValueError,"Lean rejected"):
                m.extract(self.root,[self.row])

    def test_untrusted_name_rejected(self):
        row={**self.row,"declaration":"Test.Basic.foo\n#eval IO.println \"bad\""}
        with patch.object(m,"git",side_effect=[SHA,"git@github.com:owner/repo.git"]), \
             patch.object(m.shutil,"which",return_value="/usr/bin/lake"):
            with self.assertRaisesRegex(ValueError,"Invalid Lean"):
                m.extract(self.root,[row])


if __name__ == "__main__":
    unittest.main()
