"""Offline tests: candidate headers do not become AST until Lean accepts."""
import importlib.util
import json
import pathlib
import subprocess
import tempfile
import unittest
from unittest.mock import patch

SCRIPT=pathlib.Path(__file__).with_name("jmd_lean_ast_batch_capture.py")
spec=importlib.util.spec_from_file_location("jmd_batch_capture",SCRIPT)
tool=importlib.util.module_from_spec(spec)
spec.loader.exec_module(tool)

SHA="b"*40


def git(root,*argv):
    return subprocess.run(["git",*argv],cwd=root,capture_output=True,
                          text=True,check=True).stdout.strip()


class BatchTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root=pathlib.Path(self.tmp.name)
        self.repo=self.root/"repo"
        self.repo.mkdir()
        git(self.repo,"init")
        git(self.repo,"config","user.email","fixture@example.invalid")
        git(self.repo,"config","user.name","Fixture")
        git(self.repo,"remote","add","origin","https://github.com/owner/repo.git")
        (self.repo/"Pkg").mkdir()
        self.source=self.repo/"Pkg"/"Basic.lean"
        self.source.write_text("namespace Pkg\ntheorem foo : True := by trivial\n"
                               "theorem bar : True := by trivial\nend Pkg\n")
        git(self.repo,"add",".")
        git(self.repo,"commit","-m","fixture")
        self.sha=git(self.repo,"rev-parse","HEAD")

    def test_nested_namespace_and_section(self):
        source="namespace A\nsection Test\ntheorem p : True := by trivial\nend Test\nend A\n"
        self.assertEqual(tool.source_candidates(source,module="A"),["A.p"])

    def test_source_candidates_are_not_proofs(self):
        fake="-- theorem notReal : False\nnamespace Pkg\ntheorem real : True := by trivial\nend Pkg"
        self.assertEqual(tool.source_candidates(fake,module="Pkg"),["Pkg.real"])

    def test_pinned_origin_mismatch_rejected(self):
        with patch.object(tool.shutil,"which",return_value="/usr/bin/lake"):
            with self.assertRaisesRegex(ValueError,"Origin differs"):
                tool.check_source(self.repo,expected_repo="wrong/repo",revision=self.sha)

    def test_dirty_source_rejected(self):
        self.source.write_text("modified\n")
        with patch.object(tool.shutil,"which",return_value="/usr/bin/lake"):
            with self.assertRaisesRegex(ValueError,"Dirty tracked"):
                tool.check_source(self.repo,expected_repo="owner/repo",revision=self.sha)

    def test_mock_native_export_remains_observation(self):
        rows=[
            {"meta":{"format":{"version":"3.1.0"},"lean":{"githash":SHA},
                     "exporter":{"version":"3.1.0"}}},
            {"in":1,"str":{"pre":0,"str":"Pkg"}},
            {"in":2,"str":{"pre":1,"str":"foo"}},
            {"ie":0,"sort":0},
            {"thm":{"name":2,"type":0,"value":0}},
        ]
        payload=("".join(json.dumps(r)+"\n" for r in rows)).encode()
        observations=[
            (0,b"Pkg.foo : True\n",b""),
            (0,payload,b""),
            (1,b"",b"rejected"),
        ]
        with patch.object(tool.shutil,"which",return_value="/usr/bin/lake"), \
             patch.object(tool,"run_checked",side_effect=observations):
            result=tool.capture(self.repo,github_id=7,repo="owner/repo",
               commit=self.sha,module="Pkg.Basic",source=pathlib.Path("Pkg/Basic.lean"),
               out=self.root/"out",limit=2)
        self.assertEqual(result["native_ast_exports"],1)
        self.assertEqual(result["attempted"],2)
        self.assertEqual(result["proofs_certified"],0)
        manifest=(self.root/"out"/"exports.jsonl").read_text().strip()
        row=json.loads(manifest)
        self.assertEqual(row["commit"],self.sha)
        self.assertTrue(pathlib.Path(row["path"]).is_file())
        self.assertFalse(result["coverage_complete"])

    def test_timeout_and_invalid_name_are_fail_closed(self):
        self.assertEqual(tool.source_candidates("theorem _ : False",module="A"),[])
        with self.assertRaisesRegex(ValueError,"Invalid module"):
            tool.capture(self.repo,github_id=7,repo="owner/repo",
              commit=self.sha,module="bad;command",
              source=pathlib.Path("Pkg/Basic.lean"),out=self.root/"out",limit=1)

if __name__=="__main__":
    unittest.main()
