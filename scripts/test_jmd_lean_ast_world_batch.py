"""Source-to-native-AST batch integration regressions (no real Lean required)."""
import importlib.util
import json
import pathlib
import sqlite3
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT=pathlib.Path(__file__).parent

def load(name,key):
    spec=importlib.util.spec_from_file_location(key,ROOT/name)
    mod=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

world=load("build_jmd_lean_ast_world.py","jmd_world")
intake=load("jmd_lean_world_intake_queue.py","jmd_intake")
batch=load("jmd_lean_ast_world_batch.py","jmd_batch")

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
        (self.repo/"Pkg"/"Basic.lean").write_text("theorem foo : True := by trivial\n")
        git(self.repo,"add",".")
        git(self.repo,"commit","-m","fixture")
        self.sha=git(self.repo,"rev-parse","HEAD")
        self.db_path=self.root/"existing.sqlite3"
        sqlite3.connect(self.db_path).close()
        self.db=world.connect(self.db_path)
        self.addCleanup(self.db.close)
        self.csv=self.root/"repos.csv"
        self.csv.write_text("github_id,full_name,default_branch,language\n"
                            "7,owner/repo,main,Lean\n")
        with self.db:world.import_repositories(self.db,self.csv,"fixture")
        self.row={"github_id":7,"repository":"owner/repo",
                  "checkout":str(self.repo),"commit":self.sha}
        self.output=self.root/"output"

    def test_inventory_only_never_executes_foreign_build(self):
        with patch.object(batch.exporter,"capture",side_effect=AssertionError("Must not run")):
            result=batch.run_batch(self.db,[self.row],self.output,capture=False)
        self.assertEqual(result["repositories_blocked"],0)
        self.assertEqual(result["source_files_inventoried"],1)
        self.assertEqual(result["ast_exports_imported"],0)
        self.assertEqual(result["proofs_certified"],0)
        self.assertEqual(world.report(self.db)["git_tracked_lean_sources"],1)

    def test_wrong_checkout_identity_blocks_without_promotion(self):
        bad={**self.row,"repository":"other/repo"}
        result=batch.run_batch(self.db,[bad],self.output,capture=False)
        self.assertEqual(result["repositories_blocked"],1)
        self.assertEqual(result["ast_exports_imported"],0)
        self.assertEqual(result["proofs_certified"],0)

    def test_mock_export_is_still_nonproof(self):
        native=self.root/"fake-native.ndjson"
        rows=[
            {"meta":{"format":{"version":"3.1.0"},
                     "exporter":{"version":"3.1.0"},
                     "lean":{"githash":"b"*40}}},
            {"in":1,"str":{"pre":0,"str":"Pkg"}},
            {"in":2,"str":{"pre":1,"str":"foo"}},
            {"ie":0,"sort":0},
            {"thm":{"name":2,"type":0,"value":0}},
        ]
        native.write_text("".join(json.dumps(x)+"\n" for x in rows))
        def fake_capture(*args,**kwargs):
            directory=kwargs["out"]
            directory.mkdir(parents=True,exist_ok=True)
            manifest=directory/"exports.jsonl"
            manifest.write_text(json.dumps({"github_id":7,"full_name":"owner/repo",
                "commit":self.sha,"module":"Pkg.Basic","path":str(native)})+"\n")
            return {"manifest":str(manifest)}
        with patch.object(batch.exporter,"capture",side_effect=fake_capture):
            result=batch.run_batch(self.db,[self.row],self.output,capture=True,
                                   max_modules=1)
        self.assertEqual(result["repositories_blocked"],0)
        self.assertEqual(result["ast_exports_imported"],1)
        self.assertEqual(world.report(self.db)["declarations"],1)
        self.assertEqual(world.report(self.db)["ast_exports_with_git_source_attestation"],1)
        self.assertEqual(result["proofs_certified"],0)

    def test_duplicate_source_checkpoint_rejected(self):
        path=self.root/"checkouts.jsonl"
        path.write_text(json.dumps(self.row)+"\n"+json.dumps(self.row)+"\n")
        with self.assertRaisesRegex(ValueError,"Duplicate"):
            batch.read_local_checkouts(path,10)

    def test_limits_fail_closed(self):
        with self.assertRaises(ValueError):
            batch.run_batch(self.db,[self.row],self.output,capture=False,
                            max_declarations=0)

if __name__=="__main__":
    unittest.main()
