"""Offline regression of local pinned Lean source inventory and AST queue."""
import importlib.util
import pathlib
import sqlite3
import subprocess
import tempfile
import unittest
from unittest.mock import patch

WORLD=pathlib.Path(__file__).with_name("build_jmd_lean_ast_world.py")
INTAKE=pathlib.Path(__file__).with_name("jmd_lean_world_intake_queue.py")
spec=importlib.util.spec_from_file_location("jmd_ast_world",WORLD)
world=importlib.util.module_from_spec(spec)
spec.loader.exec_module(world)
spec2=importlib.util.spec_from_file_location("jmd_lean_world_intake",INTAKE)
intake=importlib.util.module_from_spec(spec2)
spec2.loader.exec_module(intake)

def git(root,*args):
    return subprocess.run(["git",*args],cwd=root,capture_output=True,
                          text=True,check=True).stdout.strip()

class IntakeTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root=pathlib.Path(self.tmp.name)
        self.repo=self.root/"repo"
        self.repo.mkdir()
        git(self.repo,"init")
        git(self.repo,"config","user.email","tests@invalid.example")
        git(self.repo,"config","user.name","Local Test")
        git(self.repo,"remote","add","origin","https://github.com/owner/repo.git")
        (self.repo/"Pkg").mkdir()
        (self.repo/"Pkg"/"Basic.lean").write_text(
            "namespace Pkg\n theorem tautology (p : Prop) : p → p := by intro h; exact h\nend Pkg\n")
        (self.repo/"Pkg"/"Alpha.lean").write_text("import Pkg.Basic\n")
        git(self.repo,"add",".")
        git(self.repo,"commit","-m","fixture")
        self.sha=git(self.repo,"rev-parse","HEAD")
        self.db=self.root/"dashi.sqlite3"
        sqlite3.connect(self.db).close()
        self.conn=world.connect(self.db)
        self.addCleanup(self.conn.close)
        with self.conn:
            self.conn.execute("""INSERT INTO jmd_lean_world_repositories
              (github_id,full_name,default_branch,primary_language,
               starred,global_discovered,corpus_snapshot)
              VALUES(9,'owner/repo','main','Lean',1,1,'fixture')""")

    def test_inventory_writes_real_blob_and_sha(self):
        with self.conn:
            out=intake.scan(self.conn,self.repo,9,self.sha)
        self.assertEqual(out["tracked_lean_sources"],2)
        rows=self.conn.execute("""SELECT source_path,sha256,git_blob_sha
            FROM jmd_lean_world_source_files ORDER BY source_path""").fetchall()
        self.assertEqual(len(rows),2)
        self.assertEqual(len(rows[0][1]),64)
        self.assertEqual(len(rows[0][2]),40)
        self.assertEqual(world.report(self.conn)["metadata_only_repositories"],0)

    def test_missing_commit_rejected(self):
        with self.assertRaisesRegex(ValueError,"immutable full commit"):
            intake.scan(self.conn,self.repo,9,"a"*40)

    def test_wrong_remote_rejected(self):
        git(self.repo,"remote","set-url","origin","https://github.com/other/repo.git")
        with self.assertRaisesRegex(ValueError,"identity differs"):
            intake.scan(self.conn,self.repo,9,self.sha)

    def test_dirty_tracked_input_rejected(self):
        (self.repo/"Pkg"/"Basic.lean").write_text("changed\n")
        with self.assertRaisesRegex(ValueError,"dirty"):
            intake.scan(self.conn,self.repo,9,self.sha)

    def test_module_hints_do_not_pretend_to_be_ast(self):
        with self.conn: intake.scan(self.conn,self.repo,9,self.sha)
        rows=intake.source_worklist(self.conn,9,self.sha)
        self.assertEqual({r["candidate_module"] for r in rows},
                         {"Pkg.Basic","Pkg.Alpha"})
        self.assertTrue(all(not r["module_proven"] for r in rows))
        self.assertTrue(all(r["requires_environment_elaboration"] for r in rows))

    def test_repeated_source_ingest_is_idempotent(self):
        with self.conn:
            intake.scan(self.conn,self.repo,9,self.sha)
            intake.scan(self.conn,self.repo,9,self.sha)
        self.assertEqual(self.conn.execute(
            "SELECT COUNT(*) FROM jmd_lean_world_source_files").fetchone()[0],2)

    def test_source_hint_is_not_lean_module_proof(self):
        self.assertEqual(intake.source_module_hint("Pkg/Basic.lean"),"Pkg.Basic")
        self.assertEqual(intake.source_module_hint("src/Pkg/Basic.lean"),"Pkg.Basic")
        self.assertEqual(intake.source_module_hint("src/Pkg/odd-name.lean"),"")

if __name__=="__main__":
    unittest.main()
