"""Real local-Git fixture tests for source-world staging and provenance."""
import importlib.util
import pathlib
import shutil
import sqlite3
import subprocess
import tempfile
import unittest

SCRIPT=pathlib.Path(__file__).with_name("index_jmd_lean_checkout_sources.py")
SPEC=importlib.util.spec_from_file_location("jmd_index_sources",SCRIPT)
import sys
sys.path.insert(0,str(SCRIPT.parent))
idx=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(idx)
from build_jmd_lean_ast_world import connect, import_repositories, report

@unittest.skipUnless(shutil.which("git"),"Git required")
class SourceIntakeTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.dir=pathlib.Path(self.tmp.name)
        self.db=self.dir/"canonical.sqlite3"
        sqlite3.connect(self.db).close()
        self.conn=connect(self.db)
        self.addCleanup(self.conn.close)
        self.manifest=self.dir/"manifest.csv"
        self.manifest.write_text(
            "github_id,full_name,default_branch,language\n"
            "42,test/lean-example,main,Lean\n")
        with self.conn: import_repositories(self.conn,self.manifest,"unit")
        self.root=self.dir/"checkout"
        self.root.mkdir()
        self.git("init")
        self.git("config","user.email","test@invalid.local")
        self.git("config","user.name","Local Fixture")
        self.git("remote","add","origin","https://github.com/test/lean-example.git")
        (self.root/"Example.lean").write_text(
            "theorem example : True := True.intro\n")
        self.git("add","Example.lean")
        self.git("commit","-m","source")
        self.item={"github_id":42,"full_name":"test/lean-example",
                   "checkout":str(self.root)}

    def git(self,*args):
        return subprocess.run(["git",*args],cwd=self.root,
                              capture_output=True,text=True,check=True).stdout.strip()

    def test_track_real_source_without_AST_promotion(self):
        with self.conn:
            result=idx.index_one(self.conn,self.item)
        self.assertEqual(result["tracked_lean_files"],1)
        self.assertFalse(result["elaborated_ast"])
        counts=report(self.conn)
        self.assertEqual(counts["git_tracked_lean_sources"],1)
        self.assertEqual(counts["native_ast_nodes"],0)
        stage=self.conn.execute(
            "SELECT stage FROM jmd_lean_world_repositories WHERE github_id=42"
        ).fetchone()[0]
        self.assertEqual(stage,"source-inventory")

    def test_wrong_origin_fails(self):
        self.git("remote","set-url","origin","https://github.com/someone/else.git")
        with self.assertRaisesRegex(ValueError,"origin"):
            idx.index_one(self.conn,self.item)

    def test_dirty_source_fails(self):
        (self.root/"Example.lean").write_text("theorem t : True := True.intro\n")
        with self.assertRaisesRegex(ValueError,"modified"):
            idx.index_one(self.conn,self.item)

    def test_idempotent_same_revision(self):
        with self.conn:
            idx.index_one(self.conn,self.item)
            idx.index_one(self.conn,self.item)
        self.assertEqual(report(self.conn)["git_tracked_lean_sources"],1)

    def test_reject_wrong_numeric_identity(self):
        with self.assertRaisesRegex(ValueError,"numeric ID"):
            idx.index_one(self.conn,{**self.item,"github_id":43})

    def test_accept_source_change_at_new_pinned_commit(self):
        with self.conn: idx.index_one(self.conn,self.item)
        (self.root/"Example.lean").write_text("theorem t : True := True.intro\n")
        self.git("add","Example.lean")
        self.git("commit","-m","new-source")
        with self.conn: idx.index_one(self.conn,self.item)
        self.assertEqual(report(self.conn)["git_tracked_lean_sources"],2)

if __name__=="__main__":
    unittest.main()
